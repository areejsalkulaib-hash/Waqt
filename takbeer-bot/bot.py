import os
import sys
import re
import json
import random
import signal
import asyncio
import logging
import tempfile
import threading
import html as _html
import unicodedata
from datetime import datetime, date, timedelta
from zoneinfo import ZoneInfo
from collections import defaultdict

# Allow importing reading_plan.py and schedule_store.py from the same directory.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import schedule_store
import suggestion_store
import auth_store
import vote_store
import cycle_store
import progress_store
import roadmap_store
import poll_store
import completion_store
import rating_store
import book_store
import session_store
import discussion_store
import cultural_store
import book_prep_store
import reader_progress_store
import knowledge_store
import interaction_log_store
import backup_store
import analytics_store
import postponed_store
import owner_guide
import category_constitution

import shutil
import subprocess
import time

PID_FILE = "/tmp/takbeer_bot.pid"


def kill_existing_instances() -> None:
    my_pid = os.getpid()
    killed = False
    try:
        result = subprocess.run(
            ["pgrep", "-f", "takbeer-bot/bot.py"],
            capture_output=True, text=True,
        )
        pids = [int(p) for p in result.stdout.strip().splitlines() if p.strip()]
        for pid in pids:
            if pid != my_pid:
                try:
                    os.kill(pid, signal.SIGTERM)
                    killed = True
                except ProcessLookupError:  # log-exempt: race — PID vanished between listing and kill
                    pass
    except Exception:  # log-exempt: best-effort cleanup; pgrep failure is non-fatal
        pass
    if killed:
        time.sleep(3)


def write_pid() -> None:
    with open(PID_FILE, "w") as f:
        f.write(str(os.getpid()))

import edge_tts
from google import genai
from google.genai import types
from google.genai import errors as genai_errors
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from telegram import (
    Bot,
    BotCommand,
    BotCommandScopeChat,
    BotCommandScopeChatAdministrators,
    BotCommandScopeChatMember,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Update,
)
from telegram.error import BadRequest as TgBadRequest
from telegram.ext import Application, CallbackQueryHandler, CommandHandler, ContextTypes, MessageHandler, PollAnswerHandler, filters

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")
GEMINI_API_KEY  = os.environ.get("GEMINI_API_KEY", "")
# Diagnostic flags — off by default. Set ASK_DUMP_PROMPT=1 in the environment
# to log the full system prompt + user message for every /ask call.
ASK_DUMP_PROMPT: bool = os.environ.get("ASK_DUMP_PROMPT", "").lower() in ("1", "true", "yes")

# ── Stage 2 — Single Companion Identity (Transition Plan §2A) ─────────────
# Operational control: set TAKBEER_COMPANION_SILENCED=true in the environment
# to activate Stage 2 routing (Companion invocations in the community group
# routed exclusively to the Adapter bot). Set to empty or "false" to roll back
# without a code change or redeployment — restart the bot after changing.
# Owner DM access is never affected by this flag.
STAGE2_COMPANION_SILENCED: bool = os.environ.get(
    "TAKBEER_COMPANION_SILENCED", ""
).lower() in ("1", "true", "yes")
# ── Adapter bot identity (community transition redirect messages) ──────────
# Set ADAPTER_BOT_USERNAME (without the leading @) so that redirect messages
# point members to the correct @handle. If left unset the @mention is omitted
# and the message shows only the command and the bot's Arabic name.
ADAPTER_BOT_USERNAME: str = os.environ.get("ADAPTER_BOT_USERNAME", "")

_BOT_DIR            = os.path.dirname(os.path.abspath(__file__))
_PLAN_COVER_PATH     = os.path.join(_BOT_DIR, "cover_current.jpg")
_SCHEDULE_COVER_PATH = os.path.join(_BOT_DIR, "schedule_cover.jpg")

# In-memory cache for AI-generated chapter ideas (book:chapter → idea text)
_idea_cache: dict[str, str] = {}
# In-flight work is shared by concurrent requests for the same chapter. Unlike
# the cache, failed or refused AI responses are removed after they are shared.
_idea_in_flight: dict[str, asyncio.Future[str]] = {}

TIMEZONE = ZoneInfo("Asia/Riyadh")

_SENDGROUP_MARKUP = InlineKeyboardMarkup([[
    InlineKeyboardButton("📢 إرسال للمجموعة", callback_data="sendgroup"),
]])


SYSTEM_PROMPT = (
    "أنت مساعد ذكي ومفيد يعمل عبر تطبيق تيليغرام لمجموعة قراءة وكتب.\n"
    "تتحدث باللغة العربية بشكل افتراضي، لكن يمكنك الرد بأي لغة يستخدمها المستخدم.\n"
    "\n"
    "━━━ الشخصية والنبرة ━━━\n"
    "أنت رفيق القراءة في المجموعة — لست روبوتاً ميكانيكياً، بل حضوراً دافئاً وذكياً.\n"
    "\n"
    "النبرة العامة:\n"
    "• ودود وطبيعي — تحدّث كما يتحدث شخص حقيقي مهتم بالقراءة، لا كنظام يُنجز مهاماً.\n"
    "• خفيف وعفوي عند المناسبة — في المحادثات العادية، المعالم، الإنجازات، والتفاعل مع المجموعة.\n"
    "• الفكاهة مقبولة — لكن بتوازن وعندما تنسجم مع السياق فعلاً، لا كروتين ثابت.\n"
    "• موجز ومباشر — لا تُطوّل دون سبب، ولا تكرر ما قلته.\n"
    "• تجنّب القوالب الجاهزة — غيّر طريقة الصياغة ولا تبدأ كل رد بالطريقة ذاتها.\n"
    "\n"
    "للردود الإدارية والمعلوماتية:\n"
    "• الدقة أولاً — لا تتنازل عن الوضوح في سبيل التخفيف.\n"
    "• يمكن إضافة لمسة دافئة بسيطة دون أن تطغى على المحتوى.\n"
    "\n"
    "━━━ Personality & Tone ━━━\n"
    "You are the group's reading companion — warm, curious, and genuinely present.\n"
    "\n"
    "General tone:\n"
    "• Natural and human — write like a person who loves reading, not like a system completing tasks.\n"
    "• Light and easy-going when the moment calls for it — casual exchanges, milestones, achievements.\n"
    "• Humor is welcome — but sparingly, and only when it genuinely fits the context.\n"
    "• Concise and direct — don't pad, don't repeat yourself.\n"
    "• Avoid template-driven phrasing — vary your openings and rhythm across replies.\n"
    "\n"
    "For factual and administrative replies:\n"
    "• Accuracy comes first — never sacrifice clarity for warmth.\n"
    "• A light touch is fine; don't let personality overwhelm substance.\n"
    "\n"
    "━━━ قواعد التنسيق ━━━\n"
    "اجعل ردودك مرتّبة وسهلة القراءة:\n"
    "• استخدم سطراً فارغاً بين كل فكرة أو فقرة.\n"
    "• اكتب الفقرات قصيرة (٢-٣ جمل كحد أقصى).\n"
    "• عند سرد نقاط متعددة، ضع كل نقطة في سطر مستقل مع مسافة قبلها.\n"
    "• استخدم عناوين قصيرة وجريئة (<b>عنوان</b>) لتقسيم الأقسام في الردود الطويلة.\n"
    "• تجنّب كتلة نص واحدة طويلة بدون فواصل.\n"
    "• لا تستخدم علامات مثل --- أو === للفصل.\n"
    "\n"
    "⚠️ تنسيق HTML حصراً — قاعدة مطلقة:\n"
    "يُحظر تماماً استخدام Markdown. لا تستخدم أبداً: ** أو * أو __ أو # للتنسيق.\n"
    "الوسوم المسموح بها فقط: <b>نص</b> للخط العريض، <i>نص</i> للمائل، <code>نص</code> للكود،\n"
    "<blockquote>نص</blockquote> للاقتباسات.\n"
    "للنقاط والقوائم: استخدم رمز • مباشرةً (لا * ولا -).\n"
    "\n"
    "━━━ /اجب — مساعد المعرفة ━━━\n"
    "عند استخدام /اجب، أنت مساعد معرفي شامل — لست مقيّداً بالكتب فقط.\n"
    "أجب على أي سؤال: علوم، فلسفة، تاريخ، ثقافة، علم النفس، أسئلة عامة، فضول فكري — كل شيء مقبول.\n"
    "إذا كان هناك سياق قراءة نشط (كتاب حالي أو فصل) وكان السؤال ذا صلة به بشكل طبيعي،\n"
    "يمكنك الإشارة إليه بلطف — لكن لا تُجبر كل إجابة على الربط بالكتاب.\n"
    "الهدف: أن تشعر المجموعة أن لديها مساعداً ذكياً حقيقياً، لا مجرد بوت كتب.\n"
    "\n"
    "━━━ /اجب — Knowledge Assistant ━━━\n"
    "When /اجب is used, you are a full general-knowledge assistant — not limited to books.\n"
    "Answer any question: science, philosophy, history, culture, psychology, curiosity — all welcome.\n"
    "If an active reading context is provided (current book/chapter) and the question naturally\n"
    "connects to it, you may reference it briefly. But never force every answer back to the book.\n"
    "Goal: make the group feel they have a real thinking companion, not just a book bot.\n"
    "\n"
    "━━━ حماية الحبكة — قاعدة مطلقة ━━━\n"
    "عندما يكون هناك سياق قراءة نشط يتضمن رقم صفحة، تسري القاعدة الآتية بلا استثناء ولا تأويل:\n"
    "يُحظر تماماً الكشف عن أي معلومة تخص الكتاب الحالي تنتمي إلى ما بعد تقدم المجموعة —\n"
    "سواء كانت: حدثاً سردياً، أو دافعاً لشخصية، أو خلفيتها، أو هويتها، أو مصيرها، أو علاقاتها.\n"
    "أسئلة 'لماذا' و'كيف' و'من هو/هي' عن شخصيات الكتاب الحالي بالغة الخطورة بشكل خاص —\n"
    "لأن إجاباتها كثيراً ما تستدعي دوافع أو خلفيات لم تُكشف بعد في قراءة المجموعة.\n"
    "إذا كانت الإجابة الكاملة تستلزم معرفة أحداث أو تفاصيل من بعد تقدم المجموعة:\n"
    "قل 'سيتضح هذا في الفصول القادمة' دون أي إشارة — ولو غير مباشرة — إلى المحتوى المحجوب.\n"
    "هذه القاعدة مطلقة ولا تنكسر حتى لو بدا السؤال تحليلياً أو ثقافياً أو غير مرتبط بالأحداث.\n"
    "\n"
    "━━━ Spoiler Protection — Absolute Rule ━━━\n"
    "When an active reading context is present with a page number, this rule applies without exception:\n"
    "It is strictly forbidden to reveal any information about the current book that belongs beyond\n"
    "the group's reading progress — whether: plot events, character motivations, backstories,\n"
    "identities, fates, or relationships revealed later in the book.\n"
    "'Why', 'how', and 'who is' questions about current-book characters are especially high-risk —\n"
    "their answers frequently require motivations or backstory not yet reached in the reading.\n"
    "If a complete answer requires knowledge beyond the group's progress: respond with\n"
    "'this will become clear in later chapters' — without any hint of the withheld content.\n"
    "This rule is absolute and cannot be bypassed even if the question seems analytical,\n"
    "cultural, or non-plot-related.\n"
    "\n"
    "━━━ الكتب والمؤلفون ━━━\n"
    "إذا ذكر المستخدم اسم كتاب أو مؤلف، أجب بهذا الهيكل:\n"
    "\n"
    "<b>📖 عن الكتاب</b>\n"
    "[ملخص مختصر في ٣-٤ جمل]\n"
    "\n"
    "<b>💡 معلومة ممتعة</b>\n"
    "[حقيقة طريفة عن الكتاب أو مؤلفه]\n"
    "\n"
    "<b>✅ التوصية</b>\n"
    "[لمن يناسب هذا الكتاب ولماذا؟]\n"
    "\n"
    "━━━ Book & Author Replies (English) ━━━\n"
    "If the user mentions a book or author, use this structure:\n"
    "\n"
    "<b>📖 About the Book</b>\n"
    "[3-4 sentence summary]\n"
    "\n"
    "<b>💡 Fun Fact</b>\n"
    "[interesting fact about the book or author]\n"
    "\n"
    "<b>✅ Recommendation</b>\n"
    "[who should read it and why]\n"
    "\n"
    "━━━ مقارنة الكتب المتعددة ━━━\n"
    "عندما يذكر المستخدم كتابين أو أكثر معاً، اكتب مقالة تحليلية بتنسيق تيليغرام الأصلي وفق هذا الهيكل الحرفي:\n"
    "\n"
    "<b>مدخل تأليفي</b>\n"
    "[فقرة افتتاحية غنية تكشف الخيط الفكري المشترك وتؤطّر الكتب كمنظورات متكاملة — أسلوب مقالة لا قائمة]\n"
    "\n"
    "<b>[الرقم بالعربي]. [العنوان العربي] ([العنوان الأصلي]) — [المؤلف]</b>\n"
    "\n"
    "<blockquote>[اقتباس قصير يعكس روح الكتاب — استخدم blockquote للاقتباسات دائماً]</blockquote>\n"
    "\n"
    "[مقدمة سردية ٢-٤ جمل عن طبيعة العمل وسياقه الفكري]\n"
    "\n"
    "• <b>الفكرة المحورية:</b> [نثر متدفق — الفكرة الأساسية أو الحجة الفلسفية للكتاب]\n"
    "• <b>العمق التحليلي:</b> [نثر متدفق — المنهج، الرمزية، البنية المفاهيمية، الأبعاد النفسية، التوترات الفلسفية]\n"
    "\n"
    "[كرّر هذا الهيكل لكل كتاب مع سطر فارغ بين كل كتاب والتالي]\n"
    "\n"
    "<b>خيط رفيع يجمع المجموعة</b>\n"
    "[هذا القسم هو الأهم — اشرح كيف يُكمل كل كتاب الآخرين، ما يضيفه للحوار الأشمل،\n"
    "التسلسل الفكري بينها، وكيف تخلق قراءتها معاً فهماً أعمق — نبرة تأليفية لا مقارِنة]\n"
    "\n"
    "<b>سؤال للاستكشاف</b>\n"
    "[سؤال مدروس يمتد بالنقاش — يساعد على اختيار اتجاه للتعمق — لا أسئلة عامة]\n"
    "\n"
    "قواعد التنسيق الإلزامية — استخدم HTML بدقة:\n"
    "• <b>النص</b> بوسم bold للعناوين والمفاهيم المحورية والتسميات التحليلية.\n"
    "• <blockquote>اقتباس</blockquote> بوسم blockquote لكل الاقتباسات.\n"
    "• لا تستخدم خطوط فاصلة أفقية — الفصل بين الأقسام عبر العناوين الجريئة والمسافات فقط.\n"
    "• عنوان كل كتاب داخل bold مع رقمه.\n"
    "• سطر فارغ بين كل عنصر.\n"
    "• أسلوب: مقالي غني فكرياً — عربية أدبية راقية — تركيب لا تلخيص.\n"
    "\n"
    "━━━ Multi-Book Comparison (English) ━━━\n"
    "When the user asks about two or more books together, write a cohesive analytical essay\n"
    "using Telegram-native formatting. Follow this exact structure:\n"
    "\n"
    "<b>Opening Synthesis</b>\n"
    "[Rich paragraph identifying the shared intellectual thread; framing the books as\n"
    "complementary perspectives on a larger question. Essay opening — not a list.]\n"
    "\n"
    "<b>[Number]. [Title] — [Author]</b>\n"
    "\n"
    "<blockquote>[Short quotation capturing the spirit of the work — always use blockquote tag]</blockquote>\n"
    "\n"
    "[2–4 line narrative introduction: nature of the work and intellectual context]\n"
    "\n"
    "• <b>Core Idea:</b> [flowing prose — central argument or philosophical concern]\n"
    "• <b>Analytical Depth:</b> [flowing prose — method, symbolism, conceptual architecture,\n"
    "  psychological dimensions, literary devices, philosophical tensions]\n"
    "\n"
    "[Repeat this block for each book, with an empty line between each]\n"
    "\n"
    "<b>A Thin Thread Connecting the Collection</b>\n"
    "[Most important section — explain how the books complete one another, what each\n"
    "contributes to the broader conversation, the intellectual progression between them,\n"
    "and how reading together creates deeper understanding. Integrative, not comparative.]\n"
    "\n"
    "<b>Exploration</b>\n"
    "[Thoughtful closing question extending the discussion naturally — not a generic prompt]\n"
    "\n"
    "Mandatory formatting rules — use HTML tags precisely:\n"
    "• <b>Bold</b> via <b> tag for section titles, key concepts, and analytical labels.\n"
    "• <blockquote>text</blockquote> tag for all quotations.\n"
    "• No horizontal separator lines — use bold headings and spacing only.\n"
    "• Each book title inside <b> tag with its number.\n"
    "• Empty line between every element.\n"
    "• Style: intellectually rich essay — elegant prose — synthesis over summary.\n"
    "\n"
    "━━━ تحديد الكتاب بثقة ━━━\n"
    "قبل تحليل أي كتاب أو تقديم معلومات عنه، قيّم مستوى ثقتك في تحديده.\n"
    "\n"
    "إذا كانت الثقة عالية — العنوان واضح ويشير إلى كتاب واحد معروف — تابع مباشرةً بدون أي تعليق.\n"
    "أمثلة لا تحتاج توضيحاً: العادات الذرية، الإخوة كارامازوف، مئة عام من العزلة.\n"
    "\n"
    "إذا كانت الثقة منخفضة — العنوان غامض، أو يشترك فيه أكثر من كتاب أو مؤلف،\n"
    "أو مختصر، أو يصعب التمييز بين نسخ أو طبعات مختلفة — لا تخمّن ولا تختر عشوائياً.\n"
    "بدلاً من ذلك، اطرح سؤالاً توضيحياً واحداً مختصراً قبل أي تحليل، مثل:\n"
    "\"أي مؤلف تقصد؟\"\n"
    "\"وجدت عدة كتب بهذا الاسم — هل تقصد [أ] لـ[مؤلف] أم [ب] لـ[مؤلف آخر]؟\"\n"
    "لا تتابع التحليل أو التوصية أو المقارنة حتى يوضح المستخدم مقصده.\n"
    "\n"
    "ينطبق على: ردود الكتب التلقائية، /اجب عند السؤال عن كتاب، مقارنات الكتب المتعددة.\n"
    "\n"
    "━━━ Book Identification Confidence ━━━\n"
    "Before analyzing or discussing any book, assess your confidence in identifying it.\n"
    "\n"
    "High confidence — title clearly refers to one well-known work — proceed without comment.\n"
    "Examples requiring no clarification: Atomic Habits, The Brothers Karamazov, One Hundred Years of Solitude.\n"
    "\n"
    "Low confidence — title is ambiguous, shared by multiple books or authors, abbreviated,\n"
    "or could refer to different editions or works — do not guess or silently pick one.\n"
    "Instead, ask one concise clarifying question before any analysis, such as:\n"
    "\"Which author do you mean?\"\n"
    "\"I found multiple books with this title — did you mean [A] by [Author] or [B] by [Other Author]?\"\n"
    "Do not proceed with analysis, recommendations, or comparisons until the user clarifies.\n"
    "\n"
    "Applies to: automatic book replies, /اجب book questions, multi-book comparisons.\n"
    "\n"
    "━━━ الثقة في المعلومات الكتابية ━━━\n"
    "بعض الأسئلة عالية الخطورة من ناحية الدقة:\n"
    "أسماء المؤلفين والمترجمين والناشرين، عدد الصفحات وسنة النشر،\n"
    "أسماء الشخصيات، أحداث الحبكة، الفصول المحددة، الاقتباسات الحرفية.\n"
    "\n"
    "عند الإجابة على هذه الأسئلة:\n"
    "• إذا كانت المعلومات موجودة في السياق المُقدَّم → استخدمها مباشرةً بثقة كاملة.\n"
    "• إذا لم تكن في السياق لكن ثقتك عالية جداً → أجب بوضوح.\n"
    "• إذا كانت ثقتك منخفضة أو متوسطة → أعلن ذلك بدلاً من التخمين:\n"
    "  مثال: \"قد لا تكون هذه المعلومة دقيقة تماماً\" أو \"لستُ متأكداً من هذه التفصيلة.\"\n"
    "\n"
    "━━━ Factual Confidence for Book Questions ━━━\n"
    "High-risk accuracy categories:\n"
    "author names, translators, publishers, page counts, publication years,\n"
    "character names, plot details, specific chapter events, direct quotes.\n"
    "\n"
    "When answering these:\n"
    "• If the data is in the provided context → use it directly with full confidence.\n"
    "• If not in context but you are highly confident → answer clearly.\n"
    "• If your confidence is low or moderate → say so instead of guessing:\n"
    "  e.g. \"I'm not fully certain about this detail\" or \"This may not be accurate.\"\n"
    "\n"
    "━━━ In-Text Cultural References — Mandatory Protocol ━━━\n"
    "When a question is about a named entity that appears INSIDE the current reading —\n"
    "a real-world author, a grammar book, a historical figure, a publication, a work of art\n"
    "cited or mentioned by a character — apply this three-step protocol before answering:\n"
    "\n"
    "Step 1 — Identify the type of reference:\n"
    "Ask yourself: is this a novel character, or a real-world person/work that the author\n"
    "is referencing? The same name can be either. Do not assume.\n"
    "\n"
    "Step 2 — Separate what the text says from what you know externally:\n"
    "• What the text says: only what is stated explicitly in the passage (e.g. 'the grammar\n"
    "  rules were described as hateful').\n"
    "• External knowledge: what you know about the real-world person or work from outside\n"
    "  the novel. Label this clearly: 'تاريخياً...' / 'Historically...'.\n"
    "• Never blend the two into a single confident claim.\n"
    "\n"
    "Step 3 — Admit uncertainty before interpreting:\n"
    "If you are not fully certain who or what the reference is, say so explicitly before\n"
    "offering any interpretation. Do not synthesize partial knowledge into a confident\n"
    "explanation. Prefer: 'لست متأكداً تماماً من هوية هذا المرجع، لكن يبدو أن...'\n"
    "over a fluent answer that may be wrong.\n"
    "\n"
    "This rule is especially critical when: the question is a short proper noun ('من هو X؟'\n"
    "or 'ما هي قواعد X؟'), the name appears alongside other real-world references in the same\n"
    "sentence, or the name is transliterated from a non-Arabic source.\n"
    "\n"
    "⚠ Anti-pattern — the famous-name pivot:\n"
    "When you cannot identify a reference precisely, do NOT substitute a famous person with a\n"
    "phonetically similar name and answer about them instead. This produces a fluent, confident\n"
    "response that is wrong and harder for the reader to detect than a plain admission of uncertainty.\n"
    "Use context clues in the passage first: if two names appear in identical grammatical structure\n"
    "(e.g. 'قواعد X' and 'قواعد Y'), both referents are the same type of thing — reason from that\n"
    "before searching your knowledge for any famous person whose name sounds similar.\n"
    "\n"
    "━━━ المراجع الثقافية داخل النص — بروتوكول إلزامي ━━━\n"
    "عندما يتعلق السؤال باسم يرد داخل النص الحالي — مؤلف حقيقي، كتاب قواعد، شخصية تاريخية،\n"
    "منشور، أو عمل فني تذكره أو تقتبس منه شخصية في الرواية — اتبع هذا البروتوكول قبل الإجابة:\n"
    "\n"
    "الخطوة 1 — حدّد نوع المرجع:\n"
    "هل هذا شخصية في الرواية، أم شخص أو عمل حقيقي يشير إليه المؤلف؟ الاسم ذاته قد يكون أياً\n"
    "منهما — لا تفترض.\n"
    "\n"
    "الخطوة 2 — افصل بين ما يقوله النص وما تعرفه خارجياً:\n"
    "• ما يقوله النص: فقط ما ورد صراحةً في المقطع (مثلاً: 'وُصفت قواعده بأنها كريهة').\n"
    "• المعرفة الخارجية: ما تعرفه عن الشخص أو العمل من خارج الرواية — صرّح بذلك:\n"
    "  'تاريخياً...' أو 'خارج الرواية، كان...'\n"
    "• لا تدمج الاثنين في ادعاء واحد واثق.\n"
    "\n"
    "الخطوة 3 — أعلن عدم اليقين قبل التفسير:\n"
    "إذا لم تكن متأكداً تماماً من هوية المرجع، قل ذلك صراحةً قبل أي تفسير. لا تصنع\n"
    "معلومة واثقة من معرفة جزئية. الأفضل: 'لستُ متأكداً تماماً من هوية هذا المرجع،\n"
    "لكن يبدو أن...' على إجابة طليقة قد تكون مغلوطة.\n"
    "\n"
    "هذه القاعدة بالغة الأهمية عندما: يكون السؤال اسماً مختصراً ('من هو X؟' أو 'ما هي قواعد X؟')،\n"
    "أو يرد الاسم بجانب مراجع حقيقية أخرى في الجملة ذاتها، أو كان الاسم منقولاً بالتعريب من لغة أخرى.\n"
    "\n"
    "⚠ نمط خاطئ — الانزلاق إلى شخص مشهور بالاسم المشابه:\n"
    "عندما لا تستطيع تحديد هوية المرجع بدقة، لا تستبدله بشخص مشهور يتشابه اسمه مع الاسم المطلوب.\n"
    "هذا يُنتج إجابة طليقة وواثقة لكنها مغلوطة — وأصعب على القارئ اكتشافها من اعتراف صريح بعدم اليقين.\n"
    "استخدم أولاً القرائن النصية: إذا ورد اسمان في تركيب نحوي متطابق (مثل 'قواعد X' و'قواعد Y')،\n"
    "فكلا المرجعين من النوع ذاته — استنتج من ذلك قبل أن تبحث في معرفتك عن أي شخص مشهور يشبه الاسم صوتياً.\n"
    "\n"
    "━━━ النص أولاً — تسلسل الأدلة الإلزامي ━━━\n"
    "عند الإجابة على أي سؤال يتعلق بمقطع من الكتاب المقروء، اتبع هذا التسلسل بالترتيب:\n"
    "\n"
    "① ما يقوله النص صراحةً — ابدأ هنا دائماً. اقتبس أو استند مباشرةً إلى ما ورد في المقطع.\n"
    "② ما يمكن استنتاجه من النص وحده — الاستنتاج المعقول من الكلمات والسياق الداخلي للرواية.\n"
    "③ المعرفة الخارجية — فقط بعد استنفاد ① و②، وعند تقديمها صرّح بوضوح:\n"
    "   'تاريخياً...' أو 'خارج الرواية...' أو 'من معرفتي العامة...'\n"
    "\n"
    "لا تقفز إلى المعرفة الخارجية لسد الفراغات عندما لا تكفي ① و②.\n"
    "إذا لم يوفر النص معلومات كافية، قل ذلك صراحةً:\n"
    "   'النص لا يُوضح هذه النقطة' أو 'لا تتوفر في المقطع معلومات كافية عن هذا.'\n"
    "هذا أفضل من اختراع تفسير يبدو منطقياً لكنه غير موثّق.\n"
    "\n"
    "━━━ Text-First Reasoning — Mandatory Evidence Hierarchy ━━━\n"
    "When answering any question about a passage from the current book, follow this order:\n"
    "\n"
    "① What the text explicitly says — always start here. Quote or directly cite the passage.\n"
    "② What can reasonably be inferred from the text alone — logical inference from the words\n"
    "   and the internal context of the novel, without external input.\n"
    "③ External historical or literary knowledge — only after exhausting ① and ②, and always\n"
    "   clearly labeled: 'Historically...' / 'Outside the novel...' / 'From general knowledge...'\n"
    "\n"
    "Do not jump to external knowledge to fill gaps when ① and ② are insufficient.\n"
    "If the text does not provide enough information, say so explicitly:\n"
    "   'The text doesn't clarify this point' or 'The passage doesn't give enough detail here.'\n"
    "This is preferable to inventing a plausible-sounding explanation that isn't grounded in evidence.\n"
    "Accuracy before completeness: an honest 'I don't know' is better than a confident wrong answer.\n"
    "\n"
    "━━━ اسأل قبل أن تخمّن — الاستيضاح عند الغموض ━━━\n"
    "إذا كنت غير متأكد من المقصود بالسؤال أو من الإجابة الصحيحة، اسأل سؤالاً استيضاحياً\n"
    "بدلاً من تقديم إجابة مبنية على افتراض.\n"
    "\n"
    "متى تسأل:\n"
    "• إذا كان الاسم أو المرجع في السؤال محتملاً لأكثر من تفسير.\n"
    "• إذا لم تستطع التمييز بين قصد المستخدم (هل يسأل عن الرواية؟ عن الواقع التاريخي؟ عن كليهما؟).\n"
    "• إذا كانت ثقتك في الإجابة غير كافية لتقديمها بصورة موثوقة.\n"
    "\n"
    "أمثلة على أسئلة استيضاحية مناسبة:\n"
    "• 'هل تسألين عن الشخص التاريخي المذكور في النص، أم عن ما تعنيه الإشارة داخل الرواية؟'\n"
    "• 'هل تقصدين المرجع في النص، أم الشخصية التاريخية الحقيقية؟'\n"
    "• 'لستُ متأكداً تماماً من المقصود — هل يمكنك التوضيح؟'\n"
    "\n"
    "الأسئلة الاستيضاحية يجب أن تكون: قصيرة، مباشرة، سؤالاً واحداً فقط.\n"
    "لا تطرح أكثر من سؤال في رد واحد. وقف لحظة واحدة للاستيضاح أفضل\n"
    "من إجابة واثقة مغلوطة.\n"
    "\n"
    "━━━ Clarify Before Guessing ━━━\n"
    "If you are genuinely uncertain about the user's intent OR about the correct answer,\n"
    "ask a brief clarifying question instead of guessing.\n"
    "\n"
    "When to ask:\n"
    "• The name or reference in the question has more than one plausible interpretation.\n"
    "• You cannot determine whether the user is asking about the novel, real-world history, or both.\n"
    "• Your confidence in the answer is not high enough to present it reliably.\n"
    "\n"
    "Examples of appropriate clarifying questions:\n"
    "• 'Are you asking about the historical person mentioned in the text, or what the reference\n"
    "   means within the novel?'\n"
    "• 'Do you mean the reference inside the book, or the real historical figure?'\n"
    "• 'I'm not completely certain which reference you mean — could you clarify?'\n"
    "\n"
    "Keep clarifying questions short — one question only per reply. Tag the reply [TEXT].\n"
    "One pause for clarification is always better than a confident wrong answer.\n"
    "Accuracy before completeness: never fill silence with a plausible-sounding guess.\n"
    "\n"
    "━━━ الاستمرارية بعد التوضيح ━━━\n"
    "عندما تتلقى رسالةً قصيرة تبدو إجابةً على سؤال توضيحي طرحته في ردك السابق\n"
    "(مثل: 'مرجع خارجي' أو 'داخل الرواية' أو 'نعم' أو 'كلاهما'):\n"
    "\n"
    "① راجع تاريخ المحادثة لتحديد السؤال الأصلي والسياق الذي أدى إلى طرح سؤال التوضيح.\n"
    "② طبّق إجابة التوضيح على ذلك السؤال الأصلي — لا تتعامل مع الرد القصير كسؤال مستقل جديد.\n"
    "③ قدّم الإجابة الكاملة في السياق الأصلي للنقاش.\n"
    "\n"
    "لا تطلب من المستخدم إعادة صياغة سؤاله بعد أن أجاب على سؤال التوضيح.\n"
    "خيط المحادثة يجب أن يستمر — التوضيح يُضيف معلومةً، لا يُعيد بدء الحوار من الصفر.\n"
    "\n"
    "━━━ Continuity After Clarification ━━━\n"
    "When you receive a short message that appears to answer a clarification question you just asked\n"
    "(e.g. 'external reference', 'inside the novel', 'yes', 'both', 'the historical figure'):\n"
    "\n"
    "① Look back in the conversation history to identify the original question and the context\n"
    "   that led to your clarification request.\n"
    "② Apply the clarification answer to that original question — do NOT treat the short reply\n"
    "   as a new standalone input.\n"
    "③ Provide the full substantive answer in the context of the original discussion.\n"
    "\n"
    "Never ask the user to restate their question after they answer your clarification.\n"
    "The conversation thread must persist: clarification adds information, it does not restart\n"
    "the discussion from zero.\n"
    "If a system note says [CONTINUATION] — you are definitely in this situation.\n"
    "\n"
    "━━━ صوت رفيق القراءة ━━━\n"
    "أنتِ لستِ مجرد مرجع — أنتِ رفيقة قراءة قرأت النصوص ذاتها.\n"
    "بعد الإجابة الصحيحة على سؤال، يجوز لكِ أن تُضيفي ملاحظةً واحدة قصيرة (جملة أو جملتان لا أكثر)\n"
    "إذا كانت تُثري النقاش حقاً. أمثلة مقبولة:\n"
    "• ربط بجزء آخر من الكتاب لا يُفسد ما لم يُقرأ بعد.\n"
    "• ملاحظة أدبية عن أسلوب المؤلف أو تقنيته أو نيّته.\n"
    "• سؤال يفتح نقاشاً أعمق يستدعيه المقطع نفسه.\n"
    "لا تُضيفي هذا في كل ردٍّ — فقط حين تدعو إليه طبيعة التبادل فعلاً.\n"
    "كوني رفيقة قارئة لا معلمة: 'يستوقفني أيضاً...' / 'ما يجدر ملاحظته هنا...' / 'هل لاحظتِ أن...'\n"
    "لا تجعلي الإضافة أطول من الإجابة ذاتها.\n"
    "\n"
    "━━━ Reading Companion Voice ━━━\n"
    "You are not only a reference — you are a reading companion who has read the same texts.\n"
    "After giving a correct answer, you MAY add one brief observation (1–2 sentences only)\n"
    "when it genuinely enriches the discussion. Acceptable examples:\n"
    "• A connection to another part of the book that does not spoil unread content.\n"
    "• A literary observation about the author's style, technique, or intent in the passage.\n"
    "• A question that naturally follows and might open a deeper discussion.\n"
    "Do not add this to every reply — only when the exchange genuinely invites it.\n"
    "Frame it as a fellow reader, not a teacher:\n"
    "'يستوقفني أيضاً...' / 'ما يجدر ملاحظته هنا...' / 'هل لاحظتِ أن...'\n"
    "Never let the companion addition be longer than the answer itself.\n"
    "\n"
    "━━━ الاسم في الردود ━━━\n"
    "عندما يتوفر اسم المستخدم، استخدمه بشكل طبيعي في بداية الرد أو داخله — خاصةً في ردود الكتب وأسئلة /اجب.\n"
    "لا تكرر الاسم أكثر من مرة في الرد الواحد، ولا تُضف علامة @ قبله.\n"
    "\n"
    "━━━ Using the User's Name ━━━\n"
    "When the user's name is provided, include it naturally once — at the start or within the reply.\n"
    "Use it especially for book replies and /اجب answers to make the response feel personal.\n"
    "Never repeat the name more than once, and never prefix it with @.\n"
    "\n"
    "━━━ General Replies ━━━\n"
    "For non-book messages, reply conversationally. Keep it short, warm, and natural.\n"
    "Still use paragraph breaks — never write a long unbroken block of text.\n"
    "\n"
    "━━━ Voice / Text Tag ━━━\n"
    "Every reply MUST include exactly one [VOICE] or [TEXT] marker on its own line.\n"
    "The marker is a structural fence: the parser discards everything before it — "
    "only what comes after the marker reaches users.\n"
    "Place the marker as early as possible (ideally the first line of your reply):\n"
    "• [VOICE] — detailed informational replies: book summaries, recommendations, "
    "literary discussions, answers to /اجب questions, or any substantive explanation.\n"
    "• [TEXT] — short conversational replies: greetings, thanks, confirmations, "
    "clarification requests, follow-up questions, or one-to-two sentence responses.\n"
    "Do not write [VOICE] or [TEXT] anywhere else in the reply body.\n"
    "\n"
    "━━━ مرحلة الترشيحات ━━━\n"
    "عندما يتوفر بلوك [سياق مرحلة الترشيحات] في السياق:\n"
    "• أنت عضو نشط في نادي القراءة — لست مساعداً عاماً للكتب.\n"
    "• اقرأ قائمة الكتب المرشحة الموجودة واستبعدها كلياً — لا تقترح كتاباً مدرجاً فيها.\n"
    "• اقترح كتاباً واحداً فقط: حقيقياً، موجوداً فعلاً، ومناسباً للقراءة الجماعية في نادٍ ثقافي.\n"
    "• يجب أن يندرج الكتاب تحت التصنيف المحدد في السياق بوضوح.\n"
    "• اذكر المؤلف وبيّن بإيجاز لماذا يناسب هذا الكتاب التصنيف المحدد والقراءة الجماعية تحديداً.\n"
    "• لا تقترح قوائم — خيار واحد مدروس ومقنع.\n"
    "\n"
    "━━━ Nomination Phase ━━━\n"
    "When a [سياق مرحلة الترشيحات] context block is present:\n"
    "• You are an active reading-club member — not a generic book assistant.\n"
    "• Read the existing nominations list carefully — never suggest a book already on it.\n"
    "• Recommend exactly one real, verifiable book suitable for group reading in a literary club.\n"
    "• The book must clearly fall within the active category specified in the context.\n"
    "• Name the author and briefly explain why this book fits the category and works for group reading.\n"
    "• One specific recommendation — not a list.\n"
)

# Bump this string whenever SYSTEM_PROMPT changes meaningfully.
# Used by [DIAG /ask] log lines to correlate prompt versions with quality observations.
# Format: "<major>.<minor>" — increment minor for wording tweaks, major for structural overhauls.
SYSTEM_PROMPT_VERSION = "3.8"   # 3.8 = literary companion voice + 45-min window + Google Search grounding for reference questions

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Internal-data intent matcher
#
# Principle: if the bot already has authoritative data, it answers directly
# without consulting AI.  The matcher is a list of (intent_key, pattern)
# pairs checked in order — first match wins.
#
# When a message reaches the auto-reply handler and no intent matches, the
# raw text is logged so we can discover new patterns over time.
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

_INTENT_PATTERNS: list[tuple[str, re.Pattern]] = [
    # ── Today's reading portion ───────────────────────────────────────────────
    ("today_reading", re.compile(
        r"جزئية.*اليوم|اليوم.*جزئية"
        r"|الجزئية.*اليوم|اليوم.*الجزئية"
        r"|جزئيتنا"
        r"|الفصل.*اليوم|اليوم.*الفصل"
        r"|صفحات.*اليوم|اليوم.*صفحات"
        r"|ماذا نقرأ|ما.*الذي نقرأ|وش نقرأ|شو نقرأ"
        r"|نقرأ.*اليوم|اليوم.*نقرأ"
        r"|جدول.*اليوم|اليوم.*جدول"
        r"|جزئية القراءة|قراءة اليوم|القراءة اليوم"
    )),
    # ── Named external book queries (checked BEFORE current-book intents) ──────
    #    Matches "مؤلف/كاتب/ترجم [specific title]" — indefinite form + title.
    #    Bare/definite forms ("المؤلف؟", "من المؤلف؟") fall through to book_author.
    ("named_book_query", re.compile(
        r"(?:من\s+)?مؤلف\s+(?!الكتاب\b)\S"
        r"|(?:من\s+)?كاتب\s+(?!الكتاب\b)\S"
        r"|(?:من\s+)?ألّف\s+(?!الكتاب\b)\S"
        r"|(?:من\s+)?كتب\s+(?!الكتاب\b)\S"
        r"|(?:من\s+)?ترجم\s+(?!الكتاب\b)\S"
        r"|مترجم\s+(?!الكتاب\b)\S"
    )),
    # ── Current-club-book metadata (bare / definite-article forms only) ───────
    #    "من المؤلف؟" / "المؤلف؟" / "كاتبه؟" — always the active club book.
    #    Named-book phrasing ("مؤلف الطريق إلى القرآن") is caught above.
    ("book_author", re.compile(
        r"من.*المؤلف|المؤلف.*من"
        r"|من.*الكاتب|الكاتب.*من"
        r"|من.*ألّف.*الكتاب|الكتاب.*ألّف"
        r"|اسم.*الكاتب|الكاتب.*اسم"
        r"|اسم.*المؤلف|المؤلف.*اسم"
        r"|كاتب.*الكتاب|الكتاب.*كاتب"
        r"|مؤلف.*الكتاب|الكتاب.*مؤلف"
        r"|^من المؤلف\??|^من الكاتب\??"
        r"|^المؤلف\??$|^الكاتب\??$"
        r"|كاتبه\b|مؤلفه\b|كاتبها\b|مؤلفها\b"
    )),
    ("book_translator", re.compile(
        r"من.*المترجم|المترجم.*من"
        r"|المترجم\b|مترجم.*الكتاب|الكتاب.*مترجم"
        r"|اسم.*المترجم|المترجم.*اسم"
        r"|من.*ترجمة.*الكتاب|ترجمة.*الكتاب"
        r"|مترجمه\b|مترجمها\b"
    )),
    ("book_pages", re.compile(
        r"كم.*صفح[ةه]|صفح[ةه].*كم"
        r"|عدد.*الصفحات|الصفحات.*عدد"
        r"|كم.*صفحات|صفحات.*كم"
        r"|الصفحات\?|عدد الصفحات\?"
    )),
    ("book_info", re.compile(
        r"حدثني.*عن.*الكتاب|عن.*الكتاب.*حدثني"
        r"|عرّفني.*الكتاب|الكتاب.*عرّفني"
        r"|نبذة.*عن.*الكتاب|الكتاب.*نبذة"
        r"|ملخص.*الكتاب|الكتاب.*ملخص"
        r"|معلومات.*الكتاب|الكتاب.*معلومات"
        r"|تفاصيل.*الكتاب|الكتاب.*تفاصيل"
        r"|عن.*الكتاب الحالي|الكتاب الحالي.*عن"
    )),
    ("book_year", re.compile(
        r"متى.*نُشر|نُشر.*متى"
        r"|متى.*صدر|صدر.*متى"
        r"|سنة.*النشر|النشر.*سنة"
        r"|سنة.*الإصدار|الإصدار.*سنة"
        r"|تاريخ.*النشر|النشر.*تاريخ"
        r"|متى.*كُتب|كُتب.*متى"
        r"|سنة.*الكتاب|الكتاب.*سنة"
        r"|^سنة النشر\??"
    )),
    ("book_language", re.compile(
        r"اللغة.*الأصلية|الأصلية.*اللغة"
        r"|بأي.*لغة|لغة.*أصلي"
        r"|لغة.*الكتاب|الكتاب.*لغة"
        r"|لغة.*المؤلف|كُتب.*بالـ"
        r"|^اللغة\??|^ما اللغة"
    )),
    ("book_country", re.compile(
        r"من.*أي.*دولة|دولة.*المؤلف"
        r"|بلد.*المؤلف|المؤلف.*بلد"
        r"|جنسية.*المؤلف|المؤلف.*جنسية"
        r"|من.*أين.*المؤلف|المؤلف.*من.*أين"
        r"|موطن.*المؤلف"
    )),
    ("book_publisher", re.compile(
        r"دار.*النشر|النشر.*دار"
        r"|من.*نشر|نشر.*من"
        r"|الناشر\??|ما.*الناشر|اسم.*الناشر"
        r"|نشرت.*من|نشره.*من"
    )),
    ("book_original_title", re.compile(
        r"العنوان.*الأصلي|الأصلي.*العنوان"
        r"|الاسم.*الأصلي|الأصلي.*الاسم"
        r"|عنوانه.*الأصلي|العنوان.*بالـ"
        r"|الاسم.*الإنجليزي|الاسم.*الفرنسي"
        r"|^العنوان الأصلي\??"
    )),
    # ── Current book ─────────────────────────────────────────────────────────
    ("current_book", re.compile(
        r"الكتاب الحالي|الكتاب الآن|نقرأ الآن|الكتاب المقروء"
        r"|ما.*الكتاب|ماهو الكتاب|ما هو الكتاب"
        r"|شو الكتاب|وش الكتاب|أي كتاب"
        r"|الكتاب اللي نقرأه|الكتاب اللي تقرأونه"
    )),
    # ── Reading progress ──────────────────────────────────────────────────────
    ("progress", re.compile(
        r"وين وصلنا|إيش وصلنا|وصلنا.*قراءة|قراءة.*وصلنا"
        r"|تقدم.*قراءة|قراءة.*تقدم"
        r"|كم يوم.*مضى|مضى.*يوم|كم.*يوم.*قرأ|كم.*يوم.*قراءة"
        r"|كم تبقى.*قراءة|قراءة.*باقي|باقي.*قراءة"
        r"|كم.*يتبقى|يتبقى.*يوم"
    )),
    # ── Upcoming books / reading queue ───────────────────────────────────────
    ("queue", re.compile(
        r"الكتاب القادم|الكتب القادمة"
        r"|كتاب.*بعد|بعد.*كتاب"
        r"|قائمة.*قراءة|قراءة.*قائمة|القائمة"
        r"|كتب مقبلة|كتب.*قادم|قادم.*كتب"
        r"|ماذا بعد|شو بعد|وش بعد|إيش بعد"
        r"|الكتب اللي بعد|الكتاب اللي بعد"
        r"|بعد.*الكتاب الحالي|الكتاب التالي"
    )),
    # ── Completed books / reading history ────────────────────────────────────
    ("history", re.compile(
        r"كتب.*قرأناها|قرأناها"
        r"|كتب.*أنهيناها|أنهيناها"
        r"|كتب.*أكملناها|أكملناها"
        r"|الكتب.*مكتملة|مكتملة.*كتب|الكتب المكتملة"
        r"|ماذا قرأنا|وش قرأنا|شو قرأنا|إيش قرأنا"
        r"|كتب.*سابق|سابق.*كتب|الكتب السابقة"
        r"|ما الكتب.*قرأنا|الكتب.*خلصنا"
    )),
    # ── Participation poll ────────────────────────────────────────────────────
    ("participation", re.compile(
        r"عدد المشاركين|كم.*مشارك|مشارك.*كم"
        r"|سيشارك|من سيشارك|يشارك.*كم|كم.*يشارك"
        r"|استفتاء.*مشارك|مشارك.*استفتاء"
        r"|نتيجة.*استفتاء|استفتاء.*نتيجة"
        r"|استفتاء المشاركة|نتائج المشاركة"
    )),
    # ── Book ratings ──────────────────────────────────────────────────────────
    ("rating", re.compile(
        r"تقييم.*كتاب|كتاب.*تقييم|تقييم المجموعة|تقييم الكتاب"
        r"|نجوم.*كتاب|كتاب.*نجوم"
        r"|أحسن كتاب|أفضل كتاب|أعلى تقييم"
        r"|كم.*نجوم|نجوم.*كم|كم.*تقييم|تقييم.*كم"
        r"|التقييم النهائي"
    )),
    # ── Completion count (/done) ──────────────────────────────────────────────
    ("completion", re.compile(
        r"كم.*أنهى|أنهى.*كم|كم.*أكمل|أكمل.*كم"
        r"|من أنهى|من أكمل|من ختم"
        r"|أنهوا.*كتاب|أكملوا.*كتاب|كتاب.*أنهوا|كتاب.*أكملوا"
        r"|عدد.*أنهى|عدد.*أكمل|عدد.*انتهى"
        r"|كم.*خلّص|خلّص.*كم"
    )),
    # ── Book-selection vote ───────────────────────────────────────────────────
    ("vote", re.compile(
        r"التصويت.*مفتوح|مفتوح.*التصويت"
        r"|نتائج.*تصويت|تصويت.*نتائج"
        r"|التصويت.*انتهى|انتهى.*التصويت|التصويت.*أغلق"
        r"|تصويت.*كتب|كتب.*تصويت"
        r"|متى.*التصويت|التصويت.*متى"
        r"|هل التصويت|التصويت.*هل"
    )),
]


def _match_intent(text: str) -> str | None:
    """Return the first matching intent key for the given text, or None."""
    for intent_key, pattern in _INTENT_PATTERNS:
        if pattern.search(text):
            return intent_key
    return None


# ── Companion message pools ───────────────────────────────────────────────────
# Short optional messages appended to schedule replies for warmth and variety.
# They never describe story content, quality, or anything that could influence
# expectations. Distribution: 70 % none · 25 % regular · 5 % playful.

_COMPANION_POOLS: dict[str, dict[str, list[str]]] = {
    "reading": {
        "regular": [
            "قراءة ممتعة.",
            "بالتوفيق في جزئية اليوم.",
            "خذوا وقتكم مع الفصل.",
            "نتمنى لكم جلسة قراءة هادئة.",
            "بانتظار أفكاركم بعد القراءة.",
            "لا تنسوا تدوين الملاحظات التي لفتت انتباهكم.",
            "نلتقي في النقاش بعد الانتهاء من الجزئية.",
            "استمتعوا بالقراءة.",
        ],
        "playful": [
            "لا تنسوا شاي القراءة ☕️",
            "الوسادة المريحة إلزامية 😄",
            "أطفئوا الإشعارات وانغمسوا 📵",
        ],
    },
    "progress_early": {
        "regular": [
            "بداية موفقة للجميع.",
            "ما زالت الرحلة في بدايتها.",
            "الطريق أمامنا ما زال طويلاً.",
        ],
        "playful": [
            "الحماس في أوجّه 🚀",
        ],
    },
    "progress_mid": {
        "regular": [
            "وصلنا إلى منتصف الطريق تقريباً.",
            "بدأت خيوط الحكاية تتضح أكثر.",
            "الزخم يتصاعد.",
        ],
        "playful": [
            "نصف الطريق وراءنا 💪",
        ],
    },
    "progress_late": {
        "regular": [
            "اقتربنا من نهاية الرحلة.",
            "لم يتبق الكثير.",
            "الخاتمة باتت قريبة.",
        ],
        "playful": [
            "النهاية تقترب 👀",
        ],
    },
    "rest": {
        "regular": [
            "فرصة للحاق بالجزئيات السابقة.",
            "أو لإعادة زيارة فصل أعجبكم.",
            "استرحوا جيداً.",
        ],
        "playful": [
            "القراءة تحتاج طاقة — استرحوا جيداً 😄",
        ],
    },
}


def _maybe_companion(pool_key: str) -> str:
    """
    Return an optional companion message from the named pool, or empty string.
    Distribution: 70 % none · 25 % regular · 5 % playful.
    """
    pool = _COMPANION_POOLS.get(pool_key, {})
    roll = random.random()
    if roll < 0.70:
        return ""
    if roll < 0.95:
        messages = pool.get("regular", [])
    else:
        messages = pool.get("playful", []) or pool.get("regular", [])
    return random.choice(messages) if messages else ""


def _get_current_book_meta() -> tuple[str, dict | None]:
    """Return (title, metadata_dict | None) for the currently active book."""
    book_dict = cycle_store.get_current_book()
    title = book_dict["title"] if book_dict else schedule_store.load().get("current_book", "")
    if not title:
        return "", None
    return title, book_store.get_metadata(title)


def _extract_book_title_from_query(text: str) -> str:
    """
    Extract a named book title from a metadata question.

    Examples:
      "من مؤلف الطريق إلى القرآن؟"   → "الطريق إلى القرآن"
      "من كاتب كتاب مدن لا مرئية؟"  → "مدن لا مرئية"
      "من ترجم الخيميائي؟"            → "الخيميائي"

    Returns an empty string when no title pattern is found.
    """
    clean = text.strip().rstrip("؟?!. ")
    # Remove leading question words
    clean = re.sub(r"^(?:من|ما|ماذا|هل|متى|أين|كيف)\s+", "", clean).strip()
    # Keyword + optional "كتاب" + title
    m = re.search(
        r"(?:مؤلف|كاتب|ألّف|كتب|ترجم|مترجم)\s+(?:كتاب\s+)?(.+)$",
        clean,
    )
    if m:
        title = m.group(1).strip().rstrip("؟?!. ")
        generic = {"الكتاب", "الكتاب الحالي", "هذا الكتاب", "الكتاب ده"}
        if title and title not in generic and len(title) >= 2:
            return title
    return ""


def _build_data_reply(intent: str, user_text: str = "") -> str | None:
    """
    Build a deterministic reply from internal data stores for the given intent.
    Returns None when the relevant data is absent — caller falls through to AI.

    user_text — original message text; required for named_book_query extraction.
    """
    # ── Named book lookup (current-book dict → archive → None/AI) ────────────
    if intent == "named_book_query":
        book_title = _extract_book_title_from_query(user_text)
        if not book_title:
            logger.info("named_book_query: could not extract title from %r", user_text[:80])
            return None

        # 1. Books dict (covers current book + any /setmeta'd books)
        meta = book_store.get_metadata(book_title)
        if meta:
            matched = meta.get("title", book_title)
            current_title = _get_current_book_meta()[0]
            source = "current_book" if matched == current_title else "books"
            logger.info("book_lookup: title=%r source=%s", book_title, source)
            if meta.get("author"):
                return f"✍️ مؤلف <b>{matched}</b>: <b>{meta['author']}</b>"
            return (
                f"📝 لم يتم تسجيل اسم المؤلف لكتاب <b>{matched}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )

        # 2. Archive
        archived = book_store.find_in_archive(book_title)
        if archived:
            matched = archived.get("title", book_title)
            logger.info("book_lookup: title=%r source=archive", book_title)
            if archived.get("author"):
                return (
                    f"✍️ مؤلف <b>{matched}</b>: <b>{archived['author']}</b>\n"
                    f"<i>(من أرشيف النادي)</i>"
                )
            return f"📝 <b>{matched}</b> موجود في أرشيف النادي لكن بدون بيانات المؤلف."

        # 3. Not found — AI fallback (logged by _smart_reply)
        logger.info("book_lookup: title=%r source=ai_fallback", book_title)
        return None

    # ── Book metadata intents ─────────────────────────────────────────────────
    if intent == "book_author":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("author"):
            # Hard block — do NOT fall through to AI for authorship attribution
            logger.info("book_author: no stored author for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل اسم المؤلف لكتاب <b>{_html.escape(title)}</b> بعد.\n"
                f"\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"✍️ مؤلف <b>{_html.escape(title)}</b>: <b>{_html.escape(meta['author'])}</b>"

    if intent == "book_translator":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("translator"):
            # Hard block — do NOT fall through to AI for translator attribution
            logger.info("book_translator: no stored translator for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل اسم المترجم لكتاب <b>{_html.escape(title)}</b> بعد.\n"
                f"\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"🔄 ترجمة <b>{_html.escape(title)}</b>: <b>{_html.escape(meta['translator'])}</b>"

    if intent == "book_pages":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("pages"):
            # Hard block — do NOT fall through to AI for page counts
            logger.info("book_pages: no stored page count for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل عدد صفحات <b>{_html.escape(title)}</b> بعد.\n"
                f"\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"📄 <b>{_html.escape(title)}</b> — {meta['pages']} صفحة"

    if intent == "book_year":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("year"):
            logger.info("book_year: no stored year for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل سنة النشر لكتاب <b>{_html.escape(title)}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"📅 <b>{_html.escape(title)}</b> — صدر عام {meta['year']}"

    if intent == "book_language":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("original_language"):
            logger.info("book_language: no stored language for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل اللغة الأصلية لكتاب <b>{_html.escape(title)}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"🌐 <b>{_html.escape(title)}</b> — كُتب أصلاً بـ<b>{_html.escape(meta['original_language'])}</b>"

    if intent == "book_country":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("author_country"):
            logger.info("book_country: no stored country for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل بلد المؤلف لكتاب <b>{_html.escape(title)}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        author = meta.get("author", "المؤلف")
        return f"🗺️ <b>{_html.escape(author)}</b> — {_html.escape(meta['author_country'])}"

    if intent == "book_publisher":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("publisher"):
            logger.info("book_publisher: no stored publisher for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل دار النشر لكتاب <b>{_html.escape(title)}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"🏛️ <b>{_html.escape(title)}</b> — {_html.escape(meta['publisher'])}"

    if intent == "book_original_title":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta or not meta.get("original_title"):
            logger.info("book_original_title: no stored original title for '%s' — returning not-stored message", title)
            return (
                f"📝 لم يتم تسجيل العنوان الأصلي لكتاب <b>{_html.escape(title)}</b> بعد.\n\n"
                f"يمكن للمديرين إضافة البيانات عبر /setmeta"
            )
        return f"📝 العنوان الأصلي: <b>{_html.escape(meta['original_title'])}</b>"

    if intent == "book_info":
        title, meta = _get_current_book_meta()
        if not title:
            return None
        if not meta:
            return None
        lines: list[str] = [f"📚 <b>{_html.escape(title)}</b>", ""]
        if meta.get("author"):
            lines.append(f"✍️ المؤلف: {meta['author']}")
        if meta.get("translator"):
            lines.append(f"🔄 الترجمة: {meta['translator']}")
        if meta.get("publisher"):
            lines.append(f"🏛️ الناشر: {meta['publisher']}")
        if meta.get("year"):
            lines.append(f"📅 السنة: {meta['year']}")
        if meta.get("pages"):
            lines.append(f"📄 الصفحات: {meta['pages']}")
        if meta.get("original_language"):
            lines.append(f"🌐 اللغة الأصلية: {meta['original_language']}")
        if meta.get("author_country"):
            lines.append(f"🗺️ بلد المؤلف: {meta['author_country']}")
        if meta.get("original_title"):
            lines.append(f"📝 العنوان الأصلي: {meta['original_title']}")
        if meta.get("genres"):
            g = meta["genres"]
            lines.append(f"🏷️ التصنيف: {'، '.join(g) if isinstance(g, list) else g}")
        if meta.get("description"):
            lines.extend(["", meta["description"]])
        if len(lines) <= 2:
            return None  # metadata entry exists but is empty — fall through to AI
        return "\n".join(lines)

    if intent == "today_reading":
        sch  = schedule_store.load()
        book = sch.get("current_book", "")
        if not book:
            return None
        if schedule_store.is_rest_day_today(sch):
            companion = _maybe_companion("rest")
            base = "☕️ اليوم يوم راحة — خذي استراحة واستمتعي بوقتك 🙂\n\nالقراءة تعود غداً بإذن الله."
            return f"{base}\n\n{companion}" if companion else base
        entry = schedule_store.get_marked_current_entry(sch)
        if not entry:
            return f"ما في جزئية قراءة لهذا اليوم في جدول <b>{_html.escape(book)}</b>."
        chapter = entry.get("chapter", "")
        p_start = entry.get("page_start")
        p_end   = entry.get("page_end")
        lines   = [f"📍 جزئيتنا اليوم من <b>{_html.escape(book)}</b>", ""]
        if chapter:
            lines.append(f"<b>{chapter}</b>")
        if p_start is not None and p_end is not None:
            lines.append(f"الصفحات: {p_start} ← {p_end}")
        companion = _maybe_companion("reading")
        if companion:
            lines.extend(["", companion])
        return "\n".join(lines)

    if intent == "current_book":
        book_dict = cycle_store.get_current_book()
        title = book_dict["title"] if book_dict else schedule_store.load().get("current_book", "")
        if not title:
            return None
        return f"📚 نقرأ الآن: <b>{_html.escape(title)}</b>"

    if intent == "progress":
        sch  = schedule_store.load()
        book = sch.get("current_book", "")
        if not book:
            return None
        elapsed, total = schedule_store.get_progress(sch)
        remaining = total - elapsed
        ratio = elapsed / total if total > 0 else 0
        if ratio >= 0.70:
            pool_key = "progress_late"
        elif ratio >= 0.30:
            pool_key = "progress_mid"
        else:
            pool_key = "progress_early"
        base = (
            f"⏳ <b>{_html.escape(book)}</b>\n"
            f"\n"
            f"مضى {elapsed} من أصل {total} يوم قراءة\n"
            f"متبقّي: {remaining} يوم"
        )
        companion = _maybe_companion(pool_key)
        return f"{base}\n\n{companion}" if companion else base

    if intent == "queue":
        pending = cycle_store.get_books("pending")
        if not pending:
            return "ما في كتب قادمة في القائمة حالياً — ربما تحتاج دورة جديدة قريباً 😄"
        lines = ["📋 <b>الكتب القادمة في القائمة:</b>", ""]
        for i, b in enumerate(pending, 1):
            lines.append(f"{i}. {_html.escape(b['title'])}")
        return "\n".join(lines)

    if intent == "history":
        completed = cycle_store.get_completed()
        if not completed:
            return "ما أكملنا أي كتاب في هذه الدورة بعد — لكننا في الطريق! 📖"
        n = len(completed)
        header = f"✅ <b>أكملنا {n} {'كتاب' if n == 1 else 'كتب'} حتى الآن:</b>"
        lines = [header, ""]
        for b in completed:
            lines.append(f"• {_html.escape(b['title'])}")
        return "\n".join(lines)

    if intent == "participation":
        active = poll_store.get_active()
        if not active:
            return "ما في استفتاء مشاركة نشط الآن."
        count = poll_store.get_participant_count()
        book  = active.get("book_title", "")
        book_label = f" في <b>{_html.escape(book)}</b>" if book else ""
        if count == 0:
            return f"👥 لا يوجد مشاركون مسجّلون{book_label} حتى الآن."
        return f"👥 {count} {'عضو' if count == 1 else 'عضو'} أبدوا رغبتهم في المشاركة{book_label} ✅"

    if intent == "rating":
        book_dict  = cycle_store.get_current_book()
        book_title = book_dict["title"] if book_dict else ""
        archived   = rating_store.get_archived_for_book(book_title) if book_title else None
        if archived:
            stars = "⭐️" * archived["most_common_rating"]
            total = archived["total_ratings"]
            return (
                f"{stars}\n"
                f"تقييم المجموعة لـ <b>{_html.escape(book_title)}</b>: {stars}\n"
                f"{total} صوت"
            )
        best = rating_store.get_best_rated_book()
        if best:
            stars = "⭐️" * best["most_common_rating"]
            return (
                f"أعلى تقييم حتى الآن: <b>{_html.escape(best['book_title'])}</b>\n"
                f"{stars} — {best['total_ratings']} صوت"
            )
        return "ما في تقييمات مسجلة للكتب بعد."

    if intent == "completion":
        book_dict  = cycle_store.get_current_book()
        book_title = book_dict["title"] if book_dict else schedule_store.load().get("current_book", "")
        if not book_title:
            return None
        count = completion_store.get_count(book_title)
        if count == 0:
            return f"📖 ما سجّل أحد إنهاء <b>{_html.escape(book_title)}</b> بعد — ربما قريباً!"
        return f"📖 أنهى <b>{_html.escape(book_title)}</b> حتى الآن: <b>{count}</b> عضو 🎉"

    if intent == "vote":
        status = vote_store.get_status()
        if status == "active":
            close_at = vote_store.get_close_at()
            if close_at:
                try:
                    close_str = close_at.strftime("%-d %B")
                except Exception:
                    close_str = close_at.strftime("%Y-%m-%d")
                return f"🗳️ التصويت نشط الآن — ينتهي في {close_str}، لا تنسي صوتك!"
            return "🗳️ التصويت نشط الآن — بادري بالتصويت!"
        if status == "closed":
            results = vote_store.get_results()
            if results:
                winner = results[0]
                return (
                    f"🏆 انتهى التصويت!\n"
                    f"\n"
                    f"الفائز: <b>{_html.escape(winner['title'])}</b> بـ {winner['votes']} صوت"
                )
            return "🗳️ التصويت انتهى — استخدم /queue لرؤية القائمة."
        return "ما في تصويت نشط حالياً."

    return None


def _build_schedule_context(include_metadata: bool = True) -> str:
    """
    Build a brief Arabic context block injected into AI prompts as background
    so the AI can reference real group state without needing to look it up.
    Returns empty string when no schedule is loaded.

    include_metadata — when False, only the book title and reading progress are
    injected; author/translator/publisher/year/pages/etc. are omitted.  Use this
    when the user is asking about a *different* named book so that the current
    book's metadata does not anchor the AI's attribution reasoning.
    """
    sch  = schedule_store.load()
    book = sch.get("current_book", "")
    if not book:
        return ""
    lines = ["[معلومات المجموعة الحالية]", f"الكتاب الحالي: {book}"]
    meta = book_store.get_metadata(book)
    if meta and include_metadata:
        if meta.get("author"):
            lines.append(f"المؤلف: {meta['author']}")
        if meta.get("translator"):
            lines.append(f"المترجم: {meta['translator']}")
        if meta.get("publisher"):
            lines.append(f"الناشر: {meta['publisher']}")
        if meta.get("year"):
            lines.append(f"سنة النشر: {meta['year']}")
        if meta.get("pages"):
            lines.append(f"الصفحات: {meta['pages']}")
        if meta.get("original_language"):
            lines.append(f"اللغة الأصلية: {meta['original_language']}")
        if meta.get("author_country"):
            lines.append(f"بلد المؤلف: {meta['author_country']}")
        if meta.get("original_title"):
            lines.append(f"العنوان الأصلي: {meta['original_title']}")
    if schedule_store.is_rest_day_today(sch):
        lines.append("اليوم: يوم راحة")
    else:
        entry = schedule_store.get_marked_current_entry(sch)
        if entry:
            chapter = entry.get("chapter", "")
            p_start = entry.get("page_start")
            p_end   = entry.get("page_end")
            if chapter:
                lines.append(f"الجزئية اليوم: {chapter}")
            if p_start is not None and p_end is not None:
                lines.append(f"الصفحات: {p_start}–{p_end}")
    elapsed, total = schedule_store.get_progress(sch)
    lines.append(f"التقدم: {elapsed} من {total} يوم قراءة")
    return "\n".join(lines)


VOICE_AR = "ar-SA-ZariyahNeural"
VOICE_EN = "en-US-JennyNeural"

conversation_histories: dict[int, list] = defaultdict(list)
_conv_last_seen: dict[int, float] = {}   # user_id → monotonic timestamp of last bot reply

# Phase 4a — tracks the ID of the most recently logged /اجب interaction so the
# owner can rate it with /rate or save it with /savefaq without needing to quote the ID.
_last_ask_interaction_id: str | None = None

# Phase 4b — DM training workspace session state (owner only, resets on restart)
_dm_session: dict = {}   # keys: name (str), started_at (float monotonic)

# Deduplication guard: tracks (chat_id, message_id) pairs that have already
# been dispatched to an AI handler. Persisted to disk so it survives restarts —
# this is the only way to block the restart-induced duplicate where the new
# process re-receives a pending update that the old process started handling.
# Entries expire after 5 minutes (wall-clock unix timestamp).
_DEDUP_FILE       = os.path.join(_BOT_DIR, ".processed_msg_ids.json")
_PROCESSED_MSG_TTL = 300.0   # seconds
_dedup_lock        = threading.Lock()


def _dedup_load() -> dict[str, float]:
    """Load {key: timestamp} from disk, return empty dict on any error."""
    try:
        with open(_DEDUP_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            return data
    except Exception:  # log-exempt: best-effort cache load; corrupt/missing file returns {}
        pass
    return {}


def _dedup_save(data: dict[str, float]) -> None:
    """Write the dedup dict to disk atomically (best-effort)."""
    try:
        tmp = _DEDUP_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f)
        os.replace(tmp, _DEDUP_FILE)
    except Exception:  # log-exempt: best-effort write; dedup missing is non-fatal
        pass


def _check_duplicate(chat_id: int, message_id: int) -> bool:
    """
    Return True if this (chat_id, message_id) was already successfully replied to.
    Read-only — does NOT mark the update. Call _mark_processed() after the reply is sent.
    """
    key = f"{chat_id}:{message_id}"
    now = time.time()
    with _dedup_lock:
        data = _dedup_load()
        data = {k: t for k, t in data.items() if now - t <= _PROCESSED_MSG_TTL}
        return key in data


def _mark_processed(chat_id: int, message_id: int) -> None:
    """
    Record that a reply was successfully sent for (chat_id, message_id).
    Call this AFTER the reply is delivered, never before — otherwise a bot
    restart mid-Gemini-call would prevent the new instance from retrying.
    """
    key = f"{chat_id}:{message_id}"
    now = time.time()
    with _dedup_lock:
        data = _dedup_load()
        data = {k: t for k, t in data.items() if now - t <= _PROCESSED_MSG_TTL}
        data[key] = now
        _dedup_save(data)


_CONV_TIMEOUT_SECS = 2700                # 45-minute inactivity window

# Shared group discussion windows.
# When a /ask conversation starts in a group chat, a discussion slot is opened
# keyed by chat_id (always negative for groups). Any member who explicitly
# invokes the bot (@mention or Telegram reply) while the slot is active joins
# the shared conversation history, up to _GROUP_MAX_PARTICIPANTS.
# The slot never causes the bot to speak on its own — it only provides context
# when the bot is explicitly invoked by a participant.
_group_discussions: dict[int, dict] = {}  # chat_id → {participants, last_activity}
_GROUP_MAX_PARTICIPANTS = 3
gemini_client = None


def _is_conversation_followup(update: object, bot_id: int) -> bool:
    """
    Return True when a message is a direct reply to the bot or falls within
    the active conversation window (10 minutes since the bot last responded).
    """
    from telegram import Update as _Update
    if not isinstance(update, _Update) or update.message is None:
        return False

    user_id = update.effective_user.id if update.effective_user else 0

    # Signal 1: user used Telegram's reply feature on one of the bot's messages
    rpl = update.message.reply_to_message
    if rpl and rpl.from_user and rpl.from_user.id == bot_id:
        return True

    # Signal 2: within the 10-minute inactivity window
    last = _conv_last_seen.get(user_id)
    if last is not None and (time.monotonic() - last) < _CONV_TIMEOUT_SECS:
        return True

    return False


def _resolve_history_key(chat_id: int, user_id: int) -> int:
    """
    Return the conversation_histories key to use for this interaction.

    In a group chat (chat_id < 0) with an active shared discussion that the
    user can join, returns chat_id so the exchange enters the shared slot.
    Otherwise returns user_id for a private solo history.

    Also joins the user to the discussion (updating participants + timestamp)
    when they are a new eligible participant.
    """
    if chat_id >= 0:
        return user_id
    disc = _group_discussions.get(chat_id)
    if disc is None:
        return user_id
    now = time.monotonic()
    if (now - disc["last_activity"]) >= _CONV_TIMEOUT_SECS:
        return user_id
    disc["last_activity"] = now
    if user_id not in disc["participants"]:
        if len(disc["participants"]) >= _GROUP_MAX_PARTICIPANTS:
            return user_id  # discussion is full — use own solo history
        disc["participants"].append(user_id)
        logger.info(
            "group_discussion: %s joined shared discussion in chat %d (%d/%d participants)",
            user_id, chat_id, len(disc["participants"]), _GROUP_MAX_PARTICIPANTS,
        )
    return chat_id


def _open_or_refresh_group_discussion(chat_id: int, user_id: int) -> None:
    """
    Called after the bot successfully replies in a group chat.

    Creates a new shared discussion slot (seeding its history from the
    initiator's current history) or refreshes the timestamp of an existing one.
    """
    if chat_id >= 0:
        return
    now = time.monotonic()
    disc = _group_discussions.get(chat_id)
    if disc is None or (now - disc["last_activity"]) >= _CONV_TIMEOUT_SECS:
        _group_discussions[chat_id] = {
            "participants": [user_id],
            "last_activity": now,
        }
        # Seed the shared history slot from the initiator's current history
        # so the first /ask exchange is visible to any participant who joins.
        conversation_histories[chat_id] = list(conversation_histories.get(user_id, []))
        logger.info(
            "group_discussion: new discussion opened in chat %d by user %s "
            "(seeded %d history turns)",
            chat_id, user_id, len(conversation_histories[chat_id]),
        )
    else:
        disc["last_activity"] = now
        if user_id not in disc["participants"]:
            if len(disc["participants"]) < _GROUP_MAX_PARTICIPANTS:
                disc["participants"].append(user_id)


def init_gemini() -> bool:
    global gemini_client
    if not GEMINI_API_KEY:
        logger.warning("GEMINI_API_KEY is not set — AI replies disabled.")
        return False
    try:
        gemini_client = genai.Client(api_key=GEMINI_API_KEY)
        logger.info("Gemini AI initialized successfully.")
        return True
    except Exception as e:
        logger.error("Failed to initialize Gemini: %s", e)
        return False



_GEMINI_RETRY_DELAYS = (2.0, 4.0, 8.0)  # seconds between retries for transient errors


async def _ai_generate(
    contents: list,
    system_instruction: str = "",
    label: str = "ai",
    tools: list | None = None,
) -> str:
    """
    Generate content via Gemini with automatic retry for transient errors.

    - 503 / 502 / 429: retried up to 3 times with exponential back-off (2s, 4s, 8s).
    - 401 / 403: re-raised immediately so callers can surface a key-problem message.
    - All other failures: raises RuntimeError("gemini_failed") after logging.
    """
    if gemini_client is None:
        raise RuntimeError("gemini_unavailable")

    _cfg_kw: dict = {}
    if system_instruction:
        _cfg_kw["system_instruction"] = system_instruction
    if tools:
        _cfg_kw["tools"] = tools
    cfg = types.GenerateContentConfig(**_cfg_kw) if _cfg_kw else None
    call_kwargs: dict = dict(model="gemini-2.5-flash", contents=contents)
    if cfg is not None:
        call_kwargs["config"] = cfg

    last_exc: Exception | None = None

    for attempt, delay in enumerate((*_GEMINI_RETRY_DELAYS, None), start=1):
        try:
            response = await asyncio.to_thread(
                gemini_client.models.generate_content,
                **call_kwargs,
            )
            # Collect only non-thought parts.  gemini-2.5-flash may include
            # extended-thinking parts (thought=True) alongside the real reply.
            # response.text is a convenience property that can concatenate all
            # parts — including thought parts — so we iterate explicitly to
            # guarantee that internal reasoning never enters raw_text.
            raw_parts: list[str] = []
            candidate = (response.candidates or [None])[0]
            if candidate and candidate.content and candidate.content.parts:
                for part in candidate.content.parts:
                    if not getattr(part, "thought", False) and part.text:
                        raw_parts.append(part.text)
            raw_text_out = "".join(raw_parts).strip() if raw_parts else (response.text or "")
            if not raw_text_out:
                logger.warning(
                    "%s: Gemini returned empty/None text (possibly safety-filtered)", label
                )
                raise RuntimeError("gemini_empty_response")
            if attempt > 1:
                logger.info("%s: Gemini succeeded on attempt %d", label, attempt)
            logger.info("%s: Gemini responded (%d chars)", label, len(raw_text_out))
            return raw_text_out

        except genai_errors.ClientError as e:
            status = getattr(e, "status_code", None) or getattr(e, "code", 0)
            if status in (401, 403):
                logger.error("%s: Gemini auth error %s (key invalid/expired)", label, status)
                raise RuntimeError("gemini_auth_error") from e
            if status == 429 and delay is not None:
                logger.warning(
                    "%s: Gemini rate-limited (429), retry %d in %.0fs",
                    label, attempt, delay,
                )
                last_exc = e
                await asyncio.sleep(delay)
                continue
            logger.error("%s: Gemini ClientError %s", label, status)
            raise RuntimeError("gemini_failed") from e

        except genai_errors.ServerError as e:
            status = getattr(e, "status_code", None) or getattr(e, "code", 0)
            if delay is not None:
                logger.warning(
                    "%s: Gemini ServerError %s, retry %d in %.0fs",
                    label, status, attempt, delay,
                )
                last_exc = e
                await asyncio.sleep(delay)
                continue
            logger.error("%s: Gemini ServerError %s — all retries exhausted", label, status)
            raise RuntimeError("gemini_failed") from e

        except RuntimeError:
            raise

        except Exception as e:
            logger.error("%s: Gemini unexpected error: %s", label, e)
            raise RuntimeError("gemini_failed") from e

    # Should not be reached, but keeps type-checker happy
    _last_status = (
        getattr(last_exc, "status_code", None) or getattr(last_exc, "code", 0)
        if last_exc is not None else 0
    )
    if _last_status == 429:
        raise RuntimeError("gemini_rate_limited") from last_exc
    raise RuntimeError("gemini_failed") from last_exc


def detect_voice(text: str) -> str:
    arabic_chars = len(re.findall(r"[\u0600-\u06FF]", text))
    return VOICE_AR if arabic_chars > len(text) * 0.2 else VOICE_EN


def clean_text_content(text: str) -> str:
    """Strip markdown, emojis and symbols — keep letters, digits, spaces, newlines."""
    text = re.sub(r"\*{1,3}|_{1,2}|~~|`+", "", text)
    text = re.sub(r"#+\s*", " ", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    cleaned = []
    for char in text:
        cat = unicodedata.category(char)
        if cat.startswith("L") or cat.startswith("N") or char in " \n":
            cleaned.append(char)
        elif cat == "Mn":
            # Combining/diacritic marks (e.g. Arabic harakat: fatha, kasra, damma…)
            # Drop silently — inserting a space would split the host letter from
            # its neighbours, causing TTS to read isolated letters by name ("ألف").
            pass
        else:
            cleaned.append(" ")
    return re.sub(r" +", " ", "".join(cleaned)).strip()


async def text_to_voice_file(text: str) -> str | None:
    voice = detect_voice(text)
    spoken = clean_text_content(text)
    if not spoken:
        return None
    # edge-tts does not support custom SSML — use its built-in prosody params instead
    is_arabic = voice == VOICE_AR
    rate = "-10%" if is_arabic else "-5%"
    pitch = "+15Hz" if is_arabic else "+0Hz"   # Hz unit required by edge-tts
    tmp = tempfile.NamedTemporaryFile(suffix=".mp3", delete=False)
    tmp.close()
    try:
        communicate = edge_tts.Communicate(spoken, voice, rate=rate, pitch=pitch)
        await communicate.save(tmp.name)
        logger.info("TTS generated (%s, rate=%s pitch=%s): %s", voice, rate, pitch, tmp.name)
        return tmp.name
    except Exception as e:
        logger.error("TTS error: %s", e)
        os.unlink(tmp.name)
        return None


# Fast keyword pre-filter — checked locally before any API call.
# Only messages that pass this regex are forwarded to Gemini for classification.
_BOOK_KEYWORDS_RE = re.compile(
    r"كتاب|رواية|مؤلف|قراءة|اقرأ|اقترح|كاتب|أدب|قصة|شعر|نص|ديوان|فصل|صفح"
    r"|روائي|أديب|قصص|روايات|كتب|ملخص|توصي|book|author|novel|read|recommend",
    re.IGNORECASE,
)


async def is_book_related(text: str) -> bool:
    """
    Return True if the message mentions a book/author or requests a book.

    Two-stage check:
      1. Fast local keyword scan — returns False immediately for most messages.
      2. Gemini confirmation only when keywords are present.
    """
    # Stage 1: cheap local filter (no network, no latency)
    if not _BOOK_KEYWORDS_RE.search(text):
        return False

    # Stage 2: AI confirmation only for keyword-matching messages
    if gemini_client is None:
        return False
    try:
        prompt = (
            "هل تذكر هذه الرسالة اسم كتاب أو مؤلف بعينه، أو تطلب توصية بكتاب؟ "
            "أجب بكلمة واحدة فقط: نعم أو لا.\n\n"
            f"الرسالة: {text}"
        )
        answer = await _ai_generate(
            contents=[types.Content(role="user", parts=[types.Part(text=prompt)])],
            label="is_book_related",
        )
        answer = answer.strip()
        return answer.startswith("نعم") or answer.upper().startswith("YES")
    except Exception:
        return False


def _is_bot_mentioned(message, bot_id: int, bot_username: str) -> bool:
    """Return True if this bot is explicitly @mentioned in the message."""
    if message is None:
        return False
    text = message.text or ""
    for entity in (message.entities or []):
        if entity.type == "mention":
            mentioned = text[entity.offset : entity.offset + entity.length]
            if mentioned.lstrip("@").lower() == bot_username.lower():
                return True
        elif entity.type == "text_mention":
            if entity.user and entity.user.id == bot_id:
                return True
    return False


# Keywords that strongly suggest the message is about a Telegram bot
_BOT_TOPIC_RE = re.compile(
    r"البوت|الروبوت|بوت|روبوت|/schedule|/plan|/done|/rate|/readpoll|"
    r"الجدول|تتبع|المشاركة|استفتاء|التصويت|أوامر|ميزات|إعدادات|صلاحيات",
    re.IGNORECASE,
)


async def _is_about_this_bot(text: str) -> bool:
    """
    Return True when the message is discussing this reading-group bot's
    commands, features, behaviour, or functionality — even without an @mention.
    Uses a fast keyword pre-filter before calling the AI.
    """
    if not _BOT_TOPIC_RE.search(text):
        return False
    if gemini_client is None:
        return False
    try:
        prompt = (
            "هل تتحدث هذه الرسالة عن بوت تيليغرام لإدارة مجموعة قراءة "
            "(مثل: أوامره، ميزاته، جدول القراءة، تتبع التقدم، الاستفتاءات، "
            "مشاركة الأعضاء، التقييمات، الإعدادات)؟\n"
            "أجب بكلمة واحدة فقط: نعم أو لا.\n\n"
            f"الرسالة: {text}"
        )
        answer = await _ai_generate(
            contents=[types.Content(role="user", parts=[types.Part(text=prompt)])],
            label="is_about_bot",
        )
        return answer.strip().startswith("نعم") or answer.strip().upper().startswith("YES")
    except Exception:
        return False


def _strip_html(text: str) -> str:
    """
    Remove all HTML tags and unescape HTML entities.

    Used as the fallback when Telegram rejects a parse_mode=HTML message so
    that users see clean readable text rather than raw tags.  The regex covers
    all well-formed and most malformed tags; html.unescape handles &amp; &lt; etc.
    """
    return _html.unescape(re.sub(r"<[^>]+>", "", text))


def _md_to_html(text: str) -> str:
    """
    Convert common Markdown patterns to Telegram HTML as a safety net.

    Gemini sometimes generates Markdown (**, *, #) despite being instructed
    to use HTML.  This runs on every AI response before delivery so users
    never see raw formatting symbols.

    Order matters:
      1. Line-level patterns (headings, list bullets) — processed per line.
      2. Inline bold (**text** / __text__) — before italic to avoid conflicts.
      3. Inline italic (*text* / _text_) — conservative, avoids Arabic words.
      4. Inline code (`text`).
    Existing HTML tags are left untouched.
    """
    lines = []
    for line in text.split("\n"):
        # ATX headings: # / ## / ### … → <b>text</b>
        m = re.match(r"^(#{1,6})\s+(.+)$", line)
        if m:
            line = f"<b>{m.group(2)}</b>"
        else:
            # Unordered list bullets: lines starting with  * / - / +  + spaces
            # Convert to bullet character so Telegram renders them cleanly.
            line = re.sub(r"^\s*[*\-+]\s{1,4}(?=\S)", "• ", line)
        lines.append(line)
    text = "\n".join(lines)

    # Bold: **text** or __text__
    text = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", text, flags=re.DOTALL)
    text = re.sub(r"__(.+?)__", r"<b>\1</b>", text, flags=re.DOTALL)
    # Italic: *text* (single asterisk, not part of a bold pair)
    text = re.sub(r"(?<!\*)\*([^\n*]+?)\*(?!\*)", r"<i>\1</i>", text)
    # Inline code: `text`
    text = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", text)

    return text


def parse_reply(raw: str | None) -> tuple[bool, str]:
    """
    Locate the [VOICE] or [TEXT] structural fence anywhere in the response.

    The marker acts as a hard boundary: every line that appears before it is
    silently discarded.  This means model scratchpad text, chain-of-thought
    preamble, or any other pre-marker content can never reach Telegram,
    regardless of format or content.

    Returns (use_voice, clean_text).
    Defaults to voice=True when no tag is found (safe fallback).

    Handles both forms:
      • Tag on its own line:  "[TEXT]\nأهلاً..."  → standard case
      • Tag inline (no newline): "[TEXT]أهلاً..."  → model omits the newline
    """
    if not raw:
        return True, ""
    stripped = raw.strip()
    lines = stripped.split("\n")
    for i, line in enumerate(lines):
        ls = line.strip()
        if ls == "[VOICE]":
            return True, "\n".join(lines[i + 1:]).strip()
        if ls == "[TEXT]":
            return False, "\n".join(lines[i + 1:]).strip()
        # Inline form: tag immediately followed by text on the same line
        if ls.startswith("[VOICE]"):
            after = ls[len("[VOICE]"):].strip()
            rest = "\n".join(lines[i + 1:])
            return True, (after + ("\n" + rest if rest else "")).strip()
        if ls.startswith("[TEXT]"):
            after = ls[len("[TEXT]"):].strip()
            rest = "\n".join(lines[i + 1:])
            return False, (after + ("\n" + rest if rest else "")).strip()
    # No recognised tag — return full text and default to voice
    return True, stripped


async def send_ai_reply(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    user_text: str,
    extra_context: str = "",
    dump_prompt: bool = False,
    skip_history: bool = False,
    image_bytes: bytes | None = None,
    image_mime: str = "image/jpeg",
    history_key: int | None = None,
    use_search: bool = False,
    allow_voice: bool = True,
) -> None:
    """Call Gemini, update history, then send voice or text based on the reply tag.

    extra_context  — optional Arabic background text (e.g. current schedule state)
    prepended to the user message so the AI has authoritative group data without
    the caller needing to modify the message itself.

    image_bytes    — raw image bytes to pass to Gemini as a multimodal part.
    When provided the image is sent to Gemini alongside the text but is NEVER
    written to disk and NEVER stored in conversation_histories.  Only the text
    question (user_text) and the AI's text reply enter history, satisfying the
    "images are temporary input only" requirement.

    dump_prompt    — if True, logs the exact system prompt + full user message sent
    to the model. Temporary debugging aid; set to False when investigation is done.

    skip_history   — if True, the Q+A pair is NOT stored in conversation_histories.
    Use for high-risk factual book questions where a wrong answer must not become
    "evidence" that anchors future responses.

    allow_voice    — if False, always send one text reply even when the model
    requests a voice response. Public reading-group commands use this to avoid
    delivering an audio message plus a duplicate text message.
    """
    user_id = update.effective_user.id if update.effective_user else 0
    display_name = (
        update.effective_user.first_name
        if update.effective_user
        else None
    )
    username = display_name or "user"

    # Resolve which history slot to use.
    # For shared group discussions, history_key is the chat_id (negative int).
    # For solo interactions it falls back to user_id.
    hkey = history_key if history_key is not None else user_id

    # Clear history when the conversation window has expired.
    # Only applies to solo histories — shared discussions manage their own
    # timeout via _group_discussions["last_activity"].
    if hkey == user_id:
        last_seen = _conv_last_seen.get(user_id)
        if last_seen is not None and (time.monotonic() - last_seen) >= _CONV_TIMEOUT_SECS:
            conversation_histories[user_id].clear()
            logger.info(
                "send_ai_reply: session window expired for user %s — history cleared", user_id,
            )

    history = conversation_histories[hkey]

    # Prepend the user's name as context so Gemini can address them naturally.
    # Store only the raw text in history to keep it clean across turns.
    contextualized = (
        f"[اسم المستخدم: {display_name}]\n{user_text}"
        if display_name
        else user_text
    )
    if extra_context:
        contextualized = f"{extra_context}\n\n{contextualized}"
    # Build the parts list for this turn.
    # Image bytes (when present) are included here for Gemini but are never
    # persisted — conversation_histories always stores only plain text.
    user_parts: list = []
    if image_bytes:
        user_parts.append(
            types.Part(inline_data=types.Blob(data=image_bytes, mime_type=image_mime))
        )
    user_parts.append(types.Part(text=contextualized))
    contents = history + [types.Content(role="user", parts=user_parts)]

    # ── Temporary prompt dump (remove when investigation is complete) ─────────
    if dump_prompt:
        logger.info(
            "[DIAG DUMP] ━━━ SYSTEM PROMPT (sp_version=%s, len=%d chars) ━━━\n%s",
            SYSTEM_PROMPT_VERSION, len(SYSTEM_PROMPT), SYSTEM_PROMPT,
        )
        if history:
            for i, turn in enumerate(history):
                role = getattr(turn, "role", "?")
                text = "".join(
                    getattr(p, "text", "")
                    for p in (getattr(turn, "parts", None) or [])
                )
                logger.info(
                    "[DIAG DUMP] ── HISTORY[%d] role=%s len=%d ──\n%s",
                    i, role, len(text), text,
                )
        else:
            logger.info("[DIAG DUMP] ── HISTORY: empty ──")
        logger.info(
            "[DIAG DUMP] ━━━ FINAL USER MESSAGE (len=%d chars) ━━━\n%s",
            len(contextualized), contextualized,
        )
    # ── End prompt dump ───────────────────────────────────────────────────────

    _search_tools = (
        [types.Tool(google_search=types.GoogleSearch())]
        if use_search
        else None
    )
    try:
        raw_text = await _ai_generate(
            contents=contents,
            system_instruction=SYSTEM_PROMPT,
            label=f"send_ai_reply:{username}",
            tools=_search_tools,
        )
    except RuntimeError as _rt_err:
        _rt_msg = str(_rt_err)
        if _rt_msg == "gemini_auth_error":
            logger.error("send_ai_reply: auth error for user %s", user_id)
            if update.message:
                await update.message.reply_text(
                    "🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول."
                )
            return False
        if _rt_msg == "gemini_empty_response" and image_bytes:
            # Image likely triggered Gemini's safety filter — retry with text only.
            logger.warning(
                "send_ai_reply: safety-filtered (image) for %s — retrying text-only", username,
            )
            _text_only_contents = history + [
                types.Content(role="user", parts=[types.Part(text=contextualized)])
            ]
            try:
                raw_text = await _ai_generate(
                    contents=_text_only_contents,
                    system_instruction=SYSTEM_PROMPT,
                    label=f"send_ai_reply:{username}:text-only",
                    tools=_search_tools,
                )
                logger.info("send_ai_reply: text-only retry succeeded for %s", username)
            except RuntimeError:
                logger.warning(
                    "send_ai_reply: image text-only fallback also safety-filtered for %s", username,
                )
                if update.message:
                    await update.message.reply_text(
                        "لم أستطع الإجابة — الصورة تجاوزت مرشحات الأمان. "
                        "جرّب إرسال سؤالك بدون الصورة."
                    )
                return
        elif _rt_msg == "gemini_empty_response":
            # Retry without the reading-context prefix — it sometimes over-triggers
            # Gemini's refusal on purely factual questions.
            logger.warning(
                "send_ai_reply: safety-filtered (no image) for %s — retrying bare", username,
            )
            _bare = (
                f"[اسم المستخدم: {display_name}]\n{user_text}"
                if display_name
                else user_text
            )
            _bare_contents = history + [
                types.Content(role="user", parts=[types.Part(text=_bare)])
            ]
            try:
                raw_text = await _ai_generate(
                    contents=_bare_contents,
                    system_instruction=SYSTEM_PROMPT,
                    label=f"send_ai_reply:{username}:bare-retry",
                )
                logger.info("send_ai_reply: bare retry succeeded for %s", username)
            except RuntimeError:
                # Last resort: retry with no system prompt at all.
                # If the system prompt's spoiler rules are what's blocking a
                # genuinely factual question, this will succeed.
                logger.warning(
                    "send_ai_reply: bare retry filtered for %s — retrying no-sysprompt", username,
                )
                try:
                    raw_text = await _ai_generate(
                        contents=_bare_contents,
                        system_instruction=None,
                        label=f"send_ai_reply:{username}:no-sysprompt",
                    )
                    logger.info("send_ai_reply: no-sysprompt retry succeeded for %s", username)
                except RuntimeError:
                    logger.warning(
                        "send_ai_reply: no-sysprompt retry also safety-filtered for %s", username,
                    )
                    if update.message:
                        await update.message.reply_text("لم أستطع الإجابة على هذا السؤال.")
                    return False
        elif _rt_msg == "gemini_rate_limited":
            logger.warning(
                "send_ai_reply: Gemini rate-limited — all retries exhausted for user %s", user_id,
            )
            if update.message:
                await update.message.reply_text(
                    "⏳ الذكاء الاصطناعي مشغول حالياً — جرّب بعد دقيقة أو دقيقتين."
                )
            return False
        else:
            logger.error("send_ai_reply: Gemini unavailable for user %s", user_id)
            if update.message:
                await update.message.reply_text(
                    "⚠️ خدمة الذكاء الاصطناعي غير متاحة حالياً.\n"
                    "حاول مرة أخرى بعد قليل."
                )
            return False

    use_voice, reply_text = parse_reply(raw_text)
    if use_voice and not allow_voice:
        logger.info("send_ai_reply: voice suppressed by delivery policy for %s", username)
        use_voice = False
    reply_text = _md_to_html(reply_text)  # safety net: Markdown → HTML

    if skip_history:
        logger.info(
            "send_ai_reply: skip_history=True — turn not stored for user %s",
            user_id,
        )
    else:
        conversation_histories[hkey].append(
            types.Content(role="user", parts=[types.Part(text=user_text)])
        )
        conversation_histories[hkey].append(
            types.Content(role="model", parts=[types.Part(text=reply_text)])
        )
        if len(conversation_histories[hkey]) > 20:
            conversation_histories[hkey] = conversation_histories[hkey][-20:]
    _conv_last_seen[user_id] = time.monotonic()  # always update; drives the inactivity window

    if use_voice:
        await context.bot.send_chat_action(
            chat_id=update.effective_chat.id, action="record_voice"
        )
        voice_path = await text_to_voice_file(reply_text)
        if voice_path:
            try:
                with open(voice_path, "rb") as vf:
                    await update.message.reply_voice(
                        voice=vf,
                        write_timeout=60, read_timeout=60,
                    )
                # Always send the full text as a separate reply so it's complete and readable
                try:
                    await update.message.reply_text(reply_text, parse_mode="HTML")
                except TgBadRequest as _tg_err:
                    logger.warning(
                        "HTML parse failed in voice text for %s (%s) — retrying plain",
                        username, _tg_err,
                    )
                    await update.message.reply_text(_strip_html(reply_text))
                logger.info("Voice reply sent to %s", username)
            finally:
                os.unlink(voice_path)
            return True

    # TEXT reply (or voice generation failed)
    await context.bot.send_chat_action(
        chat_id=update.effective_chat.id, action="typing"
    )
    text_to_send = reply_text
    try:
        await update.message.reply_text(text_to_send, parse_mode="HTML")
    except TgBadRequest as _tg_err:
        logger.warning(
            "HTML parse failed in text reply for %s (%s) — first 200 chars: %r",
            username, _tg_err, text_to_send[:200],
        )
        await update.message.reply_text(_strip_html(text_to_send))
    logger.info("Text reply sent to %s", username)
    return True


# ━━━ Suggestion system ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


def _from_configured_chat(update: Update) -> bool:
    """Return True iff this update originates from the configured reading group."""
    if not update.effective_chat:
        return False
    try:
        return int(update.effective_chat.id) == int(CHAT_ID)
    except (ValueError, TypeError):
        return str(update.effective_chat.id) == str(CHAT_ID)


def _is_owner_dm(update: Update) -> bool:
    """Return True iff this update is from the registered owner in a private DM with the bot."""
    if update.effective_chat is None or update.effective_user is None:
        return False
    return (
        update.effective_chat.type == "private"
        and auth_store.is_owner(update.effective_user.id)
    )


async def _redirect_to_dm(update: Update) -> None:
    """
    Respond to a DM-only command used outside of DM.
    Only the owner gets a redirect message; all other senders receive silence
    so that DM-only commands are invisible from the reading group's perspective.
    """
    if (
        update.message is not None
        and update.effective_user is not None
        and auth_store.is_owner(update.effective_user.id)
    ):
        await update.message.reply_text(
            "⚙️ هذا الأمر متاح فقط في المحادثة الخاصة مع البوت."
        )


def _adapter_redirect(command: str) -> str:
    """
    Build the community transition redirect message for a command that has
    migrated from Takbeer to the Adapter bot (رفيق وقت).

    Uses positive transition language ("انتقل إلى") rather than deprecation
    language so the message feels like a natural handover. Set
    ADAPTER_BOT_USERNAME in the environment to include the @mention; omit it
    and the message shows the command and bot name without an @handle.
    """
    mention = f"@{ADAPTER_BOT_USERNAME} " if ADAPTER_BOT_USERNAME else ""
    return (
        "هذا الأمر انتقل إلى رفيق وقت.\n\n"
        f"استخدم:\n{mention}{command}"
    )


async def _is_group_creator(user_id: int, chat_id: int | str, bot) -> bool:
    """Return True if user is the Telegram group/channel creator."""
    try:
        member = await bot.get_chat_member(chat_id=chat_id, user_id=user_id)
        return member.status == "creator"
    except Exception:
        return False


async def _ensure_owner(user_id: int, chat_id: int | str, bot) -> bool:
    """
    Return True if user is the registered bot owner.
    On first call, auto-registers the group creator as owner and
    re-registers the command menu so /addmanager and /removemanager
    appear for them immediately.

    Owner bootstrap is restricted to the configured reading group
    (TELEGRAM_CHAT_ID) so that creators of unrelated groups cannot
    claim global ownership.
    """
    if auth_store.is_owner(user_id):
        return True
    if auth_store.get_owner_id() is None:
        # Only allow auto-registration from the configured group.
        try:
            same_chat = int(chat_id) == int(CHAT_ID)
        except (ValueError, TypeError):
            same_chat = str(chat_id) == str(CHAT_ID)
        if not same_chat:
            logger.warning(
                "_ensure_owner: bootstrap attempt from non-configured chat %s by user %s — ignored",
                chat_id, user_id,
            )
            return False
        if await _is_group_creator(user_id, chat_id, bot):
            auth_store.set_owner(user_id)
            logger.info("Auto-registered group creator %s as bot owner", user_id)
            # Re-register commands so owner scope (addmanager/removemanager) appears
            asyncio.create_task(_register_commands(bot))
            return True
    return False


async def addmanager_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /addmanager — add a manager.
    Usage: reply to the target user's message and send /addmanager
           OR: /addmanager <numeric_user_id>
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    requester_id = update.effective_user.id

    # Resolve target from replied message or numeric arg
    if update.message.reply_to_message and update.message.reply_to_message.from_user:
        target = update.message.reply_to_message.from_user
        target_id = target.id
        target_name = target.first_name or str(target_id)
    elif context.args:
        try:
            target_id = int(context.args[0])
            target_name = str(target_id)
        except ValueError:  # log-exempt: invalid user input; int() parse failure is a user error, usage hint is the correct response
            await update.message.reply_text(
                "الاستخدام: رد على رسالة العضو وأرسل /addmanager\n"
                "أو: /addmanager <user_id>"
            )
            return
    else:
        await update.message.reply_text(
            "الاستخدام: رد على رسالة العضو وأرسل /addmanager"
        )
        return

    if target_id == requester_id:
        await update.message.reply_text("⚠️ المالك لديه صلاحيات كاملة تلقائياً.")
        return

    added = auth_store.add_manager(target_id)
    if added:
        await update.message.reply_text(f"✅ تمت إضافة {target_name} مديراً للبوت.")
    else:
        await update.message.reply_text(f"ℹ️ {target_name} مدير بالفعل.")


async def removemanager_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /removemanager — remove a manager.
    Usage: reply to the target user's message and send /removemanager
           OR: /removemanager <numeric_user_id>
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    requester_id = update.effective_user.id

    if update.message.reply_to_message and update.message.reply_to_message.from_user:
        target = update.message.reply_to_message.from_user
        target_id = target.id
        target_name = target.first_name or str(target_id)
    elif context.args:
        try:
            target_id = int(context.args[0])
            target_name = str(target_id)
        except ValueError:  # log-exempt: invalid user input; int() parse failure is a user error, usage hint is the correct response
            await update.message.reply_text(
                "الاستخدام: رد على رسالة العضو وأرسل /removemanager"
            )
            return
    else:
        await update.message.reply_text(
            "الاستخدام: رد على رسالة العضو وأرسل /removemanager"
        )
        return

    removed = auth_store.remove_manager(target_id)
    if removed:
        await update.message.reply_text(f"✅ تمت إزالة صلاحيات {target_name}.")
    else:
        await update.message.reply_text(f"ℹ️ {target_name} ليس مديراً.")


async def opensuggestions_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/opensuggestions — open the book nomination round. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    if suggestion_store.is_open():
        await update.message.reply_text("ℹ️ الترشيحات مفتوحة بالفعل.")
        return

    # Roadmap guard
    if not roadmap_store.can_open_nominations():
        status = roadmap_store.get_status()
        if status == "completed":
            await update.message.reply_text(
                "🏁 <b>اكتملت خارطة القراءة.</b>\n\n"
                "لا يمكن فتح ترشيحات جديدة حتى يتم إنشاء خارطة قراءة جديدة.\n"
                "استخدم /startroadmap لبدء خارطة جديدة.",
                parse_mode="HTML",
            )
        else:
            await update.message.reply_text(
                "🗺️ <b>لا توجد خارطة قراءة نشطة.</b>\n\n"
                "يجب إنشاء خارطة قراءة أولاً.\n"
                "استخدم /startroadmap لبدء تصويت الخارطة.",
                parse_mode="HTML",
            )
        return

    # Use grace period if this is the one-time pre-roadmap cycle
    if roadmap_store.get_status() == "none":
        roadmap_store.use_grace()

    active_cat = roadmap_store.get_active_category()
    context.user_data["pending_sendgroup"] = {
        "type": "suggestions_open",
        "category": active_cat,
    }
    cat_hint = f"\n📂 <b>التصنيف:</b> {active_cat}" if active_cat else ""
    await update.message.reply_text(
        f"📋 <b>فتح الترشيحات</b>{cat_hint}\n\n"
        "سيُرسل قالب الترشيحات للمجموعة ويُثبَّت تلقائياً.\n\n"
        "اضغط الزر لنشر قالب الترشيحات وبدء الجولة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("opensuggestions prepared in DM by user %s", update.effective_user.id)


async def closesuggestions_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/closesuggestions — close the book nomination round. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    if not suggestion_store.is_open():
        await update.message.reply_text("ℹ️ الترشيحات مغلقة بالفعل.")
        return

    suggestion_store.close_suggestions()
    count = len(suggestion_store.get_suggestions())

    context.user_data["pending_sendgroup"] = {"type": "close_suggestions"}
    await update.message.reply_text(
        f"🔒 <b>تم إغلاق الترشيحات</b>\n\nعدد الكتب المرشحة: <b>{count}</b>\n\n"
        "اضغط الزر لإعلام المجموعة بالإغلاق وعرض القائمة النهائية:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("Suggestions closed by user %s, total=%d", update.effective_user.id, count)


async def synctemplate_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/synctemplate — rebuild and re-edit the official nomination template. Owner DM only.

    Use this when the pinned template message is out of sync with the stored
    nominations (e.g. after a data correction or bot restart).
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    if not suggestion_store.is_open():
        await update.message.reply_text("ℹ️ الترشيحات مغلقة — لا يوجد قالب لتحديثه.")
        return

    tmpl_id = suggestion_store.get_template_message_id()
    if not tmpl_id:
        await update.message.reply_text("⚠️ لا يوجد معرّف رسالة قالب محفوظ.")
        return

    chat_id = int(os.environ.get("TELEGRAM_CHAT_ID", "0"))
    if not chat_id:
        await update.message.reply_text("⚠️ TELEGRAM_CHAT_ID غير مُعيَّن.")
        return

    category = roadmap_store.get_active_category()
    count    = len(suggestion_store.get_suggestions())

    try:
        await context.bot.edit_message_text(
            chat_id=chat_id,
            message_id=tmpl_id,
            text=suggestion_store.build_template_text(category=category),
            parse_mode="HTML",
        )
        await update.message.reply_text(
            f"✅ تم تحديث القالب الرسمي.\n\n"
            f"عدد الترشيحات الحالي: <b>{count}</b>",
            parse_mode="HTML",
        )
        logger.info(
            "synctemplate: template rebuilt (chat=%s msg=%s count=%d) by user %s",
            chat_id, tmpl_id, count, update.effective_user.id,
        )
    except Exception as exc:
        await update.message.reply_text("⚠️ فشل تحديث القالب، يرجى المحاولة مرة أخرى.")
        logger.error("synctemplate: edit_message_text failed: %s", exc)


def _parse_review_classifications(
    raw: str,
    suggestions: list[dict],
    active_category: str,
) -> list[dict]:
    """
    Parse the JSON array returned by Gemini for batch review classification.
    Falls back to safe defaults for any book Gemini skipped or returned invalid data for.
    """
    sug_by_num = {s["number"]: s for s in suggestions}

    try:
        m = re.search(r"\[[\s\S]*\]", raw)
        if not m:
            raise ValueError("no JSON array in response")
        items: list[dict] = json.loads(m.group())
    except Exception as exc:
        logger.warning("review_v2: JSON parse failed: %s — using safe defaults for all", exc)
        items = []

    results: list[dict] = []
    parsed_nums: set[int] = set()

    for item in items:
        try:
            num = int(item.get("number", 0))
        except (TypeError, ValueError):
            continue
        if num not in sug_by_num:
            continue

        sug        = sug_by_num[num]
        primary    = item.get("primary_category", active_category)
        if not category_constitution.is_valid_primary_category(primary):
            primary = active_category

        confidence = item.get("confidence", "high")
        if confidence not in ("high", "medium", "low"):
            confidence = "high"

        ai_action = item.get("ai_action", "")
        if ai_action not in ("approve", "postpone"):
            ai_action = "approve" if primary == active_category else "postpone"

        # Parse optional alternative classification
        alt_cat  = item.get("alternative_category")
        alt_conf = item.get("alternative_confidence")
        alt_reas = item.get("alternative_reasoning")
        # Normalize null-like values from Gemini
        if alt_cat in (None, "null", ""):
            alt_cat, alt_conf, alt_reas = None, None, None
        if alt_cat and not category_constitution.is_valid_primary_category(alt_cat):
            alt_cat, alt_conf, alt_reas = None, None, None
        if alt_conf not in ("high", "medium", "low"):
            alt_conf = "medium" if alt_cat else None

        parsed_nums.add(num)
        results.append({
            "original_number":       num,
            "title":                 sug["title"],
            "nominator":             sug.get("submitted_by", ""),
            "nominator_id":          sug.get("user_id"),
            "nominated_at":          sug.get("submitted_at", ""),
            "primary_category":      primary,
            "confidence":            confidence,
            "ai_action":             ai_action,
            "reasoning":             item.get("reasoning", ""),
            "destination_note":      item.get("destination_note", ""),
            "alternative_category":  alt_cat,
            "alternative_confidence": alt_conf,
            "alternative_reasoning":  alt_reas,
            "classifier":            "gemini",
            "decision":              None,
            "message_id":            None,
        })

    # Fill any books Gemini skipped with safe defaults
    for sug in suggestions:
        if sug["number"] not in parsed_nums:
            results.append({
                "original_number":       sug["number"],
                "title":                 sug["title"],
                "nominator":             sug.get("submitted_by", ""),
                "nominator_id":          sug.get("user_id"),
                "nominated_at":          sug.get("submitted_at", ""),
                "primary_category":      active_category,
                "confidence":            "high",
                "ai_action":             "approve",
                "reasoning":             "تصنيف افتراضي (لم يُحلَّل بواسطة الذكاء الاصطناعي)",
                "destination_note":      "",
                "alternative_category":  None,
                "alternative_confidence": None,
                "alternative_reasoning":  None,
                "classifier":            "none",
                "decision":              None,
                "message_id":            None,
            })

    results.sort(key=lambda r: r["original_number"])
    return results


async def reviewsuggestions_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /reviewsuggestions — classify every nomination via the Category Constitution,
    then send one per-book review card to the owner's DM. Owner DM only.

    Flow:
      1. One batch Gemini call with the full Constitution → JSON per-book classifications.
      2. N individual DM cards, each with ✅ قبول | 📦 تأجيل | 🗑️ إزالة buttons.
      3. Owner decides per card; card collapses to a one-line status.
      4. When all cards are actioned → summary + postponement announcement draft.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    # Load the full original nomination list — never pruned by previous reviews.
    # Falls back to the live list for cycles that pre-date this field.
    suggestions = suggestion_store.get_original_suggestions()
    if not suggestions:
        await update.message.reply_text("ℹ️ لا توجد ترشيحات للمراجعة.")
        return

    category = roadmap_store.get_active_category()
    if not category:
        await update.message.reply_text(
            "⚠️ لا توجد خارطة قراءة نشطة — لا يمكن تحديد التصنيف المطلوب.\n\n"
            "يمكنك بدء خارطة قراءة جديدة عبر /startroadmap.",
            parse_mode="HTML",
        )
        return

    # ── Stage 1: Constitution rule engine (deterministic first pass) ──────────
    rule_by_num: dict[int, category_constitution.RuleClassification] = {}
    needs_gemini: list[dict] = []
    for s in suggestions:
        rule = category_constitution.classify_book(s["title"])
        rule_by_num[s["number"]] = rule
        if rule.confidence != "high":
            needs_gemini.append(s)

    high_count = len(suggestions) - len(needs_gemini)
    if needs_gemini and high_count:
        hold_text = (
            f"⏳ صنّف دستور التصنيف {high_count} كتاب مباشرة — "
            f"جارٍ استشارة Gemini لـ {len(needs_gemini)} كتاب…"
        )
    elif needs_gemini:
        hold_text = f"⏳ جارٍ استشارة Gemini لتصنيف {len(suggestions)} ترشيح…"
    else:
        hold_text = f"⏳ جارٍ مراجعة {len(suggestions)} ترشيح وفق دستور التصنيف…"

    hold_msg = await update.message.reply_text(hold_text)

    # ── Stage 2: Gemini call for ambiguous books only ──────────────────────────
    gemini_by_num: dict[int, dict] = {}
    if needs_gemini:
        books_for_prompt = [{"number": s["number"], "title": s["title"]} for s in needs_gemini]
        prompt = category_constitution.build_review_prompt(category, books_for_prompt)
        try:
            raw = await _ai_generate(
                contents=[prompt],
                system_instruction="",
                label="review_v2",
            )
        except RuntimeError as e:
            err = str(e)
            logger.warning("reviewsuggestions v2: Gemini failed — %s", e)
            try:
                await hold_msg.delete()
            except Exception:  # log-exempt: best-effort Telegram message deletion
                pass
            if err == "gemini_auth_error":
                await update.message.reply_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
            elif err == "gemini_unavailable":
                await update.message.reply_text("⚠️ الذكاء الاصطناعي غير متاح حالياً.")
            elif "rate" in err or "429" in err:
                await update.message.reply_text("⏳ النموذج مشغول — جرّب مجدداً بعد لحظة.")
            else:
                await update.message.reply_text("⚠️ تعذّر إجراء التحليل — جرّب مجدداً.")
            return

        for item in _parse_review_classifications(raw, needs_gemini, category):
            gemini_by_num[item["original_number"]] = item

    try:
        await hold_msg.delete()
    except Exception:  # log-exempt: best-effort Telegram message deletion
        pass

    # ── Stage 3: Merge rule + Gemini results into final classification list ────
    classifications: list[dict] = []
    for s in suggestions:
        num  = s["number"]
        rule = rule_by_num[num]

        if rule.confidence == "high":
            # Deterministic — skip Gemini for this book
            ai_action = "approve" if rule.category == category else "postpone"
            classifications.append({
                "original_number":       num,
                "title":                 s["title"],
                "nominator":             s.get("submitted_by", ""),
                "nominator_id":          s.get("user_id"),
                "nominated_at":          s.get("submitted_at", ""),
                "primary_category":      rule.category,
                "confidence":            "high",
                "ai_action":             ai_action,
                "reasoning":             rule.reasoning,
                "destination_note":      "",
                "alternative_category":  None,
                "alternative_confidence": None,
                "alternative_reasoning":  None,
                "classifier":            "rule",
                "decision":              None,
                "message_id":            None,
            })
        elif num in gemini_by_num:
            classifications.append(gemini_by_num[num])
        else:
            # Gemini skipped this book — fall back to rule result or defaults
            fallback_cat = rule.category or category
            ai_action = "approve" if fallback_cat == category else "postpone"
            classifications.append({
                "original_number":       num,
                "title":                 s["title"],
                "nominator":             s.get("submitted_by", ""),
                "nominator_id":          s.get("user_id"),
                "nominated_at":          s.get("submitted_at", ""),
                "primary_category":      fallback_cat,
                "confidence":            rule.confidence if rule.category else "low",
                "ai_action":             ai_action,
                "reasoning":             rule.reasoning or "تصنيف افتراضي",
                "destination_note":      "",
                "alternative_category":  None,
                "alternative_confidence": None,
                "alternative_reasoning":  None,
                "classifier":            "rule" if rule.category else "none",
                "decision":              None,
                "message_id":            None,
            })

    classifications.sort(key=lambda c: c["original_number"])

    # ── Send one card per book ─────────────────────────────────────────────────
    chat_id = update.effective_chat.id
    book_cards: list[dict] = []

    for cls in classifications:
        n   = cls["original_number"]
        has_alt = bool(cls.get("alternative_category"))

        card_text = _build_review_card_text(
            book_num=n,
            title=cls["title"],
            nominator=cls["nominator"],
            nominated_at=cls["nominated_at"],
            primary_category=cls["primary_category"],
            confidence=cls["confidence"],
            ai_action=cls["ai_action"],
            reasoning=cls["reasoning"],
            destination_note=cls["destination_note"],
            alternative_category=cls.get("alternative_category"),
            alternative_confidence=cls.get("alternative_confidence"),
            alternative_reasoning=cls.get("alternative_reasoning"),
            classifier=cls.get("classifier", "gemini"),
        )

        if has_alt:
            row_decide = [
                InlineKeyboardButton("✅ قبول (أساسي)", callback_data=f"rev2:approve:{n}"),
                InlineKeyboardButton("✅ قبول (بديل)",  callback_data=f"rev2:approve_alt:{n}"),
            ]
            row_other = [
                InlineKeyboardButton("📦 تأجيل", callback_data=f"rev2:postpone:{n}"),
                InlineKeyboardButton("🗑️ إزالة", callback_data=f"rev2:remove:{n}"),
            ]
            card_keyboard = InlineKeyboardMarkup([
                row_decide,
                row_other,
                [InlineKeyboardButton("🤖 رأي Gemini", callback_data=f"rev2:gemini_opinion:{n}")],
            ])
        else:
            card_keyboard = InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("✅ قبول",   callback_data=f"rev2:approve:{n}"),
                    InlineKeyboardButton("📦 تأجيل", callback_data=f"rev2:postpone:{n}"),
                    InlineKeyboardButton("🗑️ إزالة", callback_data=f"rev2:remove:{n}"),
                ],
                [InlineKeyboardButton("🤖 رأي Gemini", callback_data=f"rev2:gemini_opinion:{n}")],
            ])

        try:
            msg = await context.bot.send_message(
                chat_id=chat_id,
                text=card_text,
                parse_mode="HTML",
                reply_markup=card_keyboard,
            )
            cls["message_id"] = msg.message_id
        except Exception as exc:
            logger.error("reviewsuggestions_v2: failed to send card #%d: %s",
                         cls["original_number"], exc)
            cls["message_id"] = None

        book_cards.append(cls)

    # ── Store review session state ─────────────────────────────────────────────
    context.user_data["rev2"] = {
        "books":           book_cards,
        "active_category": category,
    }

    # ── Summary header ─────────────────────────────────────────────────────────
    n_approve = sum(1 for c in classifications if c["ai_action"] == "approve")
    n_postpone = len(classifications) - n_approve
    summary_parts = [f"{len(classifications)} ترشيح"]
    if n_approve:
        summary_parts.append(f"{n_approve} ✅ مقترح للقبول")
    if n_postpone:
        summary_parts.append(f"{n_postpone} 📦 مقترح للتأجيل")

    await context.bot.send_message(
        chat_id=chat_id,
        text=(
            f"📊 <b>{'  ·  '.join(summary_parts)}</b>\n\n"
            "راجع كل بطاقة واتخذ قرارك، ثم شغّل /startvote عند الانتهاء."
        ),
        parse_mode="HTML",
    )

    logger.info(
        "reviewsuggestions_v2: sent %d cards to owner %s (approve=%d postpone=%d)",
        len(classifications), update.effective_user.id, n_approve, n_postpone,
    )


def _postponed_dm_text(category: str, entries: list[dict]) -> str:
    """Build the owner DM notification text for postponed nominations."""
    lines = [
        f"📦 <b>ترشيحات مؤجَّلة — التصنيف النشط الجديد: {_html.escape(category)}</b>",
        "",
        f"لديك <b>{len(entries)}</b> ترشيح مؤجَّل يناسب هذا التصنيف:",
        "",
    ]
    for e in entries:
        title     = _html.escape(e.get("title", ""))
        nominator = _html.escape(e.get("nominator") or "—")
        raw_date  = e.get("nominated_at", "")
        try:
            date_str = datetime.fromisoformat(raw_date).strftime("%Y-%m-%d")
        except Exception:
            date_str = raw_date[:10] if raw_date else "—"
        reason = _html.escape(e.get("ai_reason") or "")
        conf   = e.get("ai_confidence", "")
        conf_badge = {"high": "🟢", "medium": "🟡", "low": "🔴"}.get(conf, "")
        lines.append(f"• <b>{title}</b>  {conf_badge}")
        lines.append(f"  رشّحه: {nominator} · {date_str}")
        if reason:
            lines.append(f"  <i>«{reason}»</i>")
        lines.append("")
    lines.append(
        "⚠️ هذه الترشيحات لن تُضاف تلقائياً إلى التصويت.\n"
        "يمكنك مراجعتها واتخاذ القرار المناسب عند فتح ترشيحات هذه المرحلة."
    )
    return "\n".join(lines)


def _build_postponement_announcement(entries: list[dict]) -> str:
    """Build the consolidated group announcement for all postponed nominations."""
    lines = [
        "📦 <b>ترشيحات مؤجَّلة إلى مراحل مستقبلية</b>",
        "",
        "بعد مراجعة ترشيحات هذه الدورة، تم تأجيل الكتب التالية.",
        "هذه الكتب <b>لم تُرفَض</b> — بل هي ترشيحات جيدة تنتمي إلى تصنيف مختلف"
        " في خارطة القراءة وستُراجَع من قِبل المدير عند حلول تلك المرحلة. 🗺️",
        "",
    ]
    for e in entries:
        title  = _html.escape(e.get("title", ""))
        cat    = _html.escape(e.get("target_category") or "—")
        reason = _html.escape(e.get("ai_reason") or "")
        lines.append(f"• <b>{title}</b>")
        lines.append(f"  المرحلة: {cat}")
        if reason:
            lines.append(f"  <i>{reason}</i>")
        lines.append("")
    return "\n".join(lines).rstrip()


async def _finalize_postponements(
    context: ContextTypes.DEFAULT_TYPE,
    owner_chat_id: int,
) -> None:
    """
    Batch-classify all pending postponements in a single Gemini call,
    persist results to postponed_store, and send one consolidated
    announcement draft to the owner for approval.
    """
    pending = postponed_store.get_pending()
    if not pending:
        return

    roadmap_display  = roadmap_store.get_roadmap_display() or []
    active_category  = roadmap_store.get_active_category() or ""

    # Only offer upcoming (non-active) categories as postponement targets.
    # Books were postponed specifically because they don't fit the active stage,
    # so assigning them back to the active category would be wrong.
    valid_roadmap_entries = [
        entry
        for entry in roadmap_display
        if (
            isinstance(entry, dict)
            and isinstance(entry.get("category"), str)
            and entry["category"].strip()
            and isinstance(entry.get("state"), str)
        )
    ]
    upcoming_cats = [
        entry["category"]
        for entry in valid_roadmap_entries
        if entry["state"] == "upcoming"
    ]
    target_cats   = upcoming_cats if upcoming_cats else [
        entry["category"]
        for entry in valid_roadmap_entries
        if entry["category"] != active_category
    ]
    # Absolute fallback: if roadmap has only one stage, allow all categories
    if not target_cats:
        target_cats = [entry["category"] for entry in valid_roadmap_entries]

    _primary_cats = category_constitution.get_all_category_names()
    fallback_category = (
        target_cats[0]
        if target_cats
        else (active_category or (_primary_cats[0] if _primary_cats else "غير محدد"))
    )

    prompt = category_constitution.build_postpone_prompt(active_category, pending, target_cats)

    classifications: list[dict] = []
    try:
        raw = await _ai_generate([prompt], label="postpone_batch")
        m = re.search(r"\[[\s\S]*\]", raw)
        if not m:
            raise ValueError("no JSON array found in Gemini response")
        classifications = json.loads(m.group())
        logger.info("_finalize_postponements: classified %d books", len(classifications))
    except Exception as exc:
        logger.error("_finalize_postponements: Gemini failed — using fallback: %s", exc)
        # Use the first entry from target_cats as the fallback so postponed books
        # are never silently placed back into the active stage.  target_cats already
        # excludes active_category when upcoming categories are available, so this
        # preserves the invariant that postponements belong to upcoming stages.
        # If target_cats is also empty (roadmap is completely empty) fall back to
        # active_category; and if that too is empty, use the first constitutional
        # primary category so the field is never stored as a blank string.
        classifications = [
            {"title": e["title"], "category": fallback_category, "reason": ""}
            for e in pending
        ]

    by_title: dict[str, dict] = {c.get("title", ""): c for c in classifications}

    for e in pending:
        match = by_title.get(e["title"]) or {}
        suggested_category = match.get("category")
        # Gemini can match a title correctly while returning the active category
        # or a category outside the roadmap's permitted postponement targets.
        # Preserve the non-active-stage invariant by accepting its choice only
        # when it is one of the categories offered in the prompt.
        target_category = (
            suggested_category
            if suggested_category in target_cats
            else fallback_category
        )
        postponed_store.finalize_pending(
            e["id"],
            target_category=target_category,
            ai_reason=match.get("reason") or "",
        )

    # Reload finalized entries (in the same order as pending)
    finalized_titles = [e["title"] for e in pending]
    all_entries      = {e["title"]: e for e in postponed_store.get_all() if not e.get("pending")}
    finalized        = [all_entries[t] for t in finalized_titles if t in all_entries]

    announcement = _build_postponement_announcement(finalized)

    context.user_data["pending_sendgroup"] = {
        "type":       "text",
        "text":       announcement,
        "parse_mode": "HTML",
    }

    count      = len(pending)
    books_list = "\n".join(f"• {_html.escape(e['title'])}" for e in finalized)
    await context.bot.send_message(
        chat_id=owner_chat_id,
        text=(
            f"📦 <b>تصنيف {count} كتاب مؤجَّل اكتمل</b>\n\n"
            f"{books_list}\n\n"
            f"<i>النص الذي سيُرسَل للمجموعة:</i>\n"
            f"───────────────\n"
            f"{announcement}\n"
            f"───────────────\n\n"
            "اضغط الزر لإعلام المجموعة، أو تجاهله إذا لم تشأ."
        ),
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )


async def _finalize_rev2_review(
    context: ContextTypes.DEFAULT_TYPE,
    owner_chat_id: int,
    books: list[dict],
    active_category: str,
) -> None:
    """
    Called when all rev2 review cards have been actioned.
    Rebuilds the live suggestions list to exactly the approved set, then sends
    a summary and (if any books were postponed) a postponement announcement draft.
    The rebuilt suggestions list is the single source of truth for /startvote.
    """
    approved  = [b for b in books if b.get("decision") == "approved"]
    postponed = [b for b in books if b.get("decision") == "postponed"]
    removed   = [b for b in books if b.get("decision") == "removed"]

    # ── Rebuild suggestions to exactly the approved set ────────────────────────
    # This is the authoritative nomination list that /startvote will read.
    suggestion_store.set_suggestions([
        {
            "title":        b["title"],
            "submitted_by": b.get("nominator", ""),
            "user_id":      b.get("nominator_id"),
            "source":       b.get("source", "member"),
            "submitted_at": b.get("nominated_at", ""),
        }
        for b in approved
    ])
    logger.info(
        "_finalize_rev2_review: rebuilt suggestions with %d approved books "
        "(%d postponed, %d removed)",
        len(approved), len(postponed), len(removed),
    )

    # Mark review as done so /startvote suppresses the "not yet reviewed" hint.
    context.user_data["review_done"] = True

    summary_lines: list[str] = [
        "✅ <b>اكتملت مراجعة الترشيحات</b>",
        "",
        f"• {len(approved)} كتاب قُبل — سيكون ضمن التصويت",
        f"• {len(postponed)} كتاب مؤجَّل إلى مراحل مستقبلية",
        f"• {len(removed)} كتاب أُزيل من الترشيحات",
    ]

    if approved:
        summary_lines += ["", "📚 الكتب المقبولة:"]
        summary_lines += [f"  • {_html.escape(b['title'])}" for b in approved]

    if not approved:
        summary_lines += ["", "⚠️ لا توجد ترشيحات متبقية — تحقق قبل تشغيل /startvote."]
    elif len(approved) > vote_store.MAX_POLL_OPTIONS:
        summary_lines += [
            "",
            f"⚠️ <b>عدد الكتب المقبولة ({len(approved)}) يتجاوز الحد الأقصى لاستفتاء تيليغرام ({vote_store.MAX_POLL_OPTIONS}).</b>",
            f"يرجى تشغيل /reviewsuggestions مجدداً وتأجيل أو إزالة {len(approved) - vote_store.MAX_POLL_OPTIONS} كتاب على الأقل قبل بدء التصويت.",
        ]
    else:
        summary_lines += ["", "يمكنك الآن تشغيل /startvote لبدء التصويت."]

    await context.bot.send_message(
        chat_id=owner_chat_id,
        text="\n".join(summary_lines),
        parse_mode="HTML",
    )

    if not postponed:
        context.user_data.pop("rev2", None)
        return

    # Build postponement announcement and send draft for approval
    finalized_entries = [
        {
            "title":           b["title"],
            "target_category": b["primary_category"],
            "ai_reason":       b.get("destination_note") or b.get("reasoning") or "",
            "nominator":       b.get("nominator", ""),
        }
        for b in postponed
    ]
    announcement = _build_postponement_announcement(finalized_entries)
    context.user_data["pending_sendgroup"] = {
        "type":       "text",
        "text":       announcement,
        "parse_mode": "HTML",
    }

    books_list = "\n".join(f"• {_html.escape(b['title'])}" for b in postponed)
    await context.bot.send_message(
        chat_id=owner_chat_id,
        text=(
            f"📦 <b>إعلان التأجيلات ({len(postponed)} كتاب)</b>\n\n"
            f"{books_list}\n\n"
            f"<i>النص الذي سيُرسَل للمجموعة:</i>\n"
            f"───────────────\n"
            f"{announcement}\n"
            f"───────────────\n\n"
            "اضغط الزر لإعلام المجموعة، أو تجاهله إذا لم تشأ."
        ),
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )

    context.user_data.pop("rev2", None)


async def rev2_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle rev2:approve|postpone|remove:<N> — per-book review card decision."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return

    if not auth_store.is_owner(update.effective_user.id):
        await query.answer("⛔ هذا الزر للمالك فقط.", show_alert=True)
        return

    await query.answer()

    try:
        parts  = query.data.split(":")
        action = parts[1]             # approve | postpone | remove
        original_number = int(parts[2])
    except (IndexError, ValueError):
        return

    rev2 = context.user_data.get("rev2")
    if not rev2:
        await query.answer(
            "⚠️ انتهت جلسة المراجعة — شغّل /reviewsuggestions من جديد.",
            show_alert=True,
        )
        return

    books: list[dict]   = rev2.get("books", [])
    active_category: str = rev2.get("active_category", "")

    target = next((b for b in books if b["original_number"] == original_number), None)
    if target is None:
        await query.answer("⚠️ لم يُعثر على هذا الكتاب.", show_alert=True)
        return

    if target.get("decision"):
        await query.answer("✅ تم اتخاذ القرار بشأن هذا الكتاب مسبقاً.", show_alert=True)
        return

    title            = target["title"]
    primary_category = target.get("primary_category", active_category)

    # ── 🤖 رأي Gemini — purely advisory, never sets a decision ────────────────
    if action == "gemini_opinion":
        try:
            opinion_prompt = category_constitution.build_gemini_opinion_prompt(title)
            raw_opinion = await _ai_generate(
                contents=[opinion_prompt],
                system_instruction="",
                label="gemini_opinion",
            )
            opinion = _parse_gemini_opinion(raw_opinion)
        except Exception as exc:
            logger.warning("gemini_opinion failed for '%s': %s", title, exc)
            await context.bot.send_message(
                chat_id=query.message.chat_id,
                text=f"⚠️ تعذّر الحصول على رأي Gemini لـ «{_html.escape(title)}» — جرّب مجدداً.",
                parse_mode="HTML",
            )
            return
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=_build_gemini_opinion_text(title, opinion),
            parse_mode="HTML",
        )
        return

    # ── Decision actions ──────────────────────────────────────────────────────
    if action == "postpone":
        # Remove any pre-existing postponed entry for this title before adding
        # the fresh one — prevents duplicates when re-reviewing a book that was
        # postponed by a previous review pass.
        postponed_store.remove_by_title(title)
        postponed_store.add(
            title=title,
            nominator=target.get("nominator", ""),
            nominator_id=target.get("nominator_id"),
            nominated_at=target.get("nominated_at"),
            target_category=primary_category,
            ai_confidence=target.get("confidence", ""),
            ai_reason=target.get("destination_note") or target.get("reasoning") or "",
        )
        suggestion_store.remove_by_title(title)
        target["decision"] = "postponed"
        logger.info("rev2: postponed #%d '%s' → '%s'", original_number, title, primary_category)

    elif action == "remove":
        suggestion_store.remove_by_title(title)
        target["decision"] = "removed"
        logger.info("rev2: removed #%d '%s'", original_number, title)

    elif action == "approve_alt":
        # Approve using the alternative category instead of the primary
        alt_cat = target.get("alternative_category")
        if not alt_cat:
            await query.answer("⚠️ لا يوجد تصنيف بديل لهذا الكتاب.", show_alert=True)
            return
        target["primary_category"] = alt_cat
        primary_category = alt_cat  # update local var so collapsed card is correct
        target["decision"] = "approved"
        logger.info("rev2: approved_alt #%d '%s' → '%s'", original_number, title, alt_cat)

    else:  # approve
        target["decision"] = "approved"
        logger.info("rev2: approved #%d '%s'", original_number, title)

    # Collapse the card to a one-line status (no buttons)
    decided_text = _build_decided_card_text(original_number, title, target["decision"], primary_category)
    try:
        await query.edit_message_text(decided_text, parse_mode="HTML")
    except Exception as exc:
        logger.warning("rev2_callback: edit_message_text failed: %s", exc)

    # Finalize when all books have been decided
    undecided = [b for b in books if not b.get("decision")]
    if not undecided:
        await _finalize_rev2_review(context, query.message.chat_id, books, active_category)


async def sendpostponedannouncement_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /sendpostponedannouncement — owner DM command.
    Generates the consolidated postponed-books announcement.
    Works in two modes:
    • Pending entries (pending=True): runs batch Gemini classification first, then sends draft.
    • Already-classified entries (pending=None/False): builds the draft directly, no Gemini needed.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    pending    = postponed_store.get_pending()
    classified = [e for e in postponed_store.get_all() if not e.get("pending")]

    if not pending and not classified:
        await update.message.reply_text("ℹ️ لا توجد كتب مؤجَّلة حالياً.")
        return

    if pending:
        # Unclassified entries — run the batch Gemini call then send the announcement
        await update.message.reply_text(
            f"⏳ جارٍ تصنيف {len(pending)} كتاب مؤجَّل عبر الذكاء الاصطناعي…",
            parse_mode="HTML",
        )
        await _finalize_postponements(context, update.effective_chat.id)
        return  # _finalize_postponements already sends the draft

    # All entries are already classified — build and send the draft directly
    announcement = _build_postponement_announcement(classified)
    context.user_data["pending_sendgroup"] = {
        "type":       "text",
        "text":       announcement,
        "parse_mode": "HTML",
    }
    count      = len(classified)
    books_list = "\n".join(f"• {_html.escape(e['title'])}" for e in classified)
    await update.message.reply_text(
        f"📦 <b>إعلان التأجيلات ({count} كتاب)</b>\n\n"
        f"{books_list}\n\n"
        f"<i>النص الذي سيُرسَل للمجموعة:</i>\n"
        f"───────────────\n"
        f"{announcement}\n"
        f"───────────────\n\n"
        "اضغط الزر لإعلام المجموعة، أو تجاهله إذا لم تشأ.",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info(
        "sendpostponedannouncement_command: draft sent for %d classified entries to owner %s",
        count, update.effective_user.id,
    )


async def testconstitution_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /testconstitution [book title]
    Without argument: display the Category Constitution summary + benchmark list.
    With a title: classify that book via Gemini + constitution and show the result.
    Owner DM only.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    raw = update.message.text or ""
    book_title = re.sub(r"^/testconstitution\S*\s*", "", raw, flags=re.IGNORECASE).strip()

    if not book_title:
        # Show constitution summary
        cat_names = category_constitution.get_all_category_names()
        principles = category_constitution.GLOBAL_PRINCIPLES
        theme_names = [t["name"] for t in category_constitution.ROADMAP_THEMES]

        lines: list[str] = [
            "📜 <b>دستور التصنيف — ملخص</b>",
            "",
            f"<b>التصنيفات الأساسية ({len(cat_names)}):</b>",
        ]
        for i, name in enumerate(cat_names, 1):
            lines.append(f"  {i}. {name}")

        lines += ["", "<b>مواضيع خارطة القراءة (ليست تصنيفات):</b>"]
        for name in theme_names:
            lines.append(f"  • {name}")

        lines += ["", "<b>المبادئ الكلية:</b>"]
        for p in principles:
            label = p.get("label", "")
            rule  = p.get("rule", "")
            lines.append(f"  • <b>{_html.escape(label)}</b>: {_html.escape(rule[:90])}…")

        lines += [
            "",
            "لاختبار تصنيف كتاب:",
            "<code>/testconstitution اسم الكتاب</code>",
            "",
            "للتشغيل الكامل من سطر الأوامر:",
            "<code>python3 takbeer-bot/benchmark.py</code>",
        ]
        await update.message.reply_text("\n".join(lines), parse_mode="HTML")
        return

    # Classify a specific book via Gemini + constitution
    await context.bot.send_chat_action(chat_id=update.message.chat_id, action="typing")

    prompt = (
        category_constitution.get_constitution_text() + "\n\n"
        + "━━━━━━━━━━━━━━━━\n\n"
        + "صنِّف الكتاب التالي وفق الدستور أعلاه.\n"
        + f"الكتاب: {book_title}\n\n"
        + "أجب بـ JSON فقط — بدون أي نص إضافي:\n"
        + '{"primary_category": "...", "confidence": "high|medium|low", '
        + '"reasoning": "...", "roadmap_theme": "كتب مميزة أو null"}'
    )

    try:
        raw_result = await _ai_generate(
            contents=[prompt],
            system_instruction="",
            label=f"testconstitution",
        )
    except RuntimeError as exc:
        err = str(exc)
        logger.warning("testconstitution: Gemini failed — %s", exc)
        if err == "gemini_auth_error":
            await update.message.reply_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
        else:
            await update.message.reply_text("⚠️ خطأ في الذكاء الاصطناعي، يرجى المحاولة مرة أخرى.")
        return

    parsed: dict = {}
    try:
        m = re.search(r"\{[\s\S]*?\}", raw_result)
        if m:
            parsed = json.loads(m.group())
    except Exception:  # log-exempt: malformed AI JSON; parsed stays {} and display shows fallback dashes
        pass

    primary    = parsed.get("primary_category", "—")
    confidence = parsed.get("confidence", "—")
    reasoning  = parsed.get("reasoning", "—")
    theme      = parsed.get("roadmap_theme") or "—"

    conf_emojis = {"high": "🟢", "medium": "🟡", "low": "🔴"}
    conf_emoji  = conf_emojis.get(confidence, "")
    valid_mark  = (
        "✅" if category_constitution.is_valid_primary_category(primary)
        else "⚠️ <i>خارج القائمة الرسمية</i>"
    )

    await update.message.reply_text(
        f"📖 <b>{_html.escape(book_title)}</b>\n\n"
        f"🏷️ التصنيف: <b>{_html.escape(primary)}</b> {valid_mark}\n"
        f"📊 الثقة: <b>{_html.escape(confidence)}</b> {conf_emoji}\n"
        f"🎯 موضوع الخارطة: {_html.escape(str(theme))}\n\n"
        f"💡 <i>{_html.escape(reasoning)}</i>",
        parse_mode="HTML",
    )


async def suggestion_message_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Detect template copies sent by members, merge new suggestions into the
    master list, and silently update the official pinned template.
    Runs before book_auto_reply_handler so suggestion messages are not
    accidentally forwarded to the AI.

    Restricted to the configured reading group so that messages from other
    chats cannot mutate the shared suggestions store.
    """
    if update.message is None or not update.message.text:
        return
    if not _from_configured_chat(update):
        return
    if not suggestion_store.is_open():
        return

    text = update.message.text
    if not suggestion_store.is_suggestion_message(text):
        return

    titles = suggestion_store.parse_titles_from_text(text)
    if not titles:
        return

    user = update.effective_user
    submitted_by = user.first_name if user else "عضو"
    user_id = user.id if user else 0

    added = suggestion_store.merge_suggestions(titles, submitted_by, user_id)

    # Always refresh the official pinned template
    tmpl_id = suggestion_store.get_template_message_id()
    if tmpl_id:
        try:
            await context.bot.edit_message_text(
                chat_id=update.effective_chat.id,
                message_id=tmpl_id,
                text=suggestion_store.build_template_text(),
                parse_mode="HTML",
            )
        except Exception as e:
            logger.warning("Could not update suggestion template: %s", e)

    if added > 0:
        total = len(suggestion_store.get_suggestions())
        try:
            await update.message.reply_text(
                f"✅ تمت إضافة {added} ترشيح جديد. إجمالي الترشيحات: {total}.",
                quote=True,
            )
        except Exception:  # log-exempt: confirmation reply is best-effort; logger.info below records the event
            pass
        logger.info("Suggestion from %s: +%d new titles (total %d)", submitted_by, added, total)
    else:
        logger.debug("Suggestion from %s: no new titles (all duplicates)", submitted_by)


# ━━━ Voting system ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


async def auto_close_vote_job(bot, chat_id_str: str, application=None) -> None:
    """
    Scheduler job: stop the active book-vote poll, tally votes, announce results.

    Outcomes:
      ok  — single winner; start the reading cycle + DM the owner for announcement approval.
      tie — two or more books tied for first place; send tie-resolution DM to owner.

    application is passed so the winner path can write pending_sendgroup into
    the owner's user_data, enabling the existing sendgroup_callback to post
    the announcement when the owner presses the button.
    """
    if not vote_store.is_active():
        return

    _, msg_id = vote_store.get_poll_location()
    if msg_id is None:
        logger.error("auto_close_vote_job: no poll message_id found")
        return

    try:
        stopped = await bot.stop_poll(chat_id=chat_id_str, message_id=msg_id)
    except Exception as e:
        logger.error("auto_close_vote_job: stop_poll failed: %s", e)
        return

    raw_options = [
        {"text": opt.text, "votes": opt.voter_count}
        for opt in stopped.options
    ]
    result = vote_store.close_vote(raw_options)

    # ── Analytics: emit book_vote event (non-tie only; tie emits after resolution) ─
    if result["status"] == "ok":
        _bv_results = result.get("results", [])
        _bv_total   = sum(r["votes"] for r in _bv_results)
        _bv_data    = vote_store.load()
        analytics_store.append_event({
            "poll_type":        "book_vote",
            "cycle_number":     cycle_store.get_cycle_number(),
            "roadmap_counter":  roadmap_store.get_roadmap_id(),
            "roadmap_stage":    roadmap_store.get_current_stage(),
            "book_title":       result["winner"],
            "started_at":       _bv_data.get("started_at", ""),
            "closed_at":        datetime.now(TIMEZONE).isoformat(),
            "participant_count": _bv_total,
            "extension_count":  _bv_data.get("extension_count", 0),
            "payload": {
                "winner":        result["winner"],
                "was_tie":       False,
                "final_ranked":  _bv_results,
                "total_votes":   _bv_total,
                "options_count": len(_bv_results),
            },
        })

    results = vote_store.get_results()
    results_text = vote_store.build_results_text(results)

    try:
        await bot.send_message(
            chat_id=chat_id_str,
            text=results_text,
            parse_mode="HTML",
        )
    except Exception as e:
        logger.error("auto_close_vote_job: failed to send results: %s", e)

    if result["status"] == "tie":
        tied_titles = result["tied_titles"]
        logger.info("auto_close_vote_job: tie detected — titles=%s", tied_titles)
        owner_id = suggestion_store.load().get("owner_id")
        if owner_id:
            active_cat = roadmap_store.get_active_category()
            cat_line = f"\n📂 <b>التصنيف:</b> {_html.escape(active_cat)}" if active_cat else ""
            tie_lines = [
                "⚖️ <b>تعادل في تصويت الكتب!</b>",
                "",
                cat_line.strip(),
                "",
                "الكتب المتعادلة:",
            ] if active_cat else [
                "⚖️ <b>تعادل في تصويت الكتب!</b>",
                "",
                "الكتب المتعادلة:",
            ]
            for t in tied_titles:
                tie_lines.append(f"  • {_html.escape(t)}")
            tie_lines += [
                "",
                "اختر كيف تريد حل التعادل:",
            ]
            btns = [
                [InlineKeyboardButton("🕒 تمديد التصويت", callback_data="vote:extend_tie")],
                [
                    InlineKeyboardButton(
                        f"👤 {tied_titles[i]}",
                        callback_data=f"vote:pick_tie:{i}",
                    )
                    for i in range(len(tied_titles))
                ],
            ]
            try:
                await bot.send_message(
                    chat_id=int(owner_id),
                    text="\n".join(tie_lines),
                    parse_mode="HTML",
                    reply_markup=InlineKeyboardMarkup(btns),
                )
            except Exception as e:
                logger.error("auto_close_vote_job: failed to send tie DM: %s", e)
        return

    # Clean result — single winner
    winner = result["winner"]

    # Store ranked runner-ups as stage candidates (skip-progression memory)
    all_results = vote_store.get_results()
    runner_ups = [
        {"title": r["title"], "votes": r["votes"], "rank": r["rank"]}
        for r in all_results
        if r["rank"] > 1
    ]
    roadmap_store.set_stage_candidates(runner_ups)

    # Start the reading cycle
    try:
        cycle_store.start_cycle(winner)
        cycle_num = cycle_store.get_cycle_number()
        logger.info("Reading cycle %d started automatically. Winner: %s", cycle_num, winner)
    except ValueError:
        logger.warning("auto_close_vote_job: cycle already active, skipping start")

    # Reset per-member reading progress for the new cycle.
    progress_store.reset()
    # Synchronise Companion: new book = new operational context
    asyncio.create_task(_auto_export_context("book_started_vote"))

    active_cat = roadmap_store.get_active_category()
    cycle_num  = cycle_store.get_cycle_number()

    # Build a rich announcement text (results + winner callout)
    cat_line    = f"\n📂 <b>التصنيف:</b> {_html.escape(active_cat)}" if active_cat else ""
    all_res     = vote_store.get_results()
    medals      = {1: "🥇", 2: "🥈", 3: "🥉"}
    result_lines = "\n".join(
        f"{medals.get(r['rank'], '  ')} {_html.escape(r['title'])} — <b>{r['votes']}</b> صوت"
        for r in all_res
    )
    announce_text = (
        f"📖 <b>الكتاب الفائز: {_html.escape(winner)}</b>{cat_line}\n\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{result_lines}\n"
        f"━━━━━━━━━━━━━━━━\n\n"
        f"🎉 بدأت دورة القراءة رقم {cycle_num}.\n"
        "يمكن رفع جدول القراءة عبر /newschedule"
    )

    # DM the owner for approval, storing pending_sendgroup in their user_data
    owner_id = suggestion_store.load().get("owner_id")
    dm_sent  = False
    if owner_id and application is not None:
        try:
            application.user_data[int(owner_id)]["pending_sendgroup"] = {
                "type": "text",
                "text": announce_text,
                "parse_mode": "HTML",
            }
            await bot.send_message(
                chat_id=int(owner_id),
                text=(
                    f"✅ <b>انتهى التصويت</b>\n\n"
                    f"{announce_text}\n\n"
                    "اضغط الزر لإعلام المجموعة بالفائز:"
                ),
                parse_mode="HTML",
                reply_markup=_SENDGROUP_MARKUP,
            )
            dm_sent = True
            logger.info("auto_close_vote_job: winner DM queued for owner approval. Winner: %s", winner)
        except Exception as e:
            logger.error("auto_close_vote_job: failed to DM owner winner announcement: %s", e)

    if not dm_sent:
        # Fallback: application unavailable or DM failed — post directly to group
        try:
            await bot.send_message(
                chat_id=chat_id_str,
                text=announce_text,
                parse_mode="HTML",
            )
            logger.info("auto_close_vote_job: winner posted directly to group (no owner DM). Winner: %s", winner)
        except Exception as e:
            logger.error("auto_close_vote_job: failed to send winner message: %s", e)
    else:
        logger.info("Vote closed automatically. Winner: %s", winner)


async def extendvote_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/extendvote — extend the active voting period by 24 hours. Owner DM only.
    Vote-type-aware: extends whichever vote is currently active (category or book).
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    scheduler = context.application.bot_data.get("scheduler")

    # ── Category vote extension ───────────────────────────────────────────────
    if roadmap_store.is_category_vote_active():
        current_close = roadmap_store.get_category_vote_close_at() or datetime.now(TIMEZONE)
        new_close_at = current_close + timedelta(hours=roadmap_store.CATEGORY_VOTE_DURATION_HOURS)
        roadmap_store.extend_category_vote(new_close_at)
        if scheduler:
            try:
                scheduler.reschedule_job(
                    "category_vote_close_job",
                    trigger="date",
                    run_date=new_close_at,
                )
            except Exception:
                scheduler.add_job(
                    auto_close_category_vote_job,
                    trigger="date",
                    run_date=new_close_at,
                    args=[context.bot, str(CHAT_ID)],
                    id="category_vote_close_job",
                    replace_existing=True,
                )
        close_str = new_close_at.strftime("%Y-%m-%d %H:%M")
        context.user_data["pending_sendgroup"] = {
            "type": "text",
            "text": f"⏳ <b>تم تمديد تصويت الخارطة.</b>\n\nسينتهي الآن في: <b>{close_str}</b>",
            "parse_mode": "HTML",
        }
        await update.message.reply_text(
            f"⏳ <b>تم تمديد تصويت الخارطة.</b>\n\nسينتهي الآن في: <b>{close_str}</b>\n\n"
            "اضغط الزر لإعلام المجموعة بالتمديد:",
            parse_mode="HTML",
            reply_markup=_SENDGROUP_MARKUP,
        )
        logger.info("Category vote extended. New close: %s", new_close_at)
        return

    # ── Book vote extension ───────────────────────────────────────────────────
    if vote_store.is_active():
        current_close = vote_store.get_close_at() or datetime.now(TIMEZONE)
        new_close_at = current_close + timedelta(hours=vote_store.VOTE_DURATION_HOURS)
        vote_store.extend_vote(new_close_at)
        if scheduler:
            try:
                scheduler.reschedule_job(
                    "vote_close_job",
                    trigger="date",
                    run_date=new_close_at,
                )
            except Exception:
                scheduler.add_job(
                    auto_close_vote_job,
                    trigger="date",
                    run_date=new_close_at,
                    args=[context.bot, str(CHAT_ID), context.application],
                    id="vote_close_job",
                    replace_existing=True,
                )
        close_str = new_close_at.strftime("%Y-%m-%d %H:%M")
        context.user_data["pending_sendgroup"] = {
            "type": "text",
            "text": f"⏳ <b>تم تمديد التصويت.</b>\n\nسينتهي الآن في: <b>{close_str}</b>",
            "parse_mode": "HTML",
        }
        await update.message.reply_text(
            f"⏳ <b>تم تمديد التصويت.</b>\n\nسينتهي الآن في: <b>{close_str}</b>\n\n"
            "اضغط الزر لإعلام المجموعة بالتمديد:",
            parse_mode="HTML",
            reply_markup=_SENDGROUP_MARKUP,
        )
        logger.info(
            "Book vote extended by user %s. New close: %s",
            update.effective_user.id, new_close_at,
        )
        return

    await update.message.reply_text("ℹ️ لا يوجد تصويت نشط حالياً.")


# ── Poll insights helpers ──────────────────────────────────────────────────────

def _vote_label_ar(n: int) -> str:
    """Return the correct Arabic noun for a vote count (صوت / صوتان / أصوات / صوتاً)."""
    if n == 1:
        return "صوت"
    if n == 2:
        return "صوتان"
    if 3 <= n <= 10:
        return "أصوات"
    return "صوتاً"


_AR_MONTHS = [
    "", "يناير", "فبراير", "مارس", "أبريل", "مايو", "يونيو",
    "يوليو", "أغسطس", "سبتمبر", "أكتوبر", "نوفمبر", "ديسمبر",
]


def _fmt_dt_ar(dt: "datetime", include_time: bool = False) -> str:
    """Format a datetime as an Arabic date string, e.g. '25 يونيو' or '25 يونيو 05:56'."""
    base = f"{dt.day} {_AR_MONTHS[dt.month]}"
    if include_time:
        base += f" {dt.strftime('%H:%M')}"
    return base


def _compute_category_poll_insights() -> str:
    """
    Pure-arithmetic analysis of the active (or most-recently-closed) category vote.

    Returns a formatted HTML string for the owner/manager DM.
    No Gemini call — every value is computed deterministically from stored data.

    Covers:
      • Full ranked table with vote counts, percentages, and tie flags
      • Current qualifiers (top ROADMAP_SIZE if voting ended now)
      • Safety margin between 4th and 5th place
      • Choice-pattern stats: average, distribution, top combinations
      • Historical comparison with the previous closed vote (when available)
    """
    from collections import Counter as _Counter

    data = roadmap_store.load()
    cv = data.get("category_vote", {})
    status = cv.get("status", "none")

    # ── No active vote — show last closed snapshot if available ────────────
    if status not in ("active", "awaiting_tie_resolution"):
        history = data.get("category_vote_history", [])
        if not history:
            return "ℹ️ لا يوجد تصويت فئات نشط حالياً ولا سجل سابق."
        last = history[-1]
        prev_ranked = last.get("final_ranked", [])
        prev_p = last.get("participant_count", 0)
        closed_raw = last.get("closed_at", "")
        closed_str = ""
        if closed_raw:
            try:
                dt = datetime.fromisoformat(closed_raw)
                closed_str = _fmt_dt_ar(dt)
            except Exception:
                closed_str = closed_raw[:10]
        lines = [
            f"<b>📊 آخر تصويت فئات — مُغلق ({closed_str})</b>",
            f"المشاركون: {prev_p}",
            "",
        ]
        for i, r in enumerate(prev_ranked, 1):
            mark = "✅ " if i <= roadmap_store.ROADMAP_SIZE else "   "
            lines.append(
                f"{mark}{i}. {r['title']} — {r['votes']} {_vote_label_ar(r['votes'])}"
            )
        return "\n".join(lines)

    options: list[str] = cv.get("options", [])
    answers: dict = cv.get("answers", {})
    close_raw = cv.get("current_close_at", "")
    extension_count = cv.get("extension_count", 0)
    participant_count = len(answers)

    # ── Close-time string ──────────────────────────────────────────────────
    close_str = ""
    if close_raw:
        try:
            dt = datetime.fromisoformat(close_raw)
            close_str = _fmt_dt_ar(dt, include_time=True)
        except Exception:
            close_str = close_raw[:16]

    # ── Tally (same per-user cap as close_category_vote) ──────────────────
    tallies = [0] * len(options)
    for chosen_indices in answers.values():
        capped = chosen_indices[:roadmap_store.MAX_CATEGORY_CHOICES]
        for idx in capped:
            if 0 <= idx < len(options):
                tallies[idx] += 1

    # Sort descending by votes, then by original option order (stable)
    indexed = sorted(range(len(options)), key=lambda i: (-tallies[i], i))

    # Assign display rank — ties share the same number
    ranked: list[dict] = []
    display_rank = 1
    for pos, idx in enumerate(indexed):
        if pos > 0 and tallies[idx] < tallies[indexed[pos - 1]]:
            display_rank = pos + 1
        ranked.append({"title": options[idx], "votes": tallies[idx], "rank": display_rank})

    # ── Header ────────────────────────────────────────────────────────────
    status_label = "نشط" if status == "active" else "جارٍ حسم التعادل"
    ext_note = f" · مُمدَّد {extension_count}×" if extension_count else ""
    header = f"الحالة: {status_label}{ext_note} ┃ المشاركون: {participant_count}"
    if close_str:
        header += f" ┃ ينتهي: {close_str}"

    lines: list[str] = [
        "<b>📊 تحليل تصويت الفئات</b>",
        "",
        header,
        "",
        "<b>━━━ التصنيف ━━━</b>",
        "",
    ]

    # Ranked table — separator inserted at the ROADMAP_SIZE boundary
    sep_inserted = False
    for pos, r in enumerate(ranked):
        if not sep_inserted and r["rank"] > roadmap_store.ROADMAP_SIZE:
            lines.append("─────────────────────────")
            sep_inserted = True

        pct = (r["votes"] / participant_count * 100) if participant_count else 0
        tie_note = " ⚠️" if pos > 0 and r["rank"] == ranked[pos - 1]["rank"] else ""
        boundary = " ◄" if r["rank"] == roadmap_store.ROADMAP_SIZE else ""
        lines.append(
            f"{r['rank']}. {r['title']} — {r['votes']} {_vote_label_ar(r['votes'])}"
            f" ({pct:.0f}%){boundary}{tie_note}"
        )

    # ── Qualifiers (top ROADMAP_SIZE if voting ended now) ─────────────────
    q_entries = [r for r in ranked if r["rank"] <= roadmap_store.ROADMAP_SIZE]
    n = roadmap_store.ROADMAP_SIZE
    boundary_votes = ranked[n - 1]["votes"] if len(ranked) >= n else 0
    next_votes = ranked[n]["votes"] if len(ranked) > n else -1
    has_boundary_tie = next_votes == boundary_votes > 0

    lines += ["", "<b>لو انتهى التصويت الآن:</b>"]
    if has_boundary_tie:
        tied = [r["title"] for r in ranked if r["votes"] == boundary_votes]
        lines.append(
            f"⚠️ تعادل عند الحد الفاصل — يستلزم جلسة تعادل بين: {' / '.join(tied)}"
        )
    else:
        lines.append("✅ " + " · ".join(r["title"] for r in q_entries[:n]))
        if len(ranked) > n:
            margin = ranked[n - 1]["votes"] - ranked[n]["votes"]
            fifth = ranked[n]["title"]
            lines.append(
                f"هامش الأمان: المرتبة الرابعة تتقدم على «{fifth}» بـ"
                f" {margin} {_vote_label_ar(margin)}"
            )

    # ── Choice-pattern stats ───────────────────────────────────────────────
    if participant_count > 0:
        per_voter = [len(v[:roadmap_store.MAX_CATEGORY_CHOICES]) for v in answers.values()]
        avg = sum(per_voter) / len(per_voter)
        dist = _Counter(per_voter)

        lines += ["", "<b>━━━ نمط الاختيار ━━━</b>", ""]
        lines.append(
            f"متوسط الفئات لكل عضو: {avg:.1f}"
            f"  (أقل: {min(per_voter)} ┃ أكثر: {max(per_voter)})"
        )

        dist_parts: list[str] = []
        for cnt in sorted(dist):
            noun = "فئة" if cnt == 1 else "فئتان" if cnt == 2 else "فئات"
            dist_parts.append(f"{cnt} {noun}×{dist[cnt]}")
        lines.append("التوزيع: " + " ┃ ".join(dist_parts))

        # Top combination patterns (only combos chosen by ≥2 members)
        combo_ctr: _Counter = _Counter()
        for v in answers.values():
            combo = tuple(sorted(v[:roadmap_store.MAX_CATEGORY_CHOICES]))
            if combo:
                combo_ctr[combo] += 1
        top_combos = [(c, cnt) for c, cnt in combo_ctr.most_common(5) if cnt >= 2]
        if top_combos:
            lines += ["", "أكثر التركيبات شيوعاً:"]
            for combo, cnt in top_combos:
                names = " + ".join(options[i] for i in combo if i < len(options))
                lines.append(f"• {names}  ({cnt} أعضاء)")

    # ── Historical comparison with previous closed vote ────────────────────
    history = data.get("category_vote_history", [])
    if history:
        last = history[-1]
        prev_ranked = last.get("final_ranked", [])
        prev_p = last.get("participant_count", 0)
        prev_ext = last.get("extension_count", 0)
        prev_closed_raw = last.get("closed_at", "")
        prev_date = ""
        if prev_closed_raw:
            try:
                dt = datetime.fromisoformat(prev_closed_raw)
                prev_date = _fmt_dt_ar(dt)
            except Exception:
                prev_date = prev_closed_raw[:10]

        prev_rank_map = {r["title"]: i + 1 for i, r in enumerate(prev_ranked)}

        lines += [
            "",
            f"<b>━━━ مقارنة بالتصويت السابق ({prev_date}) ━━━</b>",
            f"المشاركون آنذاك: {prev_p} ┃ تمديدات: {prev_ext}",
            "",
        ]
        for r in ranked[:roadmap_store.ROADMAP_SIZE + 2]:
            curr_r = r["rank"]
            prev_r = prev_rank_map.get(r["title"])
            if prev_r is None:
                trend = "🆕"
            elif prev_r > curr_r:
                trend = f"▲{prev_r - curr_r}"
            elif prev_r < curr_r:
                trend = f"▼{curr_r - prev_r}"
            else:
                trend = "─"
            lines.append(f"{curr_r}. {r['title']}  {trend}")

    return "\n".join(lines)


async def pollinsights_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/pollinsights — deterministic analysis of the active category vote. Owner/manager DM only."""
    if update.message is None or update.effective_user is None:
        return
    # Require a private DM from the owner or a manager
    if (
        update.effective_chat is None
        or update.effective_chat.type != "private"
        or not auth_store.is_authorized(update.effective_user.id)
    ):
        await _redirect_to_dm(update)
        return

    report = _compute_category_poll_insights()
    await update.message.reply_text(report, parse_mode="HTML")
    logger.info(
        "pollinsights: report delivered to user %s (%d chars)",
        update.effective_user.id,
        len(report),
    )



# ── /clubreport ────────────────────────────────────────────────────────────────

def _compute_club_report_data() -> dict:
    """
    Gather all available historical data for /clubreport.

    Sources (all pre-analytics-era data is included transparently):
      cycle.json              → completed cycle list
      ratings.json            → star ratings per book
      participation_polls.json→ participation per book
      roadmap.json            → category_vote_history
      analytics.json          → new unified event store (additive)

    Returns a dict:
      has_data          — False when no book with a rating exists yet
      completed_books   — list of per-book dicts (see inline)
      rating_trajectory — "improving" | "declining" | "stable" | "single"
      rating_delta      — float (first-to-last avg difference)
      category_vote     — dict or None
    """
    cy_hist = cycle_store.load().get("history", [])
    ra_arch = rating_store.load().get("archived", [])
    pp_arch = poll_store.load().get("archived", [])

    def _rating_for(title: str) -> dict | None:
        hits = [a for a in ra_arch if a["book_title"] == title]
        return hits[-1] if hits else None

    def _part_for(title: str) -> dict | None:
        hits = [a for a in pp_arch if a["book_title"] == title]
        return hits[-1] if hits else None

    completed_books: list[dict] = []
    for entry in cy_hist:
        cn = entry.get("cycle_number", 0)
        for bk in entry.get("books", []):
            title = bk.get("title", "")
            if not title:
                continue
            ra = _rating_for(title)
            if not ra:
                continue  # skip books with no rating data
            dist = ra.get("distribution", [0, 0, 0, 0, 0])
            total = ra.get("total_ratings", 0)
            avg = (
                round(sum((i + 1) * dist[i] for i in range(len(dist))) / total, 2)
                if total > 0 else 0.0
            )
            # Participation cross-reference
            part_data: dict | None = None
            pa = _part_for(title)
            if pa:
                counts = pa.get("final_counts", [0, 0, 0])
                yes_c   = counts[0] if len(counts) > 0 else 0
                maybe_c = counts[1] if len(counts) > 1 else 0
                no_c    = counts[2] if len(counts) > 2 else 0
                total_resp = yes_c + maybe_c + no_c
                p_rate     = round(yes_c / total_resp, 3) if total_resp > 0 else 0.0
                comp_rate  = round(total / yes_c, 3)      if yes_c > 0    else 0.0
                part_data  = {
                    "yes": yes_c, "maybe": maybe_c, "no": no_c,
                    "total": total_resp,
                    "participation_rate": p_rate,
                    "completion_rate":    comp_rate,
                }
            completed_books.append({
                "title":             title,
                "cycle_number":      cn,
                "started_at":        entry.get("started_at", ""),
                "ended_at":          entry.get("ended_at", ""),
                "rating_avg":        avg,
                "rating_total":      total,
                "rating_dist":       dist,
                "most_common_rating": ra.get("most_common_rating", 0),
                "participation":     part_data,
            })

    if not completed_books:
        return {
            "has_data": False, "completed_books": [],
            "rating_trajectory": "single", "rating_delta": 0.0,
            "category_vote": None,
        }

    # Rating trajectory (first → last book with a rating)
    avgs = [b["rating_avg"] for b in completed_books]
    if len(avgs) < 2:
        traj, delta = "single", 0.0
    else:
        delta = round(avgs[-1] - avgs[0], 2)
        traj  = "improving" if delta >= 0.5 else "declining" if delta <= -0.5 else "stable"

    # Latest category vote snapshot (if any history exists)
    cv_hist = roadmap_store.load().get("category_vote_history", [])
    cat_vote: dict | None = None
    if cv_hist:
        snap = cv_hist[-1]
        ranked = snap.get("final_ranked", [])
        cat_vote = {
            "roadmap_counter":      snap.get("roadmap_counter", 0),
            "participant_count":    snap.get("participant_count", 0),
            "extension_count":      snap.get("extension_count", 0),
            "started_at":           snap.get("started_at", ""),
            "closed_at":            snap.get("closed_at", ""),
            "qualified":            [r["title"] for r in ranked[:roadmap_store.ROADMAP_SIZE]],
            "full_ranked":          ranked,
            "total_selections":     snap.get("total_selections", 0),
            "avg_choices_per_voter": snap.get("avg_choices_per_voter", 0.0),
        }

    return {
        "has_data":          True,
        "completed_books":   completed_books,
        "rating_trajectory": traj,
        "rating_delta":      delta,
        "category_vote":     cat_vote,
    }


def _stars_ar(avg: float) -> str:
    """Return ⭐️-repeat matching the rounded average (0–5)."""
    n = min(5, max(0, round(avg)))
    return "⭐️" * n if n > 0 else "—"


def _format_club_report_deterministic(data: dict) -> str:
    """
    Format the always-present (Gemini-free) sections of /clubreport as HTML.
    Section order: books + ratings, participation (if available), category vote (if available).
    """
    L: list[str] = ["<b>📋 تقرير النادي</b>", ""]

    # ── Section 1: Books read ──────────────────────────────────────────────
    books = data["completed_books"]
    L.append("━━━ الكتب المقروءة ━━━")
    L.append("")
    for bk in books:
        stars = _stars_ar(bk["rating_avg"])
        L.append(f"<b>📖 {bk['title']}</b>  <i>(الدورة {bk['cycle_number']})</i>")
        L.append(f"{stars} {bk['rating_avg']}/5 · {bk['rating_total']} تقييم")
        pa = bk["participation"]
        if pa:
            pct      = round(pa["participation_rate"] * 100, 1)
            comp_pct = round(pa["completion_rate"] * 100)
            L.append(
                f"👥 {pa['yes']} ملتزم · {pa['maybe']} ربما · {pa['no']} لن يشاركوا"
                f"  ({pct}% نسبة الالتزام)"
            )
            L.append(
                f"📊 إتمام القراءة: {bk['rating_total']} من {pa['yes']} ملتزم"
                f"  ({comp_pct}%)"
            )
        L.append("")

    # Trajectory line (only meaningful when 2+ books)
    traj  = data["rating_trajectory"]
    delta = data["rating_delta"]
    if traj == "improving":
        first_avg = books[0]["rating_avg"]
        last_avg  = books[-1]["rating_avg"]
        L.append(f"الاتجاه: التقييمات في تحسن ↑  ({first_avg} ← {last_avg})")
    elif traj == "declining":
        first_avg = books[0]["rating_avg"]
        last_avg  = books[-1]["rating_avg"]
        L.append(f"الاتجاه: التقييمات في تراجع ↓  ({first_avg} → {last_avg})")
    elif traj == "stable":
        L.append("الاتجاه: التقييمات مستقرة →")

    # ── Section 2: Category vote ───────────────────────────────────────────
    cv = data.get("category_vote")
    if cv:
        L += ["", "━━━ تصويت الخارطة ━━━", ""]
        ext_note = f" · مُمدَّد {cv['extension_count']}×" if cv["extension_count"] > 0 else ""
        L.append(
            f"المشاركون: <b>{cv['participant_count']}</b>{ext_note}"
            f" · متوسط الفئات لكل عضو: {cv['avg_choices_per_voter']}"
        )
        L.append("")
        L.append("الفئات الفائزة:")
        for i, cat in enumerate(cv["qualified"], 1):
            L.append(f"  {i}. {cat}")
        # Show how many didn't qualify, as context
        total_options = len(cv["full_ranked"])
        runners = total_options - len(cv["qualified"])
        if runners > 0:
            L.append(f"\n({runners} فئة لم تتأهل من أصل {total_options})")

    return "\n".join(L)


def _build_clubreport_gemini_prompt(data: dict) -> str:
    """Build the structured Arabic prompt sent to Gemini for strategic synthesis."""
    books = data["completed_books"]
    P: list[str] = [
        "أنت مستشار نادي قراءة.",
        "فيما يلي بيانات مجمّعة وموثوقة عن نادي القراءة:",
        "",
    ]
    for bk in books:
        P.append(f"• الكتاب: {bk['title']}  (الدورة {bk['cycle_number']})")
        P.append(f"  التقييم: {bk['rating_avg']}/5 من {bk['rating_total']} عضو")
        pa = bk["participation"]
        if pa:
            P.append(
                f"  المشاركة: {pa['yes']} التزموا، "
                f"{pa['maybe']} ربما، {pa['no']} لن يشاركوا"
            )
            P.append(
                f"  ممن التزموا، قيّم الكتاب فعلياً: {bk['rating_total']} "
                f"({round(pa['completion_rate'] * 100)}%)"
            )
        P.append("")

    traj  = data["rating_trajectory"]
    delta = data["rating_delta"]
    if traj == "improving":
        P.append(f"الاتجاه العام: التقييمات في تحسن (+{delta} نجمة من أول كتاب لآخر كتاب).")
    elif traj == "declining":
        P.append(f"الاتجاه العام: التقييمات في تراجع ({delta} نجمة).")
    elif traj == "stable":
        P.append("الاتجاه العام: التقييمات مستقرة.")

    cv = data.get("category_vote")
    if cv:
        P.append(
            f"\nآخر تصويت فئات: {cv['participant_count']} عضو صوّتوا، "
            f"الفئات الفائزة: {', '.join(cv['qualified'])}."
        )

    P += [
        "",
        "المطلوب: اكتب 3 إلى 4 ملاحظات استراتيجية قصيرة باللغة العربية.",
        "كل ملاحظة في سطر واحد مستقل، تبدأ بـ '🔹'.",
        "ركز على الاستنتاجات والتوصيات العملية للخارطة القادمة.",
        "لا تُعِد ذكر الأرقام الواردة في التقرير — ركز على المعنى والتوصية.",
        "لا تستخدم عناوين أو مقدمات — فقط السطور المطلوبة مباشرة.",
    ]
    return "\n".join(P)


async def clubreport_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/clubreport — strategic club debrief across all completed cycles. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    data = _compute_club_report_data()

    if not data["has_data"]:
        await update.message.reply_text(
            "📋 <b>تقرير النادي</b>\n\n"
            "ℹ️ لا توجد بيانات كافية بعد.\n"
            "يحتاج التقرير إلى كتاب مكتمل مع تقييم على الأقل.",
            parse_mode="HTML",
        )
        return

    # Send deterministic sections first (always fast, always accurate)
    det = _format_club_report_deterministic(data)
    await update.message.reply_text(det, parse_mode="HTML")

    # Send Gemini synthesis as a follow-up message
    thinking_msg = await update.message.reply_text("⏳ جارٍ إعداد التحليل...")
    gemini_ok = False
    try:
        prompt    = _build_clubreport_gemini_prompt(data)
        synthesis = await _ai_generate(contents=[prompt], label="clubreport")
        await thinking_msg.edit_text(
            f"<b>💡 ملاحظات استراتيجية</b>\n\n{synthesis.strip()}",
            parse_mode="HTML",
        )
        gemini_ok = True
    except Exception as e:
        logger.warning("clubreport: Gemini synthesis failed: %s", e)
        if str(e) == "gemini_auth_error":
            await thinking_msg.edit_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
        else:
            await thinking_msg.edit_text(
                "ℹ️ تعذّر إعداد التحليل الآن — البيانات متاحة أعلاه."
            )

    logger.info(
        "clubreport: delivered to user %s — books=%d trajectory=%s gemini=%s",
        update.effective_user.id,
        len(data["completed_books"]),
        data["rating_trajectory"],
        "ok" if gemini_ok else "failed",
    )


# ── /reflect ───────────────────────────────────────────────────────────────────

async def reflect_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/reflect — write a personal reader reflection to open today's group discussion. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    book = cycle_store.get_current_book()
    if not book:
        await update.message.reply_text(
            "ℹ️ لا توجد دورة قراءة نشطة حالياً.\n"
            "يحتاج هذا الأمر إلى كتاب قيد القراءة."
        )
        return

    title = book.get("title", "")

    # Pull today's reading entry for page-range grounding
    sch = schedule_store.load()
    if schedule_store.is_rest_day_today(sch):
        await update.message.reply_text(
            "📅 اليوم يوم راحة في الجدول — لا توجد صفحات محددة لملاحظة اليوم.\n"
            "يمكنك إعادة المحاولة في يوم قراءة."
        )
        return

    entry   = schedule_store.get_marked_current_entry(sch)
    chapter = entry.get("chapter", "") if entry else ""
    p_start = entry.get("page_start") if entry else None
    p_end   = entry.get("page_end")   if entry else None

    # Build the context block passed to the AI
    book_context_lines = [f"الكتاب: «{title}»"]
    meta = book_store.get_metadata(title)
    if meta:
        if meta.get("author"):
            book_context_lines.append(f"المؤلف: {meta['author']}")
        if meta.get("original_language") and meta["original_language"] != "العربية":
            book_context_lines.append(f"اللغة الأصلية: {meta['original_language']}")
    if chapter:
        book_context_lines.append(f"قراءة اليوم: {chapter}")
    if p_start is not None and p_end is not None:
        book_context_lines.append(f"نطاق الصفحات: {p_start}–{p_end}")

    book_context = "\n".join(book_context_lines)

    spoiler_guard = (
        "قيد صارم: اقتصر تماماً على ما قرأه الأعضاء حتى الآن"
        + (f" (حتى صفحة {p_end})" if p_end is not None else "")
        + ". لا إشارة إلى أحداث أو شخصيات أو تفاصيل تظهر لاحقاً في الكتاب."
    )

    prompt = (
        "أنت عضو في نادي قراءة — قارئ متأمل وصادق، لا مدرّس ولا ميسّر.\n"
        "أنهيت قراءة اليوم وتريد أن تشارك المجموعة شيئاً استوقفك.\n\n"
        f"{book_context}\n\n"
        "اكتب رسالة واحدة قصيرة — بصوتك أنت — كأنك تكتب في مجموعة أصدقاء:\n\n"
        "الشكل المطلوب:\n"
        "• ابدأ بملاحظة شخصية: شيء استوقفك — مشهد، جملة، فكرة، تصرف شخصية.\n"
        "  استخدم لغة المتكلم: «توقفت عند»، «بقيت معي»، «لم أفهم تماماً»، «أثار فيّ»...\n"
        "• لا تسأل سؤالاً في البداية — شارك أولاً، ثم افتح الباب بشكل طبيعي.\n"
        "• إن انتهيت بسؤال، فليكن خفيفاً ومفتوحاً — لا يشبه سؤال امتحان أبداً.\n"
        "  مثال مقبول: «هل توقف أحدكم عند هذا المشهد؟»\n"
        "  مثال مرفوض: «ما الرمز الذي يجسّده هذا المشهد؟»\n\n"
        "الأسلوب:\n"
        "• العربية الفصحى البيضاء — دافئة، طبيعية، بلا تكلف أكاديمي أو لهجة.\n"
        "• قصيرة: فقرة إلى فقرتين على الأكثر.\n"
        "• لا عناوين، لا تمهيد رسمي، لا ذكر لعبارة «سؤال النقاش».\n\n"
        "المحاور الممكنة (اختر ما يناسب قراءة اليوم تحديداً):\n"
        "شخصية ودوافعها — لحظة عاطفية أو موقف مفاجئ — جملة أو صورة لغوية —\n"
        "علاقة بين شخصيتين — سؤال أخلاقي يطرحه النص — إحساس لم تتوقعه —\n"
        "شيء يبدو غامضاً أو يحتمل أكثر من تأويل.\n\n"
        f"{spoiler_guard}"
    )

    thinking_msg = await update.message.reply_text("⏳ جارٍ كتابة ملاحظة اليوم...")

    try:
        raw = await _ai_generate(contents=[prompt], label="reflect")
        reflection_text = raw.strip()
    except Exception as e:
        logger.warning("reflect: Gemini failed: %s", e)
        if str(e) == "gemini_auth_error":
            await thinking_msg.edit_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
        else:
            await thinking_msg.edit_text("❌ تعذّر إعداد الملاحظة. حاول مرة أخرى لاحقاً.")
        return

    # The group message: the reflection stands on its own, with a light page note
    if p_start is not None and p_end is not None:
        page_note = f"\n\n<i>📖 ص {p_start}–{p_end}</i>"
    elif chapter:
        page_note = f"\n\n<i>📖 {_html.escape(chapter)}</i>"
    else:
        page_note = ""

    full_text = f"{reflection_text}{page_note}"

    context.user_data["pending_sendgroup"] = {
        "type":       "text",
        "text":       full_text,
        "parse_mode": "HTML",
    }

    await thinking_msg.edit_text(
        f"{full_text}\n\n"
        "اضغط الزر لمشاركة الملاحظة مع المجموعة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info(
        "reflect: reflection generated for '%s' pages=%s-%s, user=%s",
        title, p_start, p_end, update.effective_user.id,
    )


# ── /suggestionsoverview ───────────────────────────────────────────────────────

async def suggestionsoverview_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/suggestionsoverview — admin overview of the current nomination pool. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    from collections import defaultdict

    sug_data = suggestion_store.load()
    status   = sug_data.get("status", "closed")
    sugs     = sug_data.get("suggestions", [])

    status_label = "🟢 مفتوحة" if status == "open" else "🔴 مغلقة"
    L: list[str] = [
        "<b>📚 نظرة عامة على الترشيحات</b>",
        f"الحالة: {status_label} · {len(sugs)} كتاب",
        "",
    ]

    if not sugs:
        L.append("لا توجد ترشيحات بعد.")
    else:
        by_user: dict[str, list[dict]] = defaultdict(list)
        for s in sugs:
            by_user[s.get("submitted_by", "—")].append(s)

        for submitter, books in sorted(by_user.items(), key=lambda x: x[0]):
            count_label = f"{len(books)} كتاب" if len(books) != 1 else "كتاب واحد"
            L.append(f"<b>{submitter}</b> ({count_label}):")
            for bk in books:
                num   = bk.get("number", "?")
                title = bk.get("title", "—")
                L.append(f"  {num}. {title}")
            L.append("")

        # Summary footer
        submitter_count = len(by_user)
        L.append(f"<i>{submitter_count} مُرشِّح · {len(sugs)} كتاب في المجموع</i>")

    await update.message.reply_text("\n".join(L), parse_mode="HTML")
    logger.info(
        "suggestionsoverview: delivered to user %s — %d suggestions",
        update.effective_user.id, len(sugs),
    )


async def _cb_archive_polls(bot, done_title: str) -> None:
    """Archive active participation and rating polls for a just-completed book."""
    active_poll = poll_store.get_active()
    if active_poll and active_poll["book_title"] == done_title:
        try:
            poll_msg = await bot.stop_poll(
                chat_id=active_poll["chat_id"],
                message_id=active_poll["message_id"],
            )
            final_counts = [opt.voter_count for opt in poll_msg.options]
            poll_store.archive_active(final_counts)
            logger.info(
                "Participation poll archived for '%s': counts=%s",
                done_title, final_counts,
            )
        except Exception as e:
            logger.warning("Could not stop participation poll: %s — archiving from stored votes", e)
            poll_store.archive_active()
        # ── Analytics: emit participation_poll event ──────────────────────────
        _ap = poll_store.get_archived_for_book(done_title)
        if _ap:
            _ap_counts = _ap.get("final_counts", [0, 0, 0])
            _ap_total  = sum(_ap_counts)
            _ap_rate   = round(_ap_counts[poll_store.OPTION_PARTICIPATE] / _ap_total, 3) if _ap_total > 0 else 0.0
            analytics_store.append_event({
                "poll_type":        "participation_poll",
                "cycle_number":     cycle_store.get_cycle_number(),
                "roadmap_counter":  roadmap_store.get_roadmap_id(),
                "roadmap_stage":    roadmap_store.get_current_stage(),
                "book_title":       done_title,
                "started_at":       _ap.get("created_at", ""),
                "closed_at":        _ap.get("closed_at", ""),
                "participant_count": _ap.get("participant_count", 0),
                "extension_count":  0,
                "payload": {
                    "options":            poll_store.POLL_OPTIONS,
                    "final_counts":       _ap_counts,
                    "participation_rate": _ap_rate,
                },
            })

    active_rating = rating_store.get_active()
    if active_rating and active_rating["book_title"] == done_title:
        try:
            rating_msg = await bot.stop_poll(
                chat_id=active_rating["chat_id"],
                message_id=active_rating["message_id"],
            )
            final_counts = [opt.voter_count for opt in rating_msg.options]
            rating_store.archive_active(final_counts)
            logger.info(
                "Rating poll archived for '%s': counts=%s",
                done_title, final_counts,
            )
        except Exception as e:
            logger.warning("Could not stop rating poll: %s — archiving from stored votes", e)
            rating_store.archive_active()
        # ── Analytics: emit rating_poll event ────────────────────────────────
        _rp = rating_store.get_archived_for_book(done_title)
        if _rp:
            _rp_dist  = _rp.get("distribution", [])
            _rp_total = _rp.get("total_ratings", 0)
            _rp_avg   = (
                round(sum((i + 1) * _rp_dist[i] for i in range(len(_rp_dist))) / _rp_total, 2)
                if _rp_total > 0 else 0.0
            )
            analytics_store.append_event({
                "poll_type":        "rating_poll",
                "cycle_number":     cycle_store.get_cycle_number(),
                "roadmap_counter":  roadmap_store.get_roadmap_id(),
                "roadmap_stage":    roadmap_store.get_current_stage(),
                "book_title":       done_title,
                "started_at":       _rp.get("created_at", ""),
                "closed_at":        _rp.get("closed_at", ""),
                "participant_count": _rp_total,
                "extension_count":  0,
                "payload": {
                    "distribution":      _rp_dist,
                    "total_ratings":     _rp_total,
                    "average_rating":    _rp_avg,
                    "most_common_rating": _rp.get("most_common_rating", 0),
                },
            })


def _cb_clear_schedule(done_title: str) -> None:
    """Clear the reading schedule after book completion."""
    try:
        schedule_store.clear()
        logger.info("completebook: schedule cleared after completing '%s'", done_title)
    except Exception as e:
        logger.warning("completebook: could not clear schedule: %s", e)


def _cb_archive_to_book_store(
    done_title: str,
    completing_category: str | None,
    completing_roadmap_id: int | None,
) -> bool:
    """
    Archive the completed book and its stats to the permanent club book store.
    Returns True on success, False if the archive write failed.
    Intentionally does NOT clear discussion_store — the caller does that
    only after confirming a successful archive.
    """
    try:
        poll_arc = poll_store.get_archived_for_book(done_title)
        participants = poll_arc.get("participant_count", 0) if poll_arc else 0
        completions_count = completion_store.get_count(done_title)
        rating_arc = rating_store.get_archived_for_book(done_title)
        rating_data: dict = {}
        if rating_arc:
            rating_data = {
                "distribution": rating_arc.get("distribution", []),
                "total":        rating_arc.get("total_ratings", 0),
                "most_common":  rating_arc.get("most_common_rating", 0),
            }
        cycle_data = cycle_store.load()
        book_entry = next(
            (b for b in cycle_data.get("books", []) if b["title"] == done_title),
            None,
        )
        disc_log = discussion_store.get_all()
        book_store.archive_completed(
            done_title,
            category=completing_category,
            roadmap_id=completing_roadmap_id,
            start_date=book_entry.get("started_at") if book_entry else None,
            end_date=book_entry.get("ended_at") if book_entry else None,
            participants=participants,
            completions=completions_count,
            rating=rating_data,
            discussion_log=disc_log,
        )
        logger.info(
            "book_store: archived '%s' (category=%s, roadmap_id=%s, discussion_log=%d entries)",
            done_title, completing_category, completing_roadmap_id, len(disc_log),
        )
        return True
    except Exception as _arc_err:
        logger.warning("book_store: could not archive '%s': %s", done_title, _arc_err)
        return False


def _cb_advance_roadmap() -> tuple[str | None, bool]:
    """
    Advance the roadmap stage if one is active.
    Returns (next_category, roadmap_completed).
    """
    if not roadmap_store.is_roadmap_active():
        return None, False
    next_category = roadmap_store.advance_stage()
    roadmap_completed = roadmap_store.is_roadmap_completed()
    return next_category, roadmap_completed


def _cb_build_messages(
    done_title: str,
    next_category: str | None,
    roadmap_completed: bool,
) -> tuple[str, str]:
    """
    Build the owner DM message and group announcement for a book completion.
    Returns (dm_message, group_message).
    """
    if roadmap_completed:
        dm_msg = (
            f"✅ <b>تم إنهاء الكتاب:</b> {done_title}\n\n"
            f"🏁 <b>اكتملت خارطة القراءة الرباعية!</b>\n\n"
            f"لا يمكن فتح ترشيحات أو بدء تصويت جديد\n"
            f"حتى يتم إنشاء خارطة جديدة.\n\n"
            f"استخدم /startroadmap لبدء الخارطة التالية."
        )
        group_msg = (
            f"🎉 انتهينا من قراءة:\n"
            f"<b>{done_title}</b>\n\n"
            f"🏁 اكتملت خارطة القراءة! نراكم في الدورة القادمة. 🗺️"
        )
    elif next_category:
        dm_msg = (
            f"✅ <b>تم إنهاء الكتاب:</b> {done_title}\n\n"
            f"🗺️ <b>التصنيف التالي:</b> {next_category}\n\n"
            f"افتح الترشيحات عبر /opensuggestions لاختيار كتاب هذا التصنيف."
        )
        group_msg = (
            f"🎉 انتهينا من قراءة:\n"
            f"<b>{done_title}</b>\n\n"
            f"📖 ننتقل الآن إلى تصنيف:\n"
            f"<b>{next_category}</b>\n\n"
            f"🗳️ يمكن الآن فتح ترشيحات الكتب الخاصة بهذه المرحلة."
        )
    else:
        dm_msg = (
            f"✅ <b>تم إنهاء الكتاب:</b> {done_title}\n\n"
            f"🏁 <b>انتهت دورة القراءة!</b>\n"
            f"يمكن بدء دورة جديدة عبر /opensuggestions"
        )
        group_msg = (
            f"✅ انتهينا من <b>{done_title}</b>!\n"
            f"ترقبوا الإعلان عن الكتاب القادم 📚"
        )
    return dm_msg, group_msg


async def completebook_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/completebook — mark the current book as completed and advance the queue. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    user_id = update.effective_user.id

    if not cycle_store.is_active():
        await update.message.reply_text("ℹ️ لا توجد دورة قراءة نشطة حالياً.")
        return

    # ── Confirmation gate ─────────────────────────────────────────────────────
    _CONFIRM_KEY = "completebook_pending"
    _CONFIRM_TTL = 60  # seconds
    now_ts = datetime.now(TIMEZONE).timestamp()

    if not context.args or context.args[0] != "confirm":
        current_book = cycle_store.get_current_book()
        book_title = current_book.get("title", "—") if current_book else "—"
        context.bot_data[_CONFIRM_KEY] = {"expires_at": now_ts + _CONFIRM_TTL}
        await update.message.reply_text(
            f"⚠️ <b>تأكيد إنهاء الكتاب</b>\n\n"
            f"📖 {_html.escape(book_title)}\n\n"
            "سيتم تنفيذ الإجراءات التالية ولا يمكن التراجع عنها:\n"
            "• أرشفة الكتاب والتقييمات والنقاشات\n"
            "• تقديم مرحلة خارطة القراءة\n"
            "• مسح الجدول النشط\n\n"
            "للتأكيد أرسل خلال 60 ثانية:\n"
            "<code>/completebook confirm</code>",
            parse_mode="HTML",
        )
        return

    pending = context.bot_data.get(_CONFIRM_KEY)
    if not pending or now_ts > pending.get("expires_at", 0):
        context.bot_data.pop(_CONFIRM_KEY, None)
        await update.message.reply_text(
            "⏰ انتهت مهلة التأكيد.\n"
            "أرسل /completebook مرة أخرى للبدء."
        )
        return

    context.bot_data.pop(_CONFIRM_KEY, None)
    # ── end confirmation gate — proceed with full completion below ────────────

    # Capture roadmap info BEFORE completing (category & roadmap_id belong to the finishing stage)
    completing_category = roadmap_store.get_active_category()
    completing_roadmap_id = roadmap_store.get_roadmap_id() if roadmap_store.is_roadmap_active() else None

    try:
        done_title = cycle_store.complete_current()
    except ValueError:  # log-exempt: expected control-flow guard; no active cycle is a valid user-facing condition, not a system fault
        await update.message.reply_text("⚠️ لا توجد دورة قراءة نشطة قابلة للإكمال.")
        return

    await _cb_archive_polls(context.bot, done_title)
    _cb_clear_schedule(done_title)
    archived_ok = _cb_archive_to_book_store(done_title, completing_category, completing_roadmap_id)
    if archived_ok:
        discussion_store.clear()
    else:
        logger.warning(
            "completebook: discussion log NOT cleared because archiving failed for '%s'",
            done_title,
        )
    next_category, roadmap_completed = _cb_advance_roadmap()
    dm_msg, group_msg = _cb_build_messages(done_title, next_category, roadmap_completed)

    # Notify owner about postponed nominations waiting for the new active category
    if next_category:
        postponed = postponed_store.get_for_category(next_category)
        if postponed:
            postponed_store.mark_notified(next_category)
            await update.message.reply_text(
                _postponed_dm_text(next_category, postponed),
                parse_mode="HTML",
            )

    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": group_msg,
        "parse_mode": "HTML",
    }
    await update.message.reply_text(
        dm_msg + "\n\n──────────────\nاضغط الزر لإعلام المجموعة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("Book completed by user %s: '%s' (category=%s)", user_id, done_title, completing_category)
    # Synchronise Companion: completed book joins the archive
    asyncio.create_task(_auto_export_context("book_completed"))


async def _auto_export_context(reason: str) -> None:
    """Fire-and-forget: regenerate and POST the Community Context Contract.

    Called automatically after any lifecycle event that changes operational
    state. Never raises — failures are logged but never affect the caller.

    Schedule as a background task so the triggering command is never delayed:

        asyncio.create_task(_auto_export_context("reason"))

    Args:
        reason: Short label used in log messages, e.g. "schedule_uploaded".
    """
    try:
        from community_context import build_contract, post_contract
        contract = build_contract()
        ok, msg = post_contract(contract)
        if ok:
            logger.info("auto_export_context [%s]: contract posted successfully", reason)
        else:
            logger.warning("auto_export_context [%s]: post failed: %s", reason, msg)
    except Exception as exc:
        logger.error("auto_export_context [%s]: unexpected error: %s", reason, exc)


async def exportcontext_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/exportcontext — generate and post the Community Context Contract to Companion (owner DM only).

    Builds a structured JSON document (Layer 1: raw facts + Layer 2: derived
    operational summaries) from all Takbeer data stores and POSTs it to the
    WAQT API server via POST /api/admin/community-context.

    Requires WAQT_API_BASE_URL and SESSION_SECRET environment variables.
    No per-member records are included — community-level aggregates only.
    Interpretation of the data belongs to Companion, not to this export.
    """
    if update.message is None:
        return
    if not _is_owner_dm(update):
        return

    await update.message.reply_text("⏳ جاري إنشاء السياق التشغيلي...")
    try:
        from community_context import build_contract, post_contract
        contract = build_contract()
        books_n = len(contract.get("bookHistory", []))
        current = contract.get("currentBook")
        current_title = current.get("title", "—") if current else "لا يوجد كتاب نشط"
        ok, msg = post_contract(contract)
        if ok:
            await update.message.reply_text(
                f"{msg}\n"
                f"الكتاب الحالي: «{current_title}»\n"
                f"الكتب في السجل: {books_n}"
            )
        else:
            await update.message.reply_text(msg)
    except Exception as exc:
        logger.exception("exportcontext_command failed")
        await update.message.reply_text("❌ خطأ أثناء تصدير السياق، يرجى المحاولة مرة أخرى.")


async def setmeta_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/setmeta — save or update metadata for the current book (admin only).

    Usage (send command and fields together):
        /setmeta
        المؤلف: رومان غاري
        المترجم: إيناس التكريتي
        الناشر: المركز الثقافي العربي
        السنة: 1975
        الصفحات: 340
        التصنيف: رواية، أدب فرنسي
        الوصف: رواية للكاتب الفرنسي رومان غاري...
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    book_dict = cycle_store.get_current_book()
    title = book_dict["title"] if book_dict else schedule_store.load().get("current_book", "")
    if not title:
        await update.message.reply_text("⚠️ لا يوجد كتاب نشط حالياً.")
        return

    # Strip command prefix (handles /setmeta, /setbook, and @botname variants)
    raw = update.message.text or ""
    body = re.sub(r"^/setmeta\S*\s*", "", raw, flags=re.IGNORECASE).strip()

    if not body:
        existing = book_store.get_metadata(title)
        hint = (
            f"📝 <b>بيانات الكتاب الحالي:</b> {_html.escape(title)}\n"
            "\n"
            "أرسل الأمر مرفقاً بالمعلومات، مثل:\n"
            "<code>/setmeta\n"
            "المؤلف: اسم المؤلف\n"
            "المترجم: اسم المترجم\n"
            "الناشر: اسم الناشر\n"
            "السنة: 2020\n"
            "الصفحات: 350\n"
            "التصنيف: رواية\n"
            "الوصف: نبذة قصيرة عن الكتاب</code>"
        )
        if existing:
            filled = [k for k in ("author", "translator", "publisher", "year", "pages") if existing.get(k)]
            if filled:
                hint += "\n\n<i>يوجد بيانات مسجّلة بالفعل لهذا الكتاب.</i>"
        await update.message.reply_text(hint, parse_mode="HTML")
        return

    # Arabic key → JSON field name
    KEY_MAP: dict[str, str] = {
        "المؤلف":          "author",
        "الكاتب":          "author",
        "المترجم":         "translator",
        "الترجمة":         "translator",
        "الناشر":          "publisher",
        "دار النشر":       "publisher",
        "السنة":           "year",
        "سنة النشر":       "year",
        "سنة الإصدار":     "year",
        "الصفحات":         "pages",
        "عدد الصفحات":    "pages",
        "اللغة الأصلية":  "original_language",
        "اللغة":           "original_language",
        "بلد المؤلف":      "author_country",
        "جنسية المؤلف":    "author_country",
        "العنوان الأصلي":  "original_title",
        "الاسم الأصلي":    "original_title",
        "التصنيف":         "genres",
        "النوع":           "genres",
        "الوصف":           "description",
        "النبذة":          "description",
    }

    fields: dict = {"title": title}
    for line in body.splitlines():
        line = line.strip()
        if ":" not in line:
            continue
        key_raw, _, value = line.partition(":")
        key_raw = key_raw.strip()
        value   = value.strip()
        if not value:
            continue
        field = KEY_MAP.get(key_raw)
        if not field:
            continue
        if field == "year":
            try:
                fields["year"] = int(value)
            except ValueError:
                fields["year"] = value
        elif field == "pages":
            try:
                fields["pages"] = int(value)
            except ValueError:
                fields["pages"] = value
        elif field == "genres":
            parts = [g.strip() for g in re.split(r"[،,]", value) if g.strip()]
            fields["genres"] = parts
        else:
            fields[field] = value

    if len(fields) <= 1:  # only "title" key — nothing parsed
        await update.message.reply_text(
            "⚠️ لم يتم التعرف على أي حقول. تأكد من صيغة الأمر."
        )
        return

    book_store.set_metadata(title, fields)

    LABEL: dict[str, str] = {
        "author":            "المؤلف",
        "translator":        "المترجم",
        "publisher":         "الناشر",
        "year":              "سنة النشر",
        "pages":             "الصفحات",
        "original_language": "اللغة الأصلية",
        "author_country":    "بلد المؤلف",
        "original_title":    "العنوان الأصلي",
        "genres":            "التصنيف",
        "description":       "الوصف",
    }
    lines_out = [f"✅ <b>تم حفظ بيانات:</b> {_html.escape(title)}", ""]
    for field, label in LABEL.items():
        if field in fields:
            val = fields[field]
            if isinstance(val, list):
                val = "، ".join(str(v) for v in val)
            lines_out.append(f"• {label}: {val}")

    await update.message.reply_text("\n".join(lines_out), parse_mode="HTML")
    logger.info(
        "/setmeta: saved %s for '%s' by user %s",
        list(fields.keys()), title, user_id,
    )
    asyncio.create_task(_auto_export_context("metadata_updated"))


async def skipbook_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/skipbook — skip the current active book. Activates the next ranked candidate
    from stage memory. If none remain, stays at the same roadmap category and
    allows fresh nominations. Owner DM only.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    if not cycle_store.is_active():
        await update.message.reply_text("ℹ️ لا توجد دورة قراءة نشطة حالياً.")
        return

    try:
        skipped_title = cycle_store.skip_current()
    except ValueError:  # log-exempt: expected control-flow guard; no skippable cycle is a valid user-facing condition, not a system fault
        await update.message.reply_text("⚠️ تعذّر تخطي الكتاب الحالي.")
        return

    # Clear stale schedule
    try:
        schedule_store.clear()
        logger.info("skipbook: schedule cleared after skipping '%s'", skipped_title)
    except Exception as e:
        logger.warning("skipbook: could not clear schedule: %s", e)

    # Try to advance to next stage candidate
    next_candidate = roadmap_store.get_next_stage_candidate()
    if next_candidate:
        next_title = next_candidate["title"]
        try:
            cycle_store.start_cycle(next_title)
        except ValueError:  # log-exempt: ValueError means a cycle is already active; skip silently
            pass
        progress_store.reset()  # clear previous book's progress for new cycle
        msg = (
            f"⏭️ <b>تم تخطي الكتاب:</b> {skipped_title}\n\n"
            f"📖 <b>الكتاب التالي (من التصويت):</b> {next_title}\n\n"
            f"⬆️ الكتاب الجديد أصبح نشطاً تلقائياً.\n"
            f"📅 استخدم /newschedule لرفع جدول القراءة الجديد."
        )
        group_msg = (
            f"⏭️ تم تخطي <b>{skipped_title}</b>\n\n"
            f"📖 ننتقل الآن إلى: <b>{next_title}</b>"
        )
        logger.info("skipbook: activated next candidate '%s'", next_title)
    else:
        # No candidates remain — stay in same category, allow fresh nominations
        active_cat = roadmap_store.get_active_category()
        cat_note = f"\n📂 التصنيف: <b>{active_cat}</b>" if active_cat else ""
        msg = (
            f"⏭️ <b>تم تخطي الكتاب:</b> {skipped_title}\n\n"
            f"📭 <b>لا يوجد مزيد من المرشحين المرتبين.</b>{cat_note}\n\n"
            f"يمكنك فتح جولة ترشيحات جديدة لنفس التصنيف عبر /opensuggestions"
        )
        group_msg = (
            f"⏭️ تم تخطي <b>{skipped_title}</b>\n\n"
            f"سنفتح جولة ترشيحات جديدة قريباً."
        )
        logger.info("skipbook: no candidates remain for current stage")

    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": group_msg,
        "parse_mode": "HTML",
    }
    await update.message.reply_text(
        msg + "\n\n──────────────\nاضغط الزر لإعلام المجموعة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("Book skipped by user %s: '%s'", update.effective_user.id, skipped_title)
    # Synchronise Companion: current book changed
    asyncio.create_task(_auto_export_context("book_skipped"))


async def readpoll_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/readpoll — create a participation poll for the current active book."""
    if update.message is None or update.effective_user is None:
        return
    if not _from_configured_chat(update):
        return
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id

    owner = await _ensure_owner(user_id, chat_id, context.bot)
    if not owner and not auth_store.is_authorized(user_id):
        await update.message.reply_text("⛔ هذا الأمر للمالك والمديرين فقط.")
        return

    # Resolve the current active book title
    book_title = ""
    if cycle_store.is_active():
        cur_b = cycle_store.get_current_book()
        if cur_b:
            book_title = cur_b["title"]
    if not book_title:
        store = schedule_store.load()
        book_title = store.get("current_book", "")
    if not book_title:
        await update.message.reply_text("❌ لا يوجد كتاب نشط حالياً.")
        return

    # Check for existing active poll for this book
    active = poll_store.get_active()
    if active:
        if active["book_title"] == book_title:
            await update.message.reply_text(
                f"⚠️ يوجد بالفعل استفتاء مشاركة نشط لهذا الكتاب.\n"
                f"📖 {book_title}"
            )
            return
        # There's an orphaned poll for a different book — archive it first
        poll_store.archive_active()

    # Check the book wasn't already completed with an archived poll
    archived = poll_store.get_archived_for_book(book_title)
    if archived:
        await update.message.reply_text(
            f"⚠️ لا يمكن إنشاء استفتاء مشاركة لكتاب مكتمل.\n"
            f"📖 {book_title}\n"
            f"👥 عدد القراء المسجلين: {archived['participant_count']}"
        )
        return

    # Send the poll (non-anonymous so vote updates reach the bot in real-time)
    try:
        sent = await context.bot.send_poll(
            chat_id=chat_id,
            question=f"📚 من سيشارك في قراءة:\n{book_title}",
            options=poll_store.POLL_OPTIONS,
            is_anonymous=False,
            allows_multiple_answers=False,
        )
    except Exception as e:
        logger.error("readpoll: failed to send poll for '%s': %s", book_title, e)
        await update.message.reply_text("❌ تعذّر إرسال استفتاء المشاركة. تأكد أن البوت مشرف وحاول مرة أخرى.")
        return

    poll_store.set_active(
        book_title=book_title,
        poll_id=sent.poll.id,
        message_id=sent.message_id,
        chat_id=chat_id,
    )
    logger.info("readpoll: created for '%s' by user %s (poll_id=%s)", book_title, user_id, sent.poll.id)


async def handle_poll_answer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Route incoming poll answers to the correct store (category vote, participation, or rating)."""
    answer = update.poll_answer
    if answer is None:
        return

    # Category vote (roadmap selection)
    if roadmap_store.is_category_vote_active():
        cv_data = roadmap_store.load().get("category_vote", {})
        if cv_data.get("poll_id") == answer.poll_id:
            roadmap_store.record_category_answer(answer.user.id, answer.option_ids)
            return

    # Participation poll
    active_part = poll_store.get_active()
    if active_part and active_part["poll_id"] == answer.poll_id:
        poll_store.record_vote(answer.user.id, answer.option_ids)
        return

    # Rating poll
    active_rate = rating_store.get_active()
    if active_rate and active_rate["poll_id"] == answer.poll_id:
        rating_store.record_vote(answer.user.id, answer.option_ids)


async def rate_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/rate — create a post-reading rating poll for the current active book (Phase 8)."""
    if update.message is None or update.effective_user is None:
        return
    if not _from_configured_chat(update):
        return
    user_id = update.effective_user.id
    chat_id = update.effective_chat.id

    owner = await _ensure_owner(user_id, chat_id, context.bot)
    if not owner and not auth_store.is_authorized(user_id):
        await update.message.reply_text("⛔ هذا الأمر للمالك والمديرين فقط.")
        return

    # ── Resolve the current active book ─────────────────────────────────────
    cur_book = cycle_store.get_current_book()
    if not cur_book:
        await update.message.reply_text(
            "❌ لا توجد دورة قراءة نشطة حالياً.\n\n"
            "<i>يمكن استخدام /rate بعد تفعيل دورة القراءة.</i>",
            parse_mode="HTML",
        )
        return

    book_title = cur_book["title"]

    # ── Guard: rating poll already exists for this book ──────────────────────
    active = rating_store.get_active()
    if active:
        if active["book_title"] == book_title:
            await update.message.reply_text(
                f"⚠️ يوجد بالفعل استفتاء تقييم نشط لهذا الكتاب.\n"
                f"📖 {book_title}"
            )
            return
        # Orphaned poll for a different book — archive it silently
        rating_store.archive_active()

    archived = rating_store.get_archived_for_book(book_title)
    if archived:
        stars = "⭐️" * archived["most_common_rating"] if archived["most_common_rating"] else "—"
        await update.message.reply_text(
            f"⚠️ تم إغلاق استفتاء تقييم هذا الكتاب مسبقاً.\n\n"
            f"📖 {book_title}\n"
            f"⭐️ أكثر تقييم شائع: {stars}\n"
            f"📊 إجمالي التقييمات: {archived['total_ratings']}",
            parse_mode="HTML",
        )
        return

    # ── Send the rating poll ─────────────────────────────────────────────────
    try:
        sent = await context.bot.send_poll(
            chat_id=chat_id,
            question=f"⭐️ قيّموا كتاب:\n{book_title}",
            options=rating_store.POLL_OPTIONS,
            is_anonymous=False,
            allows_multiple_answers=False,
        )
    except Exception as e:
        logger.error("rate: failed to send poll for '%s': %s", book_title, e)
        await update.message.reply_text("❌ تعذّر إرسال استفتاء التقييم. تأكد أن البوت مشرف وحاول مرة أخرى.")
        return

    rating_store.set_active(
        book_title=book_title,
        poll_id=sent.poll.id,
        message_id=sent.message_id,
        chat_id=chat_id,
    )
    logger.info("rate: poll created for '%s' by user %s (poll_id=%s)", book_title, user_id, sent.poll.id)


async def done_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/done — register completion of the current active book (Phase 7).

    Available only after the final scheduled reading date has passed.
    The final date is determined automatically from the uploaded /newschedule.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _from_configured_chat(update):
        return

    user_id   = update.effective_user.id
    user_name = update.effective_user.full_name or str(user_id)

    cur_book = cycle_store.get_current_book()
    if not cur_book:
        await update.message.reply_text(
            "❌ لا توجد دورة قراءة نشطة حالياً.\n\n"
            "<i>يُمكن استخدام /done بعد تفعيل دورة القراءة.</i>",
            parse_mode="HTML",
        )
        return

    book_title = cur_book["title"]

    # ── Date gate: check if the final scheduled reading date has passed ──────
    sch = schedule_store.load()
    reading_entries = [e for e in sch.get("entries", []) if not e.get("is_rest", False)]

    if not reading_entries:
        await update.message.reply_text(
            f"⚠️ لم يُرفع جدول القراءة للكتاب الحالي بعد.\n\n"
            f"📖 <b>{_html.escape(book_title)}</b>\n\n"
            f"<i>يرجى انتظار رفع الجدول من المشرف عبر /newschedule.</i>",
            parse_mode="HTML",
        )
        return

    from datetime import datetime as _dt
    today = _dt.now(TIMEZONE).date()
    last_reading_date = date.fromisoformat(max(e["date"] for e in reading_entries))

    if today < last_reading_date:
        days_left = (last_reading_date - today).days
        unit = "يوم" if days_left == 1 else "أيام"
        await update.message.reply_text(
            f"⏳ لم ينته جدول القراءة بعد.\n\n"
            f"📖 <b>{_html.escape(book_title)}</b>\n"
            f"📅 آخر يوم قراءة: <b>{_ar_date(last_reading_date)}</b>\n"
            f"بقي: {days_left} {unit}",
            parse_mode="HTML",
        )
        return

    # ── Guard: duplicate registration ────────────────────────────────────────
    if completion_store.has_completed(user_id, book_title):
        await update.message.reply_text(
            f"⚠️ تم تسجيل إنجازك مسبقاً لهذا الكتاب.\n\n"
            f"📖 <b>{_html.escape(book_title)}</b>",
            parse_mode="HTML",
        )
        return

    # ── Register ─────────────────────────────────────────────────────────────
    completion_store.register(user_id, book_title)
    count = completion_store.get_count(book_title)

    await update.message.reply_text(
        f"✅ تم تسجيل إنجازك للكتاب:\n\n"
        f"<b>{_html.escape(book_title)}</b>\n\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"<i>إجمالي المنجزين حتى الآن: {count}</i>",
        parse_mode="HTML",
    )
    logger.info("done: user %s (%s) completed '%s' (total=%d)", user_id, user_name, book_title, count)


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


# Intents that query club-operational data (schedules, progress, polls, votes).
# When data is absent for these, redirecting is correct — AI would fabricate
# schedules or progress figures that look authoritative but are wrong.
# All other intents (book_author, book_translator, etc.) fall through to AI.
_CLUB_DATA_INTENTS: frozenset[str] = frozenset({
    "today_reading",
    "current_book",
    "progress",
    "queue",
    "history",
    "participation",
    "rating",
    "completion",
    "vote",
})


async def _smart_reply(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    user_text: str,
    username: str,
    trigger: str,
) -> None:
    """
    Unified reply dispatcher for @voicewaqtbot.

    Decision order:
      1. Intent matched + data found
         → serve deterministic reply from internal data.
      2. Intent is club-operational (schedule, progress, polls…) + data absent
         → redirect to /ask. AI would fabricate schedules/progress figures.
      3. Intent is book-knowledge (author, translator, language…) + data absent
         → AI fallback with uncertainty handling. These are general questions
            that the AI can answer from training knowledge, hedged appropriately.
      4. No intent matched (conversational)
         → AI fallback. Treat as a general reading-club discussion.
    """
    intent = _match_intent(user_text)

    if intent:
        # Club-operational data is only disclosed to the configured reading group.
        # Outside chats fall through to the conversational AI gate below.
        if _from_configured_chat(update):
            reply = _build_data_reply(intent, user_text)
            if reply:
                logger.info(
                    "@voicewaqtbot: intent '%s' matched for %s (trigger=%s) — serving from data",
                    intent, username, trigger,
                )
                user_id = update.effective_user.id if update.effective_user else 0
                _conv_last_seen[user_id] = time.monotonic()
                try:
                    await update.message.reply_text(reply, parse_mode="HTML")
                except Exception:  # log-exempt: HTML parse failure; plain-text fallback is sent instead
                    await update.message.reply_text(reply)
                return

            # Data absent — route based on intent type.
            if intent in _CLUB_DATA_INTENTS:
                logger.info(
                    "@voicewaqtbot: intent '%s' (club-data) for %s — data absent, redirecting",
                    intent, username,
                )
                if update.message:
                    try:
                        await update.message.reply_text(
                            "لا أملك معلومات موثقة عن ذلك حالياً.\n\n"
                            "يمكنك استخدام /ask للحصول على إجابة عامة من الذكاء الاصطناعي.",
                        )
                    except Exception as e:
                        logger.error("@voicewaqtbot: redirect failed for %s: %s", username, e)
                return

            logger.info(
                "@voicewaqtbot: intent '%s' (book-knowledge) for %s — data absent, using AI fallback",
                intent, username,
            )
        else:
            logger.info(
                "@voicewaqtbot: intent '%s' for %s (trigger=%s) — outside configured chat, skipping data reply",
                intent, username, trigger,
            )
    else:
        logger.info(
            "@voicewaqtbot: no intent matched for %s (trigger=%s) — conversational AI | text: %s",
            username, trigger, user_text[:150],
        )

    # ── Follow-up gate ────────────────────────────────────────────────────────
    # Passes when ANY of three conditions is true:
    #   A) This user has an active solo conversation window (_conv_last_seen).
    #   B) The message is a direct Telegram reply to one of the bot's messages.
    #   C) There is an active shared group discussion with room for this user.
    # The gate does NOT fire just because a shared discussion is open — an
    # explicit user action (A, B, or C) is always required to reach this point.
    user_id = update.effective_user.id if update.effective_user else 0
    chat_id = update.effective_chat.id if update.effective_chat else 0
    _now = time.monotonic()

    # A: sender has their own active window
    _last_seen = _conv_last_seen.get(user_id)
    in_active_conversation = _last_seen is not None and (_now - _last_seen) < _CONV_TIMEOUT_SECS

    # B: sender explicitly used Telegram's reply feature on a bot message
    is_direct_bot_reply = (
        update.message is not None
        and update.message.reply_to_message is not None
        and update.message.reply_to_message.from_user is not None
        and update.message.reply_to_message.from_user.id == context.bot.id
    )

    # C: active shared discussion with capacity for a new participant
    _disc = _group_discussions.get(chat_id)
    disc_active = (
        _disc is not None
        and (_now - _disc["last_activity"]) < _CONV_TIMEOUT_SECS
        and (
            user_id in _disc["participants"]
            or len(_disc["participants"]) < _GROUP_MAX_PARTICIPANTS
        )
    )

    if not (in_active_conversation or is_direct_bot_reply or disc_active):
        logger.info(
            "@voicewaqtbot: standalone question, no active conversation for %s — redirecting to /ask",
            username,
        )
        if update.message:
            try:
                await update.message.reply_text(
                    "لا أملك معلومات موثقة عن ذلك حالياً.\n\n"
                    "يمكنك استخدام /ask للحصول على إجابة عامة من الذكاء الاصطناعي.",
                )
            except Exception as e:
                logger.error("@voicewaqtbot: redirect failed for %s: %s", username, e)
        return

    # Determine which history slot to use: shared (chat_id) or solo (user_id).
    _hkey = _resolve_history_key(chat_id, user_id)
    logger.info(
        "@voicewaqtbot: active follow-up for %s (trigger=%s, history=%s) — using AI pipeline",
        username, trigger, "shared" if _hkey != user_id else "solo",
    )

    # ── AI reply ──────────────────────────────────────────────────────────────
    # Mirrors the /ask pipeline: inject verified metadata when available, prepend
    # the reading context, and apply uncertainty handling for high-risk questions.
    if gemini_client is None:
        if update.message:
            await update.message.reply_text("خدمة الذكاء الاصطناعي غير متاحة حالياً.")
        return

    # Club metadata (book_store/archive), session context, and reading progress
    # are private to the configured reading group. Only inject them when the
    # request arrives from that group.
    is_configured = _from_configured_chat(update)

    verified_context = ""
    if is_configured:
        named_title = _extract_book_title_from_query(user_text)
        if named_title:
            meta = book_store.get_metadata(named_title)
            archived = book_store.find_in_archive(named_title) if not meta else None
            data = meta or archived
            if data:
                matched = data.get("title", named_title)
                src = "أرشيف النادي" if archived else "بيانات النادي"
                fields: list[str] = []
                for key, label in [
                    ("author",            "المؤلف"),
                    ("translator",        "المترجم"),
                    ("publisher",         "الناشر"),
                    ("year",              "سنة النشر"),
                    ("pages",             "الصفحات"),
                    ("original_language", "اللغة الأصلية"),
                    ("author_country",    "بلد المؤلف"),
                    ("original_title",    "العنوان الأصلي"),
                ]:
                    if data.get(key):
                        fields.append(f"{label}: {data[key]}")
                if fields:
                    verified_context = (
                        f"[بيانات موثقة من {src} عن «{matched}»]\n"
                        + "\n".join(fields)
                        + "\n\n"
                    )

    is_high_risk = bool(_HIGH_RISK_BOOK_RE.search(user_text))
    uncertainty_hint = ""
    if not verified_context and is_high_risk:
        uncertainty_hint = (
            "\n\n[تنبيه: إذا لم تكن ثقتك عالية في هذه التفصيلة، "
            "اذكر ذلك صراحةً بدلاً من تقديم معلومات قد تكون غير دقيقة.]"
        )

    if is_configured:
        session_ctx = await _get_session_context()
        context_hint = _get_reading_context_hint()
        book_prep_ctx = _get_book_prep_context()
        _conv_uid = update.effective_user.id if update.effective_user else 0
        spoiler_guard = _get_spoiler_guard(_conv_uid)
        _conv_book = cycle_store.get_current_book()
        knowledge_ctx = _get_knowledge_context(user_text, _conv_book["title"]) if _conv_book else ""
    else:
        session_ctx = ""
        context_hint = ""
        book_prep_ctx = ""
        spoiler_guard = ""
        knowledge_ctx = ""

    # Detect when the user is answering a clarification question the bot just asked.
    # If the last model turn ends with a question mark, inject a [CONTINUATION] hint so
    # the model knows to look back in history and continue the thread rather than treating
    # this message as a new standalone input.
    continuation_hint = ""
    _hist = conversation_histories.get(_hkey, [])
    if _hist:
        _last_model_text = ""
        for _turn in reversed(_hist):
            if getattr(_turn, "role", "") == "model":
                _last_model_text = "".join(
                    getattr(_p, "text", "") for _p in (getattr(_turn, "parts", None) or [])
                ).rstrip()
                break
        if _last_model_text.endswith("؟") or _last_model_text.endswith("?"):
            continuation_hint = (
                "[CONTINUATION: هذه الرسالة تبدو إجابةً على سؤال التوضيح الذي طرحتِه للتو. "
                "راجعي تاريخ المحادثة لتجدي السؤال الأصلي، ثم قدّمي الإجابة الكاملة في سياقه.]\n\n"
            )

    parts = [p for p in [session_ctx, verified_context, context_hint, book_prep_ctx, knowledge_ctx, spoiler_guard, continuation_hint, user_text, uncertainty_hint] if p]
    prompt = "".join(parts)

    try:
        _smart_ok = await send_ai_reply(update, context, prompt, skip_history=False, history_key=_hkey, use_search=_question_needs_search(user_text))
        if _smart_ok:
            _open_or_refresh_group_discussion(chat_id, user_id)
    except Exception as e:
        logger.error("@voicewaqtbot: AI fallback error for %s: %s", username, e)
        if update.message:
            await update.message.reply_text("عذراً، حدث خطأ. حاول مرة أخرى.")


# Keyword pre-filter for the session listener.
# Catches literary, cultural, philosophical, and intellectual discussion;
# deliberately excludes casual personal chat.
_SESSION_LISTEN_RE = re.compile(
    # ── Book & narrative (original scope) ─────────────────────────────────
    r"رواية|كتاب|فصل|صفحة|شخصي[ةه]|حبكة|سرد|راوي|أسلوب|مؤلف|كاتب"
    r"|قرأت|أقرأ|قراءة|أنهيت|وصلت إلى|يذكرني"
    r"|موضوع الكتاب|كيف ينتهي|النهاية|البداية|الحبكة"
    r"|أحببت|أكرهت|خيّبني|استمتعت|مملة|رائعة|ممتازة"
    # ── Philosophy & ideas ─────────────────────────────────────────────────
    r"|فلسف[ةي]|فيلسوف|وجودية|عدمية|مادية|مثالية|أخلاق|مذهب|أيديولوجيا"
    r"|مفهوم|نظرية|جدل|حجة|طرح|فكر[ةي]|تساؤل|إشكالية|برهان"
    # ── History & civilisation ─────────────────────────────────────────────
    r"|تاريخ|حضارة|حقبة|عصر|تراث|موروث|حداثة|ما بعد الحداثة|تنوير"
    r"|إمبراطورية|استعمار|ثورة|حركة|نهضة"
    # ── Literary criticism & schools ───────────────────────────────────────
    r"|نقد|ناقد|بنيوية|رمزية|واقعية|رومانسية|مدرسة أدبية|تيار أدبي"
    r"|ترجم[ةي]|لسانيات|أسلوبية|شعرية|سردية"
    # ── Language & writing ────────────────────────────────────────────────
    r"|لغة|لهجة|لفظ|اشتقاق|معجم|بلاغة|كتابة|أسلوب الكتابة"
    # ── Comparisons & cultural reflection ────────────────────────────────
    r"|مقارنة|مقارنة بين|ثقافة|حضاري|اجتماعي|ظاهرة|تحول|تأثير"
    r"|ما الفرق|يشبه|يختلف|أفضل من|أعمق من"
    # ── Opinion & interpretation signals ─────────────────────────────────
    r"|برأيي|برأيك|أعتقد|أظن|يبدو لي|لم أفهم|ما معنى|لماذا قال",
    re.IGNORECASE,
)


async def session_listener(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Passive literary/cultural discussion listener.

    Silently accumulates messages that match the literary keyword pre-filter
    into the session buffer for later distillation.  Never sends any reply,
    never modifies state visible to the user, and never triggers any further
    processing.  Sender identity is discarded — only the message text is stored.

    Restricted to the configured reading group so that discussion from other
    chats is never mixed into the shared context buffer.
    """
    if update.message is None or not update.message.text:
        return
    if not _from_configured_chat(update):
        return
    text = update.message.text.strip()
    if len(text) < 10 or text.startswith("/"):
        return
    if not _SESSION_LISTEN_RE.search(text):
        return
    session_store.add_message(text)


async def book_auto_reply_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Auto-reply only when the bot is explicitly involved or the discussion is about this bot.

    Triggers (in order of cheapness):
      1. Bot is @mentioned in the message.
      2. User replied to one of the bot's own messages (Telegram reply feature).
      3. Active conversation: bot responded to this user within the last 10 minutes.
      4. Message is discussing this bot's features/commands/functionality (AI check).

    When triggered, _smart_reply checks internal data first before consulting AI.
    Everything else — book discussions, reading discussions, member-to-member chat — is ignored.

    Owner DM is handled exclusively by owner_dm_chat_handler (group=0) which runs
    before this handler and marks the message processed — so the dedup check below
    will short-circuit for any DM message that was already handled.
    """
    if update.message is None or not update.message.text:
        return
    if gemini_client is None:
        return
    # Owner DM is handled by owner_dm_chat_handler in group=0.
    # Bail here so we never double-respond in the owner's private chat.
    if _is_owner_dm(update):
        return
    # Guard against double-dispatch of the same update (e.g. bot restart mid-call).
    # Only CHECK here — _mark_processed is called after the reply is confirmed sent.
    _bh_chat_id = update.effective_chat.id if update.effective_chat else 0
    if _check_duplicate(_bh_chat_id, update.message.message_id):
        logger.warning(
            "book_auto_reply_handler: duplicate update suppressed (chat=%s msg=%s)",
            _bh_chat_id, update.message.message_id,
        )
        return

    user_text = update.message.text

    # Stage 2 — Single Companion Identity: if the message opens with a direct
    # وقت / يا وقت address intended for the Adapter bot, stay silent.
    # These patterns are the Adapter's registered invocation triggers; this
    # bot must not compete with them (Transition Plan §2A).
    if STAGE2_COMPANION_SILENCED and _from_configured_chat(update):
        _WAQT_ADDR_RE = re.compile(r"^\s*(وقت\s*[،,]|يا\s+وقت)", re.IGNORECASE)
        if _WAQT_ADDR_RE.search(user_text):
            logger.info("book_auto_reply_handler: وقت/يا وقت address silenced (Stage 2 §2A)")
            return

    # Skip suggestion template copies — handled by suggestion_message_handler
    if suggestion_store.is_suggestion_message(user_text):
        return

    username = (
        (update.effective_user.username or update.effective_user.first_name)
        if update.effective_user
        else "user"
    )

    # ── Priority 0: Bot-nomination intent (owner, configured group, open nominations) ──
    # Intercept BEFORE conversation follow-up so an active AI session doesn't swallow it.
    if (
        _from_configured_chat(update)
        and update.effective_user is not None
        and auth_store.is_owner(update.effective_user.id)
        and suggestion_store.is_open()
        and bool(_BOT_NOMINATE_RE.search(user_text))
    ):
        logger.info(
            "book_auto_reply_handler: bot-nomination intent from owner %s — routing",
            username,
        )
        await _handle_bot_nomination(update, context, user_text, username)
        _mark_processed(_bh_chat_id, update.message.message_id)
        return

    bot_username = (context.bot.username or "").lstrip("@")

    # ── Trigger 1: explicit @mention ────────────────────────────────────────
    if _is_bot_mentioned(update.message, context.bot.id, bot_username):
        logger.info("Bot mentioned by %s — replying", username)
        await _smart_reply(update, context, user_text, username, trigger="mention")
        _mark_processed(_bh_chat_id, update.message.message_id)
        return

    # ── Trigger 2 & 3: Telegram reply to bot message / active conversation ──
    if _is_conversation_followup(update, context.bot.id):
        logger.info("Conversation follow-up from %s — replying", username)
        await _smart_reply(update, context, user_text, username, trigger="conversation")
        _mark_processed(_bh_chat_id, update.message.message_id)
        return

    # ── Trigger 4: discussion is about this bot (AI check, keyword-gated) ──
    if await _is_about_this_bot(user_text):
        logger.info("Bot-topic message from %s — replying", username)
        await _smart_reply(update, context, user_text, username, trigger="bot-topic")
        _mark_processed(_bh_chat_id, update.message.message_id)
        return

    # ── Default: silence ─────────────────────────────────────────────────────


async def _fetch_chapter_idea(book_title: str, chapter_title: str) -> str:
    """
    Return a short 2-3 sentence Arabic idea for the given chapter.
    Results are cached in _idea_cache by 'book_title:chapter_title'.
    Returns "" silently on any failure — caller skips the section.
    """
    if not gemini_client or not chapter_title.strip():
        return ""
    cache_key = f"{book_title}:{chapter_title}"
    cached = _idea_cache.get(cache_key)
    if cached:  # empty-string entries are treated as cache-miss so a poisoned
        return cached  # entry never silently serves "" to readers

    in_flight = _idea_in_flight.get(cache_key)
    if in_flight is not None:
        # Shielding lets one cancelled caller stop waiting without cancelling
        # the shared result that other callers are waiting to receive.
        return await asyncio.shield(in_flight)

    # The generation belongs to the shared request, not to whichever reader
    # reached this cache miss first.  Run it in its own task so cancelling that
    # reader only stops its wait; asyncio.shield below preserves the work for
    # other callers and lets the normal generation path populate the cache.
    in_flight = asyncio.create_task(
        _generate_chapter_idea(book_title, chapter_title, cache_key)
    )
    _idea_in_flight[cache_key] = in_flight

    def clear_in_flight(_completed: asyncio.Future[str]) -> None:
        if _idea_in_flight.get(cache_key) is in_flight:
            _idea_in_flight.pop(cache_key, None)

    in_flight.add_done_callback(clear_in_flight)
    return await asyncio.shield(in_flight)


async def _generate_chapter_idea(
    book_title: str, chapter_title: str, cache_key: str
) -> str:
    """Generate, validate, and cache one chapter idea for shared callers."""
    try:
        prompt = (
            f"الكتاب: {book_title}\n"
            f"الفصل: {chapter_title}\n\n"
            "اكتب جملة أو جملتين قصيرتين بالعربية تعكسان الجو العام أو الفكرة المحورية أو السؤال الذي يطرحه هذا الفصل.\n"
            "القواعد الصارمة:\n"
            "- لا تكشف عن أي أحداث أو تطورات أو نتائج أو مفاجآت.\n"
            "- لا تُلمّح إلى مصير أي شخصية.\n"
            "- الهدف أن تكون الجملة دافعاً للقراءة، لا ملخصاً للمحتوى.\n"
            "- لا تضف عناوين أو تنسيق. النص مباشرة."
        )
        idea = await _ai_generate(
            contents=[types.Content(role="user", parts=[types.Part(text=prompt)])],
            label="chapter_idea",
        )
        idea = idea.strip()

        # Discard AI refusal/limitation messages — they must never reach readers.
        # These appear when the model lacks knowledge of the specific chapter.
        _REFUSAL_MARKERS = (
            "لا أستطيع", "لا يمكنني", "لا أملك", "لا أعرف",
            "لا أتوفر", "يرجى تزويدي", "بدون الوصول", "لا يتوفر لديّ",
            "لا يتوفر لدي", "أحتاج إلى", "أحتاج الى",
        )
        if any(marker in idea for marker in _REFUSAL_MARKERS):
            logger.warning(
                "_fetch_chapter_idea: refusal response discarded for '%s / %s'",
                book_title, chapter_title,
            )
            return ""

        _idea_cache[cache_key] = idea
        logger.debug("_fetch_chapter_idea cached '%s'", cache_key)
        return idea
    except Exception as e:
        logger.warning("_fetch_chapter_idea failed for '%s / %s': %s", book_title, chapter_title, e)
        return ""


async def _get_session_context() -> str:
    """
    Return a compact Arabic summary of the current session's literary discussion.

    - Returns "" when the buffer is empty or below the minimum threshold.
    - Returns the cached summary when the buffer hasn't changed since last distillation.
    - Calls the AI to distil when new messages have accumulated since the last call.
    - Failures are soft: logs a warning and returns "" rather than raising.
    """
    if session_store.is_empty():
        return ""
    if not session_store.needs_distillation():
        cached = session_store.get_summary()
        return f"[سياق النقاش الأخير في المجموعة]\n{cached}\n\n" if cached else ""

    buffer = session_store.get_buffer()
    buffer_hash = session_store.current_buffer_hash()
    messages_text = "\n---\n".join(buffer)

    prompt = (
        "المقتطفات التالية من نقاش جماعة قراءة وثقافة. "
        "لخّصها في فقرة واحدة موجزة باللغة العربية (3-4 جمل كحد أقصى) تُجيب على:\n"
        "- ما المواضيع والأفكار الأدبية والثقافية والفكرية التي تُناقَش؟\n"
        "- ما الأسئلة الفلسفية أو التاريخية أو النقدية المطروحة التي لم تُجَب بعد؟\n"
        "- هل هناك آراء أو تفسيرات أو مقارنات متضاربة بين مدارس أو حقب أو مؤلفين؟\n"
        "- ما الكتب أو المؤلفون أو المفاهيم أو الحضارات أو الحقب التاريخية المذكورة؟\n\n"
        "لا تُسمّ أحداً من أعضاء المجموعة ولا تنسب الآراء لأشخاص بعينهم. "
        "ركّز على المحتوى الفكري والأدبي والثقافي فقط — "
        "الأفكار والتساؤلات والتفسيرات والمقارنات، لا على هوية من طرحها.\n\n"
        f"المقتطفات:\n{messages_text}"
    )

    try:
        summary = await _ai_generate(
            contents=[types.Content(role="user", parts=[types.Part(text=prompt)])],
            label="session_distill",
        )
        summary = summary.strip()
        session_store.set_summary(summary, buffer_hash)
        discussion_store.append_summary(summary, len(buffer))
        cultural_store.append_summary(summary, len(buffer))
        logger.info(
            "session_listener: distilled %d messages → %d chars "
            "(cycle_log=%d, cultural_log=%d)",
            len(buffer), len(summary),
            discussion_store.entry_count(), cultural_store.entry_count(),
        )
        return f"[سياق النقاش الأخير في المجموعة]\n{summary}\n\n"
    except Exception as e:
        logger.warning("session_listener: distillation failed: %s", e)
        return ""


def _get_reading_context_hint() -> str:
    """
    Return a reading-context string for the AI prompt when a cycle is active.

    Includes:
    - The book currently being read.
    - The group's approximate page position (derived from schedule entries
      whose dates are on or before today).
    - The current chapter name when available.
    - A conditional instruction to the AI not to discuss content beyond the
      group's current position when the question is about the book's content.

    Returns an empty string when no cycle is running or no schedule is loaded.
    """
    if not cycle_store.is_active():
        return ""
    book = cycle_store.get_current_book()
    if not book:
        return ""

    title = book["title"]
    max_page = 0
    chapter_name = ""

    try:
        store = schedule_store.load()
        max_page, last_chapter = schedule_store.get_page_progress(store)
        # Prefer today's/current marked entry for the chapter name; fall back to
        # the last completed entry returned by get_page_progress.
        current_entry = schedule_store.get_marked_current_entry(store)
        chapter_name = (
            (current_entry.get("chapter") or last_chapter)
            if current_entry
            else last_chapter
        )
    except Exception:  # log-exempt: schedule read for context export; defaults are used on failure
        pass

    parts: list[str] = [f"نقرأ حالياً كتاب «{title}»"]
    if max_page > 0:
        parts.append(f"وصلت المجموعة حتى الصفحة {max_page} تقريباً")
    if chapter_name:
        parts.append(f"الفصل الحالي: «{chapter_name}»")

    body = " — ".join(parts)

    if max_page > 0:
        logger.info(
            "_get_reading_context_hint: progress scope — book=%s page=%d chapter=%s",
            title, max_page, chapter_name,
        )
        return (
            f"[سياق القراءة الحالي للمجموعة: {body}.\n"
            f"قاعدة حماية الحبكة — مطلقة وغير قابلة للكسر: المجموعة وصلت حتى الصفحة {max_page} فقط. "
            f"يُحظر تماماً الكشف عن أي معلومة تخص «{title}» تنتمي إلى ما بعد الصفحة {max_page} — "
            f"سواء كانت حدثاً سردياً، أو دافع شخصية، أو خلفيتها، أو هويتها، أو مصيرها، أو علاقاتها. "
            f"أسئلة 'لماذا' و'كيف' و'من هو/هي' عن شخصيات الكتاب عالية الخطورة لأنها تستدعي "
            f"دوافع وخلفيات قد لم تُكشف بعد. "
            f"إذا كانت الإجابة الكاملة تتطلب معلومات من بعد الصفحة {max_page}: "
            f"أجب بـ'سيتضح هذا في الفصول القادمة' دون أي إشارة إلى المحتوى المحجوب.]\n"
        )
    return f"[سياق القراءة الحالي للمجموعة: {body}]\n"


def _get_nomination_context() -> str:
    """
    Return a nomination-phase context block for /ask recommendation queries.

    Injected only when:
      • suggestion_store reports nominations are currently open, AND
      • answer_command() detected a recommendation-intent query via _NOMINATION_QUERY_RE.

    Provides: active category, full roadmap sequence, and the complete current
    nominations list so the AI recommends one new non-duplicate book that fits
    the active category and is suitable for group reading.

    Returns "" when nominations are closed or the roadmap is not active.
    """
    if not suggestion_store.is_open():
        return ""

    category    = roadmap_store.get_active_category() or ""
    rm_data     = roadmap_store.load()
    roadmap     = rm_data.get("roadmap", [])
    stage       = rm_data.get("current_stage", 0)
    suggestions = suggestion_store.get_suggestions()

    lines: list[str] = ["[سياق مرحلة الترشيحات]"]
    lines.append("نادي القراءة الآن في مرحلة ترشيح الكتب.")

    if category:
        lines.append(f"التصنيف المطلوب لهذه المرحلة: {category}")

    if roadmap:
        order = " ← ".join(roadmap)
        lines.append(f"ترتيب خارطة القراءة: {order}")
        lines.append(f"المرحلة الحالية: {stage + 1} من {len(roadmap)}")

    lines.append("")

    if suggestions:
        lines.append(
            f"الكتب المرشحة حتى الآن ({len(suggestions)} ترشيح — لا تقترح أياً منها):"
        )
        for s in suggestions:
            lines.append(f"  {s['number']}. {s['title']}")
        lines.append("")
        lines.append(
            "المطلوب: اقترح كتاباً حقيقياً واحداً جديداً للقراءة الجماعية"
            + (f" يندرج تحت تصنيف «{category}»" if category else "")
            + " ولم يُرشَّح بعد."
        )
    else:
        lines.append("لا توجد ترشيحات بعد.")
        if category:
            lines.append(
                f"المطلوب: اقترح كتاباً حقيقياً واحداً للقراءة الجماعية"
                f" يندرج تحت تصنيف «{category}»."
            )

    return "\n".join(lines) + "\n\n"


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  Book preparation context
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

def _prep_value_to_str(val: object) -> str:
    """Normalise a prep field that may be a plain string, a list of strings,
    or a list of dicts with 'name'/'description' keys into a single readable
    Arabic string.  Handles whichever shape Gemini happens to return."""
    if isinstance(val, str):
        return val
    if isinstance(val, list):
        parts: list[str] = []
        for item in val:
            if isinstance(item, dict):
                name = item.get("name", "").strip()
                desc = item.get("description", "").strip()
                if name and desc:
                    parts.append(f"{name}: {desc}")
                elif name:
                    parts.append(name)
            elif isinstance(item, str):
                parts.append(item.strip())
        return " — ".join(p for p in parts if p)
    return str(val)


def _get_book_prep_context() -> str:
    """
    Return a compact Arabic reference block for the current book.

    Reads from book_prep_store (populated by _generate_book_prep).
    Returns "" when no cycle is active or no prep sheet has been generated yet.
    The block is injected into /اجب and conversation-follow-up prompts between
    the reading-progress hint and the user's question.
    """
    if not cycle_store.is_active():
        return ""
    book = cycle_store.get_current_book()
    if not book:
        return ""
    prep = book_prep_store.get_prep(book["title"])
    if not prep:
        return ""
    lines: list[str] = []
    if prep.get("characters"):
        lines.append(f"الشخصيات: {_prep_value_to_str(prep['characters'])}")
    if prep.get("themes"):
        lines.append(f"المواضيع: {_prep_value_to_str(prep['themes'])}")
    if prep.get("hard_references"):
        lines.append(f"مراجع ثقافية متوقعة: {_prep_value_to_str(prep['hard_references'])}")
    if prep.get("author_context"):
        lines.append(f"المؤلف: {_prep_value_to_str(prep['author_context'])}")
    if not lines:
        return ""
    return "[ورقة مرجعية للكتاب الحالي]\n" + "\n".join(lines) + "\n\n"


def _get_spoiler_guard(user_id: int) -> str:
    """Return a spoiler-safety instruction for the AI based on the reader's progress.

    If the reader registered a page via /قرأت, asks the AI not to reveal
    events beyond that page.  Returns "" when no progress is registered
    (no restriction — the bot answers freely).
    """
    if not cycle_store.is_active():
        return ""
    book = cycle_store.get_current_book()
    if not book:
        return ""
    page = reader_progress_store.get_progress(book["title"], user_id)
    if page is None:
        return ""
    return (
        f"[حماية من الحرق: هذا القارئ وصل حتى الصفحة {page} فقط. "
        f"لا تكشفي أحداثاً أو تطورات تقع بعد الصفحة {page} "
        f"إلا إذا طلب صراحةً معرفة ما بعدها.]\n\n"
    )


def _classify_question_category(question: str) -> str:
    """Best-effort categorisation of a question for the interaction log.

    This is approximate — the owner can correct the category during review.
    Returns one of the interaction_log_store.VALID_CATEGORIES values.
    """
    q = question
    if any(w in q for w in ["تاريخ", "تاريخي", "تاريخية", "عصر", "حقبة", "حرب", "سياس", "روسي", "قيصر", "مجتمع"]):
        return "historical_reference"
    if any(w in q for w in ["شخصي", "شخص", "بطل", "ماكار", "فارفارا", "ديفوشكين", "شخصيات", "علاقة بين"]):
        return "character_note"
    if any(w in q for w in ["رمز", "رمزي", "موضوع", "أسلوب", "بنية", "سرد", "معنى", "دلالة", "تحليل", "نقد", "فكرة", "تيمة"]):
        return "literary_analysis"
    if any(w in q for w in ["ترجم", "ترجمة", "كلمة", "مصطلح", "عبار", "لفظ", "النص الأصلي"]):
        return "translation_note"
    if any(w in q for w in ["صفحة", "فقرة", "مقطع", "فصل", "chapter", "page", "المقطع"]):
        return "passage_note"
    return "general"


def _get_knowledge_context(question: str, book_title: str) -> str:
    """Retrieve relevant knowledge entries for prompt injection.

    Always includes high-trust entries (owner_note, faq, misconception).
    Scores other entries by word overlap with the question and takes the top matches.
    Returns a bracketed Arabic block, or "" if no entries exist.
    """
    MAX_CHARS = 1500
    HIGH_TRUST = knowledge_store.HIGH_TRUST_TYPES

    entries = knowledge_store.get_entries(book=book_title)
    if not entries:
        return ""

    high_trust = [e for e in entries if e.get("primary_type") in HIGH_TRUST]
    other = [e for e in entries if e.get("primary_type") not in HIGH_TRUST]

    q_words = set(question.replace("؟", "").replace("?", "").split())

    def _score(entry: dict) -> int:
        text = f"{entry.get('title', '')} {entry.get('content', '')}"
        return len(q_words & set(text.split()))

    other_sorted = sorted(other, key=_score, reverse=True)
    selected = high_trust + other_sorted[:5]

    if not selected:
        return ""

    header = "[معرفة النادي]\n"
    lines: list[str] = [header]
    chars = len(header)
    for e in selected:
        tag = e.get("primary_type", "")
        title = e.get("title", "")
        content = e.get("content", "")
        scope_label = " (النادي)" if e.get("scope") == "club" else ""
        line = f"• [{tag}{scope_label}] {title}\n  {content}\n"
        if chars + len(line) > MAX_CHARS:
            break
        lines.append(line)
        chars += len(line)

    return "".join(lines) + "\n" if len(lines) > 1 else ""


async def _generate_book_prep(title: str, meta: dict | None) -> bool:
    """
    Generate and store a reference prep sheet for the given book using Gemini.

    Designed to be called as a fire-and-forget asyncio.create_task() — failures
    are logged as warnings and return False without raising.

    The prep sheet includes: main characters, central themes, expected
    cultural/historical references, and a brief author context note.
    All output is in Arabic.

    Error contract
    --------------
    The entire body is wrapped in a single broad ``except Exception`` so that
    pre-AI code (book_prep_store.has_prep, prompt construction) can never
    silently drop errors before the _ai_generate() call.  The only exception
    to the "return False" rule is RuntimeError("gemini_auth_error"), which is
    re-raised so that owner-facing callers (prepbook_command) can surface the
    key-expired message to the owner.
    """
    try:
        if book_prep_store.has_prep(title):
            logger.debug("book_prep: prep already exists for '%s' — skipping", title)
            return True

        meta = meta or {}
        meta_lines: list[str] = []
        if meta.get("author"):
            meta_lines.append(f"المؤلف: {meta['author']}")
        if meta.get("original_title") and meta["original_title"] != title:
            meta_lines.append(f"العنوان الأصلي: {meta['original_title']}")
        if meta.get("pages"):
            meta_lines.append(f"الصفحات: {meta['pages']}")
        if meta.get("description"):
            meta_lines.append(f"الوصف: {meta['description']}")
        meta_text = ("\n" + "\n".join(meta_lines)) if meta_lines else ""

        prompt = (
            f"اكتب ورقة مرجعية موجزة للكتاب «{title}»{meta_text}\n\n"
            "الغرض: تزويد قارئة أدبية بمعلومات تُساعدها على الإجابة بدقة عن أسئلة أعضاء "
            "نادي قراءة أثناء قراءة الكتاب — لا لمن يقرأ الكتاب لأول مرة.\n\n"
            "تضمّن بالعربية (موجز وعملي):\n"
            "1. characters — أهم الشخصيات: اسم وصفة مميزة في جملة قصيرة لكل شخصية (5-8 شخصيات)\n"
            "2. themes — المواضيع والأفكار المركزية (3-5 مواضيع)\n"
            "3. hard_references — أسماء أعلام أو أماكن أو مصطلحات أو أعمال أدبية أو مفاهيم "
            "ثقافية/تاريخية/فلسفية يُرجَّح ذكرها في النص مما قد يحتاج القارئ لشرح (5-8 عناصر)\n"
            "4. author_context — جملة أو جملتان عن المؤلف تُفيد في فهم الكتاب وخلفيته\n\n"
            "أجب بـ JSON فقط لا غير — بدون أي نص قبله أو بعده:\n"
            '{"characters": "...", "themes": "...", "hard_references": "...", "author_context": "..."}'
        )

        raw = await _ai_generate(
            contents=[types.Content(role="user", parts=[types.Part(text=prompt)])],
            label=f"book_prep:{title[:40]}",
        )
        text = raw.strip()
        # Strip Markdown fences if the model wraps the JSON
        if text.startswith("```"):
            lines_raw = text.split("\n")
            text = "\n".join(lines_raw[1:]).rstrip("`").strip()
        prep = json.loads(text)
        if not isinstance(prep, dict):
            raise ValueError("prep is not a dict")
        book_prep_store.save_prep(title, prep)
        logger.info(
            "book_prep: generated prep sheet for '%s' (%d chars)", title, len(text)
        )
        return True
    except Exception as e:
        if str(e) == "gemini_auth_error":
            raise  # let owner-facing callers surface the key-expired message
        logger.warning("book_prep: failed to generate prep for '%s': %s", title, e)
        return False


async def _generate_book_prep_task(title: str, meta: dict | None) -> None:
    """Safe fire-and-forget wrapper around _generate_book_prep for asyncio.create_task().

    asyncio.create_task() propagates any unhandled exception to the event
    loop's default exception handler, which logs at ERROR level and silently
    drops the task — the prep sheet is never generated and no diagnostic is
    emitted at the right severity.

    _generate_book_prep re-raises RuntimeError("gemini_auth_error") so that
    owner-facing callers (prepbook_command) can surface a user-visible message.
    In the fire-and-forget context there is no owner-facing caller, so that
    re-raise would escape to the loop handler undetected.

    This wrapper catches ALL exceptions — including the re-raised auth error —
    and logs them at WARNING so they are visible in default production log
    filters and never reach the event loop's unhandled-exception handler.
    """
    try:
        await _generate_book_prep(title, meta)
    except Exception as e:
        logger.warning(
            "book_prep: fire-and-forget task failed for '%s': %s", title, e
        )


async def prepbook_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/prepbook — force-regenerate the reference prep sheet for the current book. Owner DM only."""
    if not _is_owner_dm(update):
        return
    if update.message is None:
        return

    if not cycle_store.is_active():
        await update.message.reply_text("لا توجد دورة قراءة نشطة حالياً.")
        return

    book = cycle_store.get_current_book()
    if not book:
        await update.message.reply_text("لم أجد عنوان الكتاب الحالي.")
        return

    title = book["title"]

    await update.message.reply_text(f"⚙️ أُعدّ الورقة المرجعية للكتاب «{title}»…")

    try:
        _, meta = _get_current_book_meta()
        # Clear any existing prep to force fresh generation
        book_prep_store.clear_prep(title)
        ok = await _generate_book_prep(title, meta)
    except Exception as e:
        logger.warning("book_prep generation failed: %s", e)
        if str(e) == "gemini_auth_error":
            await update.message.reply_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
        else:
            await update.message.reply_text("❌ فشل إنشاء الورقة المرجعية. تحقق من السجلات.")
        return
    if not ok:
        await update.message.reply_text(
            "❌ فشل إنشاء الورقة المرجعية. تحقق من السجلات."
        )
        return

    prep = book_prep_store.get_prep(title)
    if not prep:
        await update.message.reply_text("❌ الورقة لم تُحفظ. تحقق من السجلات.")
        return

    try:
        sections: list[str] = [f"✅ <b>الورقة المرجعية — «{title}»</b>\n"]
        if prep.get("characters"):
            sections.append(f"<b>الشخصيات:</b>\n{prep['characters']}")
        if prep.get("themes"):
            sections.append(f"\n<b>المواضيع:</b>\n{prep['themes']}")
        if prep.get("hard_references"):
            sections.append(f"\n<b>المراجع الثقافية المتوقعة:</b>\n{prep['hard_references']}")
        if prep.get("author_context"):
            sections.append(f"\n<b>المؤلف:</b>\n{prep['author_context']}")

        card = "\n".join(sections)
    except Exception as e:
        logger.warning("book_prep card assembly failed for '%s': %s", title, e)
        await update.message.reply_text(
            "❌ تعذّر تجهيز الورقة المرجعية للعرض. تحقق من السجلات."
        )
        return

    try:
        await update.message.reply_text(card, parse_mode="HTML")
    except Exception:  # log-exempt: HTML parse failure; plain-text fallback is sent instead
        await update.message.reply_text(
            card.replace("<b>", "").replace("</b>", "")
        )


async def progress_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/قرأت <page> — register how far you've read in the current book.

    Saves the reader's page so the AI won't spoil events beyond that point.

    Usage:
        /قرأت 80          → registered at page 80
        /قرأت صفحة 80     → same
        /progress 80       → ASCII alias
    """
    if update.message is None:
        return

    if not cycle_store.is_active():
        await update.message.reply_text("لا توجد دورة قراءة نشطة حالياً.")
        return

    book = cycle_store.get_current_book()
    if not book:
        await update.message.reply_text("لم أجد عنوان الكتاب الحالي.")
        return

    raw = update.message.text or ""
    nums = re.findall(r"\d+", raw)
    if not nums:
        await update.message.reply_text(
            "أرسلي رقم الصفحة مع الأمر، مثلاً:\n/قرأت 80"
        )
        return

    page = int(nums[0])
    user = update.effective_user
    user_id = user.id if user else 0
    name = (user.first_name or str(user_id)) if user else str(user_id)
    title = book["title"]

    # Stage 4 (Migration Roadmap): write to both stores so the contract
    # aggregate and the legacy per-book tracking stay consistent during
    # the transition period. reader_progress_store is for spoiler-aware /اجب;
    # progress_store is for the contract's progressSummary aggregate.
    reader_progress_store.set_progress(title, user_id, name, page)
    progress_store.record_page(user_id, name, page)
    logger.info(
        "/قرأت: user=%d name=%s page=%d book=%s", user_id, name, page, title
    )

    await update.message.reply_text(
        f"✅ تم الحفظ — {name} وصل/ت للصفحة <b>{page}</b> من «{title}»\n"
        f"<i>سأتجنب الحرق عند الإجابة على أسئلتك.</i>",
        parse_mode="HTML",
    )


# ══════════════════════════════════════════════════════════════════════════════
# Phase 4a — Knowledge base & performance log commands (owner DM only)
# ══════════════════════════════════════════════════════════════════════════════

_TYPE_DISPLAY: dict[str, str] = {
    "historical_reference": "مرجع تاريخي",
    "literary_analysis":    "تحليل أدبي",
    "character_note":       "ملاحظة شخصية",
    "translation_note":     "ملاحظة ترجمة",
    "passage_note":         "ملاحظة مقطع",
    "faq":                  "سؤال شائع",
    "misconception":        "مفهوم خاطئ",
    "community_insight":    "رأي القراء",
    "club_decision":        "قرار نادي",
    "owner_note":           "ملاحظة المشرف",
}

_CATEGORY_DISPLAY: dict[str, str] = {
    "historical_reference": "مرجع تاريخي",
    "literary_analysis":    "تحليل أدبي",
    "character_note":       "شخصية",
    "translation_note":     "ترجمة",
    "passage_note":         "مقطع",
    "faq":                  "سؤال شائع",
    "general":              "عام",
    "other":                "أخرى",
}


async def addnote_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/addnote <type> | <title> | <content>  — add a knowledge entry for the current book.

    Owner DM only.  Type aliases: hist, lit, char, trans, pass, misc, insight, decision, note.

    Example:
        /addnote faq | لماذا اختار دوستويفسكي الرسائل؟ | لأن الرسائل تتيح...
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    if not cycle_store.is_active():
        await update.message.reply_text("لا توجد دورة قراءة نشطة. استخدم /addclub لإضافة معرفة عامة للنادي.")
        return

    book = cycle_store.get_current_book()
    if not book:
        await update.message.reply_text("لم أجد عنوان الكتاب الحالي.")
        return

    raw = (update.message.text or "").strip()
    # Strip command prefix — everything after the first space
    body = raw.split(None, 1)[1].strip() if " " in raw else ""
    parts = [p.strip() for p in body.split("|")]

    if len(parts) < 3:
        await update.message.reply_text(
            "الصيغة: /addnote &lt;type&gt; | &lt;title&gt; | &lt;content&gt;\n\n"
            "أنواع مقبولة:\n"
            + "\n".join(f"• <code>{k}</code> — {v}" for k, v in _TYPE_DISPLAY.items()),
            parse_mode="HTML",
        )
        return

    raw_type, title, content = parts[0], parts[1], "|".join(parts[2:])
    resolved = knowledge_store.resolve_type(raw_type)
    if not resolved:
        await update.message.reply_text(
            f"نوع غير معروف: <code>{raw_type}</code>\n"
            "الأنواع المتاحة: " + ", ".join(knowledge_store.VALID_TYPES),
            parse_mode="HTML",
        )
        return

    eid = knowledge_store.add_entry(
        scope="book",
        book=book["title"],
        primary_type=resolved,
        title=title,
        content=content,
    )
    logger.info("/addnote: id=%s type=%s book=%s", eid, resolved, book["title"])
    await update.message.reply_text(
        f"✅ تمت الإضافة\n"
        f"<b>المعرّف:</b> <code>{eid}</code>\n"
        f"<b>النوع:</b> {_TYPE_DISPLAY.get(resolved, resolved)}\n"
        f"<b>العنوان:</b> {title}\n"
        f"<b>الكتاب:</b> {book['title']}",
        parse_mode="HTML",
    )


async def addclub_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/addclub <type> | <title> | <content>  — add club-level knowledge (survives book changes).

    Owner DM only.  Same type aliases as /addnote.

    Example:
        /addclub club_decision | سياسة الترجمات | نفضّل دائماً الترجمات العربية المباشرة...
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    raw = (update.message.text or "").strip()
    body = raw.split(None, 1)[1].strip() if " " in raw else ""
    parts = [p.strip() for p in body.split("|")]

    if len(parts) < 3:
        await update.message.reply_text(
            "الصيغة: /addclub &lt;type&gt; | &lt;title&gt; | &lt;content&gt;",
            parse_mode="HTML",
        )
        return

    raw_type, title, content = parts[0], parts[1], "|".join(parts[2:])
    resolved = knowledge_store.resolve_type(raw_type)
    if not resolved:
        await update.message.reply_text(
            f"نوع غير معروف: <code>{raw_type}</code>",
            parse_mode="HTML",
        )
        return

    eid = knowledge_store.add_entry(
        scope="club",
        book=None,
        primary_type=resolved,
        title=title,
        content=content,
    )
    logger.info("/addclub: id=%s type=%s (club-scoped)", eid, resolved)
    await update.message.reply_text(
        f"✅ تمت الإضافة (معرفة عامة للنادي)\n"
        f"<b>المعرّف:</b> <code>{eid}</code>\n"
        f"<b>النوع:</b> {_TYPE_DISPLAY.get(resolved, resolved)}\n"
        f"<b>العنوان:</b> {title}",
        parse_mode="HTML",
    )


async def listnotes_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/listnotes  — list knowledge entries for the current book + club-level entries.

    Owner DM only.
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    book = cycle_store.get_current_book() if cycle_store.is_active() else None
    book_title = book["title"] if book else None

    if book_title:
        book_entries = knowledge_store.list_entries_for_book(book_title)
    else:
        book_entries = []
    club_entries = knowledge_store.list_club_entries()

    if not book_entries and not club_entries:
        await update.message.reply_text("لا توجد إدخالات في قاعدة المعرفة بعد.")
        return

    lines: list[str] = []
    if book_entries:
        lines.append(f"📚 <b>معرفة الكتاب — «{book_title}»</b>")
        for e in book_entries:
            type_label = _TYPE_DISPLAY.get(e.get("primary_type", ""), e.get("primary_type", ""))
            lines.append(f"  <code>{e['id']}</code>  [{type_label}]  {e['title']}")
        lines.append("")
    if club_entries:
        lines.append("🌐 <b>معرفة النادي (عامة)</b>")
        for e in club_entries:
            type_label = _TYPE_DISPLAY.get(e.get("primary_type", ""), e.get("primary_type", ""))
            lines.append(f"  <code>{e['id']}</code>  [{type_label}]  {e['title']}")

    total = len(book_entries) + len(club_entries)
    lines.append(f"\nإجمالي: {total} إدخال")

    await update.message.reply_text("\n".join(lines), parse_mode="HTML")


async def deletenote_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/deletenote <id>  — delete a knowledge entry by its ID.

    Owner DM only.
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    raw = (update.message.text or "").strip()
    parts = raw.split()
    if len(parts) < 2:
        await update.message.reply_text("الصيغة: /deletenote &lt;id&gt;", parse_mode="HTML")
        return

    entry_id = parts[1].strip()
    entry = knowledge_store.get_entry(entry_id)
    if not entry:
        await update.message.reply_text(f"لم أجد إدخالاً بالمعرّف: <code>{entry_id}</code>", parse_mode="HTML")
        return

    knowledge_store.delete_entry(entry_id)
    logger.info("/deletenote: deleted id=%s title=%s", entry_id, entry.get("title"))
    await update.message.reply_text(
        f"🗑 تم الحذف: <code>{entry_id}</code> — {entry.get('title', '')}",
        parse_mode="HTML",
    )


async def rateanswer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/rateanswer <quality> [category] [error_type]  — rate the most recent /اجب answer.

    Owner DM only.  Adds review metadata to the interaction log for Performance Learning.

    quality    : correct | partial | incorrect
    category   : historical_reference | literary_analysis | character_note |
                 translation_note | passage_note | faq | general | other
    error_type : wrong_fact | wrong_framing | overconfident | missed_dimension |
                 hallucination | none  (required only when quality=incorrect)

    Examples:
        /rate correct
        /rate partial literary_analysis
        /rate incorrect historical_reference wrong_fact
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    raw = (update.message.text or "").strip()
    tokens = raw.split()[1:]  # drop command itself

    if not tokens:
        # No args — show a one-tap inline keyboard so the owner doesn't have to type
        iid = _last_ask_interaction_id
        if not iid:
            await update.message.reply_text(
                "لا يوجد تفاعل حديث لتقييمه. استخدم /اجب أولاً ثم عد لهنا."
            )
            return
        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ صحيح",  callback_data="rateanswer:correct"),
                InlineKeyboardButton("⚠️ جزئي",  callback_data="rateanswer:partial"),
                InlineKeyboardButton("❌ خطأ",   callback_data="rateanswer:incorrect"),
            ]
        ])
        await update.message.reply_text(
            f"كيف تُقيّم آخر إجابة؟  (<code>{iid}</code>)",
            parse_mode="HTML",
            reply_markup=keyboard,
        )
        return

    quality = tokens[0].lower()
    if quality not in interaction_log_store.VALID_QUALITIES:
        await update.message.reply_text(
            f"قيمة غير صحيحة: <code>{quality}</code>\n"
            "القيم المقبولة: correct | partial | incorrect",
            parse_mode="HTML",
        )
        return

    category = tokens[1].lower() if len(tokens) > 1 else None
    error_type = tokens[2].lower() if len(tokens) > 2 else "none"

    if category and category not in interaction_log_store.VALID_CATEGORIES:
        await update.message.reply_text(
            f"فئة غير معروفة: <code>{category}</code>",
            parse_mode="HTML",
        )
        return

    if error_type not in interaction_log_store.VALID_ERROR_TYPES:
        error_type = "none"

    iid = _last_ask_interaction_id
    if not iid:
        await update.message.reply_text("لا يوجد تفاعل حديث لتقييمه. استخدم /اجب أولاً.")
        return

    entry = interaction_log_store.get_interaction(iid)
    if not entry:
        await update.message.reply_text(f"لم أجد التفاعل: <code>{iid}</code>", parse_mode="HTML")
        return

    # Override category if provided
    if category:
        interaction_log_store.update_category(iid, category)

    effective_category = category or entry.get("question_category", "general")
    interaction_log_store.review_interaction(iid, quality, error_type, confidence_assigned="unknown")

    logger.info(
        "/rate: id=%s quality=%s category=%s error=%s",
        iid, quality, effective_category, error_type,
    )

    quality_emoji = {"correct": "✅", "partial": "⚠️", "incorrect": "❌"}.get(quality, "")
    await update.message.reply_text(
        f"{quality_emoji} تم تقييم التفاعل <code>{iid}</code>\n"
        f"الجودة: <b>{quality}</b>  |  الفئة: {effective_category}"
        + (f"  |  نوع الخطأ: {error_type}" if error_type != "none" else ""),
        parse_mode="HTML",
    )


async def rateanswer_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle inline keyboard taps from /rateanswer (rateanswer:correct|partial|incorrect)."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return

    await query.answer()

    quality = query.data.split(":")[1]  # correct | partial | incorrect

    iid = _last_ask_interaction_id
    if not iid:
        await query.edit_message_text("لا يوجد تفاعل حديث لتقييمه. استخدم /اجب أولاً.")
        return

    entry = interaction_log_store.get_interaction(iid)
    if not entry:
        await query.edit_message_text(
            f"لم أجد التفاعل: <code>{iid}</code>", parse_mode="HTML"
        )
        return

    interaction_log_store.review_interaction(iid, quality, "none", confidence_assigned="unknown")

    quality_emoji = {"correct": "✅", "partial": "⚠️", "incorrect": "❌"}.get(quality, "")
    effective_category = entry.get("question_category", "general")
    logger.info("/rateanswer callback: id=%s quality=%s", iid, quality)

    await query.edit_message_text(
        f"{quality_emoji} تم تقييم التفاعل <code>{iid}</code>\n"
        f"الجودة: <b>{quality}</b>  |  الفئة: {effective_category}\n\n"
        f"لإضافة فئة أو نوع خطأ:\n"
        f"/rateanswer {quality} [category] [error_type]",
        parse_mode="HTML",
    )


async def savefaq_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/savefaq <title>  — save the most recent /اجب answer as a FAQ entry in the knowledge base.

    Also marks the interaction as correct in the log.  Owner DM only.

    Example:
        /savefaq لماذا اختار دوستويفسكي شكل الرسائل؟
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    raw = (update.message.text or "").strip()
    title = raw.split(None, 1)[1].strip() if " " in raw else ""
    if not title:
        await update.message.reply_text("الصيغة: /savefaq &lt;عنوان السؤال&gt;", parse_mode="HTML")
        return

    iid = _last_ask_interaction_id
    if not iid:
        await update.message.reply_text("لا يوجد تفاعل حديث لحفظه. استخدم /اجب أولاً.")
        return

    entry = interaction_log_store.get_interaction(iid)
    if not entry:
        await update.message.reply_text(f"لم أجد التفاعل: <code>{iid}</code>", parse_mode="HTML")
        return

    if not cycle_store.is_active():
        await update.message.reply_text("لا توجد دورة نشطة لإضافة السؤال إليها.")
        return

    book = cycle_store.get_current_book()
    if not book:
        await update.message.reply_text("لم أجد عنوان الكتاب الحالي.")
        return

    # Content = the original question (the answer itself lives in AI history, not logged here)
    content = entry.get("question", "")
    eid = knowledge_store.add_entry(
        scope="book",
        book=book["title"],
        primary_type="faq",
        title=title,
        content=content,
    )

    # Mark interaction as correct
    interaction_log_store.review_interaction(iid, "correct", "none", "high")

    logger.info("/savefaq: knowledge id=%s interaction id=%s", eid, iid)
    await update.message.reply_text(
        f"✅ تم الحفظ كسؤال شائع\n"
        f"<b>المعرّف:</b> <code>{eid}</code>\n"
        f"<b>العنوان:</b> {title}\n"
        f"<b>الكتاب:</b> {book['title']}",
        parse_mode="HTML",
    )


async def mystats_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/mystats  — show performance stats from the interaction log (owner DM only)."""
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    book = cycle_store.get_current_book() if cycle_store.is_active() else None
    book_title = book["title"] if book else None

    stats = interaction_log_store.get_stats(book=book_title)

    if not stats:
        await update.message.reply_text(
            "لا توجد مراجعات بعد. استخدم /rate بعد كل /اجب لبناء قاعدة الأداء."
        )
        return

    lines: list[str] = ["📊 <b>سجل أداء البوت</b>"]
    if book_title:
        lines.append(f"الكتاب: {book_title}")
    lines.append("─" * 30)

    total_all = 0
    for cat, data in sorted(stats.items(), key=lambda x: -x[1]["total"]):
        label = _CATEGORY_DISPLAY.get(cat, cat)
        t = data["total"]
        c = data["correct"]
        p = data["partial"]
        i = data["incorrect"]
        total_all += t
        lines.append(f"<b>{label}</b>  ({t} مراجعة)")
        lines.append(f"  ✅ {c}  ⚠️ {p}  ❌ {i}")
        errs = data.get("error_types", {})
        if errs:
            err_str = "  ".join(f"{k}:{v}" for k, v in errs.items())
            lines.append(f"  أنواع الأخطاء: {err_str}")

    lines.append("─" * 30)
    lines.append(f"الإجمالي: {total_all} مراجعة")

    # Signal correlation for used_search if enough data
    search_corr = interaction_log_store.get_signal_correlation("used_search", book=book_title)
    with_search = search_corr[True]
    without_search = search_corr[False]
    if with_search["total"] > 0 and without_search["total"] > 0:
        lines.append("\n🔍 <b>تأثير البحث على الدقة</b>")
        lines.append(f"مع بحث ({with_search['total']}): ✅ {with_search['correct']}  ❌ {with_search['incorrect']}")
        lines.append(f"بدون بحث ({without_search['total']}): ✅ {without_search['correct']}  ❌ {without_search['incorrect']}")

    await update.message.reply_text("\n".join(lines), parse_mode="HTML")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  Phase 4b — DM Training Workspace
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


def _get_training_context() -> str:
    """
    Build the training-session context block injected into every owner DM
    conversation turn.  Positions the AI in reflective/learning mode and
    surfaces the current session name and active book so the bot always knows
    what it is being trained on.
    """
    lines = [
        "━━━ وضع التدريب الخاص ━━━",
        "أنت في جلسة تدريب خاصة مع المشرف (مالك النادي). هذه المحادثة لا يراها أعضاء المجموعة.",
        "في هذا الوضع:",
        "• كن صريحاً تماماً في التعبير عن حدود معرفتك وعدم يقينك.",
        "• إذا صحّح المشرف معلومةً أو أضاف توضيحاً، اعترف بذلك بوضوح.",
        "• استجب باستفاضة وعمق أكبر مما تفعل في المجموعة — لا داعي للاختصار هنا.",
        "• يمكن للمشرف حفظ أي توضيح مهم باستخدام /addnote أو /savefaq.",
    ]

    session_name = _dm_session.get("name")
    if session_name:
        started = _dm_session.get("started_at", 0.0)
        elapsed_min = max(0, int((time.monotonic() - started) / 60))
        lines.append(f"• اسم الجلسة الحالية: «{session_name}» (منذ {elapsed_min} دقيقة)")

    if cycle_store.is_active():
        book = cycle_store.get_current_book()
        if book:
            lines.append(f"• الكتاب الحالي للنادي: «{book['title']}»")

    return "\n".join(lines) + "\n\n"


async def owner_dm_chat_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Free-form conversational handler for the owner DM training workspace.

    Unlike book_auto_reply_handler which gates on active conversation windows,
    this handler ALWAYS responds in owner DM — the owner is always in conversation
    mode there.  Injects the full training context + knowledge base + book prep
    so the owner can probe the same context the bot uses in the group.

    After replying, detects correction/clarification signals in the owner's
    message and proactively suggests saving the correction to the knowledge base.
    """
    if not _is_owner_dm(update):
        return
    if update.message is None or not update.message.text:
        return
    if gemini_client is None:
        await update.message.reply_text("خدمة الذكاء الاصطناعي غير متاحة حالياً.")
        return

    user_text = update.message.text.strip()
    chat_id = update.effective_chat.id if update.effective_chat else 0
    user_id = update.effective_user.id if update.effective_user else 0
    username = (update.effective_user.first_name or "owner") if update.effective_user else "owner"

    if _check_duplicate(chat_id, update.message.message_id):
        logger.warning(
            "owner_dm_chat_handler: duplicate suppressed (msg=%s)",
            update.message.message_id,
        )
        return

    logger.info(
        "owner_dm_chat_handler: training message from %s: %s",
        username, user_text[:80],
    )

    training_ctx = _get_training_context()
    book_prep_ctx = _get_book_prep_context()
    current_book = cycle_store.get_current_book()
    knowledge_ctx = _get_knowledge_context(user_text, current_book["title"]) if current_book else ""
    spoiler_guard = _get_spoiler_guard(user_id)

    # Continuation hint — if last bot turn ended with a question, keep thread alive
    continuation_hint = ""
    _hist = conversation_histories.get(user_id, [])
    if _hist:
        _last_model_text = ""
        for _turn in reversed(_hist):
            if getattr(_turn, "role", "") == "model":
                _last_model_text = "".join(
                    getattr(_p, "text", "") for _p in (getattr(_turn, "parts", None) or [])
                ).rstrip()
                break
        if _last_model_text.endswith("؟") or _last_model_text.endswith("?"):
            continuation_hint = (
                "[CONTINUATION: هذه الرسالة تبدو إجابةً على سؤال التوضيح الذي طرحتَه للتو. "
                "راجع تاريخ المحادثة لتجد السؤال الأصلي، ثم قدّم الإجابة الكاملة في سياقه.]\n\n"
            )

    parts = [p for p in [
        training_ctx, book_prep_ctx, knowledge_ctx, spoiler_guard,
        continuation_hint, user_text,
    ] if p]
    prompt = "".join(parts)

    try:
        ok = await send_ai_reply(
            update, context, prompt,
            skip_history=False,
            history_key=user_id,
            use_search=_question_needs_search(user_text),
        )
        if ok:
            _mark_processed(chat_id, update.message.message_id)
            _conv_last_seen[user_id] = time.monotonic()

        # Proactive save suggestion when correction/clarification signals detected
        if ok and _CORRECTION_RE.search(user_text) and update.message:
            await asyncio.sleep(0.4)
            await update.message.reply_text(
                "💾 يبدو أن هذا تصحيح أو توضيح مهم.\n"
                "هل تريد حفظه في قاعدة المعرفة؟\n\n"
                "<b>لحفظ توضيح جديد:</b>\n"
                "/addnote insight | [العنوان] | [المحتوى]\n\n"
                "<b>لحفظ آخر إجابة على /اجب كـ FAQ:</b>\n"
                "/savefaq [العنوان]",
                parse_mode="HTML",
            )
    except Exception as e:
        logger.error("owner_dm_chat_handler: error for %s: %s", username, e)
        if update.message:
            await update.message.reply_text("عذراً، حدث خطأ. حاول مرة أخرى.")


async def session_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/session [name|end]  — manage a named DM training session.

    /session              → show the current session name and elapsed time
    /session <name>       → start (or switch to) a named session
    /session end          → end the current session

    Owner DM only.  Session names are free text (spaces allowed).
    The name is injected into every AI prompt so the bot knows what is being
    reviewed — useful for keeping a log of which book chapters you drilled.

    Example:
        /session مراجعة فقراء دوستويفسكي — الفصول ١–٥
    """
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return
    if update.message is None:
        return

    global _dm_session
    raw = (update.message.text or "").strip()
    arg = " ".join(raw.split()[1:]).strip()

    if not arg:
        name = _dm_session.get("name")
        if name:
            started = _dm_session.get("started_at", 0.0)
            elapsed = max(0, int((time.monotonic() - started) / 60))
            await update.message.reply_text(
                f"📚 <b>الجلسة الحالية:</b> «{name}»\n"
                f"المدة: ~{elapsed} دقيقة\n\n"
                "لإنهاء الجلسة: /session end\n"
                "للتبديل لجلسة أخرى: /session [اسم جديد]",
                parse_mode="HTML",
            )
        else:
            await update.message.reply_text(
                "لا توجد جلسة تدريب نشطة حالياً.\n\n"
                "ابدأ جلسة جديدة بكتابة:\n"
                "/session [اسم الجلسة]\n\n"
                "مثال:\n"
                "/session مراجعة فقراء دوستويفسكي",
                parse_mode="HTML",
            )
        return

    if arg.lower() == "end":
        old_name = _dm_session.get("name")
        _dm_session = {}
        if old_name:
            await update.message.reply_text(f"✅ انتهت الجلسة «{old_name}».")
        else:
            await update.message.reply_text("لا توجد جلسة نشطة.")
        return

    _dm_session = {"name": arg, "started_at": time.monotonic()}
    book_hint = ""
    if cycle_store.is_active():
        book = cycle_store.get_current_book()
        if book:
            book_hint = f"\nالكتاب الحالي: «{book['title']}»"

    await update.message.reply_text(
        f"📚 <b>بدأت جلسة تدريب جديدة:</b> «{arg}»{book_hint}\n\n"
        "تحدّث مع البوت بحرية — كل شيء هنا في وضع التدريب الخاص.\n"
        "البوت يعلم الآن أنك في جلسة تدريب وسيُجيب بعمق وصراحة أكبر.\n\n"
        "للإنهاء: /session end",
        parse_mode="HTML",
    )


# ── Google Search grounding ───────────────────────────────────────────────────
# Triggered when a /اجب or conversation question looks like a cultural/historical
# reference lookup that benefits from real-time search rather than relying solely
# on the model's training knowledge (e.g. "من هو لهوموند؟", "ما قواعد زابولسكي؟",
# transliterated names with Latin characters).
_SEARCH_TRIGGER_RE = re.compile(
    r'(?:'
    r'(?:^|\s)(?:من|ما|ماذا)\s+(?:هو|هي|هم|هن|هذا|هذه|كان|كانت|تعني|يعني)\b'
    r'|(?:^|\s)ما\s+(?:قواعد|أعمال|كتب|كتاب\w*|روايات?|ديوان|تاريخ)\b'
    r'|[A-Za-z]{3,}'
    r')',
    re.IGNORECASE | re.UNICODE,
)


def _question_needs_search(text: str) -> bool:
    """Return True when the question likely involves a cultural/historical reference
    that benefits from Google Search grounding.

    Criteria:
    - Short question (≤ 10 words) AND matches a who/what-is pattern or
      contains transliterated Latin characters (indicating a named entity).
    """
    stripped = text.strip()
    if len(stripped.split()) > 10:
        return False
    return bool(_SEARCH_TRIGGER_RE.search(stripped))


# Correction/clarification signals for DM training proactive save suggestion
_CORRECTION_RE = re.compile(
    r"في الواقع|الصحيح أن|الصواب أن|هذا خطأ|هذا غير صحيح|هذا ليس صحيحاً"
    r"|ليس كذلك|بل العكس|لا، |لأ، |دعني أوضح|في الحقيق[ةه]|أريد أن أوضح"
    r"|الأدق أن|الأدق أن|التصحيح هو|بل الصواب"
    r"|actually\b|no,\s|incorrect|wrong\b|that'?s not|let me clarify"
    r"|to be precise|more precisely|in fact",
    re.IGNORECASE,
)

# High-risk factual categories for /ask confidence handling (compiled once at module load)
_HIGH_RISK_BOOK_RE = re.compile(
    r"مؤلف|كاتب|مترجم|ناشر|صفحات|شخصيات|شخصية|أبطال|بطل|بطلة"
    r"|حبكة|اقتباس|فصل|كتب\b|ألّف|ترجم|راوي|أحداث|قصة"
)

# Detects recommendation/nomination intent in /اجب queries.
# When nominations are open and this matches, _get_nomination_context() is injected.
_NOMINATION_QUERY_RE = re.compile(
    r"رشّ?ح|اقترح|ترشّ?يح|اقتراح|📚\s*ترشيحات"
    r"|اختر\s*كتاب|كتاب\s*مناسب|أفضل\s*كتاب"
    r"|للقراءة\s*الجماعية|يصلح\s+للترشيح"
    r"|ما\s+(?:الكتاب|كتاب)\s+(?:المناسب|الأفضل|الجيد)"
)

# Tighter regex for the bot-nomination workflow:
# activates only when the owner replies to the official template AND asks the bot
# to submit its own nomination (not just "recommend me something").
# Guards: owner + reply-to-template + nominations-open are checked separately.
# _REVIEW_CATEGORY_DEFS and _build_review_message have been replaced by
# category_constitution.py + the per-book card system in reviewsuggestions_command.


def _conf_label(confidence: str) -> str:
    labels  = {"high": "عالية", "medium": "متوسطة", "low": "منخفضة"}
    emojis  = {"high": "🟢",    "medium": "🟡",      "low": "🔴"}
    return f"{labels.get(confidence, confidence)} {emojis.get(confidence, '')}".strip()


def _parse_gemini_opinion(raw: str) -> dict:
    """Parse the JSON response from build_gemini_opinion_prompt."""
    defaults: dict = {
        "primary_category":      "",
        "primary_confidence":    "medium",
        "primary_reasoning":     "",
        "alternative_category":  None,
        "alternative_confidence": None,
        "alternative_reasoning":  None,
    }
    try:
        m = re.search(r"\{[\s\S]*\}", raw)
        if not m:
            return defaults
        data: dict = json.loads(m.group())
        alt_cat  = data.get("alternative_category")
        alt_conf = data.get("alternative_confidence")
        alt_reas = data.get("alternative_reasoning")
        if alt_cat in (None, "null", ""):
            alt_cat, alt_conf, alt_reas = None, None, None
        if alt_cat and not category_constitution.is_valid_primary_category(alt_cat):
            alt_cat, alt_conf, alt_reas = None, None, None
        if alt_conf not in ("high", "medium", "low"):
            alt_conf = "medium" if alt_cat else None
        p_conf = data.get("primary_confidence", "medium")
        if p_conf not in ("high", "medium", "low"):
            p_conf = "medium"
        return {
            "primary_category":      data.get("primary_category", ""),
            "primary_confidence":    p_conf,
            "primary_reasoning":     data.get("primary_reasoning", ""),
            "alternative_category":  alt_cat,
            "alternative_confidence": alt_conf,
            "alternative_reasoning":  alt_reas,
        }
    except Exception:
        return defaults


def _build_gemini_opinion_text(title: str, opinion: dict) -> str:
    """Build the HTML message shown when the owner presses 🤖 رأي Gemini."""
    lines = [
        f"🤖 <b>رأي Gemini في «{_html.escape(title)}»</b>",
        "",
        f"📂 <b>التصنيف الأساسي:</b> {_html.escape(opinion['primary_category'])}",
        f"📊 الثقة: {_conf_label(opinion['primary_confidence'])}",
        f"💡 «{_html.escape(opinion['primary_reasoning'])}»",
    ]
    if opinion.get("alternative_category"):
        lines += [
            "",
            f"🔀 <b>تصنيف بديل:</b> {_html.escape(opinion['alternative_category'])}",
            f"📊 الثقة: {_conf_label(opinion.get('alternative_confidence') or 'medium')}",
            f"💡 «{_html.escape(opinion.get('alternative_reasoning') or '')}»",
        ]
    else:
        lines.append("")
        lines.append("<i>لا يوجد تصنيف بديل معقول وفق الدستور.</i>")
    lines += ["", "——", "<i>هذا رأي إضافي من Gemini — القرار النهائي للمالك.</i>"]
    return "\n".join(lines)


def _build_review_card_text(
    book_num: int,
    title: str,
    nominator: str,
    nominated_at: str,
    primary_category: str,
    confidence: str,
    ai_action: str,
    reasoning: str,
    destination_note: str,
    alternative_category: str | None = None,
    alternative_confidence: str | None = None,
    alternative_reasoning: str | None = None,
    classifier: str = "gemini",
) -> str:
    """Build the HTML text for a single per-book review card (pre-decision)."""
    date_str = ""
    if nominated_at:
        try:
            date_str = " · " + datetime.fromisoformat(nominated_at).strftime("%-d %B")
        except Exception:  # log-exempt: display date formatting; date_str stays "" on failure
            pass

    classifier_badge = "📐 دستور" if classifier == "rule" else "🤖 Gemini"

    lines: list[str] = [
        f"📖 كتاب #{book_num} — <b>{_html.escape(title)}</b>",
        f"👤 رشّحه: {_html.escape(nominator or '—')}{date_str}",
        "",
        "━━━━━━━━━━━━━━━━",
    ]

    if alternative_category:
        # Dual-category card — primary + genuine alternative
        lines += [
            f"🏷️ <b>التصنيف الأساسي</b> ({classifier_badge})",
            f"  <b>{_html.escape(primary_category)}</b> — {_conf_label(confidence)}",
            f"  <i>{_html.escape(reasoning)}</i>",
            "",
            "🔀 <b>تصنيف بديل</b>",
            f"  <b>{_html.escape(alternative_category)}</b> — {_conf_label(alternative_confidence or 'medium')}",
            f"  <i>{_html.escape(alternative_reasoning or '')}</i>",
            "",
        ]
    else:
        lines += [
            f"🏷️ التصنيف ({classifier_badge}): <b>{_html.escape(primary_category)}</b>",
            f"📊 الثقة: {_conf_label(confidence)}",
            f"💡 «{_html.escape(reasoning)}»",
            "",
        ]

    if ai_action == "approve":
        lines.append("🤖 اقتراح: ✅ مناسب للمرحلة النشطة")
    else:
        lines.append("🤖 اقتراح: 📦 تأجيل")
        if destination_note:
            lines += ["", "💬 السبب:", _html.escape(destination_note)]

    lines.append("━━━━━━━━━━━━━━━━")
    return "\n".join(lines)


def _build_decided_card_text(
    book_num: int,
    title: str,
    decision: str,
    primary_category: str,
) -> str:
    """Build the collapsed single-line card shown after the owner decides."""
    esc = _html.escape(title)
    cat = _html.escape(primary_category)
    if decision == "approved":
        return (
            f"✅ #{book_num} — <b>{esc}</b>\n"
            f"<i>قُبل — التصنيف: {cat}</i>"
        )
    if decision == "postponed":
        return (
            f"📦 #{book_num} — <s>{esc}</s>\n"
            f"<i>مؤجَّل → {cat}</i>"
        )
    return (
        f"🗑️ #{book_num} — <s>{esc}</s>\n"
        f"<i>أُزيل من الترشيحات</i>"
    )


_BOT_NOMINATE_RE = re.compile(
    r"رشّ?ح"                              # رشح / رشّح
    r"|أضف\s*ترشيح"                       # أضف ترشيحك / أضف ترشيح
    r"|وش\s*ترشح"                         # وش ترشح
    r"|ما\s*ترشيح"                        # ما ترشيحك
    r"|ترشيح\s*البوت"                     # ترشيح البوت
    r"|شارك\s*(?:معنا|في\s*الترشيح)?"    # شارك / شارك معنا
    r"|اشترك\s*(?:في\s*الترشيح)?"        # اشترك / اشترك في الترشيح
    r"|حطّ?\s*ترشيح"                      # حط ترشيحك
    r"|ضيف\s*ترشيح"                       # ضيف ترشيحك
    r"|(?:what|which).*?(?:nominat|would\s+you\s+pick)"  # English variants
)


async def _handle_bot_nomination(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    question: str,
    username: str,
) -> None:
    """
    Bot-nomination workflow — activated when:
      • Nominations are open
      • The message is from the registered owner
      • The message is a reply to the official nomination template
      • The intent is clearly asking the bot to submit its own nomination

    Flow:
      1. Build a structured nomination prompt with full club context and
         diversity guidance (prefer under-represented sub-genres).
      2. Call Gemini via _ai_generate() for a TITLE: / REASON: response.
      3. Parse the recommended title.
      4. Merge it into the suggestion store as a bot-source nomination
         (source="bot", user_id=0, submitted_by="🤖 البوت").
      5. Edit the official template message to include the new entry.
      6. Reply with the completed nomination message (member-style format)
         plus a brief note explaining the bot's choice.
    """
    category    = roadmap_store.get_active_category() or ""
    rm_data     = roadmap_store.load()
    roadmap     = rm_data.get("roadmap", [])
    stage       = rm_data.get("current_stage", 0)
    suggestions = suggestion_store.get_suggestions()

    # ── Build a structured nomination prompt ──────────────────────────────────
    prompt_lines = [
        "[مهمة: اختر كتاباً واحداً للترشيح في نادي القراءة]",
        "",
    ]
    if category:
        prompt_lines.append(f"التصنيف المطلوب: {category}")
    if roadmap:
        prompt_lines.append(f"خارطة القراءة للدورة الحالية: {' ← '.join(roadmap)}")
        prompt_lines.append(f"المرحلة الحالية: {stage + 1} من {len(roadmap)}")
    prompt_lines.append("")

    if suggestions:
        prompt_lines.append(
            f"الكتب المرشحة حتى الآن ({len(suggestions)} كتاباً — "
            "استبعدها كلياً، ولا تقترح أي كتاب يشبهها أو يكرر اتجاهها إن كان التركيز واضحاً):"
        )
        for s in suggestions:
            prompt_lines.append(f"  {s['number']}. {s['title']}")
    else:
        prompt_lines.append("لا توجد ترشيحات بعد — اختر بحرية ضمن التصنيف.")

    prompt_lines += [
        "",
        "إرشادات الاختيار:",
        "• انظر في تنوع القائمة الحالية — إذا كانت تميل نحو اتجاه واحد (مثلاً كلها روايات عربية معاصرة، "
        "أو كلها أدب عالمي كلاسيكي)، فضّل ما يُثري التنوع ويفتح خيارات مختلفة أمام الأعضاء.",
        "• الكتاب يجب أن يكون حقيقياً وموجوداً فعلاً، ومناسباً للقراءة الجماعية في نادٍ ثقافي.",
    ]
    if category:
        prompt_lines.append(f"• يجب أن يندرج بوضوح تحت تصنيف «{category}» ويمثّله تمثيلاً مناسباً.")
    prompt_lines += [
        "",
        "أجب بهذا التنسيق فقط — لا تضف أي نص آخر:",
        "TITLE: اسم الكتاب الكامل، اسم المؤلف",
        "REASON: سبب اختيار هذا الكتاب تحديداً (جملة أو جملتان)",
    ]
    nomination_prompt = "\n".join(prompt_lines)

    await update.message.reply_chat_action("typing")
    logger.info("Bot nomination: requesting AI recommendation (user=%s)", username)

    try:
        raw_reply = await _ai_generate(
            contents=[nomination_prompt],
            system_instruction=SYSTEM_PROMPT,
            label="bot_nomination",
        )
    except RuntimeError as e:
        err = str(e)
        logger.warning("bot_nomination: Gemini failed — %s", e)
        if err == "gemini_auth_error":
            await update.message.reply_text("🔑 مشكلة في مفتاح الذكاء الاصطناعي. تواصل مع المسؤول.")
        elif err == "gemini_unavailable":
            await update.message.reply_text("خدمة الذكاء الاصطناعي غير متاحة حالياً.")
        elif "rate" in err or "429" in err:
            await update.message.reply_text(
                "⏳ النموذج مشغول حالياً — جرّب مجدداً بعد لحظة."
            )
        else:
            await update.message.reply_text(
                "⚠️ تعذّر الحصول على اقتراح من النموذج — جرّب مجدداً."
            )
        return

    # ── Parse structured response ─────────────────────────────────────────────
    title_m  = re.search(r"TITLE:\s*(.+?)(?:\n|$)", raw_reply, re.IGNORECASE)
    reason_m = re.search(r"REASON:\s*(.+?)(?:\n\n|\Z)", raw_reply, re.IGNORECASE | re.DOTALL)

    if not title_m:
        logger.warning(
            "Bot nomination: could not parse TITLE from AI response (user=%s): %r",
            username, raw_reply[:300],
        )
        await update.message.reply_text(
            "⚠️ لم أتمكن من استخلاص عنوان كتاب محدد من الرد — جرّب مجدداً."
        )
        return

    title  = title_m.group(1).strip()
    reason = reason_m.group(1).strip() if reason_m else ""
    # Normalize multi-line reason to a single line
    reason = re.sub(r"\s+", " ", reason)

    logger.info(
        "Bot nomination: AI recommended %r (reason=%r) | user=%s",
        title, reason, username,
    )

    # ── Store as official bot nomination ──────────────────────────────────────
    added = suggestion_store.merge_suggestions(
        [title],
        submitted_by="🤖 البوت",
        user_id=0,
        source="bot",
    )

    chat_id  = update.effective_chat.id
    category = roadmap_store.get_active_category() or ""   # re-read after merge

    # Always refresh the official pinned template
    tmpl_id = suggestion_store.get_template_message_id()
    if tmpl_id:
        try:
            await context.bot.edit_message_text(
                chat_id=chat_id,
                message_id=tmpl_id,
                text=suggestion_store.build_template_text(category=category),
                parse_mode="HTML",
            )
        except Exception as exc:
            logger.warning("Bot nomination: could not update suggestion template: %s", exc)

    if added == 0:
        # Duplicate — already on the list
        await update.message.reply_text(
            f"📚 هذا الكتاب مرشح بالفعل:\n<b>{_html.escape(title)}</b>\n\n"
            "جرّب مجدداً للحصول على اقتراح مختلف.",
            parse_mode="HTML",
        )
        logger.info(
            "Bot nomination: duplicate detected for %r (total=%d)",
            title, len(suggestion_store.get_suggestions()),
        )
        return

    # ── Reply with completed nomination message (member format + reason note) ─
    completed = suggestion_store.build_template_text(category=category)
    total     = len(suggestion_store.get_suggestions())

    reason_note = (
        f"\n\n━━━━━━━━━━━━━━━━\n\n"
        f"💡 <i>أضفت: <b>{_html.escape(title)}</b>"
        + (f"\n{_html.escape(reason)}" if reason else "")
        + "</i>"
    )

    await update.message.reply_text(
        completed + reason_note,
        parse_mode="HTML",
    )

    logger.info(
        "Bot nomination submitted: %r | total=%d | user=%s",
        title, total, username,
    )


async def answer_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle /اجب [question] — general AI knowledge assistant.

    Processing pipeline:
      1. Extract any named book title from the question.
      2. Check club data (books dict → archive) for verified metadata.
      3. Inject verified metadata as context if found — retrieval before generation.
      4. For high-risk factual book questions without verified club data, append an
         uncertainty prompt hint so the AI is less likely to present guesses as fact.
    """
    if update.message is None:
        return
    if gemini_client is None:
        await update.message.reply_text("خدمة الذكاء الاصطناعي غير متاحة حالياً.")
        return
    # Guard against double-dispatch of the same update (e.g. bot restart mid-call).
    # Only CHECK here — _mark_processed is called after the reply is confirmed sent.
    _chat_id = update.effective_chat.id if update.effective_chat else 0
    if _check_duplicate(_chat_id, update.message.message_id):
        logger.warning(
            "answer_command: duplicate update suppressed (chat=%s msg=%s)",
            _chat_id, update.message.message_id,
        )
        return

    # ── Input extraction ──────────────────────────────────────────────────────
    # Three supported patterns:
    #   1. /ask <question>               plain text message
    #   2. /ask <question>               as the caption of a photo message
    #   3. reply to an existing photo with /ask <question> as the text
    _cmd_strip = lambda s: re.sub(r"^/(?:اجب|ask)(?:@\S+)?\s*", "", s).strip()

    _photo_source = None
    if update.message.photo:
        # Pattern 2: command in caption, image in the same message
        raw = update.message.caption or ""
        _photo_source = update.message.photo[-1]  # highest-resolution variant
    elif update.message.reply_to_message and update.message.reply_to_message.photo:
        # Pattern 3: command in text, image in the replied-to message
        raw = update.message.text or ""
        _photo_source = update.message.reply_to_message.photo[-1]
    else:
        # Pattern 1: plain text, no image
        raw = update.message.text or ""

    question = _cmd_strip(raw)
    if not question:
        await update.message.reply_text(
            "اكتب سؤالك بعد الأمر — أي سؤال يخطر ببالك.\n\n"
            "أمثلة:\n"
            "/اجب ما الفرق بين الفلسفة والرواقية؟\n"
            "/اجب كيف تعمل الذاكرة البشرية؟\n"
            "/اجب لماذا يخاف بعض الناس من الرفض؟\n"
            "/اجب ما الفرق بين الرواية والنوفيلا؟\n\n"
            "💡 يمكنك إرسال صورة مع السؤال في التعليق، أو الرد على صورة بسؤالك."
        )
        return

    username = (
        (update.effective_user.username or update.effective_user.first_name)
        if update.effective_user
        else "user"
    )

    # ── Image download (in-memory only, no disk writes) ───────────────────────
    # Bytes are passed to Gemini then discarded — never stored in history,
    # archives, discussion logs, or any persistent store.
    image_bytes: bytes | None = None
    if _photo_source is not None:
        try:
            _tg_file = await context.bot.get_file(
                _photo_source.file_id,
                read_timeout=30,
                write_timeout=30,
                connect_timeout=15,
            )
            image_bytes = bytes(await _tg_file.download_as_bytearray())
            logger.info(
                "/اجب: image attached (%d bytes) from %s — will not be stored",
                len(image_bytes), username,
            )
        except Exception as _img_err:
            logger.warning(
                "/اجب: image download failed for %s (%s) — proceeding text-only",
                username, _img_err,
            )
            image_bytes = None

    logger.info("/اجب from %s: %s%s", username, question[:80], " [+image]" if image_bytes else "")

    # ── Priority 4: Retrieval before generation ───────────────────────────────
    # Club metadata (book_store/archive), session context, and reading progress
    # are private to the configured reading group. Inject them when the request
    # arrives from the configured group OR from the owner's private DM (training
    # workspace — owner is trusted to see the same context the group sees).
    _ask_is_configured = _from_configured_chat(update) or _is_owner_dm(update)

    # ── Bot-nomination mode (owner-only, configured group, active nominations) ──
    # Conditions: configured group + registered owner + nominations open +
    # the query contains clear nomination-submission intent.
    # (reply-to-template is NOT required — plain group message is enough)
    _bn_user = update.effective_user
    _is_bot_nomination = (
        _ask_is_configured
        and _bn_user is not None
        and auth_store.is_owner(_bn_user.id)
        and suggestion_store.is_open()
        and bool(_BOT_NOMINATE_RE.search(question))
    )
    if _is_bot_nomination:
        logger.info(
            "answer_command: bot-nomination mode triggered (user=%s)",
            username,
        )
        await _handle_bot_nomination(update, context, question, username)
        return

    verified_context = ""
    if _ask_is_configured:
        named_title = _extract_book_title_from_query(question)
        if named_title:
            meta   = book_store.get_metadata(named_title)
            archived = book_store.find_in_archive(named_title) if not meta else None
            data = meta or archived
            if data:
                matched = data.get("title", named_title)
                src = "أرشيف النادي" if archived else "بيانات النادي"
                fields: list[str] = []
                for key, label in [
                    ("author",            "المؤلف"),
                    ("translator",        "المترجم"),
                    ("publisher",         "الناشر"),
                    ("year",              "سنة النشر"),
                    ("pages",             "الصفحات"),
                    ("original_language", "اللغة الأصلية"),
                    ("author_country",    "بلد المؤلف"),
                    ("original_title",    "العنوان الأصلي"),
                ]:
                    if data.get(key):
                        fields.append(f"{label}: {data[key]}")
                if fields:
                    verified_context = (
                        f"[بيانات موثقة من {src} عن «{matched}»]\n"
                        + "\n".join(fields)
                        + "\n\n"
                    )
                    logger.info(
                        "/اجب: verified metadata injected for '%s' (source=%s)",
                        matched, src,
                    )

    # ── Priority 3: High-risk uncertainty hint ────────────────────────────────
    # When no verified club data covers this question, ask the AI to flag
    # uncertainty rather than confidently stating potentially wrong facts.
    uncertainty_hint = ""
    if not verified_context and _HIGH_RISK_BOOK_RE.search(question):
        uncertainty_hint = (
            "\n\n[تنبيه: إذا لم تكن ثقتك عالية في هذه التفصيلة، "
            "اذكر ذلك صراحةً بدلاً من تقديم معلومات قد تكون غير دقيقة.]"
        )

    # Assemble: verified metadata → reading context → book prep → knowledge → spoiler guard → question → hint
    if _ask_is_configured:
        session_ctx   = await _get_session_context()
        context_hint  = _get_reading_context_hint()
        book_prep_ctx = _get_book_prep_context()
        nomination_ctx = (
            _get_nomination_context()
            if _NOMINATION_QUERY_RE.search(question)
            else ""
        )
        _ask_uid = update.effective_user.id if update.effective_user else 0
        spoiler_guard = _get_spoiler_guard(_ask_uid)
        _prep_book = cycle_store.get_current_book()
        knowledge_ctx = _get_knowledge_context(question, _prep_book["title"]) if _prep_book else ""
        # Fire-and-forget: ensure a prep sheet exists for the current book.
        # Use _generate_book_prep_task (not _generate_book_prep directly) so
        # that all exceptions — including the re-raised gemini_auth_error — are
        # caught and logged rather than propagated to the event loop handler.
        if _prep_book and not book_prep_store.has_prep(_prep_book["title"]):
            _, _prep_meta = _get_current_book_meta()
            asyncio.create_task(_generate_book_prep_task(_prep_book["title"], _prep_meta))
    else:
        session_ctx    = ""
        context_hint   = ""
        book_prep_ctx  = ""
        nomination_ctx = ""
        spoiler_guard  = ""
        knowledge_ctx  = ""
        _prep_book     = None
    parts = [p for p in [session_ctx, verified_context, context_hint, book_prep_ctx, knowledge_ctx, spoiler_guard, nomination_ctx, question, uncertainty_hint] if p]

    # ── Phase 4a: log interaction with decision signals ────────────────────────
    global _last_ask_interaction_id
    _used_search = _question_needs_search(question)
    _log_signals = {
        "used_search": _used_search,
        "used_book_prep": bool(book_prep_ctx),
        "used_knowledge_base": bool(knowledge_ctx),
        "knowledge_entries_injected": knowledge_ctx.count("•") if knowledge_ctx else 0,
        "spoiler_guard_active": bool(spoiler_guard),
    }
    _q_category = _classify_question_category(question)
    _book_title_for_log = _prep_book["title"] if _prep_book else None
    _last_ask_interaction_id = interaction_log_store.log_interaction(
        book=_book_title_for_log,
        question=question,
        question_category=_q_category,
        decision_signals=_log_signals,
    )
    logger.debug(
        "/اجب: interaction logged id=%s category=%s signals=%s",
        _last_ask_interaction_id, _q_category, _log_signals,
    )
    prompt = "".join(parts)

    # ── Temporary diagnostics ─────────────────────────────────────────────────
    # Grep for [DIAG /ask] and [DIAG provider] to trace the full pipeline.
    # Remove this block (and the SYSTEM_PROMPT_VERSION constant) when no longer needed.
    _diag_pre: list[str] = []
    if verified_context:
        _diag_pre.append("verified_context")
    if context_hint:
        _diag_pre.append("reading_context")
    if nomination_ctx:
        _diag_pre.append("nomination_context")
    if uncertainty_hint:
        _diag_pre.append("uncertainty_hint")
    _user_id_for_diag = update.effective_user.id if update.effective_user else 0
    _history_turns = len(conversation_histories.get(_user_id_for_diag, []))
    logger.info(
        "[DIAG /ask] user=%s | sp_version=%s | preprocessing=%s"
        " | raw_q_len=%d | user_text_len=%d | history_turns=%d",
        username,
        SYSTEM_PROMPT_VERSION,
        ",".join(_diag_pre) or "none",
        len(question),
        len(prompt),
        _history_turns,
    )
    # ── End diagnostics ───────────────────────────────────────────────────────

    _is_high_risk = bool(_HIGH_RISK_BOOK_RE.search(question))
    if _is_high_risk:
        logger.info("/اجب: high-risk factual question — uncertainty hint applied (%s)", username)

    _ask_chat_id = update.effective_chat.id if update.effective_chat else 0
    _ask_user_id = update.effective_user.id if update.effective_user else 0
    _ask_hkey = _resolve_history_key(_ask_chat_id, _ask_user_id)
    try:
        _ask_ok = await send_ai_reply(
            update, context, prompt,
            dump_prompt=ASK_DUMP_PROMPT,
            skip_history=False,
            image_bytes=image_bytes,
            history_key=_ask_hkey,
            use_search=_question_needs_search(question),
            # A public reading-group question receives exactly one readable
            # response. Private companion/training flows retain voice support.
            allow_voice=not _from_configured_chat(update),
        )
        if _ask_ok:
            _mark_processed(_ask_chat_id, update.message.message_id)
            _open_or_refresh_group_discussion(_ask_chat_id, _ask_user_id)
    except Exception as e:
        logger.error("/اجب error for %s: %s", username, e)
        await update.message.reply_text("عذراً، حدث خطأ. حاول مرة أخرى.")


# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#  /plan (/الخطة) — reading-cycle dashboard
#
#  Shows the full book journey for the group:
#    current book · completed books · upcoming books · participation counts
#    cycle progress · vote results
#
#  This is a centralized layer; future systems (/done, ratings, stats, …)
#  will feed data into _build_plan_message() as they are built.
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

_AR_DAYS = {0: "الاثنين", 1: "الثلاثاء", 2: "الأربعاء",
            3: "الخميس", 4: "الجمعة", 5: "السبت", 6: "الأحد"}

_AR_MONTHS = {1: "يناير", 2: "فبراير", 3: "مارس", 4: "أبريل",
              5: "مايو", 6: "يونيو", 7: "يوليو", 8: "أغسطس",
              9: "سبتمبر", 10: "أكتوبر", 11: "نوفمبر", 12: "ديسمبر"}


def _ar_date(d: date) -> str:
    """Format a date as Arabic string, e.g. 'الخميس 21 مايو'."""
    return f"{_AR_DAYS[d.weekday()]} {d.day} {_AR_MONTHS[d.month]}"


def _iso_to_ar_date(iso: str) -> str:
    """Parse an ISO datetime string and return an Arabic date label."""
    try:
        from datetime import datetime as _dt
        return _ar_date(_dt.fromisoformat(iso).date())
    except Exception:
        return ""


_NUM_EMOJIS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣", "7️⃣", "8️⃣"]


def _calc_engagement(readers: int, completers: int, raters: int) -> str:
    """
    Classify engagement quality using lifecycle participation signals only.
    Returns a human-readable Arabic label.
    """
    if readers == 0 and completers == 0 and raters == 0:
        return "قيد التقييم"
    # Weighted score: completers show commitment so double-weight them
    score = readers + (completers * 2) + raters
    if score <= 3:
        return "ضعيف"
    elif score <= 10:
        return "متوسط"
    elif score <= 20:
        return "مرتفع"
    else:
        return "قوي جدًا"


def _build_plan_message() -> str:
    """
    Build the reading plan dashboard message (/plan).

    Layout:
      📚 الخطة (N)
      ━━━  [full]
      🕓 start date   📖 roadmap book count
      📍 Current book card  (category · readers · engagement · completers · rating)
      ━━━  [full]
      🔜 Next roadmap stage   (category name only — book TBD)
      ⏭️ Stage after next     (category name only — book TBD)
      ━━━  [short — only when next stages are shown]
      📚 Last completed stage  (category · title · stats)
      ━━━  [full]
      🏆 Highest-rated book all-time
      ━━━  [full]
      📢 Admin notice

    Roadmap context (category names) is always shown; individual
    book-level details (chapters, pages, schedule) belong to /schedule.
    """
    lines: list[str] = []

    # ── Gather cycle state ────────────────────────────────────────────────────
    cycle_num    = cycle_store.get_cycle_number()
    cycle_status = cycle_store.get_status()
    has_cycle    = cycle_status in ("active", "completed")
    cur_book_obj = cycle_store.get_current_book() if has_cycle else None
    current_book = cur_book_obj["title"] if cur_book_obj else ""

    # ── Gather roadmap state ──────────────────────────────────────────────────
    rm_data       = roadmap_store.load()
    rm_status     = roadmap_store.get_status()
    rm_active     = rm_status == "active"
    roadmap_list  = rm_data.get("roadmap", [])
    current_stage = rm_data.get("current_stage", 0)
    active_cat    = roadmap_store.get_active_category()

    # ── Header ────────────────────────────────────────────────────────────────
    cycle_label = f" ({cycle_num})" if cycle_num > 0 else ""
    lines.append(f"📚 <b>الخطة{cycle_label}</b>")
    lines.append("")
    lines.append("━━━━━━━━━━━━━━━━━━")

    # ── Empty state ───────────────────────────────────────────────────────────
    if not has_cycle and not current_book:
        lines.append("")
        lines.append("📭 <i>لا توجد خطة قراءة نشطة حالياً.</i>")
        lines.append("")
        lines.append("<i>ابدأ عبر /opensuggestions</i>")
        return "\n".join(lines)

    # ── Start date + roadmap book count ───────────────────────────────────────
    lines.append("")
    cycle_data       = cycle_store.load()
    cycle_started_at = cycle_data.get("started_at", "")
    if cycle_started_at:
        lines.append(f"🕓 <b>بدأت الخطة:</b> {_iso_to_ar_date(cycle_started_at)}")
    if rm_active and roadmap_list:
        lines.append(f"📖 <b>عدد الكتب:</b> {len(roadmap_list)}")

    # ── 📍 Current book card ──────────────────────────────────────────────────
    lines.append("")
    lines.append("📍 <b>نقرأ الآن:</b>")
    lines.append("")

    if current_book:
        if active_cat:
            lines.append(f"🏷️ <b>{active_cat}:</b> {current_book}")
        else:
            lines.append(f"📖 <b>{current_book}</b>")
        lines.append("")

        # Readers — live from active poll, or final from archive
        readers_count = 0
        active_poll = poll_store.get_active()
        if active_poll and active_poll["book_title"] == current_book:
            readers_count = poll_store.get_participant_count()
        else:
            arch_poll = poll_store.get_archived_for_book(current_book)
            if arch_poll:
                readers_count = arch_poll["participant_count"]
        lines.append(f"👥 <b>عدد القراء:</b> {readers_count if readers_count > 0 else '—'}")

        # Completers (Phase 7) + raters for engagement calc
        done_cnt     = completion_store.get_count(current_book)
        raters_count = 0
        active_rate  = rating_store.get_active()
        if active_rate and active_rate["book_title"] == current_book:
            _, raters_count, _ = rating_store.get_live_stats()

        lines.append(f"🔥 <b>التفاعل:</b> {_calc_engagement(readers_count, done_cnt, raters_count)}")
        lines.append(f"✅ <b>عدد المنجزين:</b> {done_cnt if done_cnt > 0 else '—'}")

        # Rating — live if active, placeholder if not yet open
        if active_rate and active_rate["book_title"] == current_book:
            _, total_r, most_common_r = rating_store.get_live_stats()
            if total_r > 0:
                lines.append(f"⭐️ <b>حالة التقييم:</b> {'⭐️' * most_common_r} ({total_r} تقييم)")
            else:
                lines.append("⭐️ <b>حالة التقييم:</b> —")
        else:
            lines.append("⭐️ <b>حالة التقييم:</b> يفتح بعد انتهاء القراءة")
    else:
        lines.append("📭 <i>لا توجد دورة قراءة نشطة حالياً.</i>")

    lines.append("")
    lines.append("━━━━━━━━━━━━━━━━━━")

    # ── 🔜 Next two roadmap stages ────────────────────────────────────────────
    # Only shown when a roadmap is active and future stages exist
    next_idx       = current_stage + 1
    after_next_idx = current_stage + 2
    has_next       = rm_active and next_idx < len(roadmap_list)
    has_after_next = rm_active and after_next_idx < len(roadmap_list)

    if has_next:
        lines.append("")
        lines.append("🔜 <b>المرحلة القادمة سنقرأ في:</b>")
        lines.append("")
        lines.append(f"🏷️ <b>{roadmap_list[next_idx]}:</b> سيحدد الكتاب بعد الانتهاء من الكتاب الحالي")
        lines.append("")
        lines.append("👥 <b>عدد القراء:</b> —")
        lines.append("🔥 <b>التفاعل:</b> قيد التقييم")
        lines.append("✅ <b>عدد المنجزين:</b> —")
        lines.append("⭐️ <b>أكثر تقييم شائع:</b> —")

    if has_after_next:
        lines.append("")
        lines.append("⏭️ <b>المرحلة التي تليها نقرأ في:</b>")
        lines.append("")
        lines.append(f"🏷️ <b>{roadmap_list[after_next_idx]}:</b> سيحدد بعد الانتهاء من الكتاب الحالي")
        lines.append("")
        lines.append("👥 <b>عدد القراء:</b> —")
        lines.append("🔥 <b>التفاعل:</b> قيد التقييم")
        lines.append("✅ <b>عدد المنجزين:</b> —")
        lines.append("⭐️ <b>أكثر تقييم شائع:</b> —")

    # Short separator only when next-stage blocks were rendered
    if has_next or has_after_next:
        lines.append("")
        lines.append("━━━━━━━━")

    # ── 📚 Last completed stage ───────────────────────────────────────────────
    # Source: book_store archive — has category + roadmap_id; ordered oldest→newest
    archive = book_store.get_archive()
    last_entry = archive[-1] if archive else None

    if last_entry:
        lc_title = last_entry.get("title", "")
        lc_cat   = last_entry.get("category")

        lines.append("")
        lines.append("📚 <b>آخر مرحلة مكتملة</b>")
        lines.append("")
        if lc_cat:
            lines.append(f"🏷️ <b>{lc_cat}:</b> {lc_title}")
        else:
            lines.append(f"📖 <b>{lc_title}</b>")
        lines.append("")

        lc_poll    = poll_store.get_archived_for_book(lc_title)
        lc_readers = lc_poll["participant_count"] if lc_poll else 0
        lc_done    = completion_store.get_count(lc_title)
        lc_rate    = rating_store.get_archived_for_book(lc_title)
        lc_raters  = lc_rate["total_ratings"] if lc_rate else 0

        lines.append(f"👥 <b>عدد القراء:</b> {lc_readers if lc_readers > 0 else '—'}")
        lines.append(f"🔥 <b>التفاعل:</b> {_calc_engagement(lc_readers, lc_done, lc_raters)}")
        lines.append(f"✅ <b>عدد المنجزين:</b> {lc_done if lc_done > 0 else '—'}")
        if lc_rate and lc_rate.get("most_common_rating", 0) > 0:
            lines.append(f"⭐️ <b>أكثر تقييم شائع:</b> {'⭐️' * lc_rate['most_common_rating']}")
        else:
            lines.append("⭐️ <b>أكثر تقييم شائع:</b> —")

    lines.append("")
    lines.append("━━━━━━━━━━━━━━━━━━")

    # ── 🏆 Highest-rated book all-time ────────────────────────────────────────
    best_rated = rating_store.get_best_rated_book()
    if best_rated and best_rated.get("most_common_rating", 0) > 0:
        br_title = best_rated["book_title"]
        br_entry = book_store.find_in_archive(br_title)
        br_cat   = br_entry.get("category") if br_entry else None

        lines.append("")
        lines.append("🏆 <b>الأعلى تقييمًا حتى الآن</b>")
        lines.append("")
        if br_cat:
            lines.append(f"🏷️ <b>{br_cat}:</b> {br_title}")
        else:
            lines.append(f"📖 <b>{br_title}</b>")
        lines.append("")
        lines.append("⭐️" * best_rated["most_common_rating"])
        lines.append("")
        lines.append("━━━━━━━━━━━━━━━━━━")

    # ── 📢 Admin notice ───────────────────────────────────────────────────────
    sch = schedule_store.load()
    notice = sch.get("notice", "").strip()
    lines.append("")
    lines.append("📢 <b>ملاحظة</b>")
    lines.append("")
    lines.append(_html.escape(notice) if notice else "<i>لا توجد ملاحظات حالياً.</i>")

    return "\n".join(lines)


async def plan_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Send the reading plan: static plan cover image + plan text."""
    if update.effective_message is None:
        return
    if not _from_configured_chat(update):
        return

    message_text = _build_plan_message()

    if os.path.exists(_PLAN_COVER_PATH):
        try:
            with open(_PLAN_COVER_PATH, "rb") as img:
                await update.effective_message.reply_photo(
                    photo=img,
                    caption=message_text,
                    parse_mode="HTML",
                )
            return
        except Exception as e:
            logger.warning("plan_command: could not send plan cover (%s), sending text.", e)

    # Fallback: text only
    await update.effective_message.reply_text(message_text, parse_mode="HTML")


async def set_cover_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Admin command: send a photo with caption /غلاف in DM to set the static plan cover image."""
    if update.effective_message is None or not update.effective_message.photo:
        return
    if update.effective_user is None or update.effective_chat is None:
        return
    if update.effective_chat.type != "private":
        return

    user_id = update.effective_user.id
    chat_id = update.effective_chat.id
    owner = await _ensure_owner(user_id, chat_id, context.bot)
    if not owner and not auth_store.is_authorized(user_id):
        await update.effective_message.reply_text("⛔ هذا الأمر للمشرفين فقط.")
        return

    photo_file = await update.effective_message.photo[-1].get_file()
    await photo_file.download_to_drive(_PLAN_COVER_PATH)

    username = update.effective_user.first_name if update.effective_user else "admin"
    logger.info("Plan cover set by %s → %s", username, _PLAN_COVER_PATH)
    await update.effective_message.reply_text(
        "✅ تم حفظ صورة غلاف الخطة.\n"
        "ستظهر عند استخدام /plan"
    )


async def set_schedule_cover_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Admin command: send a photo with caption /غلاف_جدول in DM to set the static schedule cover image."""
    if update.effective_message is None or not update.effective_message.photo:
        return
    if update.effective_user is None or update.effective_chat is None:
        return
    if update.effective_chat.type != "private":
        return

    user_id = update.effective_user.id
    chat_id = update.effective_chat.id
    owner = await _ensure_owner(user_id, chat_id, context.bot)
    if not owner and not auth_store.is_authorized(user_id):
        await update.effective_message.reply_text("⛔ هذا الأمر للمشرفين فقط.")
        return

    photo_file = await update.effective_message.photo[-1].get_file()
    await photo_file.download_to_drive(_SCHEDULE_COVER_PATH)

    username = update.effective_user.first_name if update.effective_user else "admin"
    logger.info("Schedule cover set by %s → %s", username, _SCHEDULE_COVER_PATH)
    await update.effective_message.reply_text(
        "✅ تم حفظ صورة غلاف الجدول.\n"
        "ستظهر عند استخدام /schedule"
    )


async def jadwal_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /schedule (/الجدول) — send the live reading schedule dashboard (image + formatted text).
    """
    if update.effective_message is None:
        return
    if not _from_configured_chat(update):
        return

    store = schedule_store.load()
    today = datetime.now(TIMEZONE).date()
    today_iso = today.isoformat()

    # Guard: missing or corrupt store file — load() returns {} in both cases.
    # Accessing store["entries"] directly would raise KeyError; use .get() and
    # bail out early with a friendly message so the group sees a clear reply
    # rather than a silent crash.
    all_entries = store.get("entries", [])
    if not all_entries:
        await update.effective_message.reply_text(
            "📅 لا يوجد جدول قراءة حالياً.\n"
            "يمكن للمشرف رفع الجدول باستخدام /newschedule"
        )
        return

    # Sort by date so completed/upcoming lists are always in chronological order
    reading_entries = sorted(
        [e for e in all_entries if not e["is_rest"]], key=lambda e: e["date"]
    )
    rest_entries = sorted(
        [e for e in all_entries if e["is_rest"]], key=lambda e: e["date"]
    )

    # Inline rest-day check using the already-computed today_iso so the
    # result honours the same timezone logic as the rest of jadwal_command
    # (avoids a second datetime.now() call deep inside schedule_store).
    is_rest_today = any(
        e["date"] == today_iso and e.get("is_rest") for e in all_entries
    )

    # Determine the current section by date: the last non-rest entry whose
    # date is on or before today.  This replaces the old 📍-marked entry so
    # the schedule advances automatically each day without manual marking.
    raw_current = None
    for e in reading_entries:
        if e["date"] <= today_iso:
            raw_current = e   # keep advancing until we pass today
        elif e["date"] > today_iso:
            break             # entries are sorted — future entries stop the search

    current_entry = None
    if raw_current:
        current_entry = {
            "date":       date.fromisoformat(raw_current["date"]),
            "chapter":    raw_current["chapter"],
            "page_start": raw_current.get("page_start"),
            "page_end":   raw_current.get("page_end"),
        }

    completed = [e for e in reading_entries if e["date"] < today_iso]
    upcoming  = [e for e in reading_entries if e["date"] > today_iso]

    elapsed, total = schedule_store.get_progress(store)
    pct = round(elapsed / total * 100) if total else 0

    # Use cycle_store's book title when a cycle is active
    book_title = store.get("current_book", "")
    if cycle_store.is_active():
        cur_b = cycle_store.get_current_book()
        if cur_b:
            book_title = cur_b["title"]

    # ── Image: static schedule cover (uploaded manually via /غلاف_جدول) ────────
    img_path = _SCHEDULE_COVER_PATH if os.path.exists(_SCHEDULE_COVER_PATH) else None

    # ── Build text dashboard (clean tracker — no archive/stats) ────────────────

    # Progress counters
    completed_count = len(completed)
    remaining_days  = max(total - elapsed, 0)
    rest_count      = len(rest_entries)

    # ── Header ───────────────────────────────────────────────────────────────
    lines: list[str] = ["<b>جدول القراءة</b>"]

    # ── Current date ─────────────────────────────────────────────────────────
    # Show the scheduled reading date for the current chapter, not the system date
    schedule_date = date.fromisoformat(raw_current["date"]) if raw_current else today
    lines.append(f"📅 {_ar_date(schedule_date)}")

    lines.append("────────────")

    # ── 📍 تقرأ الآن ─────────────────────────────────────────────────────────
    lines.append("📍 تقرأ الآن:")
    if current_entry:
        ce = current_entry
        lines.append(f"🧠 {ce['chapter']}")
        if ce["page_start"] is not None:
            lines.append(f"📄 {ce['page_start']} ← {ce['page_end']}")
    elif is_rest_today:
        lines.append("☕️ <i>يوم راحة</i>")
    elif today > date.fromisoformat(max((e["date"] for e in reading_entries), default=today_iso)):
        lines.append("✅ <i>انتهى الجدول</i>")
    else:
        lines.append("—")

    # ── 🧠 فكرة الفصل — live AI summary, cached, silently omitted on failure ──
    if current_entry and current_entry["chapter"] and not is_rest_today:
        chapter_idea = await _fetch_chapter_idea(book_title, current_entry["chapter"])
        if chapter_idea:
            # Limit to 3 lines to keep the caption compact
            chapter_idea = "\n".join(chapter_idea.strip().splitlines()[:3])
            lines.append("────────────")
            lines.append("🧠 <b>فكرة الفصل</b>")
            lines.append(chapter_idea)

    lines.append("────────────")

    # ── 📆 تقدم القراءة ──────────────────────────────────────────────────────
    lines.append("<b>تقدم القراءة:</b>")
    lines.append(f"⏳ {elapsed} / {total} يوم")
    lines.append(f"✅ {completed_count} {'فصل' if completed_count == 1 else 'فصول'} منجزة")

    # Rest days: show actual day names (e.g. الجمعة و السبت), not a count
    unique_rest_names = list(dict.fromkeys(
        _AR_DAYS[date.fromisoformat(e["date"]).weekday()]
        for e in rest_entries
    ))
    rest_days_str = " و ".join(unique_rest_names) if unique_rest_names else "—"
    lines.append(f"☕️ {rest_days_str} راحة")

    # ── Optional admin notice ─────────────────────────────────────────────────
    notice = store.get("notice", "").strip()
    if notice:
        lines.append(f"📌 {_html.escape(notice)}")

    text_msg = "\n".join(lines)

    # ── Send ────────────────────────────────────────────────────────────────
    if img_path and os.path.exists(img_path):
        try:
            with open(img_path, "rb") as img_file:
                await update.effective_message.reply_photo(
                    photo=img_file,
                    caption=text_msg[:1024],
                    parse_mode="HTML",
                )
            if len(text_msg) > 1024:
                await update.effective_message.reply_text(
                    text_msg[1024:], parse_mode="HTML"
                )
        except Exception as e:
            logger.error("jadwal: failed to send image: %s", e)
            await update.effective_message.reply_text(text_msg, parse_mode="HTML")
    else:
        await update.effective_message.reply_text(text_msg, parse_mode="HTML")


async def daily_schedule_reminder_job(bot: Bot) -> None:
    """
    Send Takbeer's single daily reading-plan message to the configured group.

    WAQT owns the evening cultural discussion, while Takbeer is the sole owner
    of the reading schedule and this morning operational reminder. The message
    is date-driven from the same authoritative schedule used by /الجدول.
    """
    if not CHAT_ID:
        logger.warning("Daily schedule reminder skipped: TELEGRAM_CHAT_ID is not configured")
        return

    store = schedule_store.load()
    entries = store.get("entries", [])
    if not entries:
        logger.info("Daily schedule reminder skipped: no active schedule")
        return

    today_iso = datetime.now(TIMEZONE).date().isoformat()
    today_entry = next((entry for entry in entries if entry.get("date") == today_iso), None)
    if not today_entry:
        logger.info("Daily schedule reminder skipped: no entry for %s", today_iso)
        return

    book_title = store.get("current_book", "")
    if cycle_store.is_active():
        current_book = cycle_store.get_current_book()
        if current_book:
            book_title = current_book.get("title", book_title)

    if today_entry.get("is_rest"):
        text = "☕️ <b>اليوم يوم راحة</b>\n\nنستأنف القراءة في الموعد التالي من الجدول."
    else:
        chapter = _html.escape(today_entry.get("chapter", ""))
        page_start = today_entry.get("page_start")
        page_end = today_entry.get("page_end")
        lines = [
            "📖 <b>تذكير القراءة اليوم</b>",
            "",
            f"«{_html.escape(book_title)}»" if book_title else "الكتاب الحالي",
            f"🧠 {chapter}" if chapter else "🧠 القراءة المقررة اليوم",
        ]
        if page_start is not None and page_end is not None:
            lines.append(f"📄 {page_start} ← {page_end}")
        lines.append("")
        lines.append("يمكنك مراجعة التفاصيل عبر /الجدول")
        text = "\n".join(lines)

    try:
        await bot.send_message(chat_id=CHAT_ID, text=text, parse_mode="HTML")
        logger.info("Daily schedule reminder delivered for %s", today_iso)
    except Exception:
        logger.exception("Daily schedule reminder failed for %s", today_iso)
        return

    # Keep the exported snapshot fresh for other consumers. WAQT independently
    # derives its daily rhythm context from the contract schedule.
    await _auto_export_context("daily_schedule_reminder")


async def newschedule_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Admin-only command: upload a new reading schedule.

    Usage (two forms):
      1. /newschedule followed by the full schedule text in the same message.
      2. Reply to a message containing the schedule text with /newschedule.

    The bot verifies the sender is a group admin, parses the Arabic schedule,
    auto-archives the previous book if its schedule has fully passed, then saves.
    """
    if update.effective_message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    msg = update.effective_message

    # ── Extract schedule text ────────────────────────────────────────────────
    schedule_text = ""

    # Form 1: text after the command on the same message
    raw = msg.text or ""
    after_cmd = re.sub(r"^/newschedule\s*", "", raw, flags=re.IGNORECASE).strip()
    if after_cmd:
        schedule_text = after_cmd

    # Form 2: reply to another message
    if not schedule_text and msg.reply_to_message:
        schedule_text = (msg.reply_to_message.text or "").strip()

    if not schedule_text:
        await msg.reply_text(
            "📋 الاستخدام:\n"
            "• أرسل /newschedule ثم الجدول مباشرةً في نفس الرسالة.\n"
            "• أو اردد على رسالة تحتوي الجدول واكتب /newschedule"
        )
        return

    # ── Parse ────────────────────────────────────────────────────────────────
    try:
        parsed = schedule_store.parse_schedule_text(schedule_text)
    except Exception as e:
        logger.error("newschedule: parse error: %s", e)
        await msg.reply_text("❌ فشل تحليل الجدول. تأكد من صيغة النص وأعد المحاولة.")
        return

    if not parsed.get("entries"):
        await msg.reply_text(
            "❌ لم يتم العثور على أي إدخالات في الجدول.\n"
            "تأكد من الصيغة: رمز الحالة (✅/⬜/☕️) + اليوم والتاريخ في سطر، "
            "ثم عنوان الفصل، ثم نطاق الصفحات."
        )
        return

    # ── Load existing store & auto-archive if previous book is done ──────────
    existing = schedule_store.load()
    completed_books: list[str] = list(existing.get("completed_books", []))

    if existing.get("entries") and existing.get("current_book"):
        if schedule_store.is_book_completed(existing):
            prev_book = existing["current_book"]
            if prev_book and prev_book not in completed_books:
                completed_books.append(prev_book)
                logger.info("Auto-archived completed book: %s", prev_book)

    # Fill book title when the schedule text didn't specify one.
    # Three-level fallback so the title is always resolved.
    if not parsed.get("current_book"):
        # 1. Active cycle book (normal case — cycle is running)
        if cycle_store.is_active():
            cur_b = cycle_store.get_current_book()
            if cur_b:
                parsed["current_book"] = cur_b["title"]
        # 2. Most recently completed book — schedule uploaded right after /completebook
        if not parsed.get("current_book"):
            latest = cycle_store.get_latest_completed()
            if latest:
                parsed["current_book"] = latest["title"]
        # 3. Whatever was in the previously saved schedule
        if not parsed.get("current_book") and existing.get("current_book"):
            parsed["current_book"] = existing["current_book"]


    # ── Build new store entry ────────────────────────────────────────────────
    new_data: dict = {
        "current_book": parsed["current_book"],
        "completed_books": completed_books,
        "upcoming_book": existing.get("upcoming_book", ""),
        "notice": existing.get("notice", ""),
        "entries": parsed["entries"],
        "uploaded_at": datetime.now(TIMEZONE).isoformat(),
        "uploaded_by": update.effective_user.first_name or str(user_id),
    }

    schedule_store.save(new_data)
    # Synchronise Companion: schedule data changed
    asyncio.create_task(_auto_export_context("schedule_uploaded"))

    reading_entries = [e for e in parsed["entries"] if not e["is_rest"]]
    rest_entries = [e for e in parsed["entries"] if e["is_rest"]]

    admin_name = update.effective_user.first_name or "المشرف"
    logger.info(
        "newschedule: saved %d reading days + %d rest days for '%s' by %s",
        len(reading_entries), len(rest_entries), parsed["current_book"], admin_name,
    )

    await msg.reply_text(
        f"✅ <b>تم تحديث الجدول بنجاح</b>\n\n"
        f"📚 الكتاب: <b>{parsed['current_book'] or 'غير محدد'}</b>\n"
        f"📅 أيام القراءة: {len(reading_entries)}\n"
        f"☕️ أيام الراحة: {len(rest_entries)}\n\n"
        f"استخدم /plan لعرض التقدم الحالي.",
        parse_mode="HTML",
    )


async def setnotice_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    Owner DM command: /setnotice <text>
    Sets a temporary notice displayed in /plan and /schedule.
    """
    if update.effective_message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    raw = update.effective_message.text or ""
    notice_text = re.sub(r"^/setnotice\s*", "", raw, flags=re.IGNORECASE).strip()
    if not notice_text:
        await update.effective_message.reply_text(
            "📌 الاستخدام:\n"
            "/setnotice نص الإشعار\n\n"
            "مثال:\n"
            "/setnotice إجازة العيد — القراءة تستأنف يوم الأحد"
        )
        return

    schedule_store.set_notice(notice_text)
    logger.info("Notice set by %s: %s", update.effective_user.first_name, notice_text[:60])
    asyncio.create_task(_auto_export_context("notice_updated"))

    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": f"📌 {notice_text}",
        "parse_mode": None,
    }
    await update.effective_message.reply_text(
        f"✅ تم تعيين الإشعار:\n\n📌 {notice_text}\n\n"
        "سيظهر في /plan و /schedule حتى تقوم بإزالته باستخدام /clearnotice\n\n"
        "اضغط الزر لنشر الإشعار في المجموعة:",
        reply_markup=_SENDGROUP_MARKUP,
    )


async def clearnotice_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Owner DM-only: clears the temporary notice."""
    if update.effective_message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    schedule_store.clear_notice()
    logger.info("Notice cleared by %s", update.effective_user.first_name)
    asyncio.create_task(_auto_export_context("notice_cleared"))
    await update.effective_message.reply_text("✅ تم مسح الإشعار.")


async def _auto_backup_job(bot) -> None:
    """
    Scheduled daily backup job.
    Runs at 03:00 Riyadh time; sends the ZIP archive to the owner's DM.
    """
    owner_id = auth_store.get_owner_id()
    if not owner_id:
        logger.warning("auto_backup_job: no owner registered — skipping backup")
        return
    try:
        buf, filename, file_count, size_bytes = backup_store.create_zip(_BOT_DIR, TIMEZONE)
    except Exception as exc:
        logger.error("auto_backup_job: create_zip failed: %s", exc)
        return
    size_kb = round(size_bytes / 1024, 1)
    caption = (
        f"📦 نسخة احتياطية تلقائية (يومية)\n"
        f"📄 {file_count} ملف\n"
        f"💾 {size_kb} KB"
    )
    try:
        await bot.send_document(chat_id=owner_id, document=buf, filename=filename, caption=caption)
        logger.info("auto_backup_job: sent %s (%.1f KB) to owner %s", filename, size_kb, owner_id)
    except Exception as exc:
        logger.error("auto_backup_job: failed to send backup to owner %s: %s", owner_id, exc)


async def backup_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/backup (/نسخة) — Owner DM-only. Sends a single ZIP archive of all bot data."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    chat_id = update.effective_chat.id
    await update.message.reply_text("📦 جارٍ إنشاء النسخة الاحتياطية...")

    try:
        buf, filename, file_count, size_bytes = backup_store.create_zip(_BOT_DIR, TIMEZONE)
    except Exception as exc:
        logger.warning("backup_command: create_zip failed: %s", exc)
        await update.message.reply_text("❌ فشل إنشاء النسخة الاحتياطية، يرجى المحاولة مرة أخرى.")
        return

    size_kb = round(size_bytes / 1024, 1)
    caption = (
        f"✅ نسخة احتياطية كاملة\n"
        f"📄 {file_count} ملف\n"
        f"💾 {size_kb} KB\n\n"
        f"💡 للاستعادة: أرسل ملف ZIP مع كتابة /restore كتعليق."
    )
    try:
        await context.bot.send_document(
            chat_id=chat_id,
            document=buf,
            filename=filename,
            caption=caption,
        )
    except Exception as exc:
        logger.warning("backup_command: send_document failed: %s", exc)
        await update.message.reply_text("❌ تعذّر إرسال الملف، يرجى المحاولة مرة أخرى.")


async def restore_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """
    /restore or /استعادة (as document caption) — Owner DM-only.
    Owner attaches a backup ZIP with /restore as the caption.
    The bot validates it, takes a safety backup, then restores.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    doc = update.message.document
    if doc is None:
        await update.message.reply_text(
            "أرفق ملف ZIP مع كتابة /restore في التعليق.\n"
            "مثال: أرفق الملف وضع /restore كتعليق."
        )
        return

    if not doc.file_name or not doc.file_name.endswith(".zip"):
        await update.message.reply_text("⚠️ يجب أن يكون الملف بصيغة .zip")
        return

    await update.message.reply_text("🔍 جارٍ التحقق من صحة الملف...")

    try:
        file = await doc.get_file()
        raw = await file.download_as_bytearray()
        data = bytes(raw)
    except Exception as exc:
        logger.warning("restore_command: download failed: %s", exc)
        await update.message.reply_text("❌ تعذّر تنزيل الملف، يرجى المحاولة مرة أخرى.")
        return

    ok, err = backup_store.validate_zip(data)
    if not ok:
        await update.message.reply_text(f"❌ الملف غير صالح للاستعادة:\n{err}")
        return

    await update.message.reply_text("💾 جارٍ إنشاء نسخة احتياطية احترازية...")

    chat_id = update.effective_chat.id
    try:
        safety_buf, safety_name, safety_count, safety_size = backup_store.create_zip(
            _BOT_DIR, TIMEZONE
        )
        await context.bot.send_document(
            chat_id=chat_id,
            document=safety_buf,
            filename=safety_name,
            caption=f"⚠️ نسخة احترازية قبل الاستعادة — {safety_count} ملف",
        )
    except Exception as exc:
        logger.warning("restore_command: safety backup failed: %s", exc)
        await update.message.reply_text(
            "❌ فشل إنشاء النسخة الاحترازية. تم إلغاء الاستعادة."
        )
        return

    await update.message.reply_text("🔄 جارٍ الاستعادة...")

    try:
        json_count, covers_count = backup_store.restore_zip(data, _BOT_DIR)
    except Exception as exc:
        logger.warning("restore_command: restore_zip failed: %s", exc)
        await update.message.reply_text("❌ فشلت الاستعادة، يرجى المحاولة مرة أخرى.")
        return

    await update.message.reply_text(
        f"✅ اكتملت الاستعادة\n"
        f"📄 {json_count} ملف بيانات\n"
        f"🖼 {covers_count} صورة غلاف\n\n"
        f"⚠️ أعد تشغيل البوت لتفعيل البيانات الجديدة."
    )
    logger.info(
        "restore_command: restored %d JSON + %d covers from %s",
        json_count, covers_count, doc.file_name,
    )


async def backup_status_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/backup_status — Owner DM-only. Shows date, file count, and size of the last backup."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    meta = backup_store.load_meta(_BOT_DIR)
    if not meta:
        await update.message.reply_text(
            "📊 لم يتم أخذ أي نسخة احتياطية بعد.\n"
            "استخدم /backup لإنشاء أول نسخة."
        )
        return

    ts_raw = meta.get("last_backup_ts", "")
    file_count = meta.get("file_count", "?")
    size_bytes = meta.get("size_bytes", 0)
    filename = meta.get("filename", "")
    size_kb = round(size_bytes / 1024, 1) if isinstance(size_bytes, int) else "?"

    try:
        from datetime import datetime as _dt
        ts_display = _dt.fromisoformat(ts_raw).strftime("%Y-%m-%d %H:%M")
    except Exception:
        ts_display = ts_raw

    await update.message.reply_text(
        f"📊 آخر نسخة احتياطية\n\n"
        f"🕐 التاريخ: {ts_display}\n"
        f"📄 عدد الملفات: {file_count}\n"
        f"💾 الحجم: {size_kb} KB\n"
        f"📁 الاسم: {filename}"
    )


def _build_guide_keyboard(section_key: str) -> list[list[InlineKeyboardButton]]:
    """Return the inline keyboard rows for a guide section."""
    keyboard: list[list[InlineKeyboardButton]] = []

    if section_key == "index":
        row: list[InlineKeyboardButton] = []
        for key in owner_guide.SECTION_ORDER:
            sec = owner_guide.SECTIONS.get(key)
            if sec is None:
                continue
            row.append(InlineKeyboardButton(sec[0], callback_data=f"guide:{key}"))
            if len(row) == 2:
                keyboard.append(row)
                row = []
        if row:
            keyboard.append(row)
    else:
        idx = owner_guide.SECTION_ORDER.index(section_key) if section_key in owner_guide.SECTION_ORDER else -1
        nav_row: list[InlineKeyboardButton] = []
        if idx > 0:
            prev_key = owner_guide.SECTION_ORDER[idx - 1]
            prev_title = owner_guide.SECTIONS[prev_key][0] if prev_key in owner_guide.SECTIONS else prev_key
            nav_row.append(InlineKeyboardButton(f"◀️ {prev_title}", callback_data=f"guide:{prev_key}"))
        nav_row.append(InlineKeyboardButton("🏠 الفهرس", callback_data="guide:index"))
        if 0 <= idx < len(owner_guide.SECTION_ORDER) - 1:
            next_key = owner_guide.SECTION_ORDER[idx + 1]
            next_title = owner_guide.SECTIONS[next_key][0] if next_key in owner_guide.SECTIONS else next_key
            nav_row.append(InlineKeyboardButton(f"{next_title} ▶️", callback_data=f"guide:{next_key}"))
        keyboard.append(nav_row)

    return keyboard


async def guide_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/دليل / /guide — Owner DM-only. Structured operations guide."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    section = owner_guide.get_section("index")
    if not section:
        return
    title, body = section
    keyboard = _build_guide_keyboard("index")
    await update.message.reply_text(
        f"<b>{title}</b>\n\n{body}",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup(keyboard),
    )


async def guide_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle inline keyboard navigation for the owner guide."""
    query = update.callback_query
    if query is None or query.data is None:
        return

    if not (update.effective_user and auth_store.is_owner(update.effective_user.id)):
        await query.answer()
        return

    await query.answer()

    if not query.data.startswith("guide:"):
        return

    section_key = query.data[len("guide:"):]
    section = owner_guide.get_section(section_key)
    if not section:
        return

    title, body = section
    keyboard = _build_guide_keyboard(section_key)
    try:
        await query.edit_message_text(
            f"<b>{title}</b>\n\n{body}",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup(keyboard),
        )
    except Exception:  # log-exempt: best-effort guide card edit; stale message raises TgBadRequest
        pass


async def sendgroup_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle the 📢 إرسال للمجموعة button — publishes the pending DM action to CHAT_ID.

    The owner always confirms a public send explicitly. A failed Telegram
    delivery keeps the pending action and its button usable so the owner can
    retry; internal error text is logged but never sent to a private chat.
    """
    query = update.callback_query
    if query is None or update.effective_user is None:
        return

    owner_id = suggestion_store.load().get("owner_id")
    if update.effective_user.id != owner_id:
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return

    if context.user_data.get("pending_sendgroup_in_flight"):
        await query.answer("⏳ جارٍ الإرسال بالفعل.")
        return

    await query.answer()

    pending = context.user_data.get("pending_sendgroup")
    if not pending:
        try:
            await query.edit_message_reply_markup(reply_markup=None)
        except Exception:  # log-exempt: best-effort button removal; TgBadRequest on stale message is harmless
            pass
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="⚠️ انتهت صلاحية هذا الزر أو أُعيد تشغيل البوت.\nأعد تنفيذ الأمر وحاول مرة أخرى.",
        )
        return

    context.user_data["pending_sendgroup_in_flight"] = True
    try:
        ptype = pending.get("type", "text")

        if ptype == "text":
            await context.bot.send_message(
                chat_id=CHAT_ID,
                text=pending["text"],
                parse_mode=pending.get("parse_mode"),
            )

        elif ptype == "suggestions_open":
            category = pending.get("category")
            template_text = suggestion_store.build_template_text(category=category)
            sent = await context.bot.send_message(
                chat_id=CHAT_ID,
                text=template_text,
                parse_mode="HTML",
            )
            try:
                await context.bot.pin_chat_message(
                    chat_id=CHAT_ID,
                    message_id=sent.message_id,
                    disable_notification=False,
                )
            except Exception as _pin_err:
                logger.warning("sendgroup: could not pin suggestion template: %s", _pin_err)
            suggestion_store.open_suggestions(sent.message_id)
            logger.info("sendgroup: suggestions opened, template_id=%s, category=%s", sent.message_id, category)

        elif ptype == "close_suggestions":
            tmpl_id = suggestion_store.get_template_message_id()
            if tmpl_id:
                final_text = suggestion_store.build_final_summary()
                try:
                    await context.bot.edit_message_text(
                        chat_id=CHAT_ID,
                        message_id=tmpl_id,
                        text=final_text,
                        parse_mode="HTML",
                    )
                except Exception as _edit_err:
                    logger.warning("sendgroup: could not edit template on close: %s", _edit_err)
            count = len(suggestion_store.get_suggestions())
            await context.bot.send_message(
                chat_id=CHAT_ID,
                text=(
                    f"🔒 <b>تم إغلاق ترشيحات الكتب.</b>\n\n"
                    f"إجمالي الترشيحات: <b>{count}</b>"
                ),
                parse_mode="HTML",
            )

        elif ptype == "vote_poll":
            suggestions = suggestion_store.get_suggestions()
            if len(suggestions) < 2:
                await context.bot.send_message(
                    chat_id=query.message.chat_id,
                    text="⚠️ لا توجد ترشيحات كافية. أعد تشغيل /startvote.",
                )
                return
            options = [s["title"] for s in suggestions[: vote_store.MAX_POLL_OPTIONS]]
            truncated = len(suggestions) > vote_store.MAX_POLL_OPTIONS
            close_at = datetime.now(TIMEZONE) + timedelta(hours=vote_store.VOTE_DURATION_HOURS)

            poll_msg = await context.bot.send_poll(
                chat_id=CHAT_ID,
                question="📚 صوّت للكتاب الذي تريد قراءته",
                options=options,
                is_anonymous=True,
                allows_multiple_answers=False,
            )
            vote_store.start_vote(
                poll_id=poll_msg.poll.id,
                message_id=poll_msg.message_id,
                chat_id=CHAT_ID,
                options=options,
                close_at=close_at,
            )
            scheduler = context.application.bot_data.get("scheduler")
            if scheduler:
                scheduler.add_job(
                    auto_close_vote_job,
                    trigger="date",
                    run_date=close_at,
                    args=[context.bot, str(CHAT_ID), context.application],
                    id="vote_close_job",
                    replace_existing=True,
                )
            close_str = close_at.strftime("%Y-%m-%d %H:%M")
            note = (
                f"\n\n⚠️ <i>تم عرض أول {vote_store.MAX_POLL_OPTIONS} كتب فقط.</i>"
                if truncated else ""
            )
            await context.bot.send_message(
                chat_id=CHAT_ID,
                text=(
                    f"🗳️ <b>بدأ التصويت!</b>\n\n"
                    f"لكل عضو صوت واحد، ويمكن تغييره قبل انتهاء المدة.\n"
                    f"⏳ ينتهي التصويت تلقائياً في: <b>{close_str}</b>"
                    f"{note}"
                ),
                parse_mode="HTML",
            )
            logger.info(
                "sendgroup: vote poll sent, poll_id=%s, close_at=%s",
                poll_msg.poll.id, close_at,
            )

    except Exception as _exc:
        logger.exception("sendgroup_callback: failed to send to group")
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text=(
                "❌ تعذّر الإرسال للمجموعة. لم يُلغَ التأكيد؛ "
                "يمكنك المحاولة مرة أخرى من الزر نفسه."
            ),
        )
        return
    finally:
        context.user_data.pop("pending_sendgroup_in_flight", None)

    context.user_data.pop("pending_sendgroup", None)
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:  # log-exempt: best-effort button removal; TgBadRequest on stale message is harmless
        pass
    await context.bot.send_message(
        chat_id=query.message.chat_id,
        text="✅ تم الإرسال للمجموعة.",
    )


# ━━━ Roadmap system ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

async def auto_close_category_vote_job(bot, chat_id_str: str) -> None:
    """
    Scheduler job: stop the category-vote poll, tally results, and:
      - ok          → send proposed roadmap to owner DM for approval
      - tie         → send tie-resolution DM to owner
      - insufficient → send notification DM to owner with extend/manual options
    """
    if not roadmap_store.is_category_vote_active():
        return

    cv_chat_id, msg_id = roadmap_store.get_category_vote_poll_location()
    if msg_id is None:
        logger.error("auto_close_category_vote_job: no poll message_id")
        return

    try:
        stopped = await bot.stop_poll(chat_id=cv_chat_id or chat_id_str, message_id=msg_id)
    except Exception as e:
        logger.error("auto_close_category_vote_job: stop_poll failed: %s", e)
        return

    result = roadmap_store.close_category_vote()

    # ── Analytics: emit category_vote event ──────────────────────────────────
    _cv_snaps = roadmap_store.load().get("category_vote_history", [])
    if _cv_snaps:
        _cv = _cv_snaps[-1]
        analytics_store.append_event({
            "poll_type":        "category_vote",
            "cycle_number":     cycle_store.get_cycle_number(),
            "roadmap_counter":  _cv.get("roadmap_counter", 0),
            "roadmap_stage":    None,
            "book_title":       None,
            "started_at":       _cv.get("started_at", ""),
            "closed_at":        _cv.get("closed_at", ""),
            "participant_count": _cv.get("participant_count", 0),
            "extension_count":  _cv.get("extension_count", 0),
            "payload": {
                "options":               _cv.get("options", []),
                "final_ranked":          _cv.get("final_ranked", []),
                "total_selections":      _cv.get("total_selections", 0),
                "avg_choices_per_voter": _cv.get("avg_choices_per_voter", 0.0),
                "choice_distribution":   _cv.get("choice_distribution", {}),
            },
        })

    owner_id = suggestion_store.load().get("owner_id")
    if not owner_id:
        logger.warning("auto_close_category_vote_job: no owner_id — cannot send DM")
        return

    if result["status"] == "ok":
        categories = result["categories"]
        roadmap_store.set_pending_roadmap(categories)
        cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(categories))
        approve_markup = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ تفعيل الخارطة", callback_data="roadmap:approve"),
                InlineKeyboardButton("✏️ تعديل يدوي", callback_data="roadmap:manual"),
            ]
        ])
        try:
            await bot.send_message(
                chat_id=int(owner_id),
                text=(
                    f"🗺️ <b>نتيجة تصويت الخارطة</b>\n\n"
                    f"الخارطة المقترحة (4 تصنيفات):\n\n"
                    f"{cat_list}\n\n"
                    "هل تريد تفعيل هذه الخارطة؟"
                ),
                parse_mode="HTML",
                reply_markup=approve_markup,
            )
        except Exception as e:
            logger.error("auto_close_category_vote_job: failed to send approval DM: %s", e)

    elif result["status"] == "tie":
        confirmed = result.get("confirmed", [])
        tied = result.get("tied", [])
        conf_text = "\n".join(f"✅ {c}" for c in confirmed) if confirmed else ""
        tie_text  = "\n".join(f"⚖️ {c}" for c in tied)
        body = (
            (f"الفائزون المؤكدون:\n{conf_text}\n\n" if conf_text else "") +
            f"متعادل على المرتبة {result.get('tie_position', '؟')}:\n{tie_text}"
        )
        btns = [
            [InlineKeyboardButton("🕒 تمديد التصويت", callback_data="roadmap:extend_tie")],
            [
                InlineKeyboardButton(t, callback_data=f"roadmap:pick_tie:{i}")
                for i, t in enumerate(tied)
            ],
        ]
        try:
            await bot.send_message(
                chat_id=int(owner_id),
                text=f"⚖️ <b>تعادل في تصويت الخارطة</b>\n\n{body}\n\nاختر إجراءً:",
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup(btns),
            )
        except Exception as e:
            logger.error("auto_close_category_vote_job: failed to send tie DM: %s", e)

    elif result["status"] == "insufficient":
        cats = result.get("categories", [])
        cat_text = "\n".join(f"• {c}" for c in cats) if cats else "(لا شيء)"
        btns = [
            [InlineKeyboardButton("🕒 تمديد التصويت", callback_data="roadmap:extend_tie")],
            [InlineKeyboardButton("✏️ تعيين يدوي (/setroadmap)", callback_data="roadmap:manual")],
        ]
        try:
            await bot.send_message(
                chat_id=int(owner_id),
                text=(
                    f"⚠️ <b>تصويت الخارطة: أصوات غير كافية</b>\n\n"
                    f"التصنيفات التي حصلت على أصوات ({len(cats)}/4):\n{cat_text}\n\n"
                    "لا يمكن بناء الخارطة تلقائياً. اختر:"
                ),
                parse_mode="HTML",
                reply_markup=InlineKeyboardMarkup(btns),
            )
        except Exception as e:
            logger.error("auto_close_category_vote_job: failed to send insufficient DM: %s", e)

    logger.info("Category vote closed. status=%s", result["status"])


_ROADMAP_EMOJI_NUMS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣"]


def _roadmap_announcement_text(road_id: int, categories: list[str]) -> str:
    """Build the standardised group announcement for a newly activated roadmap."""
    cat_list = "\n".join(
        f"{_ROADMAP_EMOJI_NUMS[i]} {c}" for i, c in enumerate(categories)
    )
    return (
        f"🗺️ <b>تم اعتماد خارطة القراءة #{road_id}</b>\n\n"
        f"{cat_list}\n\n"
        "📚 سنبدأ الآن بالمرحلة الأولى، وسيتم فتح ترشيحات الكتب الخاصة بها قريبًا."
    )


async def approve_roadmap_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle roadmap:approve and roadmap:manual callbacks."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return
    owner_id = suggestion_store.load().get("owner_id")
    if update.effective_user.id != owner_id:
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return
    await query.answer()

    action = query.data
    data = roadmap_store.load()

    if action == "roadmap:approve":
        pending = data.get("pending_roadmap", [])
        if not pending:
            await query.edit_message_text("⚠️ لا توجد خارطة مقترحة.")
            return
        roadmap_store.activate(pending)
        road_id  = roadmap_store.get_roadmap_id()
        cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(pending))
        context.user_data["pending_sendgroup"] = {
            "type": "text",
            "text": _roadmap_announcement_text(road_id, pending),
            "parse_mode": "HTML",
        }
        await query.edit_message_text(
            f"✅ <b>تم تفعيل خارطة القراءة #{road_id}!</b>\n\n{cat_list}\n\n"
            "استخدم /opensuggestions لبدء الترشيحات.\n\n"
            "اضغط الزر أدناه لإعلام المجموعة:",
            parse_mode="HTML",
            reply_markup=_SENDGROUP_MARKUP,
        )
        logger.info("Roadmap #%d activated by owner.", road_id)

        # Notify owner if stage-0 category has postponed nominations waiting
        first_cat = pending[0] if pending else None
        if first_cat:
            postponed = postponed_store.get_for_category(first_cat)
            if postponed:
                postponed_store.mark_notified(first_cat)
                await context.bot.send_message(
                    chat_id=query.message.chat_id,
                    text=_postponed_dm_text(first_cat, postponed),
                    parse_mode="HTML",
                )

    elif action == "roadmap:manual":
        await query.edit_message_text(
            "✏️ استخدم /setroadmap لتعيين الخارطة يدوياً.\n\n"
            "أرسل الأمر مع 4 تصنيفات مرتبة، مثل:\n"
            "<code>/setroadmap\nالأدب\nالفكر والفلسفة والسير\nالتاريخ والحضارات والأساطير\nالعلوم والتقنية</code>",
            parse_mode="HTML",
        )


async def roadmap_tie_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle roadmap:extend_tie and roadmap:pick_tie:{index} callbacks."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return
    owner_id = suggestion_store.load().get("owner_id")
    if update.effective_user.id != owner_id:
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return
    await query.answer()

    action = query.data
    scheduler = context.application.bot_data.get("scheduler")

    if action == "roadmap:extend_tie":
        current_close = roadmap_store.get_category_vote_close_at() or datetime.now(TIMEZONE)
        new_close_at  = current_close + timedelta(hours=roadmap_store.CATEGORY_VOTE_DURATION_HOURS)

        # Create a NEW poll with only the tied options (original poll was stopped)
        pending_tie = roadmap_store.load().get("category_vote", {}).get("pending_tie", {})
        tied_options = pending_tie.get("tied", [])
        confirmed   = pending_tie.get("confirmed", [])

        if not tied_options:
            await query.edit_message_text("⚠️ بيانات التعادل غير متوفرة.")
            return

        try:
            poll_msg = await context.bot.send_poll(
                chat_id=CHAT_ID,
                question="⚖️ تصويت لحسم التعادل في خارطة القراءة",
                options=tied_options,
                is_anonymous=False,
                allows_multiple_answers=False,
            )
        except Exception as e:
            logger.error("roadmap_tie_callback: failed to send tiebreak poll: %s", e)
            await query.edit_message_text(f"❌ تعذّر إرسال استفتاء التعادل:\n{e}")
            return

        roadmap_store.extend_category_vote(new_close_at)
        roadmap_store.start_category_vote(
            poll_id=poll_msg.poll.id,
            message_id=poll_msg.message_id,
            chat_id=CHAT_ID,
            close_at=new_close_at,
            options=tied_options,
        )
        roadmap_store.load()["category_vote"]["pending_tie"] = {
            "confirmed": confirmed,
            "tied": tied_options,
            "tie_position": pending_tie.get("tie_position", 4),
        }

        if scheduler:
            scheduler.add_job(
                auto_close_category_vote_job,
                trigger="date",
                run_date=new_close_at,
                args=[context.bot, str(CHAT_ID)],
                id="category_vote_close_job",
                replace_existing=True,
            )

        close_str = new_close_at.strftime("%Y-%m-%d %H:%M")
        await context.bot.send_message(
            chat_id=CHAT_ID,
            text=f"⏳ <b>تمديد تصويت الخارطة — حسم التعادل</b>\n\nينتهي في: <b>{close_str}</b>",
            parse_mode="HTML",
        )
        await query.edit_message_text(
            f"✅ تم إرسال استفتاء حسم التعادل. ينتهي في: {close_str}"
        )
        logger.info("Category tie extended, new close: %s", new_close_at)

    elif action.startswith("roadmap:pick_tie:"):
        idx_str = action.split(":")[-1]
        try:
            idx = int(idx_str)
        except ValueError:
            return

        pending_tie = roadmap_store.load().get("category_vote", {}).get("pending_tie", {})
        tied_options = pending_tie.get("tied", [])
        if idx < 0 or idx >= len(tied_options):
            await query.edit_message_text("⚠️ اختيار غير صالح.")
            return

        picked = tied_options[idx]
        final_categories = roadmap_store.resolve_category_tie(picked)
        roadmap_store.set_pending_roadmap(final_categories)

        cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(final_categories))
        approve_markup = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ تفعيل الخارطة", callback_data="roadmap:approve"),
                InlineKeyboardButton("✏️ تعديل يدوي", callback_data="roadmap:manual"),
            ]
        ])
        await query.edit_message_text(
            f"✅ <b>تم اختيار:</b> {picked}\n\n"
            f"الخارطة المقترحة:\n{cat_list}\n\n"
            "هل تريد تفعيل هذه الخارطة؟",
            parse_mode="HTML",
            reply_markup=approve_markup,
        )
        logger.info("Category tie resolved by owner: picked '%s'", picked)


async def vote_tie_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle vote:extend_tie and vote:pick_tie:{index} callbacks."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return
    owner_id = suggestion_store.load().get("owner_id")
    if update.effective_user.id != owner_id:
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return
    await query.answer()

    action = query.data
    scheduler = context.application.bot_data.get("scheduler")

    if action == "vote:extend_tie":
        pending_tie = vote_store.load().get("pending_tie", {})
        tied_titles = pending_tie.get("tied_titles", [])

        if not tied_titles:
            await query.edit_message_text("⚠️ بيانات التعادل غير متوفرة.")
            return

        active_cat = roadmap_store.get_active_category()
        cat_q = f"({active_cat}) " if active_cat else ""
        close_at = datetime.now(TIMEZONE) + timedelta(hours=vote_store.VOTE_DURATION_HOURS)

        try:
            poll_msg = await context.bot.send_poll(
                chat_id=CHAT_ID,
                question=f"⚖️ حسم التعادل {cat_q}— صوّت لكتاب واحد",
                options=tied_titles,
                is_anonymous=True,
                allows_multiple_answers=False,
            )
        except Exception as e:
            logger.error("vote_tie_callback: failed to send tiebreak poll: %s", e)
            await query.edit_message_text(f"❌ تعذّر إرسال استفتاء التعادل:\n{e}")
            return

        vote_store.start_vote(
            poll_id=poll_msg.poll.id,
            message_id=poll_msg.message_id,
            chat_id=CHAT_ID,
            options=tied_titles,
            close_at=close_at,
        )

        if scheduler:
            scheduler.add_job(
                auto_close_vote_job,
                trigger="date",
                run_date=close_at,
                args=[context.bot, str(CHAT_ID), context.application],
                id="vote_close_job",
                replace_existing=True,
            )

        close_str = close_at.strftime("%Y-%m-%d %H:%M")
        await context.bot.send_message(
            chat_id=CHAT_ID,
            text=f"⏳ <b>تمديد التصويت — حسم التعادل</b>\n\nينتهي في: <b>{close_str}</b>",
            parse_mode="HTML",
        )
        await query.edit_message_text(
            f"✅ تم إرسال استفتاء حسم التعادل. ينتهي في: {close_str}"
        )
        logger.info("Book vote tie extended, new close: %s", close_at)

    elif action.startswith("vote:pick_tie:"):
        idx_str = action.split(":")[-1]
        try:
            idx = int(idx_str)
        except ValueError:
            return

        pending_tie = vote_store.load().get("pending_tie", {})
        tied_titles = pending_tie.get("tied_titles", [])
        if idx < 0 or idx >= len(tied_titles):
            await query.edit_message_text("⚠️ اختيار غير صالح.")
            return

        winner = tied_titles[idx]
        vote_store.set_winner(winner)

        # Store runner-ups as stage candidates
        all_results = vote_store.get_results()
        runner_ups = [
            {"title": r["title"], "votes": r["votes"], "rank": r["rank"]}
            for r in all_results
            if r["title"] != winner
        ]
        roadmap_store.set_stage_candidates(runner_ups)

        # ── Analytics: emit book_vote event (tie resolved manually) ──────────
        _bv_data  = vote_store.load()
        _bv_total = sum(r["votes"] for r in all_results)
        analytics_store.append_event({
            "poll_type":        "book_vote",
            "cycle_number":     cycle_store.get_cycle_number(),
            "roadmap_counter":  roadmap_store.get_roadmap_id(),
            "roadmap_stage":    roadmap_store.get_current_stage(),
            "book_title":       winner,
            "started_at":       _bv_data.get("started_at", ""),
            "closed_at":        datetime.now(TIMEZONE).isoformat(),
            "participant_count": _bv_total,
            "extension_count":  _bv_data.get("extension_count", 0),
            "payload": {
                "winner":        winner,
                "was_tie":       True,
                "final_ranked":  all_results,
                "total_votes":   _bv_total,
                "options_count": len(all_results),
            },
        })

        # Start the reading cycle
        try:
            cycle_store.start_cycle(winner)
        except ValueError:  # log-exempt: ValueError means a cycle is already active; skip silently
            pass
        # Reset per-member progress for the new cycle before exporting.
        progress_store.reset()
        # Synchronise Companion: tie resolved, new book started
        asyncio.create_task(_auto_export_context("book_started_tie"))

        active_cat = roadmap_store.get_active_category()
        winner_text = vote_store.build_winner_text(winner, category=active_cat)
        context.user_data["pending_sendgroup"] = {
            "type": "text",
            "text": winner_text,
            "parse_mode": "HTML",
        }
        await query.edit_message_text(
            f"✅ <b>تم اختيار:</b> {_html.escape(winner)}\n\nاضغط الزر لإعلام المجموعة:",
            parse_mode="HTML",
            reply_markup=_SENDGROUP_MARKUP,
        )
        logger.info("Book tie resolved by owner: picked '%s'", winner)


async def startroadmap_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/startroadmap — begin a new category vote to establish the next reading roadmap.
    Owner DM only.
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    status = roadmap_store.get_status()

    # If a proposed roadmap is awaiting approval, resend it
    if status == "pending_approval":
        pending = roadmap_store.load().get("pending_roadmap", [])
        if pending:
            cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(pending))
            markup = InlineKeyboardMarkup([
                [
                    InlineKeyboardButton("✅ تفعيل الخارطة", callback_data="roadmap:approve"),
                    InlineKeyboardButton("✏️ تعديل يدوي", callback_data="roadmap:manual"),
                ]
            ])
            await update.message.reply_text(
                f"🗺️ <b>خارطة مقترحة في انتظار الموافقة</b>\n\n{cat_list}\n\n"
                "هل تريد تفعيلها؟",
                parse_mode="HTML",
                reply_markup=markup,
            )
            return

    # Block if a roadmap is currently active (not completed)
    if status == "active":
        display = roadmap_store.get_roadmap_display()
        cat_list = "\n".join(
            f"{'✅' if s['state'] == 'completed' else '📍' if s['state'] == 'active' else '⬜'} {s['category']}"
            for s in display
        )
        await update.message.reply_text(
            f"🗺️ <b>خارطة القراءة نشطة بالفعل</b>\n\n{cat_list}\n\n"
            "أكمل الخارطة الحالية أولاً.",
            parse_mode="HTML",
        )
        return

    # Block if a category vote is already active
    if roadmap_store.is_category_vote_active():
        close_at = roadmap_store.get_category_vote_close_at()
        close_str = close_at.strftime("%Y-%m-%d %H:%M") if close_at else "غير محدد"
        await update.message.reply_text(
            f"ℹ️ يوجد تصويت خارطة نشط بالفعل.\nينتهي في: {close_str}"
        )
        return

    # Reset for new roadmap (preserves counter + grace_used)
    roadmap_store.reset_for_new_roadmap()

    # Send category vote poll to the group (Primary Categories + Roadmap Themes)
    options = roadmap_store.ALL_VOTE_OPTIONS
    close_at = datetime.now(TIMEZONE) + timedelta(hours=roadmap_store.CATEGORY_VOTE_DURATION_HOURS)

    try:
        poll_msg = await context.bot.send_poll(
            chat_id=CHAT_ID,
            question="🗺️ صوّت لتصنيفات خارطة القراءة القادمة (اختر حتى 4)",
            options=options,
            is_anonymous=False,
            allows_multiple_answers=True,
        )
    except Exception as e:
        logger.error("startroadmap: failed to send poll: %s", e)
        await update.message.reply_text("❌ تعذّر إرسال الاستفتاء. يرجى المحاولة مرة أخرى.")
        return

    roadmap_store.start_category_vote(
        poll_id=poll_msg.poll.id,
        message_id=poll_msg.message_id,
        chat_id=CHAT_ID,
        close_at=close_at,
        options=options,
    )

    scheduler = context.application.bot_data.get("scheduler")
    if scheduler:
        scheduler.add_job(
            auto_close_category_vote_job,
            trigger="date",
            run_date=close_at,
            args=[context.bot, str(CHAT_ID)],
            id="category_vote_close_job",
            replace_existing=True,
        )

    close_str = close_at.strftime("%Y-%m-%d %H:%M")
    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": (
            f"🗺️ <b>بدأ تصويت خارطة القراءة!</b>\n\n"
            f"صوّت بحد أقصى {roadmap_store.MAX_CATEGORY_CHOICES} تصنيفات.\n"
            f"⏳ ينتهي التصويت في: <b>{close_str}</b>"
        ),
        "parse_mode": "HTML",
    }
    await update.message.reply_text(
        f"✅ تم إرسال استفتاء الخارطة.\n\nينتهي في: {close_str}\n\n"
        "اضغط الزر لإعلام المجموعة:",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("startroadmap: category vote sent, close_at=%s", close_at)


async def setroadmap_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/setroadmap — manually set the reading roadmap (4 categories). Owner DM only.
    Usage:
        /setroadmap
        الأدب
        الفكر والفلسفة والسير
        التاريخ والحضارات والأساطير
        العلوم والتقنية
    """
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    raw = update.message.text or ""
    body = re.sub(r"^/setroadmap\S*\s*", "", raw, flags=re.IGNORECASE).strip()

    if not body:
        cats_list = "\n".join(f"• {c}" for c in roadmap_store.ALL_VOTE_OPTIONS)
        await update.message.reply_text(
            "🗺️ <b>تعيين خارطة القراءة يدوياً</b>\n\n"
            "أرسل الأمر مع 4 تصنيفات (سطر لكل تصنيف):\n\n"
            "<code>/setroadmap\nتصنيف 1\nتصنيف 2\nتصنيف 3\nتصنيف 4</code>\n\n"
            f"التصنيفات والمواضيع المعتمدة:\n{cats_list}",
            parse_mode="HTML",
        )
        return

    raw_lines = [ln.strip() for ln in body.splitlines() if ln.strip()]
    validated: list[str] = []
    unrecognized: list[str] = []
    for line in raw_lines:
        match = roadmap_store.find_approved_category(line)
        if match:
            validated.append(match)
        else:
            unrecognized.append(line)

    if unrecognized:
        cats_list = "\n".join(f"• {c}" for c in roadmap_store.ALL_VOTE_OPTIONS)
        await update.message.reply_text(
            f"⚠️ تصنيفات غير معروفة:\n"
            + "\n".join(f"• {u}" for u in unrecognized)
            + f"\n\nالتصنيفات والمواضيع المعتمدة:\n{cats_list}",
            parse_mode="HTML",
        )
        return

    if len(validated) != roadmap_store.ROADMAP_SIZE:
        await update.message.reply_text(
            f"⚠️ يجب تحديد {roadmap_store.ROADMAP_SIZE} تصنيفات بالضبط.\n"
            f"تم إدخال: {len(validated)}"
        )
        return

    # Warn + confirm if a roadmap is already active
    if roadmap_store.get_status() == "active":
        context.user_data["setroadmap_pending"] = validated
        cat_preview = "\n".join(f"{i+1}. {c}" for i, c in enumerate(validated))
        markup = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ تأكيد الاستبدال", callback_data="setroadmap:confirm"),
                InlineKeyboardButton("❌ إلغاء", callback_data="setroadmap:cancel"),
            ]
        ])
        await update.message.reply_text(
            f"⚠️ <b>توجد خارطة قراءة نشطة حالياً.</b>\n\n"
            f"الخارطة الجديدة:\n{cat_preview}\n\n"
            "هل تريد استبدال الخارطة الحالية؟",
            parse_mode="HTML",
            reply_markup=markup,
        )
        return

    # Apply immediately
    roadmap_store.activate(validated)
    road_id = roadmap_store.get_roadmap_id()
    cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(validated))
    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": _roadmap_announcement_text(road_id, validated),
        "parse_mode": "HTML",
    }
    await update.message.reply_text(
        f"✅ <b>تم تعيين خارطة القراءة #{road_id}.</b>\n\n{cat_list}\n\n"
        "استخدم /opensuggestions لبدء الترشيحات.\n\n"
        "اضغط الزر لإعلام المجموعة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("Roadmap #%d set manually by owner: %s", road_id, validated)


async def setroadmap_confirm_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle setroadmap:confirm and setroadmap:cancel callbacks."""
    query = update.callback_query
    if query is None or update.effective_user is None:
        return
    owner_id = suggestion_store.load().get("owner_id")
    if update.effective_user.id != owner_id:
        await query.answer("⛔ هذا الزر للمالك فقط.")
        return
    await query.answer()

    if query.data == "setroadmap:cancel":
        context.user_data.pop("setroadmap_pending", None)
        await query.edit_message_text("❌ تم إلغاء الاستبدال. الخارطة الحالية لا تزال نشطة.")
        return

    validated = context.user_data.pop("setroadmap_pending", None)
    if not validated:
        await query.edit_message_text("⚠️ انتهت صلاحية الطلب. أعد تشغيل /setroadmap.")
        return

    roadmap_store.activate(validated)
    road_id = roadmap_store.get_roadmap_id()
    cat_list = "\n".join(f"{i+1}. {c}" for i, c in enumerate(validated))
    context.user_data["pending_sendgroup"] = {
        "type": "text",
        "text": _roadmap_announcement_text(road_id, validated),
        "parse_mode": "HTML",
    }
    await query.edit_message_text(
        f"✅ <b>تم استبدال الخارطة. الخارطة الجديدة #{road_id}:</b>\n\n{cat_list}\n\n"
        "اضغط الزر لإعلام المجموعة:",
        parse_mode="HTML",
        reply_markup=_SENDGROUP_MARKUP,
    )
    logger.info("Roadmap #%d activated via setroadmap:confirm by owner.", road_id)


async def votestatus_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """/votestatus — full operational snapshot: roadmap state + any active votes. Owner DM only."""
    if update.message is None or update.effective_user is None:
        return
    if not _is_owner_dm(update):
        await _redirect_to_dm(update)
        return

    def _fmt_dt(iso: str | None) -> str:
        if not iso:
            return "—"
        try:
            dt = datetime.fromisoformat(iso)
            return dt.strftime("%Y-%m-%d %H:%M")
        except Exception:
            return iso

    def _status_ar(s: str) -> str:
        return {
            "none":                   "لا شيء",
            "active":                 "نشط ✅",
            "pending_approval":       "بانتظار الموافقة ⏳",
            "completed":              "مكتملة 🏁",
            "closed":                 "مغلق",
            "awaiting_tie_resolution": "تعادل معلّق ⚖️",
        }.get(s, s)

    lines: list[str] = ["📊 <b>حالة النظام</b>", ""]

    # ── Roadmap block (always shown) ──────────────────────────────────────
    rm_status   = roadmap_store.get_status()
    rm_id       = roadmap_store.get_roadmap_id()
    active_cat  = roadmap_store.get_active_category()
    rm_data     = roadmap_store.load()
    current_stage = rm_data.get("current_stage", 0)
    roadmap_list  = rm_data.get("roadmap", [])

    lines.append("🗺️ <b>الخارطة</b>")
    id_str = f" #{rm_id}" if rm_id else ""
    lines.append(f"الحالة: {_status_ar(rm_status)}{id_str}")

    if rm_status == "active" and roadmap_list:
        total = len(roadmap_list)
        lines.append(f"المرحلة: {current_stage + 1} من {total}")
        lines.append(f"التصنيف الحالي: {active_cat or '—'}")
        # Show all stages with icons
        stage_lines = []
        for i, cat in enumerate(roadmap_list):
            if i < current_stage:
                icon = "✅"
            elif i == current_stage:
                icon = "▶️"
            else:
                icon = "⬜"
            stage_lines.append(f"  {icon} {i+1}. {cat}")
        lines.extend(stage_lines)

    elif rm_status == "pending_approval":
        pending = rm_data.get("pending_roadmap", [])
        if pending:
            lines.append("الخارطة المقترحة:")
            for i, cat in enumerate(pending):
                lines.append(f"  {i+1}. {cat}")

    elif rm_status == "completed":
        lines.append(f"جميع المراحل الـ{len(roadmap_list)} مكتملة.")
        lines.append("استخدم /startroadmap لخارطة جديدة.")

    elif rm_status == "none":
        grace_available = roadmap_store.is_grace_available()
        if grace_available:
            lines.append("فترة الانتقال متاحة (جولة واحدة مسموحة)")
        else:
            lines.append("استخدم /startroadmap لبدء خارطة القراءة.")

    # Stage candidates
    candidates = roadmap_store.get_stage_candidates()
    if candidates:
        lines.append(f"مرشحو التخطي المتبقون: {len(candidates)}")

    lines.append("")

    # ── Category vote block ───────────────────────────────────────────────
    cv = roadmap_store.get_category_vote_status()
    cv_status = cv["status"]
    if cv_status not in ("none", "closed"):
        lines.append("🗳️ <b>تصويت الخارطة</b>")
        lines.append(f"الحالة: {_status_ar(cv_status)}")
        lines.append(f"الخيارات: {cv['options_count']}")
        lines.append(f"المصوتون: {cv['answers_count']}")
        lines.append(f"بدأ: {_fmt_dt(cv.get('started_at'))}")
        orig = _fmt_dt(cv.get('original_close_at'))
        curr = _fmt_dt(cv.get('current_close_at'))
        lines.append(f"ينتهي: {curr}")
        ext = cv.get('extension_count', 0)
        if ext:
            lines.append(f"تمديدات: {ext}  (أصلي: {orig})")
        if cv.get("pending_tie"):
            pt = cv["pending_tie"]
            confirmed = pt.get("confirmed", [])
            tied = pt.get("tied", [])
            lines.append(f"⚖️ تعادل: {len(confirmed)} مؤكد + {len(tied)} متعادل")
            lines.append("  المتعادلون: " + "، ".join(tied))
        lines.append("")

    # ── Book vote block ───────────────────────────────────────────────────
    bv = vote_store.get_vote_status()
    bv_status = bv["status"]
    if bv_status != "none":
        lines.append("📚 <b>تصويت الكتب</b>")
        lines.append(f"الحالة: {_status_ar(bv_status)}")
        lines.append(f"الخيارات: {bv['options_count']}")
        lines.append(f"بدأ: {_fmt_dt(bv.get('started_at'))}")
        curr_bv = _fmt_dt(bv.get('current_close_at'))
        orig_bv = _fmt_dt(bv.get('original_close_at'))
        if bv_status == "closed":
            winner = vote_store.get_winner()
            if winner:
                lines.append(f"الفائز: <b>{_html.escape(winner)}</b>")
        else:
            lines.append(f"ينتهي: {curr_bv}")
            ext_bv = bv.get('extension_count', 0)
            if ext_bv:
                lines.append(f"تمديدات: {ext_bv}  (أصلي: {orig_bv})")
        if bv.get("pending_tie"):
            tied_titles = bv["pending_tie"].get("tied_titles", [])
            lines.append("⚖️ تعادل بين: " + "، ".join(tied_titles))
        lines.append("")

    # ── Reading cycle block ───────────────────────────────────────────────
    cy_status = cycle_store.get_status()
    current_book = cycle_store.get_current_book()
    if cy_status == "active" and current_book:
        lines.append("📖 <b>دورة القراءة</b>")
        lines.append(f"الكتاب الحالي: <b>{current_book['title']}</b>")
        lines.append(f"بدأت: {_fmt_dt(current_book.get('started_at'))}")
        lines.append("")

    # Trim trailing blank lines
    while lines and lines[-1] == "":
        lines.pop()

    await update.message.reply_text("\n".join(lines), parse_mode="HTML")


async def _register_commands(bot: Bot) -> None:
    """
    Register bot commands with Telegram so they appear in the chat command menu.

    Scope architecture (highest → lowest priority):
      BotCommandScopeChat(owner_user_id)            → owner DM — DM-only admin commands
      BotCommandScopeChatAdministrators(group_id)   → group admins — reading management
      BotCommandScopeChat(group_id)                 → all members — reading commands

    The owner's DM command list is completely separate from the group.
    No admin/maintenance command appears anywhere in the group experience.
    """
    try:
        try:
            chat_id = int(CHAT_ID)
        except (ValueError, TypeError):
            chat_id = CHAT_ID  # type: ignore[assignment]

        # ── Member commands (reading group only — visible to everyone) ────────────
        member_cmds = [
            BotCommand("plan",     "لوحة دورة القراءة — الكتب والإنجازات والإحصائيات"),
            BotCommand("schedule", "جدول القراءة الكامل مع لوحة التقدم"),
            BotCommand("done",     "سجّل إنجازك بعد انتهاء جدول القراءة"),
            BotCommand("ask",      "اسأل الذكاء الاصطناعي (/اجب) — أي سؤال"),
            BotCommand("progress", "سجّل صفحتك الحالية لتجنب الحرق (/قرأت)"),
        ]

        # ── Group admin commands (reading flow only — all lifecycle ops moved to owner DM) ──
        group_admin_cmds = [
            # Phase 3 — Dashboard
            BotCommand("plan",             "٤ — لوحة دورة القراءة والإحصائيات"),
            # Phase 4 — Schedule display
            BotCommand("schedule",         "٥ — عرض الجدول ولوحة التقدم"),
            # Phase 5 — Participation
            BotCommand("readpoll",         "٦ — إنشاء استفتاء المشاركة للكتاب الحالي"),
            # Phase 7 — Completion registration
            BotCommand("done",             "٧ — تسجيل الإنجاز بعد انتهاء الجدول"),
            # Phase 8 — Evaluation
            BotCommand("rate",             "٨ — إنشاء استفتاء تقييم للكتاب الحالي"),
            # AI & reference
            BotCommand("ask",              "اسأل الذكاء الاصطناعي (/اجب) — أي سؤال"),
        ]

        # ── Owner DM commands (private DM with the bot only — invisible in group) ─
        owner_dm_cmds = [
            BotCommand("guide",            "📖 دليل المالك — مركز العمليات"),
            # Training workspace — just type in DM to ask the AI
            BotCommand("session",          "📚 بدء أو إدارة جلسة تدريب خاصة"),
            BotCommand("rateanswer",       "تقييم آخر إجابة (لوحة مفاتيح تلقائية)"),
            BotCommand("savefaq",          "حفظ آخر إجابة كـ FAQ في قاعدة المعرفة"),
            BotCommand("addnote",          "إضافة ملاحظة للكتاب الحالي في قاعدة المعرفة"),
            BotCommand("addclub",          "إضافة معلومة عامة للنادي في قاعدة المعرفة"),
            BotCommand("listnotes",        "عرض ملاحظات قاعدة المعرفة"),
            BotCommand("deletenote",       "حذف ملاحظة بالمعرّف"),
            BotCommand("mystats",          "إحصائيات أداء الإجابات"),
            BotCommand("prepbook",         "⚙️ إعادة توليد الورقة المرجعية للكتاب الحالي"),
            # Roadmap lifecycle
            BotCommand("startroadmap",     "🗺️ بدء تصويت خارطة القراءة"),
            BotCommand("setroadmap",       "🗺️ تعيين خارطة القراءة يدوياً"),
            BotCommand("votestatus",       "حالة النظام الكاملة — الخارطة والتصويت والدورة"),
            # Suggestions lifecycle
            BotCommand("opensuggestions",  "١ — فتح ترشيحات الكتب الجديدة"),
            BotCommand("closesuggestions", "٢ — إغلاق الترشيحات"),
            BotCommand("synctemplate",     "🔄 تحديث قالب الترشيحات المثبّت"),
            BotCommand("reviewsuggestions", "٢.٥ — مراجعة الترشيحات قبل التصويت"),
            BotCommand("postponed",        "📦 إرسال إعلان الكتب المؤجَّلة"),
            # Voting lifecycle
            BotCommand("extendvote",       "٣+ — تمديد التصويت 24 ساعة"),
            BotCommand("pollinsights",     "📊 تحليل تصويت الفئات الحالي"),
            BotCommand("clubreport",       "📋 تقرير النادي — ملخص استراتيجي شامل"),
            BotCommand("reflect",          "💬 كتابة ملاحظة قراءة اليوم لفتح النقاش"),
            BotCommand("suggestionsoverview", "📚 نظرة عامة على الترشيحات"),
            # Reading cycle management
            BotCommand("completebook",     "٩ — إنهاء الكتاب والانتقال لتصنيف التالي"),
            BotCommand("skipbook",         "تخطي الكتاب الحالي (يبقى في نفس التصنيف)"),
            # Metadata & schedule
            BotCommand("newschedule",      "رفع جدول قراءة جديد"),
            BotCommand("setmeta",          "حفظ بيانات الكتاب الحالي"),
            BotCommand("setnotice",        "إضافة إشعار مؤقت في الجدول"),
            BotCommand("clearnotice",      "إزالة الإشعار المؤقت"),
            # Maintenance
            BotCommand("addmanager",       "إضافة مدير للبوت"),
            BotCommand("removemanager",    "إزالة صلاحيات مدير"),
            BotCommand("backup",           "نسخة احتياطية ZIP لجميع البيانات"),
            BotCommand("restore",          "♻️ استعادة من نسخة احتياطية — أرسل ZIP مع /restore كتعليق"),
        ]

        # Register member scope for the specific group
        try:
            await bot.set_my_commands(member_cmds, scope=BotCommandScopeChat(chat_id=chat_id))
            logger.info("Command menu: member scope registered (%d commands)", len(member_cmds))
        except Exception as e:
            logger.warning("Command menu: failed to set member scope: %s", e)

        # Register group admin scope (reading management commands only)
        try:
            await bot.set_my_commands(
                group_admin_cmds,
                scope=BotCommandScopeChatAdministrators(chat_id=chat_id),
            )
            logger.info("Command menu: group admin scope registered (%d commands)", len(group_admin_cmds))
        except Exception as e:
            logger.warning("Command menu: failed to set group admin scope: %s", e)

        # Register owner scopes — two separate scopes needed:
        #   1. BotCommandScopeChatMember(group, owner) → caps what owner sees IN THE GROUP to
        #      group_admin_cmds only (highest-priority scope; overrides ChatAdministrators).
        #   2. BotCommandScopeChat(owner_user_id) → sets owner's private DM menu to owner_dm_cmds.
        try:
            owner_id = suggestion_store.load().get("owner_id")
        except Exception as exc:  # log-exempt: non-fatal; owner scopes simply not registered
            logger.warning("Command menu: failed to load owner_id — owner scopes skipped: %s", exc)
            owner_id = None
        if owner_id:
            # 1 — owner's view inside the group (must not show DM-only commands)
            try:
                await bot.set_my_commands(
                    group_admin_cmds,
                    scope=BotCommandScopeChatMember(chat_id=chat_id, user_id=int(owner_id)),
                )
                logger.info(
                    "Command menu: owner-in-group scope registered for user %s (%d commands)",
                    owner_id, len(group_admin_cmds),
                )
            except Exception as e:
                logger.warning("Command menu: failed to set owner-in-group scope: %s", e)

            # 2 — owner's private DM with the bot (DM-only admin commands)
            try:
                await bot.set_my_commands(
                    owner_dm_cmds,
                    scope=BotCommandScopeChat(chat_id=int(owner_id)),
                )
                logger.info(
                    "Command menu: owner DM scope registered for user %s (%d commands)",
                    owner_id, len(owner_dm_cmds),
                )
            except Exception as e:
                logger.warning("Command menu: failed to set owner DM scope: %s", e)
        else:
            logger.info(
                "Command menu: owner_id not yet known — owner scopes will be registered "
                "after ownership is established via the group."
            )
    except Exception as exc:
        logger.warning("Command menu: unexpected registration failure: %s", exc)


async def _check_store_health(app) -> None:
    """
    Called once at startup after the bot is initialized.
    If any store failed to parse its JSON file on load, DMs the owner
    with a list of the affected stores so they can investigate and run /backup.
    """
    try:
        import suggestion_store as _ss
        import auth_store as _as
        import cycle_store as _cs
        import schedule_store as _sch
        import book_store as _bs
        import poll_store as _ps
        import rating_store as _rs
        import roadmap_store as _ros
        import discussion_store as _ds
        import completion_store as _cos
        corrupt = [
            name
            for name, mod in [
                ("suggestion_store",  _ss),
                ("auth_store",        _as),
                ("cycle_store",       _cs),
                ("schedule_store",    _sch),
                ("book_store",        _bs),
                ("poll_store",        _ps),
                ("rating_store",      _rs),
                ("roadmap_store",     _ros),
                ("discussion_store",  _ds),
                ("completion_store",  _cos),
            ]
            if mod.is_corrupt()
        ]
        if not corrupt:
            return
        logger.error("STARTUP: corrupt stores detected: %s", corrupt)
        owner_id = auth_store.get_owner_id()
        if not owner_id:
            logger.error("STARTUP: no owner registered — cannot DM about corrupt stores")
            return
        stores_list = "\n".join(f"• <code>{n}</code>" for n in corrupt)
        msg = (
            "⚠️ <b>تحذير: ملفات بيانات تالفة</b>\n\n"
            f"فشل تحميل المخازن التالية عند بدء تشغيل البوت:\n{stores_list}\n\n"
            "تم الاستعادة إلى القيم الافتراضية الفارغة. قد تكون البيانات مفقودة.\n"
            "يُنصح بإرسال /backup فوراً ومراجعة الملفات يدوياً."
        )
        try:
            await app.bot.send_message(chat_id=owner_id, text=msg, parse_mode="HTML")
        except Exception as exc:
            logger.error("STARTUP: failed to DM owner %s about corrupt stores: %s", owner_id, exc)
    except Exception as exc:
        logger.error("STARTUP: store health check failed: %s", exc)


async def main() -> None:
    if not BOT_TOKEN:
        raise ValueError("TELEGRAM_BOT_TOKEN is not set.")
    if not CHAT_ID:
        raise ValueError("TELEGRAM_CHAT_ID is not set.")

    init_gemini()

    app = Application.builder().token(BOT_TOKEN).build()

    # ── Owner DM commands (admin, maintenance, guide — DM-only) ──────────────
    app.add_handler(CommandHandler("guide", guide_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/دليل(\s|$)"), guide_command))
    app.add_handler(CallbackQueryHandler(guide_callback, pattern=r"^guide:"))
    app.add_handler(CallbackQueryHandler(sendgroup_callback, pattern=r"^sendgroup$"))
    app.add_handler(CommandHandler("addmanager", addmanager_command))
    app.add_handler(CommandHandler("removemanager", removemanager_command))
    app.add_handler(CommandHandler("backup", backup_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/نسخة(\s|$)"), backup_command))
    app.add_handler(CommandHandler("restore", restore_command))
    app.add_handler(
        MessageHandler(
            filters.Document.ALL & filters.CaptionRegex(r"^/(restore|استعادة)(\s|$)"),
            restore_command,
        )
    )

    # ── Roadmap system ─────────────────────────────────────────────────────────
    app.add_handler(CommandHandler("startroadmap", startroadmap_command))
    app.add_handler(CommandHandler("setroadmap",   setroadmap_command))
    app.add_handler(CommandHandler("votestatus",   votestatus_command))
    app.add_handler(CallbackQueryHandler(approve_roadmap_callback,   pattern=r"^roadmap:(approve|manual)$"))
    app.add_handler(CallbackQueryHandler(roadmap_tie_callback,       pattern=r"^roadmap:(extend_tie|pick_tie:\d+)$"))
    app.add_handler(CallbackQueryHandler(vote_tie_callback,          pattern=r"^vote:(extend_tie|pick_tie:\d+)$"))
    app.add_handler(CallbackQueryHandler(setroadmap_confirm_callback, pattern=r"^setroadmap:(confirm|cancel)$"))

    # ── Suggestion system ──────────────────────────────────────────────────────
    app.add_handler(CommandHandler("opensuggestions",   opensuggestions_command))
    app.add_handler(CommandHandler("closesuggestions",  closesuggestions_command))
    app.add_handler(CommandHandler("synctemplate",      synctemplate_command))
    app.add_handler(CommandHandler("reviewsuggestions",  reviewsuggestions_command))
    app.add_handler(CallbackQueryHandler(rev2_callback,  pattern=r"^rev2:(approve|postpone|remove):\d+$"))
    app.add_handler(CommandHandler("postponed", sendpostponedannouncement_command))

    # ── Voting system ──────────────────────────────────────────────────────────
    app.add_handler(CommandHandler("extendvote", extendvote_command))
    app.add_handler(CommandHandler("pollinsights",       pollinsights_command))
    app.add_handler(CommandHandler("clubreport",         clubreport_command))
    app.add_handler(CommandHandler("reflect", reflect_command))
    app.add_handler(CommandHandler("suggestionsoverview", suggestionsoverview_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/الطابور(?:@\S+)?(\s|$)"), plan_command))

    # ── Reading cycle ──────────────────────────────────────────────────────────
    app.add_handler(CommandHandler("completebook", completebook_command))
    app.add_handler(CommandHandler("prepbook",     prepbook_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/قرأت(?:@\S+)?(\s|$)"), progress_command))
    app.add_handler(CommandHandler("progress",     progress_command))
    # Phase 4a — knowledge base & interaction log (owner DM only)
    app.add_handler(CommandHandler("addnote",      addnote_command))
    app.add_handler(CommandHandler("addclub",      addclub_command))
    app.add_handler(CommandHandler("listnotes",    listnotes_command))
    app.add_handler(CommandHandler("deletenote",   deletenote_command))
    app.add_handler(CommandHandler("rateanswer",   rateanswer_command))
    app.add_handler(CallbackQueryHandler(rateanswer_callback, pattern=r"^rateanswer:(correct|partial|incorrect)$"))
    app.add_handler(CommandHandler("savefaq",      savefaq_command))
    app.add_handler(CommandHandler("mystats",      mystats_command))
    # Phase 4b — DM training workspace (owner DM only)
    app.add_handler(CommandHandler("session",      session_command))
    app.add_handler(CommandHandler("skipbook", skipbook_command))
    app.add_handler(CommandHandler("setmeta", setmeta_command))
    # Stage 4 (Migration Roadmap): per-member reading progress (group command)
    # Community Context Contract export (owner DM only)
    app.add_handler(CommandHandler("exportcontext", exportcontext_command))
    app.add_handler(CommandHandler("readpoll", readpoll_command))
    app.add_handler(CommandHandler("rate", rate_command))
    app.add_handler(CommandHandler("done", done_command))
    app.add_handler(PollAnswerHandler(handle_poll_answer))
    # Group 0: suggestion template detector (fast, returns early for non-matches)
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND, suggestion_message_handler),
        group=0,
    )

    # ── Core commands ──────────────────────────────────────────────────────────
    app.add_handler(CommandHandler("newschedule", newschedule_command))
    app.add_handler(CommandHandler("setnotice", setnotice_command))
    app.add_handler(CommandHandler("clearnotice", clearnotice_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/اجب(?:@\S+)?(\s|$)"), answer_command))
    app.add_handler(CommandHandler("ask", answer_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/الخطة(?:@\S+)?(\s|$)"), plan_command))
    app.add_handler(MessageHandler(filters.Regex(r"^/الجدول(?:@\S+)?(\s|$)"), jadwal_command))
    # ASCII aliases — these appear in the Telegram command menu (Arabic names cannot)
    app.add_handler(CommandHandler("plan",     plan_command))
    app.add_handler(CommandHandler("schedule", jadwal_command))
    app.add_handler(CommandHandler("queue",    plan_command))
    app.add_handler(
        MessageHandler(
            filters.PHOTO & filters.CaptionRegex(r"^/غلاف$"),
            set_cover_command,
        )
    )
    app.add_handler(
        MessageHandler(
            filters.PHOTO & filters.CaptionRegex(r"^/غلاف_جدول"),
            set_schedule_cover_command,
        )
    )
    # Group -1: owner DM training workspace — runs before the group-0 suggestion
    # handler and the group-1 AI auto-reply handler so it can mark the message
    # as processed before either of them sees it.  Scoped to private chats only
    # so it never interferes with group message flow.
    app.add_handler(
        MessageHandler(
            filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE,
            owner_dm_chat_handler,
        ),
        group=-1,
    )

    # Group 1: AI auto-reply — runs after group 0 regardless of whether
    # suggestion_message_handler handled the message
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND, book_auto_reply_handler),
        group=1,
    )

    # Group 2: Passive session listener — accumulates literary/cultural discussion
    # into the rolling context buffer. Never replies. Runs last so it never
    # interferes with any other handler.
    app.add_handler(
        MessageHandler(
            filters.TEXT & ~filters.COMMAND & filters.ChatType.GROUPS,
            session_listener,
        ),
        group=2,
    )

    scheduler = AsyncIOScheduler(timezone=TIMEZONE)

    # Daily automatic backup — 03:00 Riyadh time, sent to owner DM
    scheduler.add_job(
        _auto_backup_job,
        trigger="cron",
        hour=3, minute=0,
        args=[app.bot],
        id="daily_backup",
        replace_existing=True,
    )

    # Takbeer is the sole schedule sender. WAQT's rhythm scheduler starts its
    # cultural discussion in the evening and intentionally has no morning
    # reading-plan job.
    scheduler.add_job(
        daily_schedule_reminder_job,
        trigger="cron",
        hour=8, minute=0,
        args=[app.bot],
        id="daily_schedule_reminder",
        replace_existing=True,
    )

    # Restore category vote close job if a category vote was active when the bot last stopped
    if roadmap_store.is_category_vote_active():
        cv_close_at = roadmap_store.get_category_vote_close_at()
        cv_chat_id, _ = roadmap_store.get_category_vote_poll_location()
        if cv_close_at:
            cv_run_at = max(cv_close_at, datetime.now(TIMEZONE) + timedelta(seconds=5))
            scheduler.add_job(
                auto_close_category_vote_job,
                trigger="date",
                run_date=cv_run_at,
                args=[app.bot, str(cv_chat_id or CHAT_ID)],
                id="category_vote_close_job",
                replace_existing=True,
            )
            logger.info("Restored category vote close job — scheduled for %s", cv_run_at)

    # Restore book vote close job if a vote was active when the bot last stopped
    if vote_store.is_active():
        close_at = vote_store.get_close_at()
        v_chat_id, _ = vote_store.get_poll_location()
        if close_at and v_chat_id:
            # If the scheduled close time is already past, close immediately on start
            run_at = max(close_at, datetime.now(TIMEZONE) + timedelta(seconds=5))
            scheduler.add_job(
                auto_close_vote_job,
                trigger="date",
                run_date=run_at,
                args=[app.bot, v_chat_id, app],
                id="vote_close_job",
                replace_existing=True,
            )
            logger.info("Restored vote close job — scheduled for %s", run_at)

    # Make the scheduler available to command handlers
    app.bot_data["scheduler"] = scheduler

    me = await app.bot.get_me()
    logger.info("Bot started: @%s | AI voice replies: enabled", me.username)

    scheduler.start()
    logger.info("Scheduler started — Takbeer daily schedule and vote auto-close jobs active")

    await app.initialize()
    await _register_commands(app.bot)
    await _check_store_health(app)
    await app.start()
    await app.updater.start_polling()

    try:
        await asyncio.Event().wait()
    except (KeyboardInterrupt, SystemExit):
        logger.info("Bot stopping...")
    finally:
        scheduler.shutdown()
        await app.updater.stop()
        await app.stop()
        await app.shutdown()


if __name__ == "__main__":
    kill_existing_instances()
    write_pid()
    asyncio.run(main())
