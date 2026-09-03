/**
 * Telegram Adapter — Runtime Bootstrap.
 *
 * Source of truth: WAQT Implementation Roadmap, Commit 009 (Telegram
 * Adapter Layer). Telegram is a pure interface/transport: this module's
 * only job is "receive a Telegram update, dispatch to a handler, send the
 * handler's text back" — it owns no domain state, no identity, no
 * authority of its own (those live in `identity.ts` / the services it
 * calls). It must never crash the api-server process: if
 * `TELEGRAM_ADAPTER_BOT_TOKEN` is missing, it logs a warning and stays off.
 *
 * Deliberately uses its own `TELEGRAM_ADAPTER_BOT_TOKEN` secret — the
 * takbeer-bot's token (see `runtime/config/secrets.ts`) must never be read
 * here.
 *
 * Commit 012 — Companion Facilitation Layer:
 * `parseAddressedMessage` performs deterministic pattern matching for
 * explicit name-address (`وقت،` / `يا وقت`) and @mention. This is pure
 * transport: pattern → route. No intent inference; no ambient scanning.
 * "Companion does not respond unless explicitly invited" (Architecture
 * Ch. 35, Silence is an architectural decision, Vision Principle 10).
 * Unaddressed messages are silently dropped — never routed to Companion.
 */
import { readOptionalSecret } from "../../config/secrets";
import { logger } from "../../observability/logger";
import { GENERIC_EXCEPTION_MESSAGE } from "../../../services/companion-intelligence/editorial-methodology";
import * as articleCommands from "../../../services/cultural-articles/commands";
import { evaluateCulturalArticle } from "../../../evaluation/cultural-article-evaluator";
import {
  TelegramClient,
  TelegramGetUpdatesConflictError,
  type TelegramMessage,
} from "./client";
import {
  markTelegramPollingActive,
  markTelegramPollingDisabled,
  markTelegramPollingOwnershipConflict,
  markTelegramPollingStarting,
  TELEGRAM_POLLING_RECOVERY_GUIDANCE,
} from "./polling-status";
import { captureAmbient, resolveThread, seedIfAbsent } from "./ambient-buffer";
import {
  // Reading domain (/الجدول, /الخطة, /قرأت, /done) is owned by the Takbeer bot.
  // handleSchedule, handlePlan, handleProgress, and handleDone have been
  // removed from handlers.ts.
  handleAsk,
  handleArticle,
  handleArticleRevision,
  handleBook,
  handleChecklist,
  handleContribute,
  handleDialogue,
  handleFacilitation,
  handleHelp,
  handleMemory,
  handleStartVote,
  handleWhy,
  type CommandHandler,
  type PollHandler,
} from "./handlers";

const COMMANDS: Record<string, CommandHandler> = {
  // Arabic commands — matched by the adapter's parseCommand.
  // Reading domain (/الجدول, /الخطة, /قرأت) is owned by the Takbeer bot.
  "/وقت": handleAsk,
  "/مقال": handleArticle,
  "/ذاكرة": handleMemory,
  "/لماذا": handleWhy,
  "/ساهم": handleContribute,
  "/حوار": handleDialogue,
  "/كتاب": handleBook,
  "/مساعدة": handleHelp,
  // ASCII aliases — Telegram requires these for the command menu (only
  // lowercase Latin letters, digits, and underscores are accepted by
  // the setMyCommands API). The Arabic names still work as typed commands.
  "/waqt": handleAsk,
  "/article": handleArticle,
  "/articlerevise": handleArticleRevision,
  "/memory": handleMemory,
  "/why": handleWhy,
  "/contribute": handleContribute,
  "/dialogue": handleDialogue,
  "/book": handleBook,
  "/checklist": handleChecklist,
  "/help": handleHelp,
};

/**
 * Commands registered in Telegram's command menu via setMyCommands.
 * Must use lowercase ASCII names (Telegram API constraint). Descriptions
 * are in Arabic with the Arabic command form shown in parentheses so
 * members always know both forms.
 */
const BOT_COMMANDS = [
  // Reading domain (schedule, plan, progress) is owned by the Takbeer bot.
  { command: "waqt",       description: "اسأل وقت (/وقت)" },
  { command: "book",       description: "بطاقة ثقافية لأي كتاب (/كتاب)" },
  { command: "article",    description: "مقال ثقافي من نقاش المجموعة (/مقال)" },
  { command: "articlerevise", description: "توجيه مراجعة لمسودة مقال" },
  { command: "memory",     description: "ذاكرة المجموعة (/ذاكرة)" },
  { command: "contribute", description: "أضف مساهمة ثقافية (/ساهم)" },
  { command: "why",        description: "لماذا نقرأ هذا الكتاب (/لماذا)" },
  { command: "checklist",  description: "قائمة جاهزية وقت" },
  { command: "help",       description: "قائمة الأوامر المتاحة (/مساعدة)" },
] as const;

/**
 * Commands that produce a Telegram poll rather than a text message.
 * Dispatched separately in `dispatch()` so `sendPoll` is called instead
 * of `sendMessage`.
 */
const POLL_COMMANDS: Record<string, PollHandler> = {
  "/startvote": handleStartVote,
};

/**
 * Arabic name-address patterns through which a member may explicitly
 * invite Companion into a conversation. Pure string matching — no ML,
 * no intent detection (both of those are forbidden in the adapter layer).
 *
 * "وقت،" / "وقت:" — the natural Arabic way of addressing before speaking
 * "يا وقت"        — the classical Arabic vocative form
 *
 * Commit 013 may add further patterns (e.g., @mention-based) without
 * changing this contract: every pattern must be an explicit address, not
 * an inference about whether the topic "deserves" a response.
 */
const BOT_ADDRESS_PATTERNS = ["وقت،", "وقت:", "يا وقت"];

const POLL_TIMEOUT_SECONDS = 30;

let client: TelegramClient | undefined;
let offset = 0;
let running = false;

function countCharacters(value: string): number {
  return Array.from(value).length;
}

/**
 * Poll handlers are typed, but their results can still be malformed at runtime
 * (for example after an upstream boundary changes). Keep invalid payloads out
 * of the Telegram client, whose API accepts a 1–300 character question and
 * 2–10 non-empty options of at most 100 characters each.
 */
function isValidPollPayload(
  poll: unknown,
): poll is { readonly question: string; readonly options: readonly string[] } {
  if (typeof poll !== "object" || poll === null) return false;

  const { question, options } = poll as {
    question?: unknown;
    options?: unknown;
  };

  return (
    typeof question === "string" &&
    question.trim().length > 0 &&
    countCharacters(question) <= 300 &&
    Array.isArray(options) &&
    options.length >= 2 &&
    options.length <= 10 &&
    options.every(
      (option) =>
        typeof option === "string" &&
        option.trim().length > 0 &&
        countCharacters(option) <= 100,
    )
  );
}

function parseCommand(text: string): { command: string; args: string } | undefined {
  const trimmed = text.trim();
  if (!trimmed.startsWith("/")) return undefined;
  const spaceIndex = trimmed.indexOf(" ");
  const rawCommand = spaceIndex === -1 ? trimmed : trimmed.slice(0, spaceIndex);
  const command = rawCommand.split("@")[0];
  const args = spaceIndex === -1 ? "" : trimmed.slice(spaceIndex + 1);
  return { command, args };
}

/**
 * Determines whether a non-command message is explicitly addressed to
 * Companion. Returns the content of the address (the question/request
 * after the name or @mention) if addressed, or `undefined` if not.
 *
 * This is the gatekeeper for "Companion does not respond unless invited":
 * only deterministic pattern match → non-undefined return value → route
 * to facilitation. Any message that does not match a pattern is ignored.
 */
function parseAddressedMessage(text: string): string | undefined {
  const trimmed = text.trim();

  for (const pattern of BOT_ADDRESS_PATTERNS) {
    if (trimmed.startsWith(pattern)) {
      return trimmed.slice(pattern.length).trim();
    }
  }

  return undefined;
}

/**
 * Recovers the reply chain for a message that invokes Companion. The direct
 * parent may predate this process, so seed it before walking the adapter-local
 * ambient graph.
 */
function reconstructReplyThread(
  chatId: number,
  replyToMessage: TelegramMessage | undefined,
): readonly string[] {
  if (!replyToMessage) return [];

  if (replyToMessage.text) {
    seedIfAbsent(
      chatId,
      replyToMessage.text,
      replyToMessage.message_id,
      replyToMessage.reply_to_message?.message_id,
    );
  }

  return resolveThread(chatId, replyToMessage.message_id);
}

function splitTelegramText(text: string, maxLength = 3900): readonly string[] {
  const chunks: string[] = [];
  let remaining = text.trim();
  while (remaining.length > maxLength) {
    let cut = remaining.lastIndexOf("\n\n", maxLength);
    if (cut < maxLength / 2) cut = remaining.lastIndexOf("\n", maxLength);
    if (cut < maxLength / 2) cut = maxLength;
    chunks.push(remaining.slice(0, cut).trim());
    remaining = remaining.slice(cut).trim();
  }
  if (remaining) chunks.push(remaining);
  return chunks;
}

async function sendLongMessage(
  telegramClient: TelegramClient,
  chatId: number,
  text: string,
): Promise<number | undefined> {
  let messageId: number | undefined;
  for (const chunk of splitTelegramText(text)) {
    messageId = (await telegramClient.sendMessage(chatId, chunk)).message_id;
  }
  return messageId;
}

function ownerReviewKeyboard(articleId: string) {
  return {
    inline_keyboard: [
      [{ text: "تقييم دستوري", callback_data: `article:evaluate:${articleId}` }],
      [{ text: "اعتماد النسخة", callback_data: `article:approve:${articleId}` }],
      [{ text: "إرسال للمجموعة", callback_data: `article:publish:${articleId}` }],
    ],
  } as const;
}

async function handleArticleCallback(
  telegramClient: TelegramClient,
  update: Awaited<ReturnType<TelegramClient["getUpdates"]>>[number],
): Promise<void> {
  const callback = update.callback_query;
  if (!callback?.data?.startsWith("article:")) return;
  const [, action, articleId] = callback.data.split(":");
  if (!action || !articleId) return;
  const actor = { kind: "ExternalRelationship", id: String(callback.from.id) };
  const sourceChatId = callback.message?.chat.id;

  try {
    if (action === "generate") {
      const view = await articleCommands.generateArticle({ id: articleId, actor });
      const draft = view.versions[0];
      if (!draft) throw new Error("Generated article has no draft version.");
      const ownerIdRaw = readOptionalSecret("TELEGRAM_ADAPTER_OWNER_ID");
      const ownerId = ownerIdRaw ? Number(ownerIdRaw) : NaN;
      if (Number.isFinite(ownerId)) {
        await telegramClient.sendMessage(
          ownerId,
          `مسودة خاصة للمراجعة — ${draft.title}\nمعرف المقال: ${articleId}`,
          ownerReviewKeyboard(articleId),
        );
        await sendLongMessage(telegramClient, ownerId, draft.content);
      }
      await telegramClient.answerCallbackQuery(
        callback.id,
        Number.isFinite(ownerId) ? "تم إرسال المسودة للمالك." : "تم إنشاء المسودة في مساحة المراجعة.",
      );
      if (sourceChatId !== undefined) {
        await telegramClient.sendMessage(
          sourceChatId,
          "تم إنشاء المسودة وإيداعها في مساحة المراجعة الخاصة. لن تُنشر قبل الاعتماد الصريح.",
        );
      }
      return;
    }

    if (action === "evaluate") {
      const view = await evaluateCulturalArticle({ id: articleId, actor });
      const evaluation = view.latestEvaluation;
      await telegramClient.answerCallbackQuery(callback.id, "اكتمل التقييم.");
      if (evaluation) {
        await telegramClient.sendMessage(
          callback.from.id,
          evaluation.overallPass
            ? "اجتازت النسخة التقييم الدستوري. القرار النهائي لك."
            : `اكتمل التقييم مع ملاحظات غير مانعة:\n${evaluation.warnings.join("\n")}`,
          ownerReviewKeyboard(articleId),
        );
      }
      return;
    }

    if (action === "approve") {
      await articleCommands.approveArticle({ id: articleId, actor });
      await telegramClient.answerCallbackQuery(callback.id, "تم اعتماد النسخة.");
      await telegramClient.sendMessage(
        callback.from.id,
        "تم اعتماد النسخة. النشر ما زال يحتاج إجراءً منفصلاً.",
        ownerReviewKeyboard(articleId),
      );
      return;
    }

    if (action === "publish") {
      const { view, publication } = await articleCommands.publishArticle({ id: articleId, actor });
      const draft = view.versions[0];
      const publicChatIdRaw = readOptionalSecret("TELEGRAM_ADAPTER_CHAT_ID");
      const publicChatId = publicChatIdRaw ? Number(publicChatIdRaw) : NaN;
      if (!draft || !Number.isFinite(publicChatId)) {
        throw new Error("Public group delivery is not configured.");
      }
      try {
        const messageId = await sendLongMessage(
          telegramClient,
          publicChatId,
          `مقال وقت رقم ${publication.articleNumber}\n\n${draft.title}\n\n${draft.content}`,
        );
        await articleCommands.recordTelegramDelivery(
          publication.id,
          "delivered",
          messageId ? String(messageId) : undefined,
        );
        await telegramClient.answerCallbackQuery(callback.id, "نُشر المقال في المجموعة.");
      } catch (error) {
        await articleCommands.recordTelegramDelivery(publication.id, "failed");
        throw error;
      }
    }
  } catch (err) {
    logger.error({ err, action, articleId }, "Telegram article callback failed");
    const statusCode = (err as { statusCode?: number }).statusCode;
    const userMessage =
      statusCode === 403
        ? "هذا الإجراء مخصص لمالك مساحة المقال."
        : statusCode === 409
          ? "لا يسمح وضع المقال الحالي بهذا الإجراء."
          : "تعذر تنفيذ الإجراء الآن. بقيت الحالة محفوظة ويمكن إعادة المحاولة.";
    await telegramClient.answerCallbackQuery(callback.id, userMessage).catch(() => undefined);
  }
}

async function dispatch(
  telegramClient: TelegramClient,
  update: Awaited<ReturnType<TelegramClient["getUpdates"]>>[number],
): Promise<void> {
  if (update.callback_query) {
    await handleArticleCallback(telegramClient, update);
    return;
  }

  const message = update.message;
  if (!message?.text) return;

  // 1. Slash command — dispatch to registered command handler.
  const parsed = parseCommand(message.text);
  if (parsed) {
    // 1a. Poll commands send a Telegram poll instead of a text reply.
    const pollHandler = POLL_COMMANDS[parsed.command];
    if (pollHandler) {
      try {
        const poll = await pollHandler(parsed.args, message.from?.id, message.chat.id);
        if (poll) {
          if (!isValidPollPayload(poll)) {
            throw new Error("Poll handler returned an invalid poll payload");
          }
          await telegramClient.sendPoll(message.chat.id, poll.question, poll.options);
        }
      } catch (err) {
        logger.error({ err, command: parsed.command }, "Telegram adapter poll handler failed");
        await telegramClient.sendMessage(message.chat.id, "حدث خطأ أثناء إنشاء التصويت.").catch(() => undefined);
      }
      return;
    }

    const handler = COMMANDS[parsed.command];
    if (!handler) return;
    try {
      const replyThread =
        handler === handleAsk
          ? reconstructReplyThread(message.chat.id, message.reply_to_message)
          : undefined;
      const reply = await handler(
        parsed.args,
        message.from?.id,
        message.chat.id,
        replyThread,
      );
      if (typeof reply === "string") {
        await telegramClient.sendMessage(message.chat.id, reply);
      } else if (reply?.kind === "article-reading") {
        await telegramClient.sendMessage(message.chat.id, reply.text, {
          inline_keyboard: [[{
            text: "توليد المقال الثقافي",
            callback_data: `article:generate:${reply.articleId}`,
          }]],
        });
      }
    } catch (err) {
      logger.error({ err, command: parsed.command }, "Telegram adapter command handler failed");
      await telegramClient.sendMessage(message.chat.id, GENERIC_EXCEPTION_MESSAGE).catch(() => undefined);
    }
    return;
  }

  // 2. Explicit name-address or @mention — route to Companion facilitation.
  //    Pure pattern matching; never intent inference (adapter = transport only).
  const addressedContent = parseAddressedMessage(message.text);
  if (addressedContent !== undefined) {
    try {
      const replyThread = reconstructReplyThread(
        message.chat.id,
        message.reply_to_message,
      );

      const reply = await handleFacilitation(
        addressedContent,
        message.from?.id,
        message.chat.id,
        replyThread,
      );
      // Empty reply means the address had no content — maintain silence.
      if (reply && typeof reply === "string") {
        await telegramClient.sendMessage(message.chat.id, reply);
      }
    } catch (err) {
      logger.error({ err }, "Telegram adapter facilitation handler failed");
      await telegramClient
        .sendMessage(message.chat.id, "حدث خطأ أثناء المعالجة.")
        .catch(() => undefined);
    }
    return;
  }

  // 3. Unaddressed message — capture for ephemeral ambient context (ADR-001),
  //    then maintain silence. Companion observes the conversation without
  //    responding (Vision Principle 10, Architecture Ch. 35). The buffer is
  //    non-addressable: no persistence, no entity, no UUID, no promotion path.
  //
  //    message_id and reply_to_message.message_id are stored alongside the
  //    text so resolveThread() can reconstruct reply chains when Companion
  //    is later addressed from inside that thread.
  captureAmbient(
    message.chat.id,
    message.text,
    message.message_id,
    message.reply_to_message?.message_id,
  );
}

async function pollLoop(telegramClient: TelegramClient): Promise<void> {
  while (running) {
    try {
      const updates = await telegramClient.getUpdates(offset, POLL_TIMEOUT_SECONDS);
      // A completed getUpdates request is the only event that clears an
      // ownership-conflict health alert. Starting a new loop is not enough.
      markTelegramPollingActive();
      for (const update of updates) {
        offset = update.update_id + 1;
        await dispatch(telegramClient, update);
      }
    } catch (err) {
      if (err instanceof TelegramGetUpdatesConflictError) {
        // Telegram has assigned this token's update stream to another process.
        // Safe recovery: stop that competing poller, or use a separate bot
        // token for each bot, then restart this adapter. Never keep retrying or
        // attempt to take ownership back: alternating getUpdates calls can make
        // group questions disappear unpredictably.
        running = false;
        if (client === telegramClient) client = undefined;
        markTelegramPollingOwnershipConflict();
        logger.error(
          {
            err,
            recovery: TELEGRAM_POLLING_RECOVERY_GUIDANCE,
          },
          "Telegram adapter polling stopped because another process owns getUpdates",
        );
        return;
      }
      logger.error({ err }, "Telegram adapter poll failed; retrying");
      await new Promise((resolve) => setTimeout(resolve, 5000));
    }
  }
}

/**
 * Starts the Telegram Adapter's long-poll loop. Idempotent, and never
 * throws — a missing/invalid token degrades to "adapter off" rather than
 * bringing down the rest of the api-server process.
 */
export function startTelegramAdapter(): void {
  if (running) return;

  const token = readOptionalSecret("TELEGRAM_ADAPTER_BOT_TOKEN");
  if (!token) {
    markTelegramPollingDisabled();
    logger.warn(
      "TELEGRAM_ADAPTER_BOT_TOKEN not configured — Telegram Adapter Layer is disabled.",
    );
    return;
  }

  client = new TelegramClient(token);
  markTelegramPollingStarting();
  running = true;
  void pollLoop(client);
  // Register the command menu with Telegram (fire-and-forget; does not
  // affect polling — a menu registration failure is logged as a warning
  // but never stops the adapter from operating).
  void client.setMyCommands(BOT_COMMANDS).catch((err) => {
    logger.warn({ err }, "Telegram command menu registration failed (non-fatal)");
  });
  logger.info("Telegram Adapter Layer started.");
}

/** Test-only: stops the poll loop. */
export function stopTelegramAdapter(): void {
  running = false;
  client = undefined;
}

/** Test-only: exposes the dispatch function so unit tests can drive it directly
 *  without spinning up the full poll loop or requiring real Telegram credentials.
 */
export { dispatch as _testOnlyDispatch };
export { pollLoop as _testOnlyPollLoop };

/** Test-only: controls the local polling-loop lifecycle. */
export function _testOnlySetPollingRunning(value: boolean): void {
  running = value;
}

/**
 * Test-only: exposes the COMMANDS registry so boundary tests can derive
 * handler coverage from the real runtime map rather than hardcoding command
 * names.  If a handler is added to or removed from COMMANDS, tests that
 * iterate this export automatically pick up the change.
 */
export { COMMANDS as _testOnlyCommands };
export { BOT_COMMANDS as _testOnlyBotCommands };
export { POLL_COMMANDS as _testOnlyPollCommands };
