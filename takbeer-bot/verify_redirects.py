"""
verify_redirects.py — offline verification of Takbeer/WAQT command ownership.

The old version of this check expected Takbeer to redirect migrated commands
to the WAQT adapter.  The current contract is different: migrated commands
must not be registered or advertised by Takbeer at all, while reading-domain
aliases remain registered here.

The verifier parses bot.py without importing it and checks:
  1. WAQT-owned commands are absent from Takbeer's handlers.
  2. WAQT-owned commands are absent from Takbeer's Telegram menus.
  3. Takbeer's reading aliases are still registered.
  4. Takbeer's WAQT ownership contract matches the adapter's canonical
     command registries, including poll commands.

Run with:
    python3 takbeer-bot/verify_redirects.py
"""

from __future__ import annotations

import ast
import pathlib
import re
import sys

BOT_PY = pathlib.Path(__file__).parent / "bot.py"
WAQT_ADAPTER_TS = (
    BOT_PY.parent.parent
    / "artifacts"
    / "api-server"
    / "src"
    / "runtime"
    / "adapters"
    / "telegram"
    / "bot.ts"
)

# This is Takbeer's ownership contract.  verify_source() cross-checks it
# against the adapter's TypeScript registries below, so adding an adapter
# command without updating this contract fails the standalone verifier.
WAQT_ONLY_COMMANDS = frozenset(
    {
        # Arabic command forms from the WAQT adapter.
        "وقت",
        "مقال",
        "ذاكرة",
        "لماذا",
        "ساهم",
        "حوار",
        "كتاب",
        "مساعدة",
        # ASCII aliases registered by the adapter.
        "waqt",
        "article",
        "articlerevise",
        "memory",
        "why",
        "contribute",
        "dialogue",
        "book",
        "checklist",
        "help",
        # Poll commands are dispatched from the adapter's separate poll map.
        "startvote",
    }
)

TAKBEER_READING_ALIASES = frozenset(
    {
        "الطابور",
        "الخطة",
        "الجدول",
        "قرأت",
        "plan",
        "schedule",
        "queue",
        "progress",
        "done",
    }
)

# The command name is followed by Telegram suffix/argument matching in the
# handler regexes, for example ^/قرأت(?:@\S+)?(\s|$).
_COMMAND_REGEX = re.compile(r"^\^/([^\\?(\s]+)")
_TS_COMMAND_KEY = re.compile(r"""["'](/[^"']+)["']\s*:""")
_TS_MENU_COMMAND = re.compile(r"""command\s*:\s*["']([^"']+)["']""")


def _typescript_registry_body(
    source: str,
    registry_name: str,
    opening: str,
    closing_pattern: str,
) -> str:
    """Extract one static TypeScript registry body without executing it."""
    pattern = re.compile(
        rf"\bconst\s+{re.escape(registry_name)}\b.*?=\s*"
        rf"{re.escape(opening)}(?P<body>.*?){closing_pattern}",
        re.DOTALL,
    )
    match = pattern.search(source)
    if match is None:
        raise ValueError(f"could not find WAQT adapter registry {registry_name}")
    return match.group("body")


def canonical_waqt_commands(source: str) -> set[str]:
    """Extract all command names from the adapter's canonical registries.

    COMMANDS contains the normal text commands, BOT_COMMANDS contains the
    Telegram menu names, and POLL_COMMANDS contains commands dispatched
    through the separate poll path.  The adapter source is deliberately
    parsed rather than imported so this verifier remains offline and does not
    require Node dependencies or credentials.
    """
    commands: set[str] = set()

    for registry_name in ("COMMANDS", "POLL_COMMANDS"):
        body = _typescript_registry_body(source, registry_name, "{", r"\};")
        commands.update(
            match.lstrip("/") for match in _TS_COMMAND_KEY.findall(body)
        )

    menu_body = _typescript_registry_body(
        source,
        "BOT_COMMANDS",
        "[",
        r"\](?:\s+as\s+const)?;",
    )
    commands.update(
        match.lstrip("/") for match in _TS_MENU_COMMAND.findall(menu_body)
    )
    return commands


def _literal_string(node: ast.AST) -> str | None:
    """Return a string literal's value, or None for dynamic expressions."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    return None


def _call_name(node: ast.Call) -> str | None:
    """Return the final name of a simple call such as CommandHandler(...)."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None


def registered_handler_commands(source: str) -> set[str]:
    """Extract command names dispatched by Takbeer's handler registrations."""
    tree = ast.parse(source, filename=str(BOT_PY))
    commands: set[str] = set()

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue

        call_name = _call_name(node)
        if call_name == "CommandHandler" and node.args:
            command = _literal_string(node.args[0])
            if command:
                commands.add(command.lstrip("/"))
            continue

        if call_name != "Regex" or not node.args:
            continue
        pattern = _literal_string(node.args[0])
        if pattern is None:
            continue
        match = _COMMAND_REGEX.match(pattern)
        if match:
            commands.add(match.group(1))

    return commands


def menu_commands(source: str) -> set[str]:
    """Extract command names advertised through Telegram BotCommand menus."""
    tree = ast.parse(source, filename=str(BOT_PY))
    commands: set[str] = set()

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or _call_name(node) != "BotCommand":
            continue
        if not node.args:
            continue
        command = _literal_string(node.args[0])
        if command:
            commands.add(command.lstrip("/"))

    return commands


def verify_source(source: str, waqt_source: str | None = None) -> list[str]:
    """Return ownership violations found in Takbeer and WAQT source strings."""
    registered = registered_handler_commands(source)
    advertised = menu_commands(source)
    errors: list[str] = []

    if waqt_source is None:
        try:
            waqt_source = WAQT_ADAPTER_TS.read_text(encoding="utf-8")
        except OSError as exc:
            errors.append(
                f"Unable to read WAQT adapter command registry at "
                f"{WAQT_ADAPTER_TS}: {exc}"
            )
            waqt_source = ""

    if waqt_source:
        try:
            canonical = canonical_waqt_commands(waqt_source)
        except ValueError as exc:
            errors.append(f"Unable to read WAQT adapter command registry: {exc}")
        else:
            missing_from_contract = canonical - WAQT_ONLY_COMMANDS
            if missing_from_contract:
                errors.append(
                    "WAQT adapter commands missing from Takbeer's ownership "
                    "contract: "
                    + ", ".join(sorted(missing_from_contract))
                )

            absent_from_adapter = WAQT_ONLY_COMMANDS - canonical
            if absent_from_adapter:
                errors.append(
                    "Takbeer's ownership contract contains commands absent "
                    "from WAQT's adapter registries: "
                    + ", ".join(sorted(absent_from_adapter))
                )

    handler_collisions = WAQT_ONLY_COMMANDS & registered
    if handler_collisions:
        errors.append(
            "WAQT-only commands found in Takbeer's handlers: "
            + ", ".join(sorted(handler_collisions))
        )

    menu_collisions = WAQT_ONLY_COMMANDS & advertised
    if menu_collisions:
        errors.append(
            "WAQT-only commands found in Takbeer's menus: "
            + ", ".join(sorted(menu_collisions))
        )

    missing_aliases = TAKBEER_READING_ALIASES - registered
    if missing_aliases:
        errors.append(
            "Takbeer's reading aliases are no longer registered: "
            + ", ".join(sorted(missing_aliases))
        )

    return errors


def main() -> None:
    print(f"\nTakbeer/WAQT command ownership verification — parsing {BOT_PY.name}\n")
    try:
        source = BOT_PY.read_text(encoding="utf-8")
        errors = verify_source(source)
    except (OSError, SyntaxError) as exc:
        print(f"  ✗  could not read or parse bot.py: {exc}")
        sys.exit(1)

    if errors:
        for error in errors:
            print(f"  ✗  {error}")
        print("\nFAILED — command ownership contract violated")
        sys.exit(1)

    print("  ✓  WAQT-only commands are absent from Takbeer's handlers and menus")
    print("  ✓  Takbeer's WAQT ownership contract matches the adapter registries")
    print("  ✓  Takbeer's reading aliases remain registered")
    print("\nPASSED — Takbeer/WAQT command ownership contract is intact")


if __name__ == "__main__":
    main()
