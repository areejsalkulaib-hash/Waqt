#!/usr/bin/env python3
"""Exercise the GitHub owner route for Telegram polling incidents.

This script intentionally uses only GitHub's workflow token. It never reads or
needs either Telegram bot token.
"""

from __future__ import annotations

import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from typing import Any


INCIDENT_KEYS = (
    "telegram-polling:takbeer-bot",
    "telegram-polling:adapter-bot",
)
DRILL_MARKER = "WAQT polling owner-route synthetic drill"
API_VERSION = "2022-11-28"


class DrillFailure(RuntimeError):
    pass


@dataclass
class GitHubClient:
    repository: str
    token: str
    api_url: str = "https://api.github.com"

    def request(
        self, method: str, path: str, payload: dict[str, Any] | None = None
    ) -> Any:
        body = None if payload is None else json.dumps(payload).encode()
        request = urllib.request.Request(
            f"{self.api_url}/repos/{self.repository}{path}",
            data=body,
            method=method,
            headers={
                "Accept": "application/vnd.github+json",
                "Authorization": f"Bearer {self.token}",
                "X-GitHub-Api-Version": API_VERSION,
                "User-Agent": "waqt-polling-owner-route-drill",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                return json.load(response)
        except urllib.error.HTTPError as error:
            detail = error.read().decode(errors="replace")
            raise DrillFailure(
                f"GitHub API {method} {path} failed with {error.code}: {detail}"
            ) from error


def issue_title(incident_key: str) -> str:
    return f"[SYNTHETIC DRILL] Telegram polling degraded — {incident_key}"


def issue_body(incident_key: str) -> str:
    return "\n".join(
        (
            f"**{DRILL_MARKER}**",
            "",
            "- notification: `telegram_polling_degraded`",
            f"- incidentKey: `{incident_key}`",
            "- state: `synthetic_degraded`",
            "",
            "This scheduled credential-free drill verifies that the external owner "
            "destination opens one incident, deduplicates a repeat signal, and "
            "closes it on recovery. It does not stop or contact either Telegram bot.",
        )
    )


def list_open_drill_issues(client: GitHubClient, incident_key: str) -> list[dict[str, Any]]:
    query = urllib.parse.urlencode({"state": "open", "per_page": 100})
    issues = client.request("GET", f"/issues?{query}")
    title = issue_title(incident_key)
    return [
        issue
        for issue in issues
        if "pull_request" not in issue
        and issue.get("title") == title
        and DRILL_MARKER in issue.get("body", "")
    ]


def emit_degraded(client: GitHubClient, incident_key: str) -> None:
    matches = list_open_drill_issues(client, incident_key)
    if len(matches) > 1:
        raise DrillFailure(
            f"{incident_key} has {len(matches)} open synthetic incidents; expected one"
        )
    if not matches:
        client.request(
            "POST",
            "/issues",
            {"title": issue_title(incident_key), "body": issue_body(incident_key)},
        )
        return
    client.request(
        "POST",
        f"/issues/{matches[0]['number']}/comments",
        {
            "body": (
                f"**{DRILL_MARKER} repeated degraded signal**\n\n"
                "`notification=telegram_polling_degraded` "
                f"`incidentKey={incident_key}` `state=synthetic_degraded`"
            )
        },
    )


def emit_healthy(client: GitHubClient, incident_key: str) -> None:
    matches = list_open_drill_issues(client, incident_key)
    for issue in matches:
        client.request(
            "POST",
            f"/issues/{issue['number']}/comments",
            {
                "body": (
                    f"**{DRILL_MARKER} recovery signal**\n\n"
                    "`notification=telegram_polling_healthy` "
                    f"`incidentKey={incident_key}` `state=synthetic_healthy`"
                )
            },
        )
        client.request(
            "PATCH",
            f"/issues/{issue['number']}",
            {"state": "closed", "state_reason": "completed"},
        )


def run_drill(client: GitHubClient) -> None:
    failures: list[str] = []
    for incident_key in INCIDENT_KEYS:
        try:
            emit_degraded(client, incident_key)
            emit_degraded(client, incident_key)
            open_after_repeat = list_open_drill_issues(client, incident_key)
            if len(open_after_repeat) != 1:
                raise DrillFailure(
                    f"{incident_key} repeat produced {len(open_after_repeat)} open "
                    "synthetic incidents; expected one"
                )
        except Exception as error:
            failures.append(f"{incident_key} degraded/deduplication: {error}")
        finally:
            try:
                emit_healthy(client, incident_key)
                remaining = list_open_drill_issues(client, incident_key)
                if remaining:
                    raise DrillFailure(
                        f"{incident_key} recovery left {len(remaining)} incident(s) open"
                    )
            except Exception as error:
                failures.append(f"{incident_key} recovery: {error}")
    if failures:
        raise DrillFailure("\n".join(failures))


def main() -> int:
    repository = os.environ.get("GITHUB_REPOSITORY", "")
    token = os.environ.get("GITHUB_TOKEN", "")
    if not repository or not token:
        print("GITHUB_REPOSITORY and GITHUB_TOKEN are required", file=sys.stderr)
        return 2
    try:
        run_drill(GitHubClient(repository=repository, token=token))
    except DrillFailure as error:
        print(f"Owner-route synthetic drill failed:\n{error}", file=sys.stderr)
        return 1
    print("Owner-route synthetic drill passed for both polling incident keys.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())