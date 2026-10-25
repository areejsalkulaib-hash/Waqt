from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from typing import Any

import pytest


MODULE_PATH = Path(__file__).parents[1] / "polling_owner_route_drill.py"
SPEC = importlib.util.spec_from_file_location("polling_owner_route_drill", MODULE_PATH)
assert SPEC and SPEC.loader
drill = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = drill
SPEC.loader.exec_module(drill)


class FakeGitHub:
    def __init__(self, duplicate_on_create: bool = False, refuse_close: bool = False):
        self.issues: list[dict[str, Any]] = []
        self.next_number = 1
        self.duplicate_on_create = duplicate_on_create
        self.refuse_close = refuse_close

    def request(
        self, method: str, path: str, payload: dict[str, Any] | None = None
    ) -> Any:
        payload = payload or {}
        if method == "GET" and path.startswith("/issues?"):
            return [issue.copy() for issue in self.issues if issue["state"] == "open"]
        if method == "GET" and path.startswith("/issues/"):
            return self._issue(int(path.split("/")[2])).copy()
        if method == "POST" and path == "/issues":
            count = 2 if self.duplicate_on_create else 1
            created = None
            for _ in range(count):
                created = {
                    "number": self.next_number,
                    "title": payload["title"],
                    "body": payload["body"],
                    "state": "open",
                    "comments": [],
                }
                self.next_number += 1
                self.issues.append(created)
            return created
        if method == "POST" and path.endswith("/comments"):
            number = int(path.split("/")[2])
            self._issue(number)["comments"].append(payload["body"])
            return {}
        if method == "PATCH" and path.startswith("/issues/"):
            number = int(path.split("/")[2])
            if not self.refuse_close:
                self._issue(number)["state"] = payload["state"]
            return {}
        raise AssertionError(f"Unexpected request: {method} {path}")

    def _issue(self, number: int) -> dict[str, Any]:
        return next(issue for issue in self.issues if issue["number"] == number)


def test_drill_deduplicates_and_closes_both_stable_keys() -> None:
    client = FakeGitHub()

    drill.run_drill(client)

    assert len(client.issues) == 2
    assert {issue["state"] for issue in client.issues} == {"closed"}
    assert all(len(issue["comments"]) == 2 for issue in client.issues)
    assert {key for key in drill.INCIDENT_KEYS} == {
        "telegram-polling:takbeer-bot",
        "telegram-polling:adapter-bot",
    }


def test_drill_fails_when_a_key_creates_duplicate_incidents() -> None:
    with pytest.raises(drill.DrillFailure, match="expected one"):
        drill.run_drill(FakeGitHub(duplicate_on_create=True))


def test_drill_fails_when_recovery_does_not_close_incident() -> None:
    with pytest.raises(drill.DrillFailure, match="recovery left"):
        drill.run_drill(FakeGitHub(refuse_close=True))


def test_payload_is_clearly_synthetic_and_contains_no_telegram_credentials() -> None:
    for key in drill.INCIDENT_KEYS:
        payload = f"{drill.issue_title(key)}\n{drill.issue_body(key)}"
        assert "SYNTHETIC DRILL" in payload
        assert "TELEGRAM_BOT_TOKEN" not in payload
        assert "TELEGRAM_ADAPTER_BOT_TOKEN" not in payload
        assert "api.telegram.org" not in payload


class DelayedListGitHub(FakeGitHub):
    def __init__(self, *, never_visible: bool = False):
        super().__init__()
        self.hidden_reads = 0
        self.never_visible = never_visible

    def request(self, method: str, path: str, payload=None) -> Any:
        if method == "GET" and path.startswith("/issues?"):
            if self.never_visible or self.hidden_reads:
                self.hidden_reads = max(0, self.hidden_reads - 1)
                return []
        result = super().request(method, path, payload)
        if method == "POST" and path == "/issues":
            self.hidden_reads = 3
        return result


def test_read_after_create_lag_does_not_duplicate_or_orphan_issues(monkeypatch) -> None:
    monkeypatch.setattr(drill.time, "sleep", lambda _: None)
    client = DelayedListGitHub()
    drill.run_drill(client)
    assert len(client.issues) == 2
    assert all(i["state"] == "closed" for i in client.issues)
    assert all(len(i["comments"]) == 2 for i in client.issues)


def test_visibility_timeout_still_closes_created_issue_by_number(monkeypatch) -> None:
    monkeypatch.setattr(drill.time, "sleep", lambda _: None)
    client = DelayedListGitHub(never_visible=True)
    with pytest.raises(drill.DrillFailure, match="did not reflect"):
        drill.run_drill(client)
    assert len(client.issues) == 2
    assert all(i["state"] == "closed" for i in client.issues)