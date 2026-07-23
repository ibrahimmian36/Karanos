"""Append-only run ledger, one JSON line per evaluation.

Census discipline carried over from the platform: every candidate is
recorded whether admitted or rejected, writes are flushed immediately so
a crash loses nothing, and nothing in the engine ever rewrites a line.
"""

from __future__ import annotations

import json
from datetime import UTC, datetime
from pathlib import Path


class Ledger:
    def __init__(self, path: Path) -> None:
        self.path = path
        path.parent.mkdir(parents=True, exist_ok=True)

    def append(
        self,
        problem: str,
        generation: int,
        program: str,
        score: float | None,
        witness: object,
        note: str,
    ) -> None:
        rec = {
            "at": datetime.now(UTC).isoformat(timespec="seconds"),
            "problem": problem,
            "generation": generation,
            "score": score,
            "witness": witness,
            "note": note,
            "program": program,
        }
        with self.path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
            fh.flush()

    def lines(self) -> list[dict[str, object]]:
        if not self.path.exists():
            return []
        return [
            json.loads(line)
            for line in self.path.read_text(encoding="utf-8").splitlines()
            if line.strip()
        ]
