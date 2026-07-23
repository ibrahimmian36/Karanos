"""Tier-2 probe: build a deeper Γ quotient and cross-check it against the
current table (docs/KAPLANSKY_GPU_PLAN.md, Tier 2).

Builds BallQuotient(tree, close) for Γ, times it, records peak RSS, then
compares ball counts radius-by-radius against the existing anchored
pickle (runs/gamma_ball.pickle). The comparison is the point: the deeper
closure must reproduce the shallower table's counts exactly on every
radius the current table calls converged (≤ 10). A mismatch at ≤ 8 means
the region radii Tier 1 now trusts were wrong — loud FAIL, nothing
written for downstream use. Counts at 11+ are reported as information
(the deeper close radius may legitimately merge more there).

Artifacts: runs/gamma_ball_t{tree}c{close}.pickle (only on PASS),
runs/tier2_probe.json (always), one ledger line.

Usage:  PYTHONPATH=src python scripts/tier2_build.py [--tree 13 --close 11]
Smoke:  PYTHONPATH=src python scripts/tier2_build.py --smoke   (~seconds)
"""

from __future__ import annotations

import argparse
import json
import pickle
import resource
import sys
import time
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "engine"))

from karanos_engine.groupball import BallQuotient  # noqa: E402
from karanos_engine.kaplansky import (  # noqa: E402
    ANCHOR_BALL4,
    ANCHOR_BALL6,
    GENERATORS,
    RELATOR_1,
    RELATOR_2,
)
from karanos_engine.ledger import Ledger  # noqa: E402


def peak_rss_mb() -> float:
    """Peak RSS of this process in MB (ru_maxrss is bytes on macOS, KB on Linux)."""
    raw = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return raw / (1024 * 1024) if sys.platform == "darwin" else raw / 1024


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tree", type=int, default=13)
    ap.add_argument("--close", type=int, default=11)
    ap.add_argument("--out", type=Path, default=Path("runs"))
    ap.add_argument(
        "--smoke",
        action="store_true",
        help="tiny build (tree 8, close 7), anchor check only — validates this script",
    )
    args = ap.parse_args()
    tree, close = (8, 7) if args.smoke else (args.tree, args.close)

    # Reference counts: the existing anchored table, if present. The two
    # published anchors are checked unconditionally either way.
    reference: dict[int, int] = {}
    ref_path = args.out / "gamma_ball.pickle"
    if not args.smoke and ref_path.exists():
        with ref_path.open("rb") as fh:
            current: BallQuotient = pickle.load(fh)  # noqa: S301 — own artifact
        reference = {r: len(current.ball(r)) for r in range(min(current.close_radius, 10) + 1)}
        del current
        print(f"reference counts from {ref_path}: {reference}")

    print(f"building Γ quotient: tree={tree}, close={close} …", flush=True)
    t0 = time.perf_counter()
    quotient = BallQuotient(GENERATORS, [RELATOR_1, RELATOR_2], tree, close)
    build_s = time.perf_counter() - t0
    counts = {r: len(quotient.ball(r)) for r in range(min(tree - 1, close + 1) + 1)}
    print(f"built in {build_s:.0f}s, peak RSS {peak_rss_mb():.0f} MB; counts: {counts}")

    failures: list[str] = []
    if counts.get(4) != ANCHOR_BALL4:
        failures.append(f"B(4)={counts.get(4)} != anchor {ANCHOR_BALL4}")
    if counts.get(6) != ANCHOR_BALL6:
        failures.append(f"B(6)={counts.get(6)} != anchor {ANCHOR_BALL6}")
    # Cross-check against the current table: hard requirement through 8
    # (the Tier-1 trust boundary), informational at 9–10.
    infos: list[str] = []
    for r, expected in sorted(reference.items()):
        got = counts.get(r)
        if got is None:
            continue
        if got != expected and r <= 8:
            failures.append(f"B({r})={got} != current table {expected} — Tier-1 trust broken")
        elif got != expected:
            infos.append(f"B({r})={got} vs current {expected} (deeper close merged more)")

    result = {
        "at": datetime.now(UTC).isoformat(timespec="seconds"),
        "tree": tree,
        "close": close,
        "build_seconds": round(build_s, 1),
        "peak_rss_mb": round(peak_rss_mb(), 1),
        "counts": counts,
        "reference": reference,
        "failures": failures,
        "info": infos,
        "verdict": "FAIL" if failures else "PASS",
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "tier2_probe.json").write_text(json.dumps(result, indent=2) + "\n")

    if failures:
        print("TIER-2 PROBE FAIL — do NOT use this table or trust extended regions:")
        for f in failures:
            print(f"  {f}")
    elif args.smoke:
        print("TIER-2 PROBE PASS (smoke — no table written)")
    else:
        out_pickle = args.out / f"gamma_ball_t{tree}c{close}.pickle"
        with out_pickle.open("wb") as fh:
            pickle.dump(quotient, fh)
        print(f"TIER-2 PROBE PASS — table written to {out_pickle}")
        for note in infos:
            print(f"  info: {note}")

    if not args.smoke:
        Ledger(args.out / "kaplansky.ledger.jsonl").append(
            "kaplansky_tier2_probe",
            0,
            f"tier2-build tree={tree} close={close}",
            None,
            None,
            f"{result['verdict']}: {build_s:.0f}s, {result['peak_rss_mb']} MB peak, "
            f"counts {counts}" + (f"; failures {failures}" if failures else ""),
        )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
