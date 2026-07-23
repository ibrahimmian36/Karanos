"""P2 gate G-b: build the proof-producing closure at production config
(tree 12, close 10), extract certificates for every product coincidence
of the non-u.p. witness, and measure their total size — the number that
decides whether the Lean encoding is written as designed or redesigned.

For each product class hit by k pairs (a_i, b_j), the certificate needs
k−1 chained equalities. Every certificate is self-verified here by free
reduction (edge-locally; compositions telescope). Report to
runs/p2_certs_report.json + one ledger line.

Usage:  PYTHONPATH=src python scripts/p2_certs.py [--smoke]
"""

from __future__ import annotations

import argparse
import json
import resource
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "engine"))

from karanos_engine.certgraph import CertifiedBallQuotient  # noqa: E402
from karanos_engine.kaplansky import (  # noqa: E402
    ANCHOR_BALL4,
    ANCHOR_BALL6,
    RELATOR_1,
    RELATOR_2,
    WITNESS_NONUP_A,
    WITNESS_NONUP_B,
    parse_word,
)
from karanos_engine.ledger import Ledger  # noqa: E402


def peak_rss_mb() -> float:
    raw = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return raw / (1024 * 1024) if sys.platform == "darwin" else raw / 1024


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tree", type=int, default=12)
    ap.add_argument("--close", type=int, default=10)
    ap.add_argument("--smoke", action="store_true", help="tree 8 / close 7 — minutes, not hours")
    ap.add_argument("--out", type=Path, default=Path("runs"))
    args = ap.parse_args()
    tree, close = (8, 7) if args.smoke else (args.tree, args.close)

    print(f"building certified quotient tree={tree} close={close} …", flush=True)
    t0 = time.perf_counter()
    q = CertifiedBallQuotient(2, [RELATOR_1, RELATOR_2], tree, close)
    build_s = time.perf_counter() - t0
    b4, b6 = len(q.ball(4)), len(q.ball(6))
    print(
        f"built in {build_s:.0f}s, peak RSS {peak_rss_mb():.0f} MB, "
        f"{len(q.proof_edges)} proof edges; B(4)={b4}, B(6)={b6}",
        flush=True,
    )
    if b4 != ANCHOR_BALL4 or b6 != ANCHOR_BALL6:
        print("ANCHOR FAILED on the certified rebuild — stop.")
        return 1

    words_a = [parse_word(w) for w in WITNESS_NONUP_A]
    words_b = [parse_word(w) for w in WITNESS_NONUP_B]
    from karanos_engine.groupball import free_reduce

    by_class: dict[int, list[tuple[int, ...]]] = {}
    skipped = 0
    for wa in words_a:
        for wb in words_b:
            prod = tuple(list(wa) + list(wb))
            if len(free_reduce(prod)) > tree:
                skipped += 1  # smoke trees are too shallow for some products
                continue
            by_class.setdefault(q.class_of_word(prod), []).append(prod)
    if skipped and not args.smoke:
        print(f"{skipped} products exceed the tree — full run must cover all; stop.")
        return 1
    if skipped:
        print(f"smoke: {skipped} of 896 products beyond tree {tree}, exercising the rest")
    sizes = sorted(len(v) for v in by_class.values())
    print(
        f"{len(by_class)} product classes over {sum(sizes)} pairs; "
        f"class sizes min={sizes[0]} max={sizes[-1]}",
        flush=True,
    )
    if sizes[0] < 2 and not args.smoke:
        print("a product class of size 1 exists — witness would NOT be non-u.p.; stop.")
        return 1

    t1 = time.perf_counter()
    n_eq = 0
    path_edges: set[int] = set()
    for members in by_class.values():
        for u_word, v_word in zip(members, members[1:], strict=False):
            path, _ = q.pair_cert(u_word, v_word)
            path_edges.update(e for e, _f in path)
            n_eq += 1
            if n_eq % 50 == 0:
                print(f"  {n_eq} equalities certified …", flush=True)
    extract_s = time.perf_counter() - t1

    used = q._edge_cert_memo  # noqa: SLF001 — measurement harness reads its own build
    total_letters = sum(c.letters for c in used.values())
    total_pieces = sum(len(c.pieces) for c in used.values())
    report = {
        "config": {"tree": tree, "close": close},
        "build_seconds": round(build_s, 1),
        "extract_seconds": round(extract_s, 1),
        "peak_rss_mb": round(peak_rss_mb(), 1),
        "proof_edges_total": len(q.proof_edges),
        "product_classes": len(by_class),
        "equalities_certified": n_eq,
        "edges_on_paths": len(path_edges),
        "edges_expanded": len(used),
        "lemma_pieces_total": total_pieces,
        "lemma_letters_total": total_letters,
        "largest_edge_letters": max((c.letters for c in used.values()), default=0),
        "gate_G_b": "PASS" if total_letters <= 2_000_000 else "MEASURED-LARGE",
    }
    (args.out / "p2_certs_report.json").write_text(json.dumps(report, indent=2) + "\n")
    note = (
        f"P2 gate G-b ({'smoke' if args.smoke else 'full'}): {n_eq} equalities certified & "
        f"self-verified; {len(used)} edge lemmas, {total_pieces} relator pieces, "
        f"{total_letters} letters total (largest edge {report['largest_edge_letters']}); "
        f"build {build_s:.0f}s + extract {extract_s:.0f}s → {report['gate_G_b']}"
    )
    if not args.smoke:
        Ledger(args.out / "kaplansky.ledger.jsonl").append(
            "kaplansky_p2_certs", 0, f"cert-extract tree={tree} close={close}", None, None, note
        )
    print(note)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
