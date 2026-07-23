#!/usr/bin/env bash
# Overnight Kaplansky jobs on a rented CPU pod (docs/RUNPOD_RUNBOOK.md).
#
# Expects: this repo tree unpacked, with the anchored ball table at
# runs/gamma_ball.pickle (scp'd from the workstation — see the runbook).
# Launches three independent jobs under nohup, each on its own core:
#   1. r6-unnorm  — radius-6 zero-divisor SAT, unconditional form, 12 h budget
#   2. tier2      — deeper quotient build (tree 13, close 11) + count cross-check
#   3. slice      — exhaustive weight-≤3 a over B(3) vs all of B(8)
# Logs in runs/logs/, each ending with "exit=<code>". Ledger lines append
# to runs/kaplansky.ledger.jsonl. Idempotent: refuses to double-launch.

set -euo pipefail
cd "$(dirname "$0")/.."

if pgrep -f "erdos_engine.kaplansky|tier2_build|erdos_engine.gf2" >/dev/null 2>&1; then
    echo "jobs already running (pgrep matched) — not launching twice"; exit 1
fi
[ -f runs/gamma_ball.pickle ] || { echo "missing runs/gamma_ball.pickle — scp it first"; exit 1; }

python3 -c 'import sys; assert sys.version_info >= (3, 10), sys.version'
[ -d .venv ] || python3 -m venv .venv
.venv/bin/pip -q install python-sat

# Gates before anything runs: the SAT backend must import (otherwise the
# zd job silently degrades to DIMACS-export mode and the night is wasted)
# and a wrong table must stop everything.
.venv/bin/python -c "from pysat.solvers import Cadical195"
PYTHONPATH=engine .venv/bin/python -m erdos_engine.kaplansky anchors

mkdir -p runs/logs
launch() {
    local name=$1; shift
    nohup bash -c "$*; echo exit=\$?" > "runs/logs/$name.log" 2>&1 &
    echo "$name pid=$! log=runs/logs/$name.log"
}

PY="PYTHONPATH=engine .venv/bin/python -u"
launch r6-unnorm "$PY -m erdos_engine.kaplansky zd --radius 6 --no-normalize --timeout 43200"
launch tier2 "PYTHONPATH=engine timeout 42000 .venv/bin/python -u scripts/tier2_build.py --tree 13 --close 11"
launch slice "$PY -m erdos_engine.gf2 slice --a-radius 3 --region-radius 8 --max-weight 3"

echo
echo "all three launched; check with:  tail runs/logs/*.log"
echo "done when every log ends in exit=0 (exit=2 on slice = audited kernel hit: read the log)"
