# RunPod overnight runbook — Kaplansky jobs

Three jobs run on one rented pod overnight; the workstation runs nothing.
None of them uses a GPU (SAT is sequential CPU, the table build and kernel
sweeps are CPU Python), so rent a **CPU pod**: 8–16 vCPU, **32 GB RAM**
(the tree-13 build is the memory eater), ~40 GB disk. That is roughly
$0.20–0.40/hr on RunPod — $3–6 for a full night. An idle GPU would add
cost and nothing else.

The jobs (launched together by `scripts/runpod_bootstrap.sh`):

1. **r6-unnorm** — radius-6 zero-divisor SAT, unconditional (`--no-normalize`),
   12-hour solver budget. UNSAT = the radius-6 exclusion bound; UNKNOWN = the
   SAT track's plateau, decision point reached.
2. **tier2** — deeper quotient (tree 13, close 11) with the ball-count
   cross-check against the current table. PASS writes the new pickle that
   unlocks larger regions; FAIL is loud and blocks everything downstream.
   Capped at 11.7 h by `timeout`.
3. **slice** — exhaustive: every left factor of weight ≤ 3 over B(3)
   against all of B(8) (~25k candidates). Note: 3 + 8 = 11 exceeds the
   converged bound (10), so this slice runs in the SHELL tier — the code
   labels it as such and the verdict carries the under-merge caveat. A
   clean finish is still the first complete structure-indexed exclusion
   slice, in its caveated form; re-run it converged on a deeper table
   once table selection ships.

## Evening: upload and launch

On the workstation, pack the repo at the pushed commit plus the ball table.
Fill `$PORT` and `$HOST` from the pod's Connect → SSH panel:

```bash
cd ~/Desktop/3kvc/erdos-engine
git archive --format=tar.gz -o /tmp/erdos-engine.tar.gz HEAD
scp -P $PORT /tmp/erdos-engine.tar.gz runs/gamma_ball.pickle root@$HOST:/root/
```

On the pod:

```bash
mkdir -p erdos-engine && tar -xzf erdos-engine.tar.gz -C erdos-engine
mkdir -p erdos-engine/runs && mv gamma_ball.pickle erdos-engine/runs/
bash erdos-engine/scripts/runpod_bootstrap.sh
```

The bootstrap refuses to run without the pickle, re-checks the published
anchors before launching anything, and prints three PIDs. A quick look
before logging off:

```bash
tail erdos-engine/runs/logs/*.log
```

## Morning: retrieve and verify

Pull everything into a **subdirectory** — never onto the live `runs/`
(the local ledger must not be clobbered; results are merged after review):

```bash
scp -P $PORT -r "root@${HOST}:erdos-engine/runs/logs" runs/runpod/logs
scp -P $PORT "root@${HOST}:erdos-engine/runs/kaplansky.ledger.jsonl" "root@${HOST}:erdos-engine/runs/tier2_probe.json" runs/runpod/
```

Two traps, both hit on 2026-07-22: the pod's minimized Ubuntu has no rsync, and in
zsh an unbraced `$HOST:e…` is a history modifier (`:e` = "extension") that silently
mangles the remote path into a local one — always brace it as `${HOST}:`. The big
table pickles are deliberately not pulled; rebuild them locally with tier2_build
(minutes) — the counts are cross-checked via the ledger lines either way.

Then stop the pod (billing stops with it) and hand the `runs/runpod/`
directory to the review flow. Done-ness: each log ends in `exit=0`;
`exit=2` on slice/asym means an audited kernel hit — read that log first,
it is either the discovery or a table bug, and the log says which the
audit believes. The tier-2 verdict is in `runs/runpod/tier2_probe.json`.

## Notes

- The pickle upload (51 MB) replaces an hours-long rebuild on the pod; the
  tier-2 job builds its own deeper table and uses the uploaded one only as
  the cross-check reference.
- All three jobs append to the pod's own `runs/kaplansky.ledger.jsonl`;
  those lines are merged into the workstation ledger by hand after review,
  keeping one append-only history.
- Nothing on the pod needs credentials: no git clone, no API keys, just a
  tarball and a pickle in, artifacts out.
