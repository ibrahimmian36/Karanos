#!/bin/bash
# Karanos publication gate.
#
# Two independent layers, both required:
#
#   1. Manifest (Karanos/AxiomCheck.lean): every PUBLISHED theorem, listed by
#      name, `#print axioms`-ed for the record.
#   2. Audit (Karanos/AxiomAudit.lean): every theorem in every Karanos module,
#      discovered mechanically from the compiled environment, so a theorem
#      added tomorrow cannot slip past the hand-maintained list.
#
# Every theorem must depend on AT MOST the three standard axioms
#   propext, Classical.choice, Quot.sound
# (subsets are fine; several lemmas need less), with zero `sorryAx` and zero
# `_native.*` (native_decide is forbidden: it mints a per-theorem trust axiom).
#
# Usage: scripts/axiom_gate.sh          (from anywhere; exits 0 on PASS, 1 on FAIL)
set -uo pipefail
cd "$(dirname "$0")/.."

# ---------- Layer 1: the curated manifest ----------
out=$(lake env lean Karanos/AxiomCheck.lean 2>&1)
status=$?
echo "$out"

if [ $status -ne 0 ]; then
  echo "AXIOM GATE: FAIL (AxiomCheck.lean did not compile)"
  exit 1
fi

# Any axiom token outside the allowed three is a violation.
viol=$(echo "$out" | grep "depends on" \
  | sed 's/.*axioms: \[//; s/\]//' | tr ',' '\n' | tr -d ' ' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)

count=$(echo "$out" | grep -c "depends on")

if [ -n "$viol" ]; then
  echo "AXIOM GATE: FAIL: disallowed axioms:"
  echo "$viol" | sort -u
  exit 1
fi
if echo "$out" | grep -qE "sorryAx|_native"; then
  echo "AXIOM GATE: FAIL: sorryAx or native axiom present"
  exit 1
fi
if [ "$count" -eq 0 ]; then
  echo "AXIOM GATE: FAIL: no '#print axioms' output found"
  exit 1
fi

# ---------- Layer 2: the automated whole-library audit ----------
aud=$(lake env lean Karanos/AxiomAudit.lean 2>&1)
astatus=$?
echo "$aud"

if [ $astatus -ne 0 ]; then
  echo "AXIOM GATE: FAIL (automated audit failed, see output above)"
  exit 1
fi
audited=$(echo "$aud" | sed -n 's/.*AXIOM AUDIT: PASS: \([0-9][0-9]*\) theorems.*/\1/p' | head -1)
if [ -z "$audited" ]; then
  echo "AXIOM GATE: FAIL: audit compiled but reported no PASS line"
  exit 1
fi
if [ "$audited" -lt "$count" ]; then
  echo "AXIOM GATE: FAIL: audit saw $audited theorems, fewer than the $count in the manifest"
  exit 1
fi

echo "AXIOM GATE: PASS ($count published theorems in the manifest, $audited audited library-wide, axioms ⊆ {propext, Classical.choice, Quot.sound})"
