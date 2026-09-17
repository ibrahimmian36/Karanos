/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ibrahim Mian, Shayaan Siddique
-/
import Karanos.NonUP

/-! Publication gate, layer 1: the curated manifest. Every published
theorem below must depend on at most `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `_native.*`. Layer 2
(`AxiomAudit.lean`) re-checks every theorem in the library
mechanically, so nothing added later can slip past this list. -/

#print axioms Karanos.relWords_sound
#print axioms Karanos.wordToFree_reduce
#print axioms Karanos.eval_eq_of_check
#print axioms Karanos.abGen_kills
#print axioms Karanos.abHom_eval
#print axioms Karanos.s4Gen_kills
#print axioms Karanos.s4Hom_eval
#print axioms Karanos.eval_ne_of_sepBit
#print axioms Karanos.witnessA_pairwise
#print axioms Karanos.witnessB_pairwise
#print axioms Karanos.card_witnessFinsetA
#print axioms Karanos.card_witnessFinsetB
#print axioms Karanos.partners_cover
#print axioms Karanos.partners_ok
#print axioms Karanos.no_unique_mul
#print axioms Karanos.gamma_not_uniqueProds
#print axioms Karanos.gamma_nontrivial
