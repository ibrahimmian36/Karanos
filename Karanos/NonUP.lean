/-
Copyright (c) 2026 Millennium Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Millennium Research (Ibby Mian), with Claude
-/
import Karanos.Distinct
import Karanos.Generated.Equalities

/-!
# The headline: Γ does not have unique products

Assembly of the two certified halves. The witness Finsets `A` (32
elements) and `B` (28) come from the generated word lists via `eval`,
with cardinalities from pairwise distinctness. Every product pair has a
generated partner entry: a different pair whose product is certified
equal, so no `UniqueMul` witness exists — refuting `UniqueProds Gamma`.

Three decided facts carry the assembly: coverage (the entries project
onto the full canonical product grid — a list equality), entry validity
(partners are witness members and differ on at least one side by the
`sepBit` quotient separation), and certificate validity (`checkEquality`
per entry, all batched into one `decide`).

Torsion-freeness of Γ is Gardam's result and is NOT claimed here; this
theorem stands alone: an explicit finitely presented group, machine-
verified not to have the unique-product property.
-/

namespace Karanos

open Finset

set_option maxRecDepth 100000

/-- Equality in Γ is decided classically (the Finsets are noncomputable
throughout; nothing evaluates them). -/
noncomputable instance : DecidableEq Gamma := Classical.decEq _

/-- `eval` is multiplicative on concatenation. -/
theorem eval_append (u v : List Letter) : eval (u ++ v) = eval u * eval v := by
  unfold eval
  rw [wordToFree_append]
  exact map_mul _ _ _

/-- Witness Finset A ⊆ Γ. -/
noncomputable def witnessFinsetA : Finset Gamma :=
  (Generated.witnessA.map eval).toFinset

/-- Witness Finset B ⊆ Γ. -/
noncomputable def witnessFinsetB : Finset Gamma :=
  (Generated.witnessB.map eval).toFinset

theorem card_witnessFinsetA : witnessFinsetA.card = 32 := by
  have hnd : (Generated.witnessA.map eval).Nodup := witnessA_pairwise
  rw [witnessFinsetA, List.toFinset_card_of_nodup hnd, List.length_map]
  rfl

theorem card_witnessFinsetB : witnessFinsetB.card = 28 := by
  have hnd : (Generated.witnessB.map eval).Nodup := witnessB_pairwise
  rw [witnessFinsetB, List.toFinset_card_of_nodup hnd, List.length_map]
  rfl

/-- Everything an entry must satisfy, as one boolean: the partner words
are witness members, the partner differs on at least one side under the
quotient separation, and the certificate checks. -/
def entryOk (p : PartnerCert) : Bool :=
  Generated.witnessA.contains p.pu && Generated.witnessB.contains p.pv
    && (sepBit p.u p.pu || sepBit p.v p.pv)
    && checkEquality ⟨p.u ++ p.v, p.pu ++ p.pv, p.pieces⟩

/-- Coverage: the entries project exactly onto the canonical product
grid, so every witness product pair has an entry. -/
theorem partners_cover :
    Generated.partnerCerts.map (fun p => (p.u, p.v))
      = Generated.witnessA.flatMap fun u => Generated.witnessB.map fun v => (u, v) := by
  decide

set_option maxHeartbeats 4000000 in
-- the 896 certificates total ~10^5 letters of kernel word reduction;
-- the default heartbeat budget is sized for interactive proofs, not this
/-- Validity of every entry (memberships, separation, certificates). -/
theorem partners_ok : Generated.partnerCerts.all entryOk = true := by
  decide

theorem exists_entry {u v : List Letter}
    (hu : u ∈ Generated.witnessA) (hv : v ∈ Generated.witnessB) :
    ∃ p ∈ Generated.partnerCerts, p.u = u ∧ p.v = v := by
  have hmem : (u, v) ∈ Generated.witnessA.flatMap
      (fun u => Generated.witnessB.map fun v => (u, v)) := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨u, hu, v, hv, rfl⟩
  rw [← partners_cover] at hmem
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmem
  exact ⟨p, hp, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- No product of the witness pair is unique. -/
theorem no_unique_mul :
    ∀ a₀ ∈ witnessFinsetA, ∀ b₀ ∈ witnessFinsetB,
      ¬ UniqueMul witnessFinsetA witnessFinsetB a₀ b₀ := by
  intro a₀ ha₀ b₀ hb₀ huniq
  simp only [witnessFinsetA, witnessFinsetB, List.mem_toFinset, List.mem_map] at ha₀ hb₀
  obtain ⟨u, hu, hue⟩ := ha₀
  obtain ⟨v, hv, hve⟩ := hb₀
  obtain ⟨p, hp, hpu, hpv⟩ := exists_entry hu hv
  have hok := List.all_eq_true.mp partners_ok p hp
  simp only [entryOk, Bool.and_eq_true, Bool.or_eq_true] at hok
  obtain ⟨⟨⟨hmemA, hmemB⟩, hsep⟩, hcert⟩ := hok
  have hpuA : eval p.pu ∈ witnessFinsetA := by
    simp only [witnessFinsetA, List.mem_toFinset, List.mem_map]
    exact ⟨p.pu, by simpa using hmemA, rfl⟩
  have hpvB : eval p.pv ∈ witnessFinsetB := by
    simp only [witnessFinsetB, List.mem_toFinset, List.mem_map]
    exact ⟨p.pv, by simpa using hmemB, rfl⟩
  have heq : eval p.pu * eval p.pv = a₀ * b₀ := by
    have h := eval_eq_of_check ⟨p.u ++ p.v, p.pu ++ p.pv, p.pieces⟩ relWords_sound hcert
    rw [eval_append, eval_append] at h
    rw [← h, hpu, hpv, hue, hve]
  obtain ⟨h1, h2⟩ := huniq hpuA hpvB heq
  rcases hsep with hs | hs
  · exact eval_ne_of_sepBit hs (by rw [hpu, hue, ← h1])
  · exact eval_ne_of_sepBit hs (by rw [hpv, hve, ← h2])

/-- **Γ does not have the unique-product property.** -/
theorem gamma_not_uniqueProds : ¬ UniqueProds Gamma := by
  intro h
  obtain ⟨a₀, ha₀, b₀, hb₀, huniq⟩ :=
    h.uniqueMul_of_nonempty
      (A := witnessFinsetA) (B := witnessFinsetB)
      (card_pos.mp (by rw [card_witnessFinsetA]; omega))
      (card_pos.mp (by rw [card_witnessFinsetB]; omega))
  exact no_unique_mul a₀ ha₀ b₀ hb₀ huniq

/-- Sanity: Γ is nontrivial (already implied by `gamma_not_uniqueProds`
— a trivial group has unique products — but cheap to state directly). -/
theorem gamma_nontrivial : Nontrivial Gamma := by
  refine ⟨eval [Letter.b], 1, fun h => ?_⟩
  have himg := congrArg abHom h
  rw [abHom_eval, map_one] at himg
  have : abImage [Letter.b] = 0 := by
    have := Multiplicative.ofAdd.injective (a₁ := abImage [Letter.b]) (a₂ := 0)
    exact this himg
  exact absurd this (by decide)

end Karanos
