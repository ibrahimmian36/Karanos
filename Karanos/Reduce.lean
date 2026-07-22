/-
Copyright 2026 Millennium Research. Apache-2.0.
-/
import Karanos.Core

/-!
# Free-word reduction and certificate soundness

The computational heart of Karanos: a stack-based reducer on letter
words, its compatibility with the free-group image, and the soundness
theorem for `ProductEquality` certificates — if the checker accepts a
certificate, the two words are genuinely equal in Γ.

The reducer is written as a left fold with an explicit stack so that
kernel reduction is linear in the word length; the certificates total
about 34,000 letters, well inside `decide` territory.
-/

namespace Karanos

/-- One reduction step: push a letter onto a reduced stack, cancelling
against the top if it is the formal inverse. The stack is kept in
REVERSED order (top = head). -/
def push (stack : List Letter) (l : Letter) : List Letter :=
  match stack with
  | [] => [l]
  | t :: rest => if t = l.inv then rest else l :: t :: rest

/-- Stack-based free reduction (result in normal order). -/
def reduce (w : List Letter) : List Letter :=
  (w.foldl push []).reverse

/-- Formal inverse of a word. -/
def wordInv (w : List Letter) : List Letter :=
  (w.map Letter.inv).reverse

/-- The two relators as letter words (must match `Core.relators`;
`relators_eq_wordToFree` pins the correspondence). -/
def relWords : List (List Letter) :=
  [ [.a, .b, .a, .a, .B, .a, .a, .B, .B],
    [.a, .b, .b, .b, .a, .b, .b, .b, .b, .A, .b] ]

/-- Expansion of one certificate piece `⟨c, i, s⟩` as a letter word:
`c ++ r_i^{±1} ++ c⁻¹`. Out-of-range relator indices expand to the
conjugator sandwich with an empty middle — harmless (it reduces to the
empty word) but the generator never emits them. -/
def pieceExpand (p : List Letter × Nat × Bool) : List Letter :=
  let rel := relWords.getD p.2.1 []
  p.1 ++ (if p.2.2 then rel else wordInv rel) ++ wordInv p.1

/-- The certificate checker: the concatenated pieces must reduce to the
same word as `lhs ++ rhs⁻¹`. Pure computation — this is what `decide`
evaluates, once, over the whole generated list. -/
def checkEquality (e : ProductEquality) : Bool :=
  reduce (e.pieces.flatMap pieceExpand) == reduce (e.lhs ++ wordInv e.rhs)

/-! ## Soundness of the reducer -/

@[simp] theorem wordToFree_nil : wordToFree [] = 1 := rfl

@[simp] theorem wordToFree_cons (l : Letter) (w : List Letter) :
    wordToFree (l :: w) = l.toFree * wordToFree w := by
  simp [wordToFree]

theorem wordToFree_append (u v : List Letter) :
    wordToFree (u ++ v) = wordToFree u * wordToFree v := by
  induction u with
  | nil => simp
  | cons l u ih => simp [ih, mul_assoc]

@[simp] theorem toFree_inv (l : Letter) : l.inv.toFree = l.toFree⁻¹ := by
  cases l <;> simp [Letter.inv, Letter.toFree]

theorem wordToFree_wordInv (w : List Letter) :
    wordToFree (wordInv w) = (wordToFree w)⁻¹ := by
  induction w with
  | nil => simp [wordInv]
  | cons l w ih =>
      have : wordInv (l :: w) = wordInv w ++ [l.inv] := by
        simp [wordInv]
      rw [this, wordToFree_append, ih, wordToFree_cons, wordToFree_cons,
        wordToFree_nil, mul_one, mul_inv_rev, toFree_inv]

/-- `push` preserves the free-group image of (reversed stack) · letter. -/
theorem wordToFree_push (stack : List Letter) (l : Letter) :
    wordToFree (push stack l).reverse = wordToFree stack.reverse * l.toFree := by
  cases stack with
  | nil => simp [push]
  | cons t rest =>
      by_cases h : t = l.inv
      · subst h
        simp [push, wordToFree_append, mul_assoc]
      · simp [push, h, wordToFree_append, mul_assoc]

/-- The reducer preserves the free-group image. -/
theorem wordToFree_reduce (w : List Letter) :
    wordToFree (reduce w) = wordToFree w := by
  suffices h : ∀ stack, wordToFree (w.foldl push stack).reverse
      = wordToFree stack.reverse * wordToFree w by
    simpa [reduce] using h []
  induction w with
  | nil => simp
  | cons l w ih =>
      intro stack
      simp only [List.foldl_cons, wordToFree_cons]
      rw [ih (push stack l), wordToFree_push, mul_assoc]

/-- Equal reduced forms mean equal free-group elements. -/
theorem wordToFree_eq_of_reduce_eq {u v : List Letter} (h : reduce u = reduce v) :
    wordToFree u = wordToFree v := by
  rw [← wordToFree_reduce u, ← wordToFree_reduce v, h]

/-! ## Soundness of the certificate checker -/

/-- Each expanded piece lies in the normal closure of the relators. -/
theorem pieceExpand_mem_normalClosure (p : List Letter × Nat × Bool)
    (hrel : ∀ r ∈ relWords, wordToFree r ∈ relators) :
    wordToFree (pieceExpand p) ∈ Subgroup.normalClosure relators := by
  rcases p with ⟨c, i, s⟩
  have hN : (Subgroup.normalClosure relators).Normal := Subgroup.normalClosure_normal
  have hmid : wordToFree (if s then relWords.getD i [] else wordInv (relWords.getD i []))
      ∈ Subgroup.normalClosure relators := by
    by_cases hi : i < relWords.length
    · have hmem : relWords.getD i [] ∈ relWords := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      have hbase : wordToFree (relWords.getD i []) ∈ Subgroup.normalClosure relators :=
        Subgroup.subset_normalClosure (hrel _ hmem)
      simp only [List.getD] at hbase
      cases s <;> simp [wordToFree_wordInv, inv_mem hbase, hbase]
    · have hnil : relWords.getD i [] = [] :=
        List.getD_eq_default _ _ (le_of_not_gt hi)
      simp only [List.getD] at hnil
      cases s <;> simp [hnil, wordInv]
  have := hN.conj_mem _ hmid (wordToFree c)
  simpa [pieceExpand, wordToFree_append, wordToFree_wordInv, mul_assoc] using this

/-- The concatenated pieces of a certificate lie in the normal closure. -/
theorem pieces_mem_normalClosure (pieces : List (List Letter × Nat × Bool))
    (hrel : ∀ r ∈ relWords, wordToFree r ∈ relators) :
    wordToFree (pieces.flatMap pieceExpand) ∈ Subgroup.normalClosure relators := by
  induction pieces with
  | nil => simpa using one_mem _
  | cons p ps ih =>
      rw [List.flatMap_cons, wordToFree_append]
      exact mul_mem (pieceExpand_mem_normalClosure p hrel) ih

/-- Checker soundness: an accepted certificate proves equality in Γ. -/
theorem eval_eq_of_check (e : ProductEquality)
    (hrel : ∀ r ∈ relWords, wordToFree r ∈ relators)
    (h : checkEquality e = true) : eval e.lhs = eval e.rhs := by
  have hfree : wordToFree (e.pieces.flatMap pieceExpand)
      = wordToFree (e.lhs ++ wordInv e.rhs) :=
    wordToFree_eq_of_reduce_eq (by simpa [checkEquality] using h)
  have hmem : wordToFree e.lhs * (wordToFree e.rhs)⁻¹ ∈ Subgroup.normalClosure relators := by
    have := pieces_mem_normalClosure e.pieces hrel
    rw [hfree, wordToFree_append, wordToFree_wordInv] at this
    exact this
  have hN : (Subgroup.normalClosure relators).Normal := Subgroup.normalClosure_normal
  have hmem' : (wordToFree e.lhs)⁻¹ * wordToFree e.rhs ∈ Subgroup.normalClosure relators := by
    have hinv : wordToFree e.rhs * (wordToFree e.lhs)⁻¹ ∈ Subgroup.normalClosure relators := by
      simpa using inv_mem hmem
    simpa [mul_assoc] using hN.conj_mem _ hinv (wordToFree e.lhs)⁻¹
  exact QuotientGroup.eq.mpr hmem'

end Karanos
