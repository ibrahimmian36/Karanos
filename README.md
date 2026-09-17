# Karanos

A proof, checked by the Lean 4 kernel, that the group

    Γ = ⟨a, b | a b a² b⁻¹ a² b⁻², a b³ a b⁴ a⁻¹ b⟩

does not have the unique-product property:

    theorem gamma_not_uniqueProds : ¬ UniqueProds Gamma

The statement uses mathlib's own `UniqueProds` class. The development
depends only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`.

## Whose theorem this is

That Γ fails unique products was announced by Giles Gardam in lectures in
2021, where he presented Γ, a torsion-free Ã₂ lattice with property (T),
as a new candidate group for Kaplansky's zero-divisor conjecture
([slides, 17 Sep 2021](https://www.gilesgardam.com/slides/gncg.pdf);
[slides, 25 Nov 2021](https://sschleimer.warwick.ac.uk/Seminar/Talks/2021-11-25gardam.pdf)).
To our knowledge no proof or witness has been published. This repository
supplies a kernel-checked proof with an explicit witness found by our own
search. The mathematical statement is Gardam's.

Torsion-freeness of Γ, its description as a lattice, and property (T) are
Gardam's and are **not** formalized here. The theorem is about the
presented group and does not depend on them. Nothing here concerns zero
divisors.

## What is proved

The witness is a pair of lists of reduced words: 32 words for `A` and 28
for `B`, each of length at most six. For each of the 896 pairs `(u, v)`
the data name a different pair `(u', v')` of listed words, and Lean checks

- **an equality** `uv = u'v'` in Γ, certified by an explicit identity in
  the free group: `(uv)(u'v')⁻¹` written as a product of conjugated
  relators, verified by free reduction. In 658 cases the identity already
  holds in the free group; the other 238 certificates use 970 conjugated
  relators in all.
- **a disequality** `u ≠ u'` or `v ≠ v'` in Γ, certified by a homomorphism
  to a finite group. The map `a ↦ −8, b ↦ 1` onto `ℤ/42` separates `v`
  from `v'` in all 896 cases, which is all the theorem needs.

The development also proves that the listed words are pairwise distinct in
Γ, so that the sets have exactly 32 and 28 elements: `ℤ/42` separates 868
of the 874 pairs, and a homomorphism into `S₄` with image `A₄` separates
the other six.

## Verifying

    lake exe cache get
    lake build
    scripts/axiom_gate.sh

The gate audits every theorem constant in the compiled library (122) and
fails on any `sorry`, any `native_decide`, or any axiom beyond the
standard three. CI runs it on every push. For the main theorem it prints

    'Karanos.gamma_not_uniqueProds' depends on axioms: [propext, Classical.choice, Quot.sound]

The certificates can also be checked without Lean:

    python3 scripts/recheck_certificates.py

This script uses only the Python standard library. It reads the two
generated data files and re-verifies every equality certificate by free
reduction and every disequality through the two homomorphisms.

## Layout

    Karanos/            the Lean development
      Core.lean           Γ as a PresentedGroup; words; certificate types
      Reduce.lean         free reduction; soundness of the equality checker
      Distinct.lean       the two homomorphisms; pairwise distinctness
      NonUP.lean          the 896-certificate check; gamma_not_uniqueProds
      Generated/          witness and certificate data (never hand-edited)
      AxiomCheck.lean     manifest of published theorems
      AxiomAudit.lean     audit of every theorem constant in the library
    engine/             the search program (Python, untrusted)
      groupball.py        Todd–Coxeter ball quotients that record proofs
      certgraph.py        extraction of equality certificates
      quotients.py        search for separating finite quotients
      kaplansky.py        Γ, SAT encodings of the unique-product condition
      gf2.py              kernel test over F₂ used by the search
    scripts/            axiom gate, certificate generation, independent checker
    tests/              tests for the search program
    runs/               dated log of every search result

The Python side is untrusted. It searches, extracts and checks its own
output, then emits data that Lean re-checks; an error there can make the
build fail but cannot make a false theorem pass.

Running the tests:

    python -m pytest

Regenerating the certificate data (`scripts/p2_codegen.py`) first rebuilds
the ball quotient, which takes hours; the generated files are committed so
that this is not needed to verify the theorem.

## Paper and citation

A paper describing this development has been submitted to arXiv; the
identifier will be added here. Until then, see `CITATION.cff`.

## Use of AI tools

A large language model (Claude, Anthropic) wrote most of the Lean and
Python code in this repository under the authors' direction. The authors
take responsibility for its contents. The theorem is checked by the Lean
kernel and does not depend on the correctness of LLM-written code.

## License

Apache 2.0.
