# Henselian Pairs

This folder develops the theory of **Henselian pairs** `(R, I)` — the notion that
underlies Hensel's lemma in its factorisation form. Mathlib has `HenselianRing R I`
(a simple root of a monic polynomial over `R ⧸ I` lifts to a root over `R`) and
`HenselianLocalRing R`, but it has **no** notion of a Henselian pair. This folder
supplies one, following the Stacks Project (More on Algebra, §15.11, tag 09XD onwards),
and is packaged so it can be upstreamed to Mathlib.

## The definition

```lean
class IsHenselianPair (R : Type*) [CommRing R] (I : Ideal R) : Prop where
  le_jacobson : I ≤ Ideal.jacobson ⊥
  exists_lift_factorization : ∀ (f : R[X]), f.Monic →
    ∀ {g₀ h₀ : (R ⧸ I)[X]}, g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀
```

`(R, I)` is a Henselian pair if `I` lies in the Jacobson radical and every monic
polynomial whose reduction modulo `I` factors as a product of two monic *coprime*
polynomials lifts to a matching factorisation over `R` (Stacks tag 09XE).

It is declared as a `class` to match Mathlib's neighbours `HenselianRing` and
`HenselianLocalRing`, but the API takes it as an explicit hypothesis
`(h : IsHenselianPair R I)` rather than an instance binder.

## File Guide

- `Coprime.lean` — coprimality of monic polynomials descends along Jacobson-radical
  quotients, via the resultant.
- `Polynomial.lean` — polynomial helpers; uniqueness of simple-root lifts from
  `I ≤ Jac(R)` alone.
- `HenselianRing.lean` — uniqueness of root lifts for Mathlib's `HenselianRing`.
- `Defs.lean` — `IsHenselianPair`; the bridge `IsHenselianPair.henselianRing` to
  Mathlib's predicate; the examples `(R, ⊥)` and the local-ring case.
- `Idempotents.lean` — idempotents of `R ⧸ I` lift uniquely (Stacks tag 09XI(2));
  the converse Jacobson criteria.
- `Quotient.lean` — quotient and subideal stability (Stacks tags 09XG, 0DYD).
- `HenselianPair.lean` (parent) re-exports the folder.

## What Is Proved

- `IsHenselianPair.henselianRing` — a Henselian pair is Henselian in Mathlib's
  root-lifting sense; the factorisation definition is not a self-serving weakening.
- `IsHenselianPair.henselianLocalRing` — a local ring Henselian at its maximal ideal
  is a `HenselianLocalRing`.
- `IsHenselianPair.bot` — `(R, ⊥)` is a Henselian pair; in particular `(K, ⊥)` for a
  field `K`.
- `IsHenselianPair.existsUnique_root_lift_of_isUnit_derivative` — the simple-root lift
  is unique in its congruence class.
- `IsHenselianPair.existsUnique_isIdempotentElem_lift` and the orthogonal /
  complete-orthogonal systems — idempotents lift uniquely (Stacks tag 09XI(2)).
- `IsHenselianPair.quotient`, `IsHenselianPair.of_le`, `IsHenselianPair.of_quotient`
  and `iff_of_le_quotient` — quotient stability (tag 09XG), unconditional shrinking
  of the ideal, and the gluing statement (tag 0DYD).

## What Is Not Proved Here

Deliberately out of scope in this folder:

- The henselization `(Rʰ, Iʰ)` of a pair and the theorem that it is a Henselian pair
  (Stacks tag 0A02), and its universal property (tag 0A02.1).
- `Henselian pair ⟹ étale sections lift` (tag 09XI (1) ⇒ (2)), which needs Zariski's
  Main Theorem.
- The étale-lifting characterisation of Henselian *local* rings (tag 04GG), which is
  the subject of in-flight Mathlib PR #41086.

## Verification

`lake build FLT.Slop.HenselianPair` compiles with no errors, no `sorry`, and no
warnings, and

```lean
#print axioms IsHenselianPair.henselianRing
#print axioms IsHenselianPair.of_quotient
#print axioms IsHenselianPair.existsUnique_isIdempotentElem_lift
-- [propext, Classical.choice, Quot.sound]
```

reports only the three standard axioms.

## Relation to existing formalizations

Nothing here duplicates current Mathlib: `IsHenselianPair`,
`isCoprime_X_sub_C_of_isUnit_eval` and
`isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson` have zero occurrences
in Mathlib. `Coprime.lean`'s two general polynomial facts are the natural candidates
to be rehomed (to `Mathlib/Algebra/Polynomial/RingDivision.lean` and near
`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`) if this is upstreamed.

Stacks citations use Mathlib's `@[stacks TAG]` attribute rather than markdown links.

## Sources

The Stacks Project, More on Algebra, §15.11–15.12
([tag 09XD](https://stacks.math.columbia.edu/tag/09XD) onwards); the
coprime-factorisation definition is [tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
and the idempotent-lifting characterisation is
[tag 09XI](https://stacks.math.columbia.edu/tag/09XI).

## Possible next steps

- The henselization of a pair and its universal property (tags 0A02, 0A02.1).
- The hard direction of tag 09XI via Zariski's Main Theorem.
- Upstream the pair theory to Mathlib.
