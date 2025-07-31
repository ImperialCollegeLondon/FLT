/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Locus
import FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete

/-!
# Frobenius elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≡ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

Following `RingTheory/Invariant.lean`, we develop the theory in the setting that
there is a finite group `G` acting on a ring `S`, and `R` is the fixed subring of `S`.

## Main results

Let `S/R` be an extension of rings, `Q` be a prime of `S`,
and `P := R ∩ Q` with finite residue field of cardinality `q`.

- `AlgHom.IsArithFrobAt`: We say that a `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q`
  if `φ x ≡ x ^ q (mod Q)` for all `x : S`.
- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`:
  Suppose `S` is a domain and `φ` is a Frobenius at `Q`,
  then `φ ζ = ζ ^ q` for any `m`-th root of unity `ζ` with `q ∤ m`.
- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`:
  Suppose `S` is noetherian, `Q` contains all zero-divisors, and the extension is unramified at `Q`.
  Then the Frobenius is unique (if exists).

Let `G` be a finite group acting on a ring `S`, and `R` is the fixed subring of `S`.

- `IsArithFrobAt`: We say that a `σ : G` is an (arithmetic) Frobenius at `Q`
  if `σ • x ≡ x ^ q (mod Q)` for all `x : S`.
- `IsArithFrobAt.mul_inv_mem_inertia`:
  Two Frobenius elements at `Q` differ by an element in the inertia subgroup of `Q`.
- `IsArithFrobAt.conj`: If `σ` is a Frobenius at `Q`, then `τστ⁻¹` is a Frobenius at `σ • Q`.
- `IsArithFrobAt.exists_of_isInvariant`: Frobenius element exists.
-/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable [IsTopologicalGroup G] [Algebra.IsInvariant R S G]
variable [ContinuousSMulDiscrete G S]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in
/-- Let `G` be a finite group acting on `S`, and `R` be the fixed subring.
If `Q` is a prime of `S` with finite residue field,
then there exists a Frobenius element `σ : G` at `Q`. -/
lemma exists_of_isInvariant_of_profinite
    [Q.IsMaximal] [Finite (R ⧸ Q.under R)] : ∃ σ : G, IsArithFrobAt R σ Q := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  let P := Q.under R
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  -- have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  have : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  -- have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  have : PerfectField (S ⧸ Q) := Algebra.IsAlgebraic.perfectField (K := (R ⧸ P))
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) P Q l
  refine ⟨σ, fun x ↦ ?_⟩
  rw [← Ideal.Quotient.eq, Nat.card_eq_fintype_card, hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
lemma exists_primesOver_isConj_of_profinite (P : Ideal R) [Finite (R ⧸ P)] [P.IsPrime] :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have hP : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ P))
  have : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := G)
  obtain hs | ⟨Q, hQ, hQ₂⟩ := Set.eq_empty_or_nonempty (Ideal.primesOver P S)
  · simp [hs]
  have (Q' : Ideal.primesOver P S) : ∃ σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  have : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) Q
    (by rwa [← Ideal.under, ← hQ₂.over])
  have : Finite (R ⧸ Q.under R) := by rwa [← hQ₂.over]
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant_of_profinite R G Q
  refine ⟨fun Q' ↦ τ Q' * σ * (τ Q')⁻¹, fun Q' ↦ hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ ↦
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. It is chosen so that
the Frobenius elements of `Q₁` and `Q₂` are conjugate if they lie over the same prime. -/
noncomputable
def _root_.arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] : G :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

protected lemma arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] :
    IsArithFrobAt R (arithFrobAt' R G Q) Q :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩

lemma _root_.isConj_arithFrobAt'
    [Q.IsPrime] [Finite (R ⧸ Q.under R)] (Q' : Ideal S) [Q'.IsPrime] [Finite (R ⧸ Q'.under R)]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt' R G Q) (arithFrobAt' R G Q') := by
  obtain ⟨P, hP, h₁, h₂, h₃⟩ :
      ∃ P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R ∧ Finite (R ⧸ P) :=
    ⟨Q.under R, inferInstance, rfl, H, ‹_›⟩
  convert (exists_primesOver_isConj_of_profinite S G P).choose_spec.2
    ⟨Q, ‹_›, ⟨h₁⟩⟩ ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt
