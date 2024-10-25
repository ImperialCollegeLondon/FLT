/-
Copyright (c) 2024 Ivan Farabella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Farabella, Amelia Livingston, Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!

# DO NOT FIX THIS FILE IF IT BREAKS.

It is work in progress. If it breaks just move the #exit up to
just before it breaks. Frobenius elements need a complete refactor
so keeping this code up to date is a waste of time.

# IsFrobenius

Let `K` be a number field with integers `A` and let `L/K` be an algebraic extension.
If `g : L ≃ₐ[K] L` and `P` is a maximal ideal of `A`, then `IsFrobenius g P` is the
predicate claiming that there's a valuation `v` on `L` extending the `P`-adic valuation on `K`,
such that `g` fixes `v` and the induced action on the residue field of `v` is `x ↦ x^q`, with
`q` the size of `A ⧸ P`.

-/

open NumberField

set_option maxHeartbeats 4000000

namespace CompatibleFamily

variable {p : ℕ}[Fact (p.Prime)]

noncomputable section FrobeniusFinite

/-This section defines `IsFrobeniusFinite`, a predicate on Frobenius elements of `L ≃ₐ[K] L`
where `L/K` is finite dimensional-/

variable (A K L B : Type) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable {A B}

/-- An ideal `Q` of `B`, is invariant under a `A`-algebra equivalence from `B` to `B` iff
its image is itself-/
def IsInvariant (f : (B ≃ₐ[A] B)) (Q : Ideal B) : Prop := (Q = Q.comap (f.symm : B →+* B))

lemma comap_symm (f : (B ≃ₐ[A] B)) (Q : Ideal B)  : (Q.comap (f.symm : B →+* B) = Q.map f) :=
  Ideal.comap_symm _ _

variable (B)

/-- When `L` is finite dimensional over `K`, a `K`-algebra equivalence from `L` to `L` is
Frobenius for a maximal ideal downstairs if there exists a invariant maximal ideal upstairs above it
that induces a Frobenius map on the residue field `B ⧸ Q`. -/
def IsFrobeniusFinite (g : (L ≃ₐ[K] L)) (P : Ideal A) [Ideal.IsMaximal P] : Prop :=
  ∃ (Q : Ideal B) (h : IsInvariant ((galRestrict A K L B) g) Q), (Ideal.IsMaximal Q) ∧
  ((Ideal.map (algebraMap A B) P) ≤ Q) ∧
  (((Ideal.quotientEquivAlg Q Q ((galRestrict A K L B) g)
  (by erw [← comap_symm]; exact h)) : (B ⧸ Q) → (B ⧸ Q)) =
  fun x => x ^ (Nat.card (A ⧸ P)))

end FrobeniusFinite

section IsFrobenius
/-This section defines `IsFrobenius'` and `IsFrobenius`, propositions for Frobenius elements
of `L ≃ₐ[K] L` when the extension `L/K` isn't necessarily finite. See `IsFrobeniusAgrees.lean`
for an attempt at proving `IsFrobenius'` agrees with `IsFrobeniusFinite` when `K` and `L` are
number fields-/

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] -- not necessarily finite dimensional

open NumberField

lemma AlgEquiv_restrict_to_domain_equals_id (h1 : Normal K L) :
    AlgEquiv.restrictNormalHom (F := K) L  = MonoidHom.id _ := by
  ext a l
  simpa only [Algebra.id.map_eq_id, RingHom.id_apply, AlgHom.coe_coe] using
    AlgHom.restrictNormal_commutes (E := L) (F := K) (K₁ := L) (K₂ := L) a l

lemma AlgEquiv_restrict_to_domain_fix (h1 : Normal K L) (g : (L ≃ₐ[K] L)) :
    AlgEquiv.restrictNormalHom (F := K) L g =  g := by
  rw [AlgEquiv_restrict_to_domain_equals_id K L h1]
  rfl

/--Takes an ideal upstairs and brings it downstairs in a AKLB setup-/
def ToDownstairs  (Q : Ideal B) : Ideal A := Q.comap (algebraMap A B)

/-Depreciation note: eventually we want to state these in full generality, removing as many
instances of `NumberField` as possible. It seems like the following setup will be useful:
variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] (not : ¬ (IsField A)) [Nontrivial A] [Ring.DimensionLEOne A]
    [∀ (P : Ideal A) [P.IsMaximal], Fintype (A ⧸ P)] [Infinite A]
the local case of `Fintype_Quot_of_IsMaximal` has been formalised by
María Inés de Frutos Fernández and Filippo A. E. Nuccio at
https://github.com/mariainesdff/LocalClassFieldTheory/blob/master/LocalClassFieldTheory/DiscreteValuationRing/ResidueField.lean -/

variable {A}

lemma IsMaximal_not_eq_bot [NumberField K] (Q : Ideal (𝓞 K)) [Ideal.IsMaximal Q] : Q ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)

lemma NumberField_Ideal_IsPrime_iff_IsMaximal  [NumberField K]
    (Q : Ideal (𝓞 K)) (h1: Q ≠ ⊥) : Ideal.IsPrime Q ↔ Ideal.IsMaximal Q := by
  constructor
  · intro h
    exact Ideal.IsPrime.isMaximal h h1
  · intro h
    exact Ideal.IsMaximal.isPrime h

instance Fintype_Quot_of_IsMaximal [NumberField K] (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] : Fintype ((𝓞 K) ⧸ P) := by
  sorry

-- all broken from here but no longer sure this is the right level of generality
#exit

lemma ring_of_integers_not_Fintype [NumberField K] : ¬ (Finite (𝓞 K)) := Infinite.not_finite

lemma ne_bot_algebraMap_comap_ne_bot' (Q : Ideal B) [Ideal.IsMaximal Q] [Fintype (B ⧸ Q)]
    [Infinite A] :
    Ideal.comap (algebraMap A B) Q ≠ ⊥ := by
  by_contra hQ
  have h2 : Ideal.comap (algebraMap A B) Q ≤ Ideal.comap (algebraMap A B) Q :=
    Eq.le rfl
  let f := Ideal.quotientMap Q (algebraMap A B) h2
  have hf : Function.Injective (Ideal.quotientMap Q (algebraMap A B) h2) :=
    @Ideal.quotientMap_injective A B _ _ Q (algebraMap A B)
  have h3 : Fintype (A ⧸ Ideal.comap (algebraMap A B) Q) := Fintype.ofInjective f hf
  rw [hQ] at h3
  have h4 : Fintype A :=
    @Fintype.ofEquiv _ (A ⧸ ⊥) h3 (@QuotientAddGroup.quotientBot A _).toEquiv
  exact Fintype.false h4

lemma ne_bot_algebraMap_comap_ne_bot [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] : Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) Q ≠ ⊥ := by
  exact ne_bot_algebraMap_comap_ne_bot' (↥(𝓞 L)) Q

lemma IsMaximal_comap_IsMaximal' [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] :
    Ideal.IsMaximal (Q.comap (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [← NumberField_Ideal_IsPrime_iff_IsMaximal] at *
  · exact Ideal.IsPrime.comap (algebraMap ↥(𝓞 K) ↥(𝓞 L))
  · have h : Q ≠ ⊥ := IsMaximal_not_eq_bot L Q
    exact h
  · exact ne_bot_algebraMap_comap_ne_bot K L Q

lemma IsMaximal_ToDownstairs_IsMaximal [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] : Ideal.IsMaximal (ToDownstairs (𝓞 K) (𝓞 L) Q) := by
  rw [ToDownstairs]
  exact IsMaximal_comap_IsMaximal' K L Q

instance (k l : Type) [Field k] [Field l] [NumberField k] [NumberField l] [Algebra k l] :
    SMul (𝓞 k) (𝓞 l) := Algebra.toSMul

instance [NumberField K] [NumberField L]: IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance (k l : Type) [Field k] [Field l] [NumberField k] [NumberField l] [Algebra k l] :
    IsIntegralClosure (↥(𝓞 l)) (↥(𝓞 k)) l := sorry -- a missing theorem, needs a proof

/-- Predicate on Frobenius elements for number fields. Should be depreciated to use `IsFrobenius`
instead.-/
def IsFrobenius' [NumberField K] (g : (L ≃ₐ[K] L)) (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] : Prop :=
  ∀(N : Type) [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
  [Algebra N L] [IsScalarTower K N L],
  IsFrobeniusFinite K N (𝓞 N) (AlgEquiv.restrictNormalHom N g) P

/--A predicate on Frobenius elements in a higher level of generality-/
def IsFrobenius (g : (L ≃ₐ[K] L)) (P : Ideal A) [Ideal.IsMaximal P] : Prop :=
  ∀ (N: Type) [Field N] [Algebra K N] [Algebra A N] [FiniteDimensional K N]
  [IsGalois K N] [IsScalarTower A K N] [Algebra N L] [IsScalarTower K N L],
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C N)
  (_ : IsScalarTower A C N) (_ :IsIntegralClosure C A N),
  IsFrobeniusFinite K N C (AlgEquiv.restrictNormalHom N g) P
