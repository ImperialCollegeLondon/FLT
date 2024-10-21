import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib

universe u

section PRed
-- Don't try anything in this section because we are missing a definition.

-- see mathlib PR #16485
def NumberField.AdeleRing (K : Type u) [Field K] [NumberField K] : Type u := sorry

open NumberField

variable (K : Type*) [Field K] [NumberField K]

-- All these are already done in mathlib PRs, so can be assumed for now.
-- When they're in mathlib master we can update mathlib and then get these theorems/definitions
-- for free.
instance : CommRing (AdeleRing K) := sorry

instance : TopologicalSpace (AdeleRing K) := sorry

instance : TopologicalRing (AdeleRing K) := sorry

instance : Algebra K (AdeleRing K) := sorry

end PRed

section AdeleRingLocallyCompact
-- This theorem is proved in another project, so we may as well assume it.

-- see https://github.com/smmercuri/adele-ring_locally-compact

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing K) := sorry

end AdeleRingLocallyCompact

section TODO
-- these theorems can't be worked on yet because we don't have an actual definition
-- of the adele ring. We can work out a strategy when we do.

variable (K : Type*) [Field K] [NumberField K]

-- Maybe this isn't even stated in the best way?
theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing K),
    IsOpen U ∧ (algebraMap K (AdeleRing K)) ⁻¹' U = {k} := sorry

open NumberField

-- ditto for this one
theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing K ⧸ AddMonoidHom.range (algebraMap K (AdeleRing K)).toAddMonoidHom) :=
  sorry

end TODO

-- *************** Sorries which are not impossible start here *****************

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable [IsDomain B] -- is this necessary?
variable [Algebra.IsSeparable K L]

-- example : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B

variable [IsDedekindDomain B]

-- example : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B

variable [IsFractionRing B L]

-- example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L

variable [Algebra.IsIntegral A B]

-- Conjecture: in this generality there's a natural isomorphism `L ⊗[K] 𝔸_K^∞ → 𝔸_L^∞`
-- Note however that we don't have a definition of adeles in this generality.

-- One key input is the purely local statement that if L/K
-- is a finite extension of number fields, and v is a place of K,
-- then `L ⊗[K] Kᵥ ≅ ⊕_w|v L_w`, where the sum is over the places w
-- of L above v.
namespace DedekindDomain

open scoped TensorProduct -- ⊗ notation for tensor product

noncomputable instance : Algebra K (ProdAdicCompletions B L) := RingHom.toAlgebra <|
  (algebraMap L (ProdAdicCompletions B L)).comp (algebraMap K L)

-- Need to pull back elements of HeightOneSpectrum B to HeightOneSpectrum A
open IsDedekindDomain

namespace HeightOneSpectrum
-- first need a map from finite places of 𝓞L to finite places of 𝓞K
variable {B L} in
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

open scoped algebraMap

-- homework
def valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation x = w.valuation (algebraMap K L x) ^ (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) := sorry

-- Say w is a finite place of L lying above v a finite places
-- of K. Then there's a ring hom K_v -> L_w.
variable {B L} in
noncomputable def of_comap (w : HeightOneSpectrum B) :
    (HeightOneSpectrum.adicCompletion K (comap A w)) →+* (HeightOneSpectrum.adicCompletion L w) :=
  letI : UniformSpace K := (comap A w).adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  UniformSpace.Completion.mapRingHom (algebraMap K L) <| by
  -- question is the following:
  -- if L/K is a finite extension of sensible fields (e.g. number fields)
  -- and if w is a finite place of L lying above v a finite place of K,
  -- and if we give L the w-adic topology and K the v-adic topology,
  -- then the map K → L is continuous
  refine continuous_of_continuousAt_zero (algebraMap K L) ?hf
  delta ContinuousAt
  simp only [map_zero]
  rw [(@Valued.hasBasis_nhds_zero K _ _ _ (comap A w).adicValued).tendsto_iff
    (@Valued.hasBasis_nhds_zero L _ _ _ w.adicValued)]
  simp only [HeightOneSpectrum.adicValued_apply, Set.mem_setOf_eq, true_and, true_implies]
  refine fun i ↦ ⟨i ^ (1 / Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal), fun _ h ↦ ?_⟩
  -- last line is nonsense but use `valuation_comap` to finish
  push_cast at h
  sorry

end HeightOneSpectrum

open HeightOneSpectrum

noncomputable def ProdAdicCompletions.baseChange :
    L ⊗[K] ProdAdicCompletions A K →ₗ[K] ProdAdicCompletions B L := TensorProduct.lift <| {
  toFun := fun l ↦ {
    toFun := fun kv w ↦ l • (of_comap A K w (kv (comap A w)))
    map_add' := sorry
    map_smul' := sorry
  }
  map_add' := sorry
  map_smul' := sorry
}

-- hard but hopefully enough (this proof will be a lot of work)
theorem ProdAdicCompletions.baseChange_iso (x : ProdAdicCompletions A K) :
  ProdAdicCompletions.IsFiniteAdele x ↔
  ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChange A K L B (1 ⊗ₜ x)) := sorry

end DedekindDomain

-- Can we now write down the isomorphism L ⊗ 𝔸_K^∞ = 𝔸_L^∞ ?
