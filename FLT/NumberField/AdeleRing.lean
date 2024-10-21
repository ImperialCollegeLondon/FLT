import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Basic

universe u

variable (K : Type*) [Field K] [NumberField K]

section PRed
-- Don't try anything in this section because we are missing a definition.

-- see mathlib PR #16485
def NumberField.AdeleRing (K : Type u) [Field K] [NumberField K] : Type u := sorry

open NumberField

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

-- recall we already had `variable (K : Type*) [Field K] [NumberField K]`

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

instance : NumberField L := sorry -- inferInstance fails

-- We want the map `L ⊗[K] 𝔸_K → 𝔸_L`, but we don't have a definition of adeles.
-- However we do have a definition of finite adeles, so let's work there.

namespace DedekindDomain

open scoped TensorProduct NumberField -- ⊗ notation for tensor product and 𝓞 K notation for ring of ints

noncomputable instance : Algebra K (ProdAdicCompletions (𝓞 L) L) := RingHom.toAlgebra <|
  (algebraMap L (ProdAdicCompletions (𝓞 L) L)).comp (algebraMap K L)

-- Need to pull back elements of HeightOneSpectrum (𝓞 L) to HeightOneSpectrum (𝓞 K)
open IsDedekindDomain

variable {L} in
def HeightOneSpectrum.comap (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L))
  isPrime := Ideal.comap_isPrime (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
  ne_bot := sorry -- pullback of nonzero prime is nonzero? Certainly true for number fields.
  -- Idea of proof: show that if B/A is integral and B is an integral domain, then
  -- any nonzero element of B divides a nonzero element of A.
  -- In fact this definition should be made in that generality.
  -- Use `Algebra.exists_dvd_nonzero_if_isIntegral` in the FLT file MathlibExperiments/FrobeniusRiou.lean

variable {L} in
noncomputable def HeightOneSpectrum.of_comap (w : HeightOneSpectrum (𝓞 L)) :
    (HeightOneSpectrum.adicCompletion K (comap K w)) →+* (HeightOneSpectrum.adicCompletion L w) :=
  letI : UniformSpace K := (comap K w).adicValued.toUniformSpace;
  letI : UniformSpace L := w.adicValued.toUniformSpace;
  UniformSpace.Completion.mapRingHom (algebraMap K L) <| by
  sorry

open HeightOneSpectrum in
noncomputable def ProdAdicCompletions.baseChange :
    L ⊗[K] ProdAdicCompletions (𝓞 K) K →ₗ[K] ProdAdicCompletions (𝓞 L) L := TensorProduct.lift <| {
  toFun := fun l ↦ {
    toFun := fun kv w ↦ l • (of_comap K w (kv (comap K w)))
    map_add' := sorry
    map_smul' := sorry
  }
  map_add' := sorry
  map_smul' := sorry
}

-- hard but hopefully enough (this proof will be a lot of work)
theorem ProdAdicCompletions.baseChange_iso (x : ProdAdicCompletions (𝓞 K) K) :
  ProdAdicCompletions.IsFiniteAdele x ↔
  ProdAdicCompletions.IsFiniteAdele (ProdAdicCompletions.baseChange K L (1 ⊗ₜ x)) := sorry

-- Can we now write down the isomorphism L ⊗ 𝔸_K^∞ = 𝔸_L^∞ ?
