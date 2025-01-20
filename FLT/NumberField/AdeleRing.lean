import Mathlib
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv

open scoped TensorProduct

universe u

open NumberField

section LocallyCompact

-- see https://github.com/smmercuri/adele-ring_locally-compact
-- for a proof of this

variable (K : Type*) [Field K] [NumberField K]

instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  sorry -- issue #253

end LocallyCompact

section BaseChange

namespace NumberField.AdeleRing

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

noncomputable instance : Algebra K (NumberField.AdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)

noncomputable abbrev tensorProductLinearEquivPi : L ⊗[K] AdeleRing (𝓞 K) K ≃ₗ[K]
    (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) :=
  (TensorProduct.comm _ _ _).trans <|
  LinearEquiv.trans (TensorProduct.congr (LinearEquiv.refl K (AdeleRing (𝓞 K) K))
      (Basis.equivFun (Module.finBasis K L)))
    (TensorProduct.piScalarRight _ _ _ _)

variable {L}

theorem tensorProductLinearEquivPi_tsum_apply (l : L) :
    tensorProductLinearEquivPi K L (l ⊗ₜ[K] 1) =
      fun i => algebraMap _ _ (Module.finBasis K L |>.equivFun l i) := by
  simp [tensorProductLinearEquivPi, Algebra.algebraMap_eq_smul_one]

variable {K}

theorem tensorProductLinearEquivPi_symm_apply_of_algebraMap
    (x : Fin (Module.finrank K L) → K) :
    (tensorProductLinearEquivPi K L).symm (fun i => algebraMap _ _ (x i)) =
      ((Module.finBasis K L).equivFun.symm x) ⊗ₜ[K] 1 := by
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply, TensorProduct.comm_symm_tmul,
    Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap, TensorProduct.congr_symm_tmul,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, map_sum, Basis.equivFun_symm_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, Fintype.sum_pi_single]

-- TODO : Use `moduleTopology`
instance : TopologicalSpace (L ⊗[K] NumberField.AdeleRing (𝓞 K) K) :=
  TopologicalSpace.induced (NumberField.AdeleRing.tensorProductLinearEquivPi K L) inferInstance

variable (K L)

noncomputable def tensorProductContinuousLinearEquivPi :
    L ⊗[K] AdeleRing (𝓞 K) K ≃L[K] (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) where
  toLinearEquiv := tensorProductLinearEquivPi K L
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert (tensorProductLinearEquivPi K L).toEquiv.coinduced_symm ▸ continuous_coinduced_rng

variable {K L}

theorem tensorProductContinuousLinearEquivPi_symm_apply_of_algebraMap
    (x : Fin (Module.finrank K L) → K) :
    (tensorProductContinuousLinearEquivPi K L).symm (fun i => algebraMap _ _ (x i)) =
      ((Module.finBasis K L).equivFun.symm x) ⊗ₜ[K] 1 := by
  exact tensorProductLinearEquivPi_symm_apply_of_algebraMap _

variable (K L)

-- TODO: make this `L`-algebra equiv (works but causes an issue further down the line)
def baseChange : L ⊗[K] AdeleRing (𝓞 K) K ≃A[K] AdeleRing (𝓞 L) L := sorry

variable {L}

theorem baseChange_tsum_apply_right (l : L) :
  baseChange K L (l ⊗ₜ[K] 1) = algebraMap L (AdeleRing (𝓞 L) L) l := sorry

variable (L)

noncomputable def baseChangePi :
    (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) ≃L[K] AdeleRing (𝓞 L) L :=
  (tensorProductContinuousLinearEquivPi K L).symm.trans (baseChange K L).toContinuousLinearEquiv

variable {K L}

theorem baseChangePi_apply (x : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K) :
    baseChangePi K L x = baseChange K L ((tensorProductContinuousLinearEquivPi K L).symm x) := rfl

theorem baseChangePi_apply_eq_algebraMap_comp
    {x : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (AdeleRing (𝓞 K) K) (y i) = x i) :
    baseChangePi K L x = algebraMap L (AdeleRing (𝓞 L) L) ((Module.finBasis K L).equivFun.symm y) := by
  rw [← funext h, baseChangePi_apply, tensorProductContinuousLinearEquivPi_symm_apply_of_algebraMap,
    baseChange_tsum_apply_right]

theorem baseChangePi_mem_principalSubgroup
    {x : Fin (Module.finrank K L) → AdeleRing (𝓞 K) K}
    (h : x ∈ AddSubgroup.pi Set.univ (fun _ => principalSubgroup (𝓞 K) K)) :
    baseChangePi K L x ∈ principalSubgroup (𝓞 L) L := by
  simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const] at h
  choose y hy using h
  exact baseChangePi_apply_eq_algebraMap_comp hy ▸ ⟨(Module.finBasis K L).equivFun.symm y, rfl⟩

variable (K L)

theorem baseChangePi_map_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup (𝓞 K) K)).map
      (baseChangePi K L).toAddMonoidHom = principalSubgroup (𝓞 L) L := by
  ext x
  simp only [AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun ⟨a, h, ha⟩ => ha ▸ baseChangePi_mem_principalSubgroup h, ?_⟩
  rintro ⟨a, rfl⟩
  use fun i => algebraMap K (AdeleRing (𝓞 K) K) ((Module.finBasis K L).equivFun a i)
  refine ⟨fun i _ => ⟨(Module.finBasis K L).equivFun a i, rfl⟩, ?_⟩
  rw [baseChangePi_apply_eq_algebraMap_comp (fun i => rfl), LinearEquiv.symm_apply_apply]

noncomputable def baseChangeQuotientPi :
    (Fin (Module.finrank K L) → AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) ≃ₜ+
      AdeleRing (𝓞 L) L ⧸ principalSubgroup (𝓞 L) L :=
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ _ _ (baseChangePi K L).toContinuousAddEquiv
      (baseChangePi_map_principalSubgroup K L)

end NumberField.AdeleRing

end BaseChange

section Discrete

open DedekindDomain

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {0} := by
  use {f | ∀ v, f v ∈ (Metric.ball 0 1)} ×ˢ
    {f | ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
  refine ⟨?_, ?_⟩
  · dsimp
    sorry -- issue #252 -- should be easy (product of opens is open, product of integers is surely
          -- known to be open)
  · apply subset_antisymm
    · intro x hx
      rw [Set.mem_preimage] at hx
      simp only [Set.mem_singleton_iff]
      have : (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) x =
        (algebraMap ℚ (InfiniteAdeleRing ℚ) x, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x)
      · rfl
      rw [this] at hx
      clear this
      rw [Set.mem_prod] at hx
      obtain ⟨h1, h2⟩ := hx
      dsimp only at h1 h2
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq,
        InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
      simp only [Set.mem_setOf_eq] at h2
      specialize h1 Rat.infinitePlace
      change ‖(x : ℂ)‖ < 1 at h1
      simp at h1
      have intx: ∃ (y:ℤ), y = x
      · obtain ⟨z, hz⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
            ℚ x <| fun v ↦ by
          specialize h2 v
          letI : UniformSpace ℚ := v.adicValued.toUniformSpace
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h2
          rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        use Rat.ringOfIntegersEquiv z
        rw [← hz]
        apply Rat.ringOfIntegersEquiv_eq_algebraMap
      obtain ⟨y, rfl⟩ := intx
      simp only [abs_lt] at h1
      norm_cast at h1 ⊢
      -- We need the next line because `norm_cast` is for some reason producing a `negSucc 0`.
      -- I haven't been able to isolate this behaviour even in a standalone lemma.
      -- We could also make `omega` more robust against accidental appearances of `negSucc`.
      rw [Int.negSucc_eq] at h1
      omega
    · intro x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      rintro rfl
      simp only [map_zero]
      change (0, 0) ∈ _
      simp only [Prod.mk_zero_zero, Set.mem_prod, Prod.fst_zero, Prod.snd_zero]
      constructor
      · simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
        intro v
        have : ‖(0:InfiniteAdeleRing ℚ) v‖ = 0
        · simp only [norm_eq_zero]
          rfl
        simp [this, zero_lt_one]
      · simp only [Set.mem_setOf_eq]
        intro v
        apply zero_mem

-- Maybe this discreteness isn't even stated in the best way?
-- I'm ambivalent about how it's stated
open Pointwise in
theorem Rat.AdeleRing.discrete : ∀ q : ℚ, ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {q} := by
  obtain ⟨V, hV, hV0⟩ := zero_discrete
  intro q
  set ι  := algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)    with hι
  set qₐ := ι q                           with hqₐ
  set f  := Homeomorph.subLeft qₐ         with hf
  use f ⁻¹' V, f.isOpen_preimage.mpr hV
  have : f ∘ ι = ι ∘ Homeomorph.subLeft q := by ext; simp [hf, hqₐ]
  rw [← Set.preimage_comp, this, Set.preimage_comp, hV0]
  ext
  simp only [Set.mem_preimage, Homeomorph.subLeft_apply, Set.mem_singleton_iff, sub_eq_zero, eq_comm]

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.discrete : ∀ k : K, ∃ U : Set (AdeleRing (𝓞 K) K),
    IsOpen U ∧ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U = {k} := sorry -- issue #257

end Discrete

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  sorry -- issue #258

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  letI := Rat.AdeleRing.cocompact
  (baseChangeQuotientPi ℚ K).compactSpace

end Compact
