import Mathlib
import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.NumberField.InfiniteAdeleRing

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

section BaseChange

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField

variable [Algebra K (AdeleRing (𝓞 L) L)] [IsScalarTower K L (AdeleRing (𝓞 L) L)]

/-- The canonical map from the adeles of K to the adeles of L -/
noncomputable def NumberField.AdeleRing.baseChange :
    AdeleRing (𝓞 K) K →A[K] AdeleRing (𝓞 L) L :=
  sorry -- product of finite and infinite adele maps

open scoped TensorProduct

noncomputable instance : Algebra (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] AdeleRing (𝓞 K) K) :=
  moduleTopology (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K)

instance : IsModuleTopology (AdeleRing (𝓞 K) K) (L ⊗[K] AdeleRing (𝓞 K) K) := ⟨rfl⟩

/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.AdeleRing.baseChangeEquiv :
    (L ⊗[K] (AdeleRing (𝓞 K) K)) ≃A[L] AdeleRing (𝓞 L) L :=
  sorry

variable {L}

theorem NumberField.AdeleRing.baseChangeEquiv_tsum_apply_right (l : L) :
  baseChangeEquiv K L (l ⊗ₜ[K] 1) = algebraMap L (AdeleRing (𝓞 L) L) l := sorry

namespace NumberField.AdeleRing

scoped notation:100 "𝔸" K => AdeleRing (𝓞 K) K

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

noncomputable instance : Algebra K (𝔸 L) :=
  Algebra.compHom _ (algebraMap K L)

instance instPiIsModuleTopology : IsModuleTopology (𝔸 K) (Fin (Module.finrank K L) → 𝔸 K) :=
  IsModuleTopology.instPi

instance : IsScalarTower K L (𝔸 L) :=
  IsScalarTower.of_algebraMap_eq' rfl

open TensorProduct.AlgebraTensorModule in
noncomputable abbrev tensorProductEquivPi :
    L ⊗[K] (𝔸 K) ≃L[K] (Fin (Module.finrank K L) → 𝔸 K) :=
  letI := instPiIsModuleTopology K L
  -- `𝔸 K ⊗[K] L ≃ₗ[𝔸 K] L ⊗[K] 𝔸 K`
  -- Note: needs to be this order to avoid instance clash with inferred leftAlgebra
  let comm := (Algebra.TensorProduct.comm K (𝔸 K) L).extendScalars (𝔸 K) |>.toLinearEquiv
  -- `𝔸 K ⊗[K] L ≃ₗ[𝔸 K] ⊕ 𝔸 K`
  let π := finiteEquivPi K L (𝔸 K)
  -- Stitch together to get `L ⊗[K] 𝔸 K ≃ₗ[𝔸 K] ⊕ 𝔸 K`, which is automatically
  -- continuous due to `𝔸 K` module topologies on both sides, then restrict scalars to `K`
  IsModuleTopology.continuousLinearEquiv (comm.symm.trans π) |>.restrictScalars K

noncomputable abbrev piEquiv :
    (Fin (Module.finrank K L) → 𝔸 K) ≃L[K] 𝔸 L :=
  -- `⊕ 𝔸 K ≃L[K] L ⊗[K] 𝔸 K` from previous def
  let π := (tensorProductEquivPi K L).symm
  -- `L ⊗[K] 𝔸 K ≃L[K] 𝔸 L` base change  restricted to `K` as a continuous linear equiv
  let BC := baseChangeEquiv K L |>.restrictScalars K |>.toContinuousLinearEquiv
  π.trans BC

variable {K L}

open TensorProduct.AlgebraTensorModule in
theorem piEquiv_apply_of_algebraMap
    {x : Fin (Module.finrank K L) → 𝔸 K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (𝔸 K) (y i) = x i) :
    piEquiv K L x = algebraMap L _ (Module.Finite.equivPi _ _ |>.symm y) := by
  simp [← funext h]
  simp only [IsModuleTopology.continuousLinearEquiv]
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, finiteEquivPi_symm_apply]
  simp [AlgEquiv.extendScalars, ContinuousAlgEquiv.toContinuousLinearEquiv_apply,
    baseChangeEquiv_tsum_apply_right]

theorem piEquiv_mem_principalSubgroup
    {x : Fin (Module.finrank K L) → 𝔸 K}
    (h : x ∈ AddSubgroup.pi Set.univ (fun _ => principalSubgroup (𝓞 K) K)) :
    piEquiv K L x ∈ principalSubgroup (𝓞 L) L := by
  simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const] at h
  choose y hy using h
  exact piEquiv_apply_of_algebraMap hy ▸ ⟨Module.Finite.equivPi _ _ |>.symm y, rfl⟩

variable (K L)

theorem piEquiv_map_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup (𝓞 K) K)).map
      (piEquiv K L).toAddMonoidHom = principalSubgroup (𝓞 L) L := by
  ext x
  simp only [AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun ⟨a, h, ha⟩ => ha ▸ piEquiv_mem_principalSubgroup h, ?_⟩
  rintro ⟨a, rfl⟩
  use fun i => algebraMap K (AdeleRing (𝓞 K) K) (Module.Finite.equivPi _ _ a i)
  refine ⟨fun i _ => ⟨Module.Finite.equivPi _ _ a i, rfl⟩, ?_⟩
  rw [piEquiv_apply_of_algebraMap (fun i => rfl), LinearEquiv.symm_apply_apply]

noncomputable def piQuotientEquiv :
    (Fin (Module.finrank K L) → (𝔸 K) ⧸ principalSubgroup (𝓞 K) K) ≃ₜ+
      (𝔸 L) ⧸ principalSubgroup (𝓞 L) L :=
  -- The map `⊕ 𝔸 K ≃L[K] 𝔸 L` reduces to quotients `⊕ 𝔸 K / K ≃ₜ+ 𝔸 L / L`
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ _ _ (piEquiv K L).toContinuousAddEquiv
      (piEquiv_map_principalSubgroup K L)

end NumberField.AdeleRing

end BaseChange

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  sorry -- issue #258

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  letI := Rat.AdeleRing.cocompact
  (piQuotientEquiv ℚ K).compactSpace

end Compact
