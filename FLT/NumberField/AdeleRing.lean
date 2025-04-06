import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom
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

section BaseChange

namespace NumberField.AdeleRing

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped notation:100 "𝔸" K => AdeleRing (𝓞 K) K

noncomputable instance : Algebra K (𝔸 L) :=
  Algebra.compHom _ (algebraMap K L)

instance : IsScalarTower K L (𝔸 L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical map from the adeles of K to the adeles of L -/
noncomputable def baseChange :
    (𝔸 K) →A[K] 𝔸 L :=
  sorry -- product of finite and infinite adele maps

open scoped TensorProduct

noncomputable instance : Algebra (𝔸  K) (L ⊗[K] 𝔸 K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] 𝔸 K) :=
  moduleTopology (𝔸 K) (L ⊗[K] 𝔸 K)

instance : IsModuleTopology (𝔸 K) (L ⊗[K] 𝔸 K) := ⟨rfl⟩

instance instPiIsModuleTopology : IsModuleTopology (𝔸 K) (Fin (Module.finrank K L) → 𝔸 K) :=
  IsModuleTopology.instPi

open DedekindDomain in
/-- The canonical `L`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L` induced by the
`K`-algebra base change map `𝔸_K → 𝔸_L`. -/
def baseChangeEquiv :
    (L ⊗[K] 𝔸 K) ≃A[L] 𝔸 L :=
  sorry

variable {L}

theorem baseChangeEquiv_tsum_apply_right (l : L) :
    baseChangeEquiv K L (l ⊗ₜ[K] 1) = algebraMap L (𝔸 L) l :=
  sorry

variable (L)

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
  let BC := baseChangeEquiv K L |>.toContinuousLinearEquiv |>.restrictScalars K
  π.trans BC

variable {K L}

open TensorProduct.AlgebraTensorModule in
theorem piEquiv_apply_of_algebraMap
    {x : Fin (Module.finrank K L) → 𝔸 K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (𝔸 K) (y i) = x i) :
    piEquiv K L x = algebraMap L _ (Module.Finite.equivPi _ _ |>.symm y) := by
  simp only [← funext h, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.restrictScalars_symm_apply, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.toRingHom_eq_coe, AlgEquiv.toLinearEquiv_symm,
    ContinuousLinearEquiv.restrictScalars_apply, IsModuleTopology.continuousLinearEquiv]
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
      (piEquiv K L).toAddMonoidHom
      = principalSubgroup (𝓞 L) L := by
  ext x
  simp only [AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv]
  refine ⟨fun ⟨a, h, ha⟩ => ha ▸ piEquiv_mem_principalSubgroup h, ?_⟩
  rintro ⟨a, rfl⟩
  use fun i => algebraMap K (𝔸 K) (Module.Finite.equivPi _ _ a i)
  refine ⟨fun i _ => ⟨Module.Finite.equivPi _ _ a i, rfl⟩, ?_⟩
  rw [piEquiv_apply_of_algebraMap (fun i => rfl), LinearEquiv.symm_apply_apply]

theorem comap_piEquiv_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup (𝓞 K) K))
      = (principalSubgroup (𝓞 L) L).comap (piEquiv K L).toAddMonoidHom := by
  rw [← piEquiv_map_principalSubgroup K L,
    AddSubgroup.comap_map_eq_self_of_injective (piEquiv K L).injective]

noncomputable def piQuotientEquiv :
    (Fin (Module.finrank K L) → (𝔸 K) ⧸ principalSubgroup (𝓞 K) K) ≃ₜ+
      (𝔸 L) ⧸ principalSubgroup (𝓞 L) L :=
  -- The map `⊕ 𝔸 K ≃L[K] 𝔸 L` reduces to quotients `⊕ 𝔸 K / K ≃ₜ+ 𝔸 L / L`
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ (piEquiv K L).toContinuousAddEquiv
      (comap_piEquiv_principalSubgroup K L)

end NumberField.AdeleRing

end BaseChange

section Discrete

open DedekindDomain

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {0} := by
  let integralAdeles := {f : FiniteAdeleRing (𝓞 ℚ) ℚ |
    ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
  use {f | ∀ v, f v ∈ (Metric.ball 0 1)} ×ˢ integralAdeles
  refine ⟨?_, ?_⟩
  · apply IsOpen.prod
    . rw [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro v
      exact Metric.isOpen_ball.preimage (continuous_apply v)
    sorry
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
      simp only [integralAdeles, Set.mem_setOf_eq] at h2
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
      · simp only [integralAdeles, Set.mem_setOf_eq]
        intro v
        apply zero_mem

variable (K : Type*) [Field K] [NumberField K]

theorem NumberField.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing (𝓞 K) K),
    IsOpen U ∧ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U = {0} := by
  obtain ⟨V, hV, hV0⟩ := Rat.AdeleRing.zero_discrete
  use (piEquiv ℚ K) '' {f | ∀i, f i ∈ V }
  constructor
  . rw [← (piEquiv ℚ K).coe_toHomeomorph, Homeomorph.isOpen_image, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact hV.preimage (continuous_apply i)
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  . rw [Set.eq_singleton_iff_unique_mem, Set.mem_preimage, map_zero] at hV0
    simp only [Set.mem_preimage, map_zero, Set.mem_image,
      EmbeddingLike.map_eq_zero_iff, exists_eq_right, Pi.zero_apply]
    exact fun _ => hV0.left
  intro x ⟨y, hy, hyx⟩
  apply (Module.Finite.equivPi ℚ K).injective
  set f := Module.Finite.equivPi ℚ K x
  let g := fun i => algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (f i)
  have hfg : ∀ i, (algebraMap _ _) (f i) = g i := fun i => rfl
  have hg := piEquiv_apply_of_algebraMap hfg
  simp only [LinearEquiv.symm_apply_apply, f, ← hyx, EquivLike.apply_eq_iff_eq] at hg
  subst hg
  ext i
  rw [map_zero, Pi.zero_apply, ← Set.mem_singleton_iff, ← hV0, Set.mem_preimage]
  exact hy i

-- Maybe this discreteness isn't even stated in the best way?
-- I'm ambivalent about how it's stated
open Pointwise in
theorem NumberField.AdeleRing.discrete : ∀ x : K, ∃ U : Set (AdeleRing (𝓞 K) K),
    IsOpen U ∧ (algebraMap K (AdeleRing (𝓞 K) K)) ⁻¹' U = {x} := by
  obtain ⟨V, hV, hV0⟩ := zero_discrete K
  intro x
  set ι  := algebraMap K (AdeleRing (𝓞 K) K)    with hι
  set xₐ := ι x                           with hxₐ
  set f  := Homeomorph.subLeft xₐ         with hf
  use f ⁻¹' V, f.isOpen_preimage.mpr hV
  have : f ∘ ι = ι ∘ Equiv.subLeft x := by ext; simp [hf, hxₐ]
  rw [← Set.preimage_comp, this, Set.preimage_comp, hV0]
  ext
  simp only [Set.mem_preimage, Equiv.subLeft_apply, Set.mem_singleton_iff, sub_eq_zero, eq_comm]

end Discrete

section Compact

open NumberField

theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  sorry -- issue #258

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) :=
  letI := Rat.AdeleRing.cocompact
  (piQuotientEquiv ℚ K).compactSpace

end Compact
