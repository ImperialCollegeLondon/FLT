import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.NumberField.InfiniteAdeleRing
import FLT.Mathlib.Algebra.Algebra.Tower
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.LinearAlgebra.TensorProduct.Prod
import FLT.NumberField.FiniteAdeleRing

open scoped TensorProduct

universe u

open NumberField

section LocallyCompact

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum in
instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  Prod.locallyCompactSpace _ _

end LocallyCompact

section BaseChange

namespace NumberField.AdeleRing

open IsDedekindDomain

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `𝔸 K` for `K` a number field, is notation for `AdeleRing (𝓞 K) K`. -/
scoped notation:100 "𝔸" K => AdeleRing (𝓞 K) K

-- I am not mad keen on this instance. But we don't have continuous semialgebra maps I don't think.
noncomputable instance : Algebra K (𝔸 L) :=
  inferInstanceAs (Algebra K (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))

instance : IsScalarTower K L (𝔸 L) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The canonical map from the adeles of K to the adeles of L -/
noncomputable def baseChange :
    (𝔸 K) →A[K] 𝔸 L :=
  let finite : FiniteAdeleRing (𝓞 K) K →A[K] FiniteAdeleRing (𝓞 L) L := {
    __ := Algebra.algHom _ _ _
    cont := FiniteAdeleRing.mapSemialgHom_continuous (𝓞 K) K L (𝓞 L)
  }
  let infinite : InfiniteAdeleRing K →A[K] InfiniteAdeleRing L := {
    __ := Algebra.algHom _ _ _
    cont := NumberField.InfiniteAdeleRing.baseChange_cont K L
  }
  ContinuousAlgHom.prod
    (infinite.comp <| ContinuousAlgHom.fst K (InfiniteAdeleRing K) _)
    (finite.comp <| ContinuousAlgHom.snd K (InfiniteAdeleRing K) _)

/-- `baseChange` as a `SemialgHom` -/
noncomputable def baseChangeSemialgHom :
  (𝔸 K) →ₛₐ[algebraMap K L] 𝔸 L where
    __ := baseChange K L
    map_smul' x y := by simp

open scoped TensorProduct

noncomputable instance : Algebra (𝔸 K) (𝔸 L) :=
  (baseChangeSemialgHom K L).toAlgebra

instance instPiIsModuleTopology : IsModuleTopology (𝔸 K) (Fin (Module.finrank K L) → 𝔸 K) :=
  IsModuleTopology.instPi

instance instBaseChangeIsModuleTopology : IsModuleTopology (𝔸 K) (𝔸 L) := by
  have := BaseChange.isModuleTopology (𝓞 K) K L (𝓞 L)
  exact IsModuleTopology.instProd' (A := InfiniteAdeleRing K)
    (B := FiniteAdeleRing (𝓞 K) K) (M := InfiniteAdeleRing L) (N := FiniteAdeleRing (𝓞 L) L)

open scoped TensorProduct.RightActions in
/-- The canonical `𝔸 K`-algebra homomorphism `(L ⊗_K 𝔸 K) → 𝔸 L` induced
by the maps from `L` and `𝔸 K` into `𝔸 L`. -/
noncomputable def baseChangeAdeleAlgHom : (L ⊗[K] 𝔸 K) →ₐ[𝔸 K] 𝔸 L :=
  (baseChangeSemialgHom K L).baseChangeRightOfAlgebraMap

-- do we not have this?? Move! PR! TODO
/-- Product of algebra equivalences; the maps come from Equiv.prodCongr. -/
def _root_.AlgEquiv.prodCongr {R A A₂ A₃ A₄ : Type*} [CommSemiring R]
    [Semiring A] [Semiring A₂] [Semiring A₃] [Semiring A₄] [Algebra R A]
    [Algebra R A₂] [Algebra R A₃] [Algebra R A₄]
    (e₁ : A ≃ₐ[R] A₂) (e₂ : A₃ ≃ₐ[R] A₄) :
    (A × A₃) ≃ₐ[R] (A₂ × A₄) where
  __ := LinearEquiv.prodCongr e₁.toLinearEquiv e₂.toLinearEquiv
  map_mul' := by simp
  commutes' := by simp

/-- The L-algebra isomorphism `L ⊗[K] 𝔸_K = 𝔸_L`. -/
noncomputable def baseChangeAdeleAlgEquiv : (L ⊗[K] 𝔸 K) ≃ₐ[L] 𝔸 L :=
  let tensor :=
    Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  let prod := AlgEquiv.prodCongr
    (NumberField.InfiniteAdeleRing.baseChangeEquivAux K L)
    (FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L))
  tensor.trans prod

@[simp] lemma baseChangeAdeleAlgEquiv_apply (l : L) (a : 𝔸 K) :
    baseChangeAdeleAlgEquiv K L (l ⊗ₜ a) = algebraMap _ _ l * algebraMap _ _ a := by
  rfl

open scoped TensorProduct.RightActions in
lemma baseChangeAdeleAlgHom_bijective : Function.Bijective (baseChangeAdeleAlgHom K L) := by
  -- There's a linear equivlance `(L ⊗_K 𝔸 K) ≅ 𝔸 L`
  let linearEquiv : (L ⊗[K] 𝔸 K) ≃ₗ[L] 𝔸 L :=
    let tensor := TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
    let prod := LinearEquiv.prodCongr (InfiniteAdeleRing.baseChangeEquiv K L).toLinearEquiv
      (FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L)).toLinearEquiv
    tensor.trans prod
  -- and it's given by an equal function to the algebra homomorphism we've defined.
  have eqEquiv : ⇑(baseChangeAdeleAlgHom K L) = ⇑(linearEquiv) := by
    show ⇑((baseChangeAdeleAlgHom K L).toLinearMap.restrictScalars K) =
      ⇑(linearEquiv.toLinearMap.restrictScalars K)
    exact congr_arg DFunLike.coe (TensorProduct.ext' fun x y ↦ rfl)
  rw [eqEquiv]
  exact linearEquiv.bijective

open scoped TensorProduct.RightActions in
/-- The canonical `𝔸_K`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L` induced by the
base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeAdeleEquiv : (L ⊗[K] 𝔸 K) ≃A[𝔸 K] 𝔸 L :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <|
    AlgEquiv.ofBijective (baseChangeAdeleAlgHom K L) (baseChangeAdeleAlgHom_bijective K L)

open scoped TensorProduct.RightActions in
/-- The canonical `L`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L` induced by the
`K`-algebra base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeEquiv :
    (L ⊗[K] 𝔸 K) ≃A[L] 𝔸 L where
  __ := (baseChangeSemialgHom K L).baseChange_of_algebraMap
  __ := baseChangeAdeleEquiv K L

-- this isn't rfl. Explanation below
example (x : L ⊗[K] 𝔸 K) : baseChangeEquiv K L x = baseChangeAdeleAlgEquiv K L x := by
  induction x with
  | zero => rfl
  | tmul x y => rfl
  | add x y _ _ => simp_all

/-

We have two isomorphisms `(L ⊗[K] 𝔸 K) = 𝔸 L`.

1)
`baseChangeEquiv` is
  `(baseChangeSemialgHom K L).baseChange_of_algebraMap` *and
  `baseChangeAdeleEquiv`. The latter is `baseChangeAdeleAlgHom` which is
  `(baseChangeSemialgHom K L).baseChangeRightOfAlgebraMap`

Note:
```
example (x : L ⊗[K] 𝔸 K) :
    (baseChangeSemialgHom K L).baseChange_of_algebraMap x =
    (baseChangeSemialgHom K L).baseChangeRightOfAlgebraMap x := by
  rfl
```

This map is defined as "there is a commutative square `K → L → 𝔸 L` and `K → 𝔸 K → 𝔸 L`
so there's an induced map `L ⊗[K] 𝔸 K → 𝔸 L`; this is a bijection"

But `baseChangeAdeleAlgEquiv` is `tensor.trans prod` i.e.

`(L ⊗[K] 𝔸 K) = L ⊗[K] (𝔸^∞ x A_∞) ≅ (L ⊗[K] 𝔸^∞) x (L ⊗[K] 𝔸_∞) ≅ 𝔸_L^∞ x 𝔸_L_∞

-/

variable {L}

theorem baseChangeEquiv_tsum_apply_right (l : L) :
    baseChangeEquiv K L (l ⊗ₜ[K] 1) = algebraMap L (𝔸 L) l := by
  have h : (l ⊗ₜ[K] (1 : 𝔸 K)) = l • 1 := by
    simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  simp [h, Algebra.algebraMap_eq_smul_one]

variable (L)

open scoped TensorProduct.RightActions in
open TensorProduct.AlgebraTensorModule in
/-- A continuous `K`-linear isomorphism `L ⊗[K] 𝔸_K = (𝔸_K)ⁿ` for `n = [L:K]` -/
noncomputable abbrev tensorProductEquivPi :
    L ⊗[K] (𝔸 K) ≃L[K] (Fin (Module.finrank K L) → 𝔸 K) :=
  letI := instPiIsModuleTopology K L
  -- `𝔸 K ⊗[K] L ≃ₗ[𝔸 K] L ⊗[K] 𝔸 K`
  -- Note: needs to be this order to avoid instance clash with inferred leftAlgebra
  let comm := (TensorProduct.RightActions.Algebra.TensorProduct.comm K (𝔸 K) L) |>.toLinearEquiv
  -- `𝔸 K ⊗[K] L ≃ₗ[𝔸 K] ⊕ 𝔸 K`
  let π := finiteEquivPi K L (𝔸 K)
  -- Stitch together to get `L ⊗[K] 𝔸 K ≃ₗ[𝔸 K] ⊕ 𝔸 K`, which is automatically
  -- continuous due to `𝔸 K` module topologies on both sides, then restrict scalars to `K`
  IsModuleTopology.continuousLinearEquiv (comm.symm.trans π) |>.restrictScalars K

open scoped TensorProduct.RightActions in
/-- A continuous `K`-linear isomorphism `(𝔸_K)ⁿ ≃ 𝔸_L` for `n = [L:K]` -/
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
    ContinuousLinearEquiv.restrictScalars_apply, IsModuleTopology.continuousLinearEquiv_symm_apply]
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

/-- A continuous additive isomorphism `(𝔸_K / K)ⁿ = 𝔸_L / L` where `n = [L:K]`. -/
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

open IsDedekindDomain

theorem Rat.AdeleRing.zero_discrete : ∃ U : Set (AdeleRing (𝓞 ℚ) ℚ),
    IsOpen U ∧ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) ⁻¹' U = {0} := by
  let integralAdeles := {f : FiniteAdeleRing (𝓞 ℚ) ℚ |
    ∀ v , f v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v}
  use {f | ∀ v, f v ∈ (Metric.ball 0 1)} ×ˢ integralAdeles
  refine ⟨?_, ?_⟩
  · apply IsOpen.prod
    · rw [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro v
      exact Metric.isOpen_ball.preimage (continuous_apply v)
    · exact RestrictedProduct.isOpen_forall_mem fun v ↦ Valued.isOpen_integer _
  · apply subset_antisymm
    · intro x hx
      rw [Set.mem_preimage] at hx
      simp only [Set.mem_singleton_iff]
      rw [show (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) x =
        (algebraMap ℚ (InfiniteAdeleRing ℚ) x, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) x)
        from rfl] at hx
      rw [Set.mem_prod] at hx
      obtain ⟨h1, h2⟩ := hx
      dsimp only at h1 h2
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq,
        InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
      simp only [integralAdeles, Set.mem_setOf_eq] at h2
      specialize h1 Rat.infinitePlace
      change ‖(x : ℂ)‖ < 1 at h1
      simp only [Complex.norm_ratCast, integralAdeles] at h1
      have intx: ∃ (y:ℤ), y = x := by
        obtain ⟨z, hz⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
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
        have : ‖(0:InfiniteAdeleRing ℚ) v‖ = 0 := by
          simp only [norm_eq_zero]
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
  · rw [← (piEquiv ℚ K).coe_toHomeomorph, Homeomorph.isOpen_image, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact hV.preimage (continuous_apply i)
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · rw [Set.eq_singleton_iff_unique_mem, Set.mem_preimage, map_zero] at hV0
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
  let ι  := algebraMap K (AdeleRing (𝓞 K) K)
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
