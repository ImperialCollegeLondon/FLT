import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.NumberField.FiniteAdeleRing
import FLT.NumberField.InfiniteAdeleRing
import FLT.NumberField.Padics.RestrictedProduct
import FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdeleRing

open scoped TensorProduct

universe u

open NumberField

section LocallyCompact

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum in
instance NumberField.AdeleRing.locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  Prod.locallyCompactSpace _ _

end LocallyCompact

section T2

variable (K : Type*) [Field K] [NumberField K]

instance : T2Space (AdeleRing (𝓞 K) K) := by
  unfold AdeleRing IsDedekindDomain.FiniteAdeleRing
  infer_instance

end T2

section BaseChange

namespace NumberField.AdeleRing

open IsDedekindDomain

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `𝔸 K` for `K` a number field, is notation for `AdeleRing (𝓞 K) K`. -/
scoped notation:101 "𝔸" K => AdeleRing (𝓞 K) K

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

-- Note that this creates a diamond if K = L; however `Algebra.id` has a higher-than-default
-- priority so hopefully most of the time it won't cause problems.
noncomputable instance : Algebra (𝔸 K) (𝔸 L) :=
  (baseChangeSemialgHom K L).toAlgebra

instance instPiIsModuleTopology : IsModuleTopology (𝔸 K) (Fin (Module.finrank K L) → 𝔸 K) :=
  IsModuleTopology.instPi

instance instBaseChangeIsModuleTopology : IsModuleTopology (𝔸 K) (𝔸 L) := by
  exact IsModuleTopology.instProd' (A := InfiniteAdeleRing K)
    (B := FiniteAdeleRing (𝓞 K) K) (M := InfiniteAdeleRing L) (N := FiniteAdeleRing (𝓞 L) L)

open scoped TensorProduct.RightActions in
/-- The canonical `𝔸 K`-algebra homomorphism `(L ⊗_K 𝔸 K) → 𝔸 L` induced
by the maps from `L` and `𝔸 K` into `𝔸 L`. -/
noncomputable def baseChangeAdeleAlgHom : (L ⊗[K] (𝔸 K)) →ₐ[𝔸 K] 𝔸 L :=
  (baseChangeSemialgHom K L).baseChangeRightOfAlgebraMap

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
  -- There's a linear equivalence `(L ⊗_K 𝔸 K) ≅ 𝔸 L`
  let linearEquiv : (L ⊗[K] 𝔸 K) ≃ₗ[L] 𝔸 L :=
    let tensor := TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
    let prod := LinearEquiv.prodCongr (InfiniteAdeleRing.baseChangeEquiv K L).toLinearEquiv
      (FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L)).toLinearEquiv
    tensor.trans prod
  -- and it's given by an equal function to the algebra homomorphism we've defined.
  have eqEquiv : ⇑(baseChangeAdeleAlgHom K L) = ⇑(linearEquiv) := by
    change ⇑((baseChangeAdeleAlgHom K L).toLinearMap.restrictScalars K) =
      ⇑(linearEquiv.toLinearMap.restrictScalars K)
    exact congr_arg DFunLike.coe (TensorProduct.ext' fun x y ↦ rfl)
  rw [eqEquiv]
  exact linearEquiv.bijective

open scoped TensorProduct.RightActions in
/-- The canonical `𝔸_K`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L`
induced by the base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeAlgAdeleEquiv : (L ⊗[K] 𝔸 K) ≃ₐ[𝔸 K] 𝔸 L :=
    AlgEquiv.ofBijective (baseChangeAdeleAlgHom K L) (baseChangeAdeleAlgHom_bijective K L)

open scoped TensorProduct.RightActions in
/-- The canonical continuous `𝔸_K`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L`
induced by the base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeAdeleEquiv : (L ⊗[K] 𝔸 K) ≃A[𝔸 K] 𝔸 L :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAlgAdeleEquiv K L

open scoped TensorProduct.RightActions in
instance : Module.Finite (𝔸 K) (𝔸 L) :=
  Module.Finite.equiv (baseChangeAlgAdeleEquiv K L).toLinearEquiv

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

section vector_space

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as L-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeAddEquiv :
    V ⊗[K] (𝔸 K) ≃ₗ[L] (V ⊗[L] (𝔸 L)) :=
  TensorProduct.AlgebraTensorModule.congr ((TensorProduct.rid L V).symm) (.refl _ _) ≪≫ₗ
  TensorProduct.AlgebraTensorModule.assoc K L L V L (𝔸 K) ≪≫ₗ
  (LinearEquiv.lTensor V
    ((NumberField.AdeleRing.baseChangeAdeleAlgEquiv K L).toLinearEquiv.symm)).symm

@[simp] lemma ModuleBaseChangeAddEquiv_apply
    (v : V) (a : 𝔸 K) : ModuleBaseChangeAddEquiv K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeAddEquiv]

open scoped TensorProduct.RightActions in
/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeAddEquiv' [Module (𝔸 K) (V ⊗[L] 𝔸 L)]
    [IsScalarTower (𝔸 K) (𝔸 L) (V ⊗[L] 𝔸 L)] :
    V ⊗[K] (𝔸 K) ≃ₗ[𝔸 K] (V ⊗[L] (𝔸 L)) where
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddEquiv
  map_smul' a vb := by
    induction vb with
    | zero => simp
    | tmul x y =>
        simp [TensorProduct.smul_tmul', -algebraMap_smul,
          algebra_compatible_smul (AdeleRing (𝓞 L) L) a]
    | add x y _ _ => simp_all

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeContinuousSemilinearMap :
    V ⊗[K] (𝔸 K) →ₛₗ[algebraMap (𝔸 K) (𝔸 L)] V ⊗[L] 𝔸 L where
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddMonoidHom
  map_smul' a bc := by
    induction bc with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul', Algebra.smul_def]
    | add x y _ _ => simp_all

lemma ModuleBaseChangeContinuousSemilinearMap_apply
    (v : V) (a : 𝔸 K) :
    ModuleBaseChangeContinuousSemilinearMap K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeContinuousSemilinearMap]

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological additive groups
for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeContinuousAddEquiv
    (V : Type*) [AddCommGroup V] [Module L V] [Module K V]
    [IsScalarTower K L V] [FiniteDimensional L V] [FiniteDimensional K V] :
    V ⊗[K] (𝔸 K) ≃ₜ+ (V ⊗[L] (𝔸 L)) := by
  -- The trick is to make `(V ⊗[L] (𝔸 L))` into an 𝔸 K-module
  let : Module (AdeleRing (𝓞 K) K) (V ⊗[L] AdeleRing (𝓞 L) L) :=
    Module.compHom _ (algebraMap (𝔸 K) (𝔸 L))
  -- and ultimately prove that both sides have the 𝔸 K-module topology
  -- so the result will follow from the fact that linear maps are
  -- automatically continuous for the module topology.
  have : IsScalarTower (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (V ⊗[L] AdeleRing (𝓞 L) L) :=
    .of_algebraMap_smul fun r ↦ congrFun rfl
  have : ContinuousSMul (AdeleRing (𝓞 K) K) (V ⊗[L] AdeleRing (𝓞 L) L) :=
    IsScalarTower.continuousSMul (AdeleRing (𝓞 L) L)
  have ⟨h2⟩ : IsModuleTopology (AdeleRing (𝓞 L) L) (V ⊗[L] AdeleRing (𝓞 L) L) :=
    inferInstance
  have : IsModuleTopology (AdeleRing (𝓞 K) K) (V ⊗[L] AdeleRing (𝓞 L) L) := {
    eq_moduleTopology' := by rwa [moduleTopology.trans (𝔸 K) (𝔸 L) (V ⊗[L] (𝔸 L))] }
  exact {
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (ModuleBaseChangeAddEquiv' K L V : V ⊗[K] (𝔸 K) ≃ₗ[𝔸 K] (V ⊗[L] (𝔸 L))).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (ModuleBaseChangeAddEquiv' K L V : V ⊗[K] (𝔸 K) ≃ₗ[𝔸 K] (V ⊗[L] (𝔸 L))).symm.toLinearMap
  }

end vector_space

variable {K L}

open TensorProduct.AlgebraTensorModule in
theorem piEquiv_apply_of_algebraMap
    {x : Fin (Module.finrank K L) → 𝔸 K}
    {y : Fin (Module.finrank K L) → K}
    (h : ∀ i, algebraMap K (𝔸 K) (y i) = x i) :
    piEquiv K L x = algebraMap L _ (Module.Finite.equivPi _ _ |>.symm y) := by
  simp only [← funext h, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.restrictScalars_symm_apply,
    ContinuousLinearEquiv.restrictScalars_apply, IsModuleTopology.continuousLinearEquiv_symm_apply]
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, finiteEquivPi_symm_apply]
  simp [ContinuousAlgEquiv.toContinuousLinearEquiv_apply, baseChangeEquiv_tsum_apply_right]

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
      (piEquiv_map_principalSubgroup K L)

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
      simp only [Complex.norm_ratCast] at h1
      have intx: ∃ (y:ℤ), y = x := by
        obtain ⟨z, hz⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
            ℚ x <| fun v ↦ by
          specialize h2 v
          letI : UniformSpace ℚ := v.adicValued.toUniformSpace
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h2
          rwa [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        use Rat.ringOfIntegersEquiv z
        rw [← hz]
        apply Rat.ringOfIntegersEquiv_apply_coe
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
      simp only [Prod.mk_zero_zero]
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
      EmbeddingLike.map_eq_zero_iff, exists_eq_right]
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

open NumberField IsDedekindDomain RestrictedProduct PadicInt HeightOneSpectrum FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

namespace Rat.FiniteAdeleRing

local instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

/-- The `ℚ`-algebra equivalence between `FiniteAdeleRing (𝓞 ℚ) ℚ` and the restricted
product `Πʳ (p : Nat.Primes), [ℚ_[p], subring p]` of `Padic`s lifting the equivalence
`v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[v.natGenerator]` at each place. -/
noncomputable
def padicEquiv : FiniteAdeleRing (𝓞 ℚ) ℚ ≃ₐ[ℚ] Πʳ (p : Nat.Primes), [ℚ_[p], subring p] where
  __ := RingEquiv.restrictedProductCongr
      ratEquiv (Function.Injective.comap_cofinite_eq ratEquiv.injective).symm
      (fun v ↦ v.padicEquiv.toRingEquiv) (Filter.Eventually.of_forall padicEquiv_bijOn)
  commutes' q := by
    ext p
    obtain ⟨v, rfl⟩ := ratEquiv.surjective p
    change _ = algebraMap ℚ ℚ_[v.natGenerator] q
    -- was `simp` when `FiniteAdeleRing` was an `abbrev`.
    -- Ask on Zulip?
    simp [IsDedekindDomain.algebraMap_apply (𝓞 ℚ)]

theorem padicEquiv_bijOn :
    Set.BijOn padicEquiv (integralAdeles (𝓞 ℚ) ℚ)
      (structureSubring (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ subring p) Filter.cofinite) := by
  exact RingEquiv.restrictedProductCongr_bijOn_structureSubring
    (A₂ := fun p : Nat.Primes ↦ subring p)
    ratEquiv (Function.Injective.comap_cofinite_eq ratEquiv.injective).symm
    (fun v ↦ v.padicEquiv.toRingEquiv) (fun v ↦ v.padicEquiv_bijOn)

open FiniteAdeleRing in
theorem sub_mem_integralAdeles
    (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ x : ℚ, a - algebraMap ℚ _ x ∈ integralAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨q, hq⟩ := RestrictedProduct.padic_exists_sub_mem_structureSubring (padicEquiv a)
  use q
  simpa using padicEquiv_bijOn.symm (padicEquiv.toEquiv.invOn) |>.mapsTo hq

end Rat.FiniteAdeleRing

-- definitely shouldn't be here!
lemma Int.eq_floor {a : ℝ} {b : ℤ} (h1 : 0 ≤ a - b) (h2 : a - b < 1) : b = ⌊a⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  grind

open NumberField.InfinitePlace.Completion in
theorem Rat.InfiniteAdeleRing.exists_unique_sub_mem_Ico (a : InfiniteAdeleRing ℚ) :
  ∃! (x : 𝓞 ℚ), ∀ v, extensionEmbeddingOfIsReal (Rat.infinitePlace_isReal v)
    (a v - algebraMap ℚ (InfiniteAdeleRing ℚ) x v) ∈ Set.Ico 0 1 := by
  let v₀ : InfinitePlace ℚ := Rat.infinitePlace
  let σ : v₀.Completion →+* ℝ := extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  let x : ℤ := ⌊σ (a v₀)⌋
  use ringOfIntegersEquiv.symm x
  refine ⟨?_, ?_⟩
  · intro v
    rw [Subsingleton.elim v v₀, InfiniteAdeleRing.algebraMap_apply,
      ringOfIntegersEquiv_symm_coe, map_sub, extensionEmbeddingOfIsReal_coe,
    map_intCast, Int.self_sub_floor]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · intro y hy
    set x' := ringOfIntegersEquiv y with hx'
    rw [RingEquiv.eq_symm_apply, ← hx']
    let hy2 := (RingEquiv.eq_symm_apply _).2 hx'.symm
    specialize hy v₀
    rw [InfiniteAdeleRing.algebraMap_apply, hy2, ringOfIntegersEquiv_symm_coe,
      map_sub, extensionEmbeddingOfIsReal_coe, map_intCast] at hy
    exact Int.eq_floor hy.1 hy.2

open NumberField.InfinitePlace.Completion in
theorem Rat.InfiniteAdeleRing.exists_sub_norm_le_one (a : InfiniteAdeleRing ℚ) :
    ∃ (x : 𝓞 ℚ), ∀ v, ‖a v - algebraMap ℚ (InfiniteAdeleRing ℚ) x v‖ ≤ 1 := by
  obtain ⟨x, hx1, -⟩ := Rat.InfiniteAdeleRing.exists_unique_sub_mem_Ico a
  use x
  peel hx1 with v hv
  rw [Subsingleton.elim v Rat.infinitePlace] at *
  rw [← (isometry_extensionEmbeddingOfIsReal isReal_infinitePlace).norm_map_of_map_zero
      (map_zero _), Real.norm_eq_abs]
  grind

instance (v : InfinitePlace K) : ProperSpace v.Completion :=
  ProperSpace.of_locallyCompactSpace v.Completion

-- we might not need this now we're switching to fundamental domains?
open Metric IsDedekindDomain.FiniteAdeleRing AdeleRing in
theorem Rat.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 ℚ) ℚ ⧸ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) where
  isCompact_univ := by
    let W : Set (AdeleRing (𝓞 ℚ) ℚ) :=
      (Set.univ.pi fun _ => closedBall 0 1).prod (integralAdeles (𝓞 ℚ) ℚ)
    have h_W_compact : IsCompact W := by
      refine (isCompact_univ_pi fun v => ?_).prod
        (isCompact_iff_isCompact_univ.2 <| by simpa using CompactSpace.isCompact_univ)
      exact isCompact_iff_isClosed_bounded.2 ⟨isClosed_closedBall, isBounded_closedBall⟩
    have h_W_image : QuotientAddGroup.mk' (principalSubgroup (𝓞 ℚ) ℚ) '' W = Set.univ := by
      refine Set.eq_univ_iff_forall.2 fun x => ?_
      choose xf hf using FiniteAdeleRing.sub_mem_integralAdeles x.out.2
      choose xi hi using InfiniteAdeleRing.exists_sub_norm_le_one (x.out.1 - algebraMap _ _ xf)
      have h : x.out - algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (xi + xf) ∈ W := by
        simp only [W, Set.prod]
        refine ⟨Set.mem_univ_pi.2 fun v => by simpa [add_comm, ← sub_sub] using hi v, ?_⟩
        apply exists_structureMap_eq_of_forall
        simp only [map_add, SetLike.mem_coe]
        rw [Prod.snd_sub, Prod.snd_add, sub_add_eq_sub_sub, sub_right_comm]
        intro v
        refine sub_mem (mem_structureSubring_iff.1 hf v) ?_
        simpa using coe_algebraMap_mem (𝓞 ℚ) ℚ v xi
      exact ⟨_, h, by simp [-algebraMap.coe_inj]⟩
    exact h_W_image ▸ h_W_compact.image continuous_quot_mk

open InfinitePlace.Completion Set RestrictedProduct in
def Rat.AdeleRing.fundamentalDomain : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  (univ.pi fun v => (extensionEmbeddingOfIsReal (infinitePlace_isReal v)).toFun ⁻¹' (Ico 0 1)).prod
    (range <| structureMap _ _ _)

lemma Rat.AdeleRing.mem_fundamentalDomain (a : AdeleRing (𝓞 ℚ) ℚ) :
    ∃ g, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) g + a ∈ fundamentalDomain := by
  obtain ⟨q, f, hf⟩ := FiniteAdeleRing.sub_mem_integralAdeles a.2
  obtain ⟨r, hr, -⟩ := Rat.InfiniteAdeleRing.exists_unique_sub_mem_Ico (a.1 - algebraMap _ _ q)
  use (-q-r)
  refine Set.mem_prod.2 ⟨?_, ?_⟩
  · simp_rw [Set.mem_pi, Set.mem_preimage]
    intro v _
    have foo : (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-q - r)).1 v + a.1 v =
        a.1 v - (algebraMap ℚ (InfiniteAdeleRing ℚ)) q v -
        (algebraMap ℚ (InfiniteAdeleRing ℚ)) (r) v := by
      rw [add_comm, sub_eq_add_neg (a.1 v), add_sub_assoc]
      push_cast
      rfl
    convert hr v
  · rw [Set.mem_range]
    use fun p ↦ ⟨a.2 p + (-q - r), ?_⟩
    · rw [add_comm]
      ext v
      change _ = a.2 _ + _
      push_cast
      simp [structureMap]
      norm_cast
      push_cast
      norm_cast
      sorry
    · rw [← add_sub_assoc]
      refine sub_mem ?_ (coe_algebraMap_mem (𝓞 ℚ) ℚ p r)
      convert (f p).2
      rw [RestrictedProduct.ext_iff] at hf
      specialize hf p
      convert hf.symm
      rw [sub_eq_add_neg]
      change _ = a.2 p + _
      congr
      sorry

  -- this uses the same techniques as `Rat.AdeleRing.zero_discrete` which should
  -- be a corollary: fundamentalDomain - fundamentalDomain ⊆ the U used in the proof
  -- This lemma is in fact a "concrete version" of that one
lemma Rat.AdeleRing.fundamentalDomain_traversal {a b : AdeleRing (𝓞 ℚ) ℚ}
    (ha : a ∈ fundamentalDomain) (hb : b ∈ fundamentalDomain) {q : ℚ}
    (hq : algebraMap _ _ q + a = b) : q = 0 := by
  -- this uses the same techniques as `Rat.AdeleRing.zero_discrete` which should
  -- be a corollary: fundamentalDomain - fundamentalDomain ⊆ the U used in the proof
  -- This lemma is in fact a "concrete version" of that one
  sorry

open NumberField Metric MeasureTheory IsDedekindDomain

noncomputable instance : VAdd ℚ (AdeleRing (𝓞 ℚ) ℚ) where
  vadd q a := algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q + a

open IsDedekindDomain Rat in
theorem Rat.AdeleRing.isAddFundamentalDomain :
    IsAddFundamentalDomain ℚ Rat.AdeleRing.fundamentalDomain
    ((MeasureTheory.Measure.pi (fun _ ↦ Measure.addHaar)).prod Measure.addHaar) where
  nullMeasurableSet := by
    apply MeasureTheory.NullMeasurableSet.prod _ _
    · apply MeasurableSet.nullMeasurableSet
      apply MeasurableSet.univ_pi
      intro v
      apply MeasurableSet.preimage (by measurability)
      exact Homeomorph.measurable
        (InfinitePlace.Completion.isometryEquivRealOfIsReal _).toHomeomorph
    · refine IsOpen.nullMeasurableSet ?_
      convert isOpen_forall_mem ?_
      · ext x
        -- a tactic should do this dumb calculation
        refine ⟨?_, ?_⟩
        · rintro ⟨f, rfl⟩ v
          simp [structureMap]
        · intro h
          use fun v ↦ ⟨x v, h v⟩
          rfl
      · exact isOpenAdicCompletionIntegers ℚ
  ae_covers := by
    filter_upwards
    apply Rat.AdeleRing.mem_fundamentalDomain
  aedisjoint := by
    intro q r hqr
    apply Disjoint.aedisjoint
    rw [Set.disjoint_iff_inter_eq_empty]
    ext _
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro ⟨y, hy, (hx : q +ᵥ y = _)⟩ ⟨z, hz, h⟩
    subst hx
    change algebraMap _ _ r + z = algebraMap _ _ q + y at h
    apply hqr
    rw [← sub_eq_zero]
    apply Rat.AdeleRing.fundamentalDomain_traversal hy hz
    rw [map_sub]
    linear_combination -h

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem NumberField.AdeleRing.cocompact :
    CompactSpace (AdeleRing (𝓞 K) K ⧸ principalSubgroup (𝓞 K) K) :=
  letI := Rat.AdeleRing.cocompact
  (piQuotientEquiv ℚ K).compactSpace

end Compact
