import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.NumberField.InfiniteAdeleRing
import FLT.NumberField.Padics.RestrictedProduct
import FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdeleRing
import FLT.Mathlib.Data.Real.Archimedean
import FLT.Mathlib.NumberTheory.NumberField.AdeleRing

/-! # The adele ring of a number field

## Defining base change

One of the main results in this file is base change, which is the `L`-algebra homeomorphism
`L ⊗[K] 𝔸_K ≃A[L] 𝔸_L` for number fields `L / K`. Per the discussion in
`FLT.NumberField.InfiniteAdeleRing` there are two approaches to defining this map
(1) Piece together the base changes for the infinite and finite adele rings.
(2) Follow the same path as that of the infinite and finite adele ring by lifing the map `𝔸 K → 𝔸 L`

Previously both definitions were provided. Both still exist, but the first approach is the only one
that is now used. The second approach is given at the end of the file and we show that
both maps agree.

## Bi-scalarity

The fact that `L ⊗[K] 𝔸_K ≃A[L] 𝔸_L` is both an `L` and an `𝔸 K` algebra isomorphism is used
heavily in this file, mainly because the topologies are `𝔸 K`-module topologies. This property
has been abstracted to a typeclass `IsBiscalar` defined in `FLT.Mathlib.Algebra.Algebra.Tower`.
TODO: would it be better do define this as a bundled map `→ₐ[L, 𝔸 K]` rather than use a typeclass?

## Diamonds

Diamonds of the form `Algebra K L → Algebra (𝔸 K) (𝔸 L)` have caused issues in the past, with
instance search timing out when `K = L`. In `FLT.NumberField.InfiniteAdeleRing` we avoided this
by adding `[Algebra K∞ L∞]` as assumptions alongside compatibility instances.  A similar
approach is taken here, with `Prod.IsProdSMul` being the only extra piece of compatibility required.

The desired instances are constructed later as `scoped` instances in `FLT.NumberField.AdeleRing`.

-/
open scoped TensorProduct

universe u

open NumberField InfinitePlace

namespace NumberField.AdeleRing

open IsDedekindDomain

open scoped NumberField.InfiniteAdeleRing

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section BaseChange

/-- `𝔸 K` for `K` a number field, is notation for `AdeleRing (𝓞 K) K`. -/
scoped notation:101 "𝔸" K => AdeleRing (𝓞 K) K

instance [SMul (𝔸 K) (𝔸 L)] : SMul (K∞ × FiniteAdeleRing (𝓞 K) K) (L∞ × FiniteAdeleRing (𝓞 L) L) :=
  inferInstanceAs (SMul (𝔸 K) (𝔸 L))

lemma smul_fst [SMul K∞ L∞] [SMul (𝔸 K) (𝔸 L)]
    [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)]
    (x : 𝔸 K) (y : 𝔸 L) :
    (x • y).1 = x.1 • y.1 := by
  rw [Prod.IsProdSMul.smul_fst]

lemma smul_snd [SMul K∞ L∞] [SMul (𝔸 K) (𝔸 L)]
    [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)]
    (x : 𝔸 K) (y : 𝔸 L) :
    (x • y).2 = x.2 • y.2 := by
  rw [Prod.IsProdSMul.smul_snd]

/-- The canonical map from the adeles of K to the adeles of L -/
noncomputable def baseChange :
    (𝔸 K) →SA[algebraMap K L] 𝔸 L :=
  let finite : FiniteAdeleRing (𝓞 K) K →SA[algebraMap K L] FiniteAdeleRing (𝓞 L) L := {
    __ := FiniteAdeleRing.mapSemialgHom (𝓞 K) K L (𝓞 L)
    continuous_toFun := FiniteAdeleRing.mapSemialgHom_continuous (𝓞 K) K L (𝓞 L)
  }
  ContinuousSemialgHom.prodMap (InfiniteAdeleRing.baseChange K L) finite

@[simp] lemma baseChange_fst_apply (a : 𝔸 K) :
    (baseChange K L a).1 = InfiniteAdeleRing.baseChange K L a.1 := rfl
@[simp] lemma baseChange_snd_apply (a : 𝔸 K) :
    (baseChange K L a).2 = FiniteAdeleRing.mapSemialgHom (𝓞 K) K L (𝓞 L) a.2 := rfl

open scoped TensorProduct

instance instPiIsModuleTopology : IsModuleTopology (𝔸 K) (Fin (Module.finrank K L) → 𝔸 K) :=
  IsModuleTopology.instPi

/-- The L-algebra isomorphism `L ⊗[K] 𝔸_K = 𝔸_L`. -/
noncomputable def baseChangeAlgEquiv : (L ⊗[K] 𝔸 K) ≃ₐ[L] 𝔸 L :=
  let tensor :=
    Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
  let prod := AlgEquiv.prodCongr
    (NumberField.InfiniteAdeleRing.baseChangeAlgEquiv K L)
    (FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L))
  tensor.trans prod

@[simp] lemma baseChangeAlgEquiv_apply (l : L) (a : 𝔸 K) :
    baseChangeAlgEquiv K L (l ⊗ₜ a) = algebraMap _ _ l * baseChange K L a := by
  rfl

lemma baseChangeAlgEquiv_fst_apply (l : L) (x : 𝔸 K) :
    (baseChangeAlgEquiv K L (l ⊗ₜ x)).1 = InfiniteAdeleRing.baseChangeAlgEquiv K L (l ⊗ₜ x.1) :=
  rfl

lemma baseChangeAlgEquiv_snd_apply (l : L) (x : 𝔸 K) :
    (baseChangeAlgEquiv K L (l ⊗ₜ x)).2 =
      FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L) (l ⊗ₜ x.2) :=
  rfl

-- TODO: abstract this to a general result `Biscalar × Biscalar → Biscalar` if `Prod.IsProdSMul`?
open TensorProduct.RightActions in
/-- Take arbitrary `Algebra K L∞`, `Algebra K∞ L∞` and `Algebra (𝔸 K) (𝔸 L)` instances.
Assume that `Algebra K L∞` factors through (existing) `Algebra K L` and `Algebra L L∞`.
Assume further that `Algebra K∞ L∞` is determined by the fibers of restriction of infinite places
of `L` to `K` via (x • y) v = x (v.comap (algebraMap K L)) • y v.
Assume finally that `Algebra (𝔸 K) (𝔸 L)` is constructed as the product algebra
from `Algebra K∞ L∞` and `Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L).
Then the `L` algebra base change map is also linear in `𝔸 K`. -/
instance [Algebra K L∞] [IsScalarTower K L L∞] [Algebra K∞ L∞] [Algebra (𝔸 K) (𝔸 L)]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]
    [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)] :
    IsBiscalar L (𝔸 K) (baseChangeAlgEquiv K L).toAlgHom where
  map_smul₁ l x := (baseChangeAlgEquiv K L).toAlgHom.map_smul_of_tower l x
  map_smul₂ a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r =>
        apply Prod.ext
        · simp only [AlgEquiv.toAlgHom_eq_coe, smul_def, TensorProduct.comm_tmul,
            TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_symm_tmul, AlgHom.coe_coe,
            baseChangeAlgEquiv_fst_apply, smul_fst]
          have := IsBiscalar.map_smul₂ L (S := K∞)
            (f := InfiniteAdeleRing.baseChangeAlgEquiv K L |>.toAlgHom)
          rw [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe] at this
          simp [← this, TensorProduct.smul_tmul']
        · simp only [AlgEquiv.toAlgHom_eq_coe, smul_def, TensorProduct.comm_tmul,
            TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_symm_tmul, AlgHom.coe_coe,
            baseChangeAlgEquiv_snd_apply, smul_snd]
          change _ = _ • FiniteAdeleRing.baseChangeAdeleAlgEquiv (𝓞 K) K L (𝓞 L) _
          change FiniteAdeleRing.baseChangeAdeleAlgEquiv _ _ _ _ (a.2 • l ⊗ₜ[K] r.2) = _
          rw [← AlgHom.coe_coe, ← AlgEquiv.toAlgHom_eq_coe,
            (FiniteAdeleRing.baseChangeAdeleAlgEquiv (𝓞 K) K L (𝓞 L)).toAlgHom.map_smul_of_tower]
    | add x y _ _ => simp_all

/- Take a compatible `K∞`-algebra on `L∞`. -/
variable [Algebra K L∞] [IsScalarTower K L L∞] [Algebra K∞ L∞]
  [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]

/- Take a compatible `𝔸 K`-algebra on `𝔸 L`. -/
variable [Algebra K (𝔸 L)] [IsScalarTower K L (𝔸 L)] [Algebra (𝔸 K) (𝔸 L)]
  [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)]

open TensorProduct.RightActions in
/-- The `L`-algebra homeomorphism `L ⊗[K] 𝔸 K = 𝔸 L`. -/
noncomputable def baseChangeEquiv [IsModuleTopology (𝔸 K) (𝔸 L)] :
    (L ⊗[K] 𝔸 K) ≃A[L] 𝔸 L :=
  IsModuleTopology.continuousAlgEquivOfIsBiscalar K (𝔸 K) (baseChangeAlgEquiv K L)

variable {L} [IsModuleTopology (𝔸 K) (𝔸 L)]

open scoped TensorProduct.RightActions in
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
noncomputable abbrev piEquiv : (Fin (Module.finrank K L) → 𝔸 K) ≃L[K] 𝔸 L :=
  -- `⊕ 𝔸 K ≃L[K] L ⊗[K] 𝔸 K` from previous def
  let π := (tensorProductEquivPi K L).symm
  -- `L ⊗[K] 𝔸 K ≃L[K] 𝔸 L` base change  restricted to `K` as a continuous linear equiv
  let BC := baseChangeEquiv K L |>.toContinuousLinearEquiv |>.restrictScalars K
  π.trans BC

variable {K L}

open TensorProduct.AlgebraTensorModule TensorProduct.RightActions in
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

open scoped TensorProduct.RightActions in
theorem piEquiv_mem_principalSubgroup
    {x : Fin (Module.finrank K L) → 𝔸 K}
    (h : x ∈ AddSubgroup.pi Set.univ (fun _ => principalSubgroup (𝓞 K) K)) :
    piEquiv K L x ∈ principalSubgroup (𝓞 L) L := by
  simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_const] at h
  choose y hy using h
  exact piEquiv_apply_of_algebraMap hy ▸ ⟨Module.Finite.equivPi _ _ |>.symm y, rfl⟩

variable (K L)

open scoped TensorProduct.RightActions in
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

open scoped TensorProduct.RightActions in
theorem comap_piEquiv_principalSubgroup :
    (AddSubgroup.pi Set.univ (fun (_ : Fin (Module.finrank K L)) => principalSubgroup (𝓞 K) K))
      = (principalSubgroup (𝓞 L) L).comap (piEquiv K L).toAddMonoidHom := by
  rw [← piEquiv_map_principalSubgroup K L,
    AddSubgroup.comap_map_eq_self_of_injective (piEquiv K L).injective]

open scoped TensorProduct.RightActions in
/-- A continuous additive isomorphism `(𝔸_K / K)ⁿ = 𝔸_L / L` where `n = [L:K]`. -/
noncomputable def piQuotientEquiv :
    (Fin (Module.finrank K L) → (𝔸 K) ⧸ principalSubgroup (𝓞 K) K) ≃ₜ+
      (𝔸 L) ⧸ principalSubgroup (𝓞 L) L :=
  -- The map `⊕ 𝔸 K ≃L[K] 𝔸 L` reduces to quotients `⊕ 𝔸 K / K ≃ₜ+ 𝔸 L / L`
  (ContinuousAddEquiv.quotientPi _).symm.trans <|
    QuotientAddGroup.continuousAddEquiv _ _ (piEquiv K L).toContinuousAddEquiv
      (piEquiv_map_principalSubgroup K L)

end BaseChange

section vector_space

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as L-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeLinearEquiv :
    V ⊗[K] (𝔸 K) ≃ₗ[L] (V ⊗[L] (𝔸 L)) :=
  TensorProduct.AlgebraTensorModule.congr ((TensorProduct.rid L V).symm) (.refl _ _) ≪≫ₗ
  TensorProduct.AlgebraTensorModule.assoc K L L V L (𝔸 K) ≪≫ₗ
  (LinearEquiv.lTensor V
    ((NumberField.AdeleRing.baseChangeAlgEquiv K L).toLinearEquiv.symm)).symm

@[simp] theorem ModuleBaseChangeLinearEquiv_tmul_apply (v : V) (x : 𝔸 K) :
    ModuleBaseChangeLinearEquiv K L V (v ⊗ₜ[K] x) = v ⊗ₜ[L] (baseChangeAlgEquiv K L (1 ⊗ₜ[K] x)) :=
  rfl

open TensorProduct.RightActions in
instance [Algebra K L∞] [IsScalarTower K L L∞] [Algebra K∞ L∞] [Algebra (𝔸 K) (𝔸 L)]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]
    [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)]
    [Module (𝔸 K) (V ⊗[L] 𝔸 L)] [IsScalarTower (𝔸 K) (𝔸 L) (V ⊗[L] 𝔸 L)] :
    IsBiscalar L (𝔸 K) (ModuleBaseChangeLinearEquiv K L V) where
  map_smul₁ l x := (ModuleBaseChangeLinearEquiv K L V).map_smul l x
  map_smul₂ a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l r =>
        have := IsBiscalar.map_smul₂ L (S := 𝔸 K) (f := (baseChangeAlgEquiv K L).toAlgHom) a
        rw [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe] at this
        simp only [smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
          TensorProduct.comm_symm_tmul, ModuleBaseChangeLinearEquiv_tmul_apply,
          algebra_compatible_smul (𝔸 L) a]
        rw [algebraMap_smul, ← this]
        simp [TensorProduct.smul_tmul']
    | add x y _ _ => simp_all

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological additive groups
for V an L-module and K ⊆ L number fields. -/
noncomputable def ModuleBaseChangeContinuousLinearEquiv
    [FiniteDimensional L V] [FiniteDimensional K V]
    [Algebra K L∞] [IsScalarTower K L L∞] [Algebra K∞ L∞] [Algebra (𝔸 K) (𝔸 L)]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion]
    [Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L)]
    [Module (𝔸 K) (V ⊗[L] 𝔸 L)] [IsScalarTower (𝔸 K) (𝔸 L) (V ⊗[L] 𝔸 L)]
    [IsModuleTopology (𝔸 K) (𝔸 L)] [Module.Finite (𝔸 K) (𝔸 L)] :
    V ⊗[K] (𝔸 K) ≃L[L] (V ⊗[L] (𝔸 L)) :=
  haveI : ContinuousSMul (AdeleRing (𝓞 K) K) (V ⊗[L] AdeleRing (𝓞 L) L) :=
    IsScalarTower.continuousSMul (AdeleRing (𝓞 L) L)
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (V ⊗[L] AdeleRing (𝓞 L) L) := {
    eq_moduleTopology' := by
      obtain ⟨h2⟩ : IsModuleTopology (AdeleRing (𝓞 L) L) (V ⊗[L] AdeleRing (𝓞 L) L) :=
        inferInstance
      rwa [moduleTopology.trans (𝔸 K) (𝔸 L) (V ⊗[L] (𝔸 L))] }
  IsModuleTopology.continuousLinearEquivOfIsBiscalar K (𝔸 K) (ModuleBaseChangeLinearEquiv K L V)

end vector_space

noncomputable section AlgebraConstructions

/-! Here we construct explicit algebras and compatibility instances for `𝔸 L` over `𝔸 K`. These
are provided as scoped instances to avoid creating diamonds when `K = L`. -/

open IsDedekindDomain AdeleRing

open scoped InfiniteAdeleRing TensorProduct.RightActions NumberField.AdeleRing

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The `K∞`-algebra on `L∞`, induced by `InfiniteAdeleRing.baseChange K L`. -/
scoped instance : Algebra K∞ L∞ := (InfiniteAdeleRing.baseChange K L).toAlgebra

/-- Ensures that `Algebra K∞ L∞` is built out of local algebras
`Algebra v.Completion wv.Completion`. -/
scoped instance : Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion where
  map_smul r x b σ := by obtain ⟨a, rfl⟩ := σ; rfl

/-- The product `K`-algebra on `L∞`. -/
scoped instance : Algebra K L∞ := Pi.algebra _ _

scoped instance : IsScalarTower K L L∞ := Pi.isScalarTower

/-- The `𝔸 K`-algebra on `𝔸 L`, induced by `AdeleRing.baseChange K L`. -/
scoped instance : Algebra (𝔸 K) (𝔸 L) := (AdeleRing.baseChange K L).toAlgebra

/-- Says that `𝔸 K`-algebra on `𝔸 L` is built from the `K∞`-algebra on `L∞` and the
finite adele algebra. -/
scoped instance : Prod.IsProdSMul K∞ (FiniteAdeleRing (𝓞 K) K) L∞ (FiniteAdeleRing (𝓞 L) L) where
  map_smul _ _ := rfl

/-- The product `K`-algebra on `𝔸 L`. -/
scoped instance : Algebra K (𝔸 L) := Prod.algebra _ _ _

scoped instance : IsScalarTower K L (𝔸 L) := Prod.isScalarTower

scoped instance : Module.Finite (𝔸 K) (𝔸 L) :=
    Module.Finite.equiv ((baseChangeAlgEquiv K L).changeScalars K (𝔸 K)).toLinearEquiv

scoped instance instBaseChangeIsModuleTopology : IsModuleTopology (𝔸 K) (𝔸 L) :=
  IsModuleTopology.instProd' (A := K∞)

end AlgebraConstructions

end NumberField.AdeleRing

section Discrete

open IsDedekindDomain

theorem Rat.AdeleRing.integral_and_norm_lt_one (x : ℚ)
    (h2 : ∀ v, ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) x) v ∈
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)
    (h1 : ∀ (v : InfinitePlace ℚ), ‖algebraMap ℚ (InfiniteAdeleRing ℚ) x v‖ < 1) : x = 0 := by
  simp only [InfiniteAdeleRing.algebraMap_apply, UniformSpace.Completion.norm_coe] at h1
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
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] at h1
      exact Rat.AdeleRing.integral_and_norm_lt_one x h2 h1
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
      Rat.HeightOneSpectrum.primesEquiv
      (Function.Injective.comap_cofinite_eq Rat.HeightOneSpectrum.primesEquiv.injective).symm
      (fun v ↦ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv)
      (Filter.Eventually.of_forall Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn)
  commutes' q := by
    ext p
    obtain ⟨v, rfl⟩ := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ).surjective p
    have : Fact (Nat.Prime (HeightOneSpectrum.natGenerator v)) :=
      ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
    change _ = algebraMap ℚ ℚ_[Rat.HeightOneSpectrum.natGenerator v] q
    -- was `simp` when `FiniteAdeleRing` was an `abbrev`.
    -- Ask on Zulip?
    -- Adding `-implicitDefEqProofs` means that the kernel doesn't spend 30 seconds
    -- typchecking the declaration for some reason! See
    -- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/help.20with.20diagnosis.20of.20slow.20declaration/near/565229150
    simp -implicitDefEqProofs [IsDedekindDomain.algebraMap_apply (𝓞 ℚ)]

theorem padicEquiv_bijOn :
    Set.BijOn padicEquiv (integralAdeles (𝓞 ℚ) ℚ)
      (structureSubring (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ subring p) Filter.cofinite) := by
  apply RingEquiv.restrictedProductCongr_bijOn_structureSubring
    (A₂ := fun p : Nat.Primes ↦ subring p)
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
    (Function.Injective.comap_cofinite_eq Rat.HeightOneSpectrum.primesEquiv.injective).symm
  intro v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v)

open FiniteAdeleRing in
theorem sub_mem_integralAdeles
    (a : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ∃ x : ℚ, a - algebraMap ℚ _ x ∈ integralAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨q, hq⟩ := RestrictedProduct.padic_exists_sub_mem_structureSubring (padicEquiv a)
  use q
  simpa using padicEquiv_bijOn.symm (padicEquiv.toEquiv.invOn) |>.mapsTo hq

end Rat.FiniteAdeleRing

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
/-- The fundamental domain `ℤ^ x [0,1)` for `𝔸_ℚ ⧸ ℚ`. -/
def Rat.AdeleRing.fundamentalDomain : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  (univ.pi fun v => (extensionEmbeddingOfIsReal (infinitePlace_isReal v)).toFun ⁻¹' (Ico 0 1)).prod
    (range <| structureMap _ _ _)

/-- The canonical ring homomorphism from the finite adele ring to
a nonarchimedean local factor. -/
def FiniteAdeleRing.toAdicCompletion {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 K) K →+* v.adicCompletion K where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

-- bleurgh
lemma Rat.AdeleRing.mem_fundamentalDomain (a : AdeleRing (𝓞 ℚ) ℚ) :
    ∃ g, algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) g + a ∈ fundamentalDomain := by
  obtain ⟨q, f, hf⟩ := FiniteAdeleRing.sub_mem_integralAdeles a.2
  obtain ⟨r, hr, -⟩ := Rat.InfiniteAdeleRing.exists_unique_sub_mem_Ico (a.1 - algebraMap _ _ q)
  use (-q - r)
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
    use fun p ↦ ⟨a.2 p + algebraMap ℚ _ (-q - r), ?_⟩
    · rw [add_comm]
      ext v
      change _ = a.2 _ + _
      push_cast
      simp only [structureMap, FiniteAdeleRing.mk_apply, add_right_inj]
      rfl
    · rw [map_sub, ← add_sub_assoc]
      refine sub_mem ?_ (coe_algebraMap_mem (𝓞 ℚ) ℚ p r)
      convert (f p).2
      rw [RestrictedProduct.ext_iff] at hf
      convert (hf p).symm
      rw [map_neg, ← sub_eq_add_neg, Eq.comm]
      convert (map_sub (FiniteAdeleRing.toAdicCompletion p) a.2 _)

  -- this uses the same techniques as `Rat.AdeleRing.zero_discrete` which should
  -- be a corollary: fundamentalDomain - fundamentalDomain ⊆ the U used in the proof
  -- This lemma is in fact a "concrete version" of that one
lemma Rat.AdeleRing.fundamentalDomain_traversal {a b : AdeleRing (𝓞 ℚ) ℚ}
    (ha : a ∈ fundamentalDomain) (hb : b ∈ fundamentalDomain) {q : ℚ}
    (hq : algebraMap _ _ q + a = b) : q = 0 := by
  apply Rat.AdeleRing.integral_and_norm_lt_one
  · intro v
    apply_fun RingHom.snd (InfiniteAdeleRing ℚ) _ at hq
    rw [map_add, ← eq_sub_iff_add_eq] at hq
    unfold AdeleRing at hq
    rw [RingHom.map_rat_algebraMap (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) q]
      at hq
    rw [hq]
    apply sub_mem
    · obtain ⟨x, hx⟩ := (Set.mem_prod.1 hb).2
      change b.2 v ∈ _
      rw [← hx]
      exact (x v).2
    · obtain ⟨x, hx⟩ := (Set.mem_prod.1 ha).2
      change a.2 v ∈ _
      rw [← hx]
      exact (x v).2
  · intro v
    apply_fun RingHom.fst (InfiniteAdeleRing ℚ) _ at hq
    rw [map_add, ← eq_sub_iff_add_eq] at hq
    unfold AdeleRing at hq
    rw [RingHom.map_rat_algebraMap (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) q]
      at hq
    rw [hq]
    replace ha := (Set.mem_prod.1 ha).1
    replace hb := (Set.mem_prod.1 hb).1
    simp_rw [Set.mem_pi, Set.mem_preimage] at ha hb
    specialize ha v (Set.mem_univ _)
    specialize hb v (Set.mem_univ _)
    change ‖b.1 v - a.1 v‖ < 1
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal _ (a.1 v) ∈ _ at ha
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal _ (b.1 v) ∈ _ at hb
    suffices ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal (infinitePlace_isReal v)
        (b.1 v - a.1 v)‖ < 1 by
      convert this
      simpa only [map_zero, edist_zero_right, enorm_eq_iff_norm_eq] using
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
          (Rat.infinitePlace_isReal v) (b.1 v - a.1 v) 0).symm
    rw [map_sub, Real.norm_eq_abs, abs_sub_lt_iff]
    cases ha; cases hb; constructor <;> linarith

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

section compare

/-!
There are two ways we can construct the isomorphism (L ⊗ 𝔸 K) = 𝔸 L.

(1) Construct it from the isomorphisms `(L ⊗ K∞) = L∞` and `(L ⊗ 𝔸f K) = 𝔸f L` on the
infinite and finite adele rings respectively.
(2) Induce it from the semi-algebra homomorphism `baseChange K L : 𝔸 K → 𝔸 L`.

These turn out to be the same (although not definitionally) because the definition of the
semi-algebra homomorphims `baseChange K L : 𝔸 K → 𝔸 L` is via construction from the
infinite and finite-adele ring counterparts.

The main file above has unified them in favour of (1) but the alternative definition on (2)
is given here and shown to be equal to (1). -/

namespace NumberField.AdeleRing

open IsDedekindDomain AdeleRing InfiniteAdeleRing

open scoped TensorProduct.RightActions

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The canonical `𝔸 K`-algebra homomorphism `(L ⊗_K 𝔸 K) → 𝔸 L` induced
by the maps from `L` and `𝔸 K` into `𝔸 L`. -/
noncomputable def baseChangeAdeleAlgHom : (L ⊗[K] (𝔸 K)) →ₐ[𝔸 K] 𝔸 L :=
  (baseChange K L).baseChangeRightOfAlgebraMap

lemma baseChangeAdeleAlgHom_bijective : Function.Bijective (baseChangeAdeleAlgHom K L) := by
  -- There's a linear equivalence `(L ⊗_K 𝔸 K) ≅ 𝔸 L`
  let linearEquiv : (L ⊗[K] 𝔸 K) ≃ₗ[L] 𝔸 L :=
    let tensor := TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
    let prod := LinearEquiv.prodCongr (InfiniteAdeleRing.baseChangeAlgEquiv K L).toLinearEquiv
      (FiniteAdeleRing.baseChangeAlgEquiv (𝓞 K) K L (𝓞 L)).toLinearEquiv
    tensor.trans prod
  -- and it's given by an equal function to the algebra homomorphism we've defined.
  have eqEquiv : ⇑(baseChangeAdeleAlgHom K L) = ⇑(linearEquiv) := by
    ext x
    induction x with
    | zero => rfl
    | tmul x y => rfl
    | add x y _ _ => simp_all
  rw [eqEquiv]
  exact linearEquiv.bijective

/-- The canonical `𝔸_K`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L`
induced by the base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeAlgAdeleEquiv : (L ⊗[K] 𝔸 K) ≃ₐ[𝔸 K] 𝔸 L :=
    AlgEquiv.ofBijective (baseChangeAdeleAlgHom K L) (baseChangeAdeleAlgHom_bijective K L)

/-- The canonical `𝔸_K`-algebra homeomorphism from `L ⊗_K 𝔸_K` to `𝔸_L`
induced by the base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeAdeleEquiv : (L ⊗[K] 𝔸 K) ≃A[𝔸 K] 𝔸 L :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAlgAdeleEquiv K L

/-- The canonical `L`-algebra isomorphism from `L ⊗_K 𝔸_K` to `𝔸_L` induced by the
`K`-algebra base change map `𝔸_K → 𝔸_L`. -/
noncomputable def baseChangeEquiv' :
    (L ⊗[K] 𝔸 K) ≃A[L] 𝔸 L where
  __ := (baseChange K L).baseChange_of_algebraMap
  __ := baseChangeAdeleEquiv K L

-- this isn't rfl. Explanation below
example (x : L ⊗[K] 𝔸 K) : baseChangeEquiv K L x = baseChangeEquiv' K L x := by
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

end NumberField.AdeleRing

end compare
