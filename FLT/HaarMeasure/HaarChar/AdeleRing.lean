import FLT.HaarMeasure.HaarChar.Ring
import FLT.NumberField.AdeleRing
import FLT.Hacks.RightActionInstances
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Central.Defs
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Hacks.RightActionInstances
import FLT.NumberField.AdeleRing
/-!

# Global units are in the determinant of the adelic Haar character

If `K` is a number field and `B` is a finite-dimensional `K`-algebra
then `B ⊗ 𝔸_K` is a locally compact topological ring, so it admits
a Haar character `(B ⊗ 𝔸_K)ˣ → ℝ>0`. In this file we show
that the global units `Bˣ` are in the kernel of this character.

-/

open NumberField

open scoped TensorProduct

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

open scoped NumberField.AdeleRing -- for 𝔸 K notation

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [FiniteDimensional L V] [FiniteDimensional K V] -- the latter can be proved but
  -- can't be an instance as it uses L

local instance : SMulCommClass L (𝔸 K) (𝔸 L) :=
  SMulCommClass.of_commMonoid L (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)

attribute [local instance high] Localization.instSMulCommClassOfIsScalarTower

/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as L-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv :
    V ⊗[K] (𝔸 K) ≃ₗ[L] (V ⊗[L] (𝔸 L)) :=
  TensorProduct.AlgebraTensorModule.congr ((TensorProduct.rid L V).symm) (.refl _ _) ≪≫ₗ
  TensorProduct.AlgebraTensorModule.assoc K L L V L (𝔸 K) ≪≫ₗ
  (LinearEquiv.lTensor V
    ((NumberField.AdeleRing.baseChangeAdeleAlgEquiv K L).toLinearEquiv.symm)).symm

omit [FiniteDimensional L V] [FiniteDimensional K V] in
@[simp] lemma NumberField.AdeleRing.ModuleBaseChangeAddEquiv_apply
    (v : V) (a : 𝔸 K) : ModuleBaseChangeAddEquiv K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeAddEquiv]

open scoped TensorProduct.RightActions in
/-- V ⊗[K] 𝔸_K = V ⊗[L] 𝔸_L as 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv' [Module (𝔸 K) (V ⊗[L] 𝔸 L)]
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
noncomputable def NumberField.AdeleRing.ModuleBaseChangeContinuousSemilinearMap :
    V ⊗[K] (𝔸 K) →ₛₗ[algebraMap (𝔸 K) (𝔸 L)] V ⊗[L] 𝔸 L where
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddMonoidHom
  map_smul' a bc := by
    induction bc with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul', Algebra.smul_def]
    | add x y _ _ => simp_all

omit [FiniteDimensional L V] [FiniteDimensional K V] in
lemma NumberField.AdeleRing.ModuleBaseChangeContinuousSemilinearMap_apply
    (v : V) (a : 𝔸 K) :
    ModuleBaseChangeContinuousSemilinearMap K L V (v ⊗ₜ a) = v ⊗ₜ algebraMap _ _ a := by
  simp [ModuleBaseChangeContinuousSemilinearMap]

open scoped TensorProduct.RightActions in
/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological additive groups
for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv :
    V ⊗[K] (𝔸 K) ≃ₜ+ (V ⊗[L] (𝔸 L)) :=
  {
  __ := (NumberField.AdeleRing.ModuleBaseChangeAddEquiv K L V).toAddEquiv
  continuous_toFun := sorry
  continuous_invFun := sorry
  }

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] 𝔸 K)]
  [BorelSpace (B ⊗[K] 𝔸 K)] in
lemma NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (𝔸 K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  sorry

variable [MeasurableSpace (𝔸 ℚ)] [BorelSpace (𝔸 ℚ)]
  [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    MeasurableSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)),
    BorelSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)] in
lemma MeasureTheory.ringHaarChar_adeles_rat (x : (𝔸 ℚ)ˣ) :
  ringHaarChar x = ringHaarChar (MulEquiv.prodUnits x).1 *
    (∏ᶠ p, ringHaarChar (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2 p)) := sorry

lemma MeasureTheory.ringHaarChar_adeles_units_rat_eq_one (x : ℚˣ)
    [MeasurableSpace ((𝔸 ℚ))] [BorelSpace (𝔸 ℚ)] :
  ringHaarChar (Units.map (algebraMap ℚ (𝔸 ℚ)) x : (𝔸 ℚ)ˣ) = 1 := sorry

-- TODO: need TensorProduct.RightActions.LinearEquiv.baseChange
open scoped TensorProduct.RightActions in
/-- The continuous A-linear map (A a topological ring, tensor products have the module
topology) A ⊗[R] M ≃ A ⊗[R] N associated to an abstract R-linear isomorphism M ≃ N. -/
noncomputable def ContinuousLinearEquiv.baseChange (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (φ : M ≃ₗ[R] N) : (M ⊗[R] A) ≃L[A] (N ⊗[R] A) where
  __ := TensorProduct.RightActions.LinearEquiv.baseChange _ _ _ _ φ
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := IsModuleTopology.continuous_of_linearMap _

open scoped TensorProduct.RightActions

lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one (φ : V ≃ₗ[K] V)
    [MeasurableSpace (V ⊗[K] 𝔸 K)] [BorelSpace (V ⊗[K] 𝔸 K)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange K (𝔸 K) V V φ).toContinuousAddEquiv = 1 := by
  sorry

open scoped TensorProduct.RightActions in
/-- Left multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure. In other words, Bˣ is in the kernel of the `ringHaarChar` of `B ⊗ 𝔸_K`.
-/
lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈
    ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry

open scoped TensorProduct.RightActions in
/-- Right multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure.
-/
lemma NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    addEquivAddHaarChar
      (ContinuousAddEquiv.mulRight
        (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = 1 := by
  sorry
