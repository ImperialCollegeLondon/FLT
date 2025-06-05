import FLT.HaarMeasure.HaarChar.Ring
import FLT.NumberField.AdeleRing
import FLT.Hacks.RightActionInstances
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Central.Defs
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

open NumberField

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L] [NumberField K] [NumberField L]

-- this should be in an adele file
/-- The ring homomorphism 𝔸_K → 𝔸_L associated to a morphism K → L of number fields. -/
noncomputable def NumberField.AdeleRing.mapRingHom :
    NumberField.AdeleRing A K →+* NumberField.AdeleRing B L := RingHom.prodMap
  (algebraMap _ _)
  (IsDedekindDomain.FiniteAdeleRing.mapRingHom A K L B)

section module

/-- If K ⊆ L are number fields then 𝔸_L is an 𝔸_K-algebra. -/
noncomputable local instance : Algebra (NumberField.AdeleRing A K) (NumberField.AdeleRing B L) :=
  RingHom.toAlgebra (NumberField.AdeleRing.mapRingHom A K L B)

-- If V is a K-module I can't make V ⊗[K] 𝔸_K into an 𝔸_K-module because the tensor
-- product is on the wrong side.

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

/-

#check TensorProduct.lid
#check TensorProduct.rid
#check TensorProduct.AlgebraTensorModule.rid
#check LinearEquiv.restrictScalars

#synth Algebra (AdeleRing A K) (AdeleRing B L)
-/
local instance : SMulCommClass L (AdeleRing A K) (AdeleRing B L) := sorry

--- need open scoped RightModule
attribute [local instance high] Localization.instSMulCommClassOfIsScalarTower

/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv :
    AdeleRing A K ⊗[K] V ≃ₗ[AdeleRing A K] (AdeleRing B L ⊗[L] V) :=
  let foo : V ≃ₗ[L] L ⊗[L] V := (TensorProduct.lid L V).symm
  let foo2 : V ≃ₗ[K] L ⊗[L] V := foo.restrictScalars K
  let foo3 : AdeleRing A K ⊗[K] V ≃ₗ[AdeleRing A K] AdeleRing A K ⊗[K] (L ⊗[L] V) :=
    LinearEquiv.baseChange K (AdeleRing A K) V (L ⊗[L] V) foo2
  foo3 ≪≫ₗ
  --let foo4 : AdeleRing A K ⊗[K] L ⊗[L] V ≃ₗ[AdeleRing A K] (AdeleRing A K ⊗[K] L) ⊗[L] V := sorry
  sorry
--    LinearEquiv.lTensor (AdeleRing A K) foo2
  --let foo4 : AdeleRing A K ⊗[K] (L ⊗[L] V) ≃ₗ[K] (AdeleRing A K ⊗[K] L) ⊗[L] V := by exact?
--  sorry

/-- 𝔸_K ⊗[K] V = 𝔸_L ⊗[L] V as topological 𝔸_K-modules for V an L-module and K ⊆ L number fields. -/
noncomputable def NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv
    [TopologicalSpace (AdeleRing A K ⊗[K] V)]
    [IsModuleTopology (AdeleRing A K) (AdeleRing A K ⊗[K] V)]
    [TopologicalSpace (AdeleRing B L ⊗[L] V)]
    [IsModuleTopology (AdeleRing B L) (AdeleRing B L ⊗[L] V)] :
    AdeleRing A K ⊗[K] V ≃L[AdeleRing A K] (AdeleRing B L ⊗[L] V) :=
  sorry

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

open scoped TensorProduct.RightActions in
variable [TopologicalSpace (B ⊗[K] AdeleRing A K)]
  [IsModuleTopology (AdeleRing A K) (B ⊗[K] AdeleRing A K)]
  [MeasurableSpace (B ⊗[K] AdeleRing A K)]
  [BorelSpace (B ⊗[K] AdeleRing A K)] in
lemma NumberField.AdeleRing.isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (AdeleRing A K))ˣ) :
    haveI : IsTopologicalRing (B ⊗[K] (AdeleRing A K)) := sorry
    haveI : LocallyCompactSpace (B ⊗[K] (AdeleRing A K)) := sorry
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  sorry

instance : LocallyCompactSpace (AdeleRing ℤ ℚ) := sorry
instance (p : IsDedekindDomain.HeightOneSpectrum ℤ) :
  LocallyCompactSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p) := sorry

variable [MeasurableSpace (AdeleRing ℤ ℚ)] [BorelSpace (AdeleRing ℤ ℚ)]
  [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum ℤ),
    MeasurableSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)]
  [∀ (p : IsDedekindDomain.HeightOneSpectrum ℤ),
    BorelSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ p)] in
lemma MeasureTheory.ringHaarChar_adeles_rat (x : (AdeleRing ℤ ℚ)ˣ) :
  ringHaarChar x = ringHaarChar (MulEquiv.prodUnits x).1 *
    (∏ᶠ p, ringHaarChar (MulEquiv.restrictedProductUnits (MulEquiv.prodUnits x).2 p)) := sorry

lemma MeasureTheory.ringHaarChar_adeles_units_rat_eq_one (x : ℚˣ)
    [MeasurableSpace ((AdeleRing ℤ ℚ))] [BorelSpace (AdeleRing ℤ ℚ)] :
  ringHaarChar (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)) x : (AdeleRing ℤ ℚ)ˣ) = 1 := sorry

instance : LocallyCompactSpace (AdeleRing A K) := sorry
variable [TopologicalSpace (AdeleRing A K ⊗[K] V)]
  [IsModuleTopology (AdeleRing A K) (AdeleRing A K ⊗[K] V)]

/-- The continuous A-linear map (A a topological ring, tensor products have the module
topology) A ⊗[R] M ≃ A ⊗[R] N associated to an abstract R-linear isomorphism M ≃ N. -/
@[nolint unusedArguments] -- they will be used when the sorries are filled
noncomputable def ContinuousLinearEquiv.baseChange (R : Type*) [CommRing R]
    (A : Type*) [CommRing A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A]
    (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [TopologicalSpace (A ⊗[R] M)] [IsModuleTopology A (A ⊗[R] M)]
    [TopologicalSpace (A ⊗[R] N)] [IsModuleTopology A (A ⊗[R] N)]
    (φ : M ≃ₗ[R] N) : (A ⊗[R] M) ≃L[A] (A ⊗[R] N) where
      __ := LinearEquiv.baseChange _ _ _ _ φ
      continuous_toFun := sorry -- linear => continuous
      continuous_invFun := sorry

instance : IsTopologicalAddGroup (AdeleRing A K ⊗[K] V) := sorry
instance : LocallyCompactSpace (AdeleRing A K ⊗[K] V) := sorry

open scoped TensorProduct.RightActions

lemma MeasureTheory.addHaarScalarFactor_tensor_adeles_eq_one (φ : V ≃ₗ[K] V)
    [MeasurableSpace (AdeleRing A K ⊗[K] V)] [BorelSpace (AdeleRing A K ⊗[K] V)] :
    addEquivAddHaarChar
      (ContinuousLinearEquiv.baseChange K (AdeleRing A K) V V φ).toContinuousAddEquiv = 1 := by
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
