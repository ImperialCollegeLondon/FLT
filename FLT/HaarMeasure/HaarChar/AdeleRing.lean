import FLT.HaarMeasure.HaarChar.Ring
import FLT.NumberField.AdeleRing
import FLT.Hacks.RightAlgebraInstances
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib

open NumberField

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L] [NumberField K] [NumberField L]

-- this should be in an adele file
noncomputable def NumberField.AdeleRing.mapRingHom :
    NumberField.AdeleRing A K →+* NumberField.AdeleRing B L := RingHom.prodMap
  (algebraMap _ _)
  (IsDedekindDomain.FiniteAdeleRing.mapRingHom A K L B)

section module

noncomputable local instance : Algebra (NumberField.AdeleRing A K) (NumberField.AdeleRing B L) :=
  RingHom.toAlgebra (NumberField.AdeleRing.mapRingHom A K L B)

-- If V is a K-module I can't make V ⊗[K] 𝔸_K into an 𝔸_K-module because the tensor
-- product is on the wrong side.

variable (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]

#check TensorProduct.lid
#check TensorProduct.rid
#check TensorProduct.AlgebraTensorModule.rid
#check LinearEquiv.restrictScalars

#synth Algebra (AdeleRing A K) (AdeleRing B L)
instance : SMulCommClass L (AdeleRing A K) (AdeleRing B L) := sorry

#synth Module (AdeleRing A K) (AdeleRing B L ⊗[L] V)

attribute [instance high] Localization.instSMulCommClassOfIsScalarTower in
noncomputable def NumberField.AdeleRing.ModuleBaseChangeAddEquiv :
    AdeleRing A K ⊗[K] V ≃ₗ[AdeleRing A K] (AdeleRing B L ⊗[L] V) :=
  let foo : V ≃ₗ[L] L ⊗[L] V := (TensorProduct.lid L V).symm
  let foo2 : V ≃ₗ[K] L ⊗[L] V := foo.restrictScalars K
  let foo3 : AdeleRing A K ⊗[K] V ≃ₗ[K] AdeleRing A K ⊗[K] (L ⊗[L] V) := LinearEquiv.lTensor (AdeleRing A K) foo2
  let foo4 : AdeleRing A K ⊗[K] (L ⊗[L] V) ≃ₗ[K] (AdeleRing A K ⊗[K] L) ⊗[L] V := by exact?
  sorry

-- Cor 9.34 is called
-- NumberField.AdeleRing.ModuleBaseChangeContinuousAddEquiv

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory



open scoped RightAlgebra in
/-- Left multiplication by an element of Bˣ on B ⊗ 𝔸_K does not scale additive
Haar measure. In other words, Bˣ is in the kernel of the `ringHaarChar` of `B ⊗ 𝔸_K`.
-/
lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker
    [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]
    (b : Bˣ) :
    (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
      (B ⊗[K] AdeleRing (𝓞 K) K)ˣ) ∈
    ringHaarChar_ker (B ⊗[K] AdeleRing (𝓞 K) K) := sorry

open scoped RightAlgebra in
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
