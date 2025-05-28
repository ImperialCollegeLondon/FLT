import FLT.HaarMeasure.HaarChar.Ring
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions

section tensor_product_right_module_instances

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [Ring B] [Algebra R B]
variable (V : Type*) [AddCommGroup V] [Module R V]

open scoped TensorProduct


-- boilerplate to make `B ⊗[K] AdeleRing (𝓞 K) K` a locally compact space
-- TODO put this boilerplate into some scope?

noncomputable instance : Algebra A (B ⊗[R] A) :=
  Algebra.TensorProduct.rightAlgebra

noncomputable def i1 : Module A (B ⊗[R] A) := inferInstance

noncomputable example : A ⊗[R] V ≃+ V ⊗[R] A := TensorProduct.comm R A V

example (W : Type*) [AddCommGroup W] (φ : V ≃+ W) : Module R W :=
  AddEquiv.module R (id φ.symm)

#synth Module A (A ⊗[R] V) -- TensorProduct.leftModule

noncomputable instance Module.TensorProduct.rightModule :
    Module A (V ⊗[R] A) :=
  AddEquiv.module A (TensorProduct.comm R V A : V ⊗[R] A ≃+ A ⊗[R] V)

#check Module.TensorProduct.rightModule R A B

example : i1 R A B = Module.TensorProduct.rightModule R A B := rfl

    -- it's isomorphic to A ⊗[R] B), use this.

instance [Module.Finite R V] : Module.Finite A (V ⊗[R] A) :=
  sorry

/-
variable (R A B : Type*) [CommRing R] [CommRing A] [AddCommGroup B] [Algebra R A]
  [Module R B] [Module.Free R B] in
#synth Module.Free A (A ⊗[R] B)
-/

instance [Module.Free R V] : Module.Free A (V ⊗[R] A) :=
  sorry -- copy the proof in the commented-out code and make it work for right tensors?

noncomputable instance [TopologicalSpace A] : TopologicalSpace (V ⊗[R] A) :=
  moduleTopology A (V ⊗[R] A)

local instance [TopologicalSpace A] : IsModuleTopology A (V ⊗[R] A) := ⟨rfl⟩

-- AdeleRing is locally compact, B/R is finite, so this is just homeo to a finite
-- product of locally compact spaces
instance [TopologicalSpace A] [LocallyCompactSpace A] [Module.Finite R V] :
    LocallyCompactSpace (V ⊗[R] A) := sorry

local instance [TopologicalSpace A] [LocallyCompactSpace A] [IsTopologicalRing A]
    [Module.Finite R B] : IsTopologicalRing (B ⊗[R] A) :=
  haveI : IsModuleTopology A (B ⊗[R] A) := ⟨rfl⟩
  IsModuleTopology.Module.topologicalRing A _

end tensor_product_right_module_instances

variable [MeasurableSpace (B ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (B ⊗[K] AdeleRing (𝓞 K) K)]

lemma NumberField.AdeleRing.units_mem_ringHaarCharacter_ker (b : Bˣ) :
  (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
    (B ⊗[R] AdeleRing (𝓞 R) R)ˣ) ∈ ringHaarChar_ker (B ⊗[R] AdeleRing (𝓞 R) R) := sorry

lemma NumberField.AdeleRing.addEquivAddHaarChar_mulRight_unit_eq_one (b : Bˣ) :
    addEquivAddHaarChar
      (ContinuousAddEquiv.mulRight
      (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom b :
        (B ⊗[K] AdeleRing (𝓞 K) K)ˣ)) = 1 := by
  sorry

#synth Algebra ℚ K
