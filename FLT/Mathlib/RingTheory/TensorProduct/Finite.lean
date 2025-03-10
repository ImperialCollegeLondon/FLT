import Mathlib.RingTheory.TensorProduct.Finite

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [CommRing M] [Algebra R M]
    [h : Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.of_equiv_equiv (RingEquiv.refl A) (Algebra.TensorProduct.comm R A M).toRingEquiv rfl
