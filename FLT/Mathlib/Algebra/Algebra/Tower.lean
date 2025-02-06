import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.AlgebraTower

def AlgEquiv.extendScalars {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    C ≃ₐ[B] D where
  __ := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
  __ := f
  commutes' := fun _ => rfl
