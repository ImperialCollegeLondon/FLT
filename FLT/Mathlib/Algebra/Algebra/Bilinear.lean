import Mathlib
import FLT.Mathlib.Algebra.Algebra.Hom

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]

open scoped TensorProduct in
/-- Given S an R-algebra, and a ring homomorphism `ψ` from an R-algebra A to an S-algebra B
compatible with the algebra map R → S, `baseChange_of_algebraMap ψ` is the induced
`S`-algebra map `S ⊗[R] A → B`.
-/
noncomputable
def SemialgHom.baseChange_of_algebraMap [Algebra R S] (ψ : A →ₛₐ[algebraMap R S] B) :
    S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B := {
    toRingHom := ψ.toRingHom
    commutes' := ψ.commutes
  }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ Algebra.commutes s (ρ a)
