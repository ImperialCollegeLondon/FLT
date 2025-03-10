import Mathlib
import FLT.Mathlib.Algebra.Algebra.Hom
import FLT.Mathlib.Algebra.Algebra.Tower

open scoped TensorProduct
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}

/-- Given S an R-algebra, and a ring homomorphism `ψ` from an R-algebra A to an S-algebra B
compatible with the algebra map R → S, `baseChange_of_algebraMap ψ` is the induced
`S`-algebra map `S ⊗[R] A → B`.
-/
noncomputable
def SemialgHom.baseChange_of_algebraMap [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) :
    S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B := {
    toRingHom := ψ.toRingHom
    commutes' := ψ.commutes
  }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ Algebra.commutes s (ρ a)

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_right [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (a : A) :
    ψ.baseChange_of_algebraMap (1 ⊗ₜ[R] a) = ψ a := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe]

@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_left [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] 1) = algebraMap _ _ s := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Let `S` be an `R`-algebra and `ψ` a ring homomorphism from an `R`-algebra `A` to an
`S`-algebra `B` compatible with the algebra map `R → S`. If, in addition, `B` is
an `R`-algebra and the scalar action of `R` on `B` factors through `S`, then
`baseChangeRightOfAlgebraMap ψ` is the induced `A`-algebra map `S ⊗[R] A → B`.
-/
noncomputable
def SemialgHom.baseChangeRightOfAlgebraMap [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    S ⊗[R] A →ₐ[A] B :=
  letI := ψ.toAlgebra
  AlgHom.changeScalars R A ψ.baseChange_of_algebraMap (by simp [RingHom.algebraMap_toAlgebra])

@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_apply [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (ψ : A →ₛₐ[algebraMap R S] B) (x : S ⊗[R] A) :
    baseChangeRightOfAlgebraMap ψ x = baseChange_of_algebraMap ψ x := by
  simp [baseChangeRightOfAlgebraMap, AlgHom.changeScalars_apply]

@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_coe [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    ⇑ψ.baseChangeRightOfAlgebraMap = ⇑ψ.baseChange_of_algebraMap :=
  funext_iff.2 <| ψ.baseChangeRightOfAlgebraMap_apply
