import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.AlgebraTower
import FLT.Mathlib.Algebra.Algebra.Hom

class LinearMap.CompatibleSMulFor {R : Type*} (S : Type*) {A B : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B]
    (f : A →ₗ[R] B) : Prop where
  map_smul : ∀ (s : S) (a : A), f (s • a) = s • f a

def LinearMap.changeScalars (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*}
    [Semiring R] [Semiring S₁] [Semiring S₂] [AddCommMonoid A] [AddCommMonoid B] [Module S₂ A]
    [Module S₂ B] [Module S₁ A] [Module R S₁] [Module R S₂] [Module R A] [Module R B] [Module S₁ B]
    [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B] (f : A →ₗ[S₂] B)
    [f.CompatibleSMulFor S₁] :
    A →ₗ[S₁] B where
  __ := f.restrictScalars R
  map_smul' r x := by simpa using LinearMap.CompatibleSMulFor.map_smul r x

theorem LinearMap.changeScalars_apply (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*}
    [Semiring R] [Semiring S₁] [Semiring S₂] [AddCommMonoid A] [AddCommMonoid B] [Module S₂ A]
    [Module S₂ B] [Module S₁ A] [Module R S₁] [Module R S₂] [Module R A] [Module R B] [Module S₁ B]
    [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B] (f : A →ₗ[S₂] B)
    [f.CompatibleSMulFor S₁] (a : A) :
    LinearMap.changeScalars R S₁ f a = f a := by
  simp [changeScalars]

def LinearEquiv.changeScalars (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*}
    [Semiring R] [Semiring S₁] [Semiring S₂] [AddCommMonoid A] [AddCommMonoid B] [Module S₂ A]
    [Module S₂ B] [Module S₁ A] [Module R S₁] [Module R S₂] [Module R A] [Module R B] [Module S₁ B]
    [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A ≃ₗ[S₂] B) [f.CompatibleSMulFor S₁] :
    A ≃ₗ[S₁] B where
  __ := LinearMap.changeScalars R S₁ f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := by simp [LinearMap.changeScalars_apply]
  right_inv (b : B) := by simp [LinearMap.changeScalars_apply]

@[simps! apply symm_apply]
def AlgEquiv.extendScalars {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    C ≃ₐ[B] D where
  __ := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
  __ := f
  invFun := f.symm
  commutes' := fun _ => rfl

class AlgHom.CompatibleSMulFor {S₂ : Type*} (S₁ : Type*) {A B : Type*} [CommSemiring S₁]
    [CommSemiring S₂] [Semiring A] [Semiring B] [Algebra S₁ A] [Algebra S₁ B] [Algebra S₂ A]
    [Algebra S₂ B] (f : A →ₐ[S₂] B) where
  map_smul (s : S₁) (a : A) : f (s • a) = s • f a

theorem AlgHom.CompatibleSMulFor.commutes {S₂ : Type*} (S₁ : Type*) {A B : Type*} [CommSemiring S₁]
    [CommSemiring S₂] [Semiring A] [Semiring B] [Algebra S₁ A] [Algebra S₁ B] [Algebra S₂ A]
    [Algebra S₂ B] (f : A →ₐ[S₂] B) [f.CompatibleSMulFor S₁] (s : S₁) :
    f (algebraMap S₁ A s) = algebraMap S₁ B s := by
  simpa [Algebra.algebraMap_eq_smul_one] using AlgHom.CompatibleSMulFor.map_smul (f := f) s 1

/--
Given the following
```
f : A ––––––––––> B
     \     /\    /
      \   /  \  /
       \ /    \/
        S₁    S₂
         \   /
          \ /
           R
```
where the map `f` from `A` to `B` is an `S₂`-algebra homomorphism, `S₁` and `S₂` are parallel
algebras over some base ring `R`, and `A` and `B` are also `S₁`-algebras. If the algebras
form scalar towers and the algebra map from  `S₁` to `B` factors through `f`, then `f` can
be converted to an `S₁`-algebra homomorphism.
-/
def AlgHom.changeScalars (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*} [CommSemiring R]
    [CommSemiring A] [CommSemiring B] [CommSemiring S₁] [CommSemiring S₂] [Algebra S₂ A]
    [Algebra R S₁] [Algebra S₂ B] [Algebra S₁ A] [Algebra R S₂] [Algebra S₁ B] [Algebra R A]
    [Algebra R B] [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A →ₐ[S₂] B) [f.CompatibleSMulFor S₁] :
    A →ₐ[S₁] B where
  __ := (f.restrictScalars R).extendScalars S₁
  commutes' (r : _) := by
    simp [RingHom.algebraMap_toAlgebra, ← AlgHom.CompatibleSMulFor.commutes S₁ f, restrictDomain]

theorem AlgHom.changeScalars_apply (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [CommSemiring S₁] [CommSemiring S₂]
    [Algebra S₂ A] [Algebra R S₁] [Algebra S₂ B] [Algebra S₁ A] [Algebra R S₂] [Algebra S₁ B]
    [Algebra R A] [Algebra R B] [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A →ₐ[S₂] B) [f.CompatibleSMulFor S₁] (a : A) :
    changeScalars R S₁ f a = f a := by
  simp [changeScalars, extendScalars]

def AlgEquiv.changeScalars (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*} [CommSemiring R]
    [CommSemiring A] [CommSemiring B] [CommSemiring S₁] [CommSemiring S₂] [Algebra S₂ A]
    [Algebra R S₁] [Algebra S₂ B] [Algebra S₁ A] [Algebra R S₂] [Algebra S₁ B] [Algebra R A]
    [Algebra R B] [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A ≃ₐ[S₂] B) [f.toAlgHom.CompatibleSMulFor S₁] :
    A ≃ₐ[S₁] B where
  __ := AlgHom.changeScalars R S₁ f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars_apply]
  right_inv (b : B) := by simp [AlgHom.changeScalars_apply]
  commutes' := fun _ => by simp
