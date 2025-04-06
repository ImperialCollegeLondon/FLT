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

@[simp]
def AlgEquiv.extendScalars_apply {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) (c : C) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    (AlgEquiv.extendScalars B f) c = f c := by
  rfl

@[simp]
def AlgEquiv.symmExtendScalars_apply {A C D : Type*} (B : Type*) [CommSemiring A] [CommSemiring C]
    [CommSemiring D] [Algebra A C] [Algebra A D] [CommSemiring B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] (f : C ≃ₐ[A] D) (d : D) :
    letI := (f.toAlgHom.restrictDomain B).toRingHom.toAlgebra
    (AlgEquiv.extendScalars B f).symm d = f.symm d := by
  rfl

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
    (f : A →ₐ[S₂] B) (h : ∀ s, f (algebraMap S₁ A s) = algebraMap S₁ B s) :
    A →ₐ[S₁] B where
  __ := (f.restrictScalars R).extendScalars S₁
  commutes' (r : _) := by
    simp [RingHom.algebraMap_toAlgebra, ← h, restrictDomain]

theorem AlgHom.changeScalars_apply (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*} [CommSemiring R]
    [CommSemiring A] [CommSemiring B] [CommSemiring S₁] [CommSemiring S₂] [Algebra S₂ A]
    [Algebra R S₁] [Algebra S₂ B] [Algebra S₁ A] [Algebra R S₂] [Algebra S₁ B] [Algebra R A]
    [Algebra R B] [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A →ₐ[S₂] B) (h : ∀ s, f (algebraMap S₁ A s) = algebraMap S₁ B s) (a : A) :
    changeScalars R S₁ f h a = f a := by
  simp [changeScalars, extendScalars]

def AlgEquiv.changeScalars (R : Type*) {A B : Type*} (S₁ : Type*) {S₂ : Type*} [CommSemiring R]
    [CommSemiring A] [CommSemiring B] [CommSemiring S₁] [CommSemiring S₂] [Algebra S₂ A]
    [Algebra R S₁] [Algebra S₂ B] [Algebra S₁ A] [Algebra R S₂] [Algebra S₁ B] [Algebra R A]
    [Algebra R B] [IsScalarTower R S₂ A] [IsScalarTower R S₁ A] [IsScalarTower R S₂ B]
    (f : A ≃ₐ[S₂] B) (h : ∀ s, f (algebraMap S₁ A s) = algebraMap S₁ B s) :
    A ≃ₐ[S₁] B where
  __ := AlgHom.changeScalars R S₁ f.toAlgHom h
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars_apply]
  right_inv (b : B) := by simp [AlgHom.changeScalars_apply]
  commutes' := fun _ => by simp
