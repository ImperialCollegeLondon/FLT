import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.AlgebraTower
import FLT.Mathlib.Algebra.Algebra.Hom

-- TODO: needs work before it can go in mathlib.
-- Change `IsBiscalar` into a bundled map? Currently this is a pain to use even
-- when using `f : F` where `Funlike F A B` because some bundled maps do not coerce correctly
-- e.g. if `f : A ≃ₗ[R] B` and we assume `IsBiscalar R S f` then `IsBiscalar R S f.toLinearMap`
-- does not automatically get picked up.
-- Or remove and carry around `map_smul₂` as a hypothesis where needed?

/-- If `f : A → B` where `A` and `B` are both `R`- and `S`-modules, then `IsBiscalar R S f`
asserts that `f` satisfies the linear scalar property for both `R` and `S`. I.e.,
- `f (r • a) = r • f a`
- `f (s • a) = s • f a`
for all `r : R`, `s : S`, `a : A`.

Note that this is symmetric in its arguments and only takes in a function as input. For bundled
functions already containing a scalar, this class can be used to assert that the function
also has another scalar. The convention in this repo is to use the bundled scalar as the first
argument. For example, if `f : A →ₗ[R] B` and it is also scalar with respect to `S`, then
use `IsBiscalar R S f`. -/
class IsBiscalar (R S : Type*) {A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B] (f : A → B) where
  map_smul₁ : ∀ (r : R) (a : A), f (r • a) = r • f a
  map_smul₂ : ∀ (s : S) (a : A), f (s • a) = s • f a

section linear

variable {A B : Type*} (S' : Type*) {S : Type*}
    [Semiring S'] [Semiring S] [AddCommMonoid A] [AddCommMonoid B] [Module S A]
    [Module S B] [Module S' A] [Module S' B]

/--
Given a linear map `f : A →ₗ[S] B` which also satisfies `f (s' • a) = s' • f a` for `s : S'`,
with both `S` and `S'` sharing a common base ring `R`, then `f.changeScalars R S'` returns `f`
viewed as an `S'`-algebra homomorphism.
-/
def LinearMap.changeScalars (f : A →ₗ[S] B) [IsBiscalar S S' f] :
    A →ₗ[S'] B where
  __ := f
  map_smul' s x := by simpa using IsBiscalar.map_smul₂ S s x

theorem LinearMap.changeScalars_apply (f : A →ₗ[S] B) [IsBiscalar S S' f] (a : A) :
    LinearMap.changeScalars S' f a = f a := by
  simp [changeScalars]

/--
Given a linear isomorphism `f : A ≃ₗ[S] B` which also satisfies `f (s' • a) = s' • f a` for
`s : S'`, with both `S` and `S'` sharing a common base ring `R`, then `f.changeScalars R S'`
returns `f` viewed as an `S'`-algebra isomorphism.
-/
def LinearEquiv.changeScalars (f : A ≃ₗ[S] B) [IsBiscalar S S' f] :
    A ≃ₗ[S'] B where
  __ := LinearMap.changeScalars S' f.toLinearMap
  invFun := f.invFun
  left_inv (a : A) := by simp [LinearMap.changeScalars_apply]
  right_inv (b : B) := by simp [LinearMap.changeScalars_apply]

end linear

section algebra

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

theorem IsBiscalar.commutes {S : Type*} (S' : Type*) {A B : Type*} [CommSemiring S']
    [CommSemiring S] [Semiring A] [Semiring B] [Algebra S' A] [Algebra S' B] [Algebra S A]
    [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S' f] (s : S') :
    f (algebraMap S' A s) = algebraMap S' B s := by
  simpa [Algebra.algebraMap_eq_smul_one] using IsBiscalar.map_smul₂ (f := f) S s 1

variable {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B]

/--
Produces an `S'`-linear algebra map from an `S`-linear algebra map `f : A →ₐ[S] B` which also
has scalars `S'`.
-/
def AlgHom.changeScalars (f : A →ₐ[S] B) [IsBiscalar S S' f] :
    A →ₐ[S'] B where
  __ := f
  commutes' (r : _) := by simp [IsBiscalar.commutes]

theorem AlgHom.changeScalars_apply (f : A →ₐ[S] B) [IsBiscalar S S' f] (a : A) :
    changeScalars S' f a = f a := by
  simp [changeScalars]

/--
Produces an `S'`-linear algebra isomorphism from an `S`-linear algebra isomorphism `f : A ≃ₐ[S] B`
which also has scalars `S'`.
-/
def AlgEquiv.changeScalars (f : A ≃ₐ[S] B) [IsBiscalar S S' f.toAlgHom] :
    A ≃ₐ[S'] B where
  __ := AlgHom.changeScalars S' f.toAlgHom
  invFun := f.invFun
  left_inv (a : A) := by simp [AlgHom.changeScalars_apply]
  right_inv (b : B) := by simp [AlgHom.changeScalars_apply]
  commutes' := fun _ => by simp

end algebra

section diamond_checks

/- If we have `IsBiscalar S S f` then we can change scalars on `f : A →ₐ[S] B` to get a new
function `f' : A →ₐ[S] B`. We should have `f = f'` definitionally. -/

example {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra S A] [Algebra S B] (f : A →ₐ[S] B) [IsBiscalar S S f] :
    AlgHom.changeScalars S f = f := rfl

/- If we have `IsBiscalar S S' f` then we can change scalars on
`f : A →ₐ[S] B` to get `f' : A →ₐ[S'] B`. If we have `IsBiscalar S' S f'` and change scalars again
to get `f'' : A →ₐ[S] B`. We should have `f = f''` definitionally. -/

example {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
    [Algebra S B] [Algebra S' A] [Algebra S' B] (f : A →ₐ[S] B) [IsBiscalar S S' f]
    [IsBiscalar S' S (AlgHom.changeScalars S' f)] :
    (AlgHom.changeScalars S' f).changeScalars S = f := rfl

end diamond_checks
