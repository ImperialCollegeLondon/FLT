import Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Hom

def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
    A →ₛₐ[φ] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp

@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl

def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i) :
    ((j : J) → g j) →ₛₐ[φ] (i : I) → f i where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))

@[simp]
def Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) := rfl
