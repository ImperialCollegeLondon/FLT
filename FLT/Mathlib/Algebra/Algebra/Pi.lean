import Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Algebra.Hom

def Pi.semialgHom  {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A]  [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
  A →ₛₐ[φ] (i : I) → f i where
  __ := Pi.ringHom fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp
