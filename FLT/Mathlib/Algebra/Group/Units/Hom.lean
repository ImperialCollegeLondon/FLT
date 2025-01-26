import Mathlib
import Mathlib.Algebra.Group.Units.Hom

variable {R R' : Type*} [CommRing R] [CommRing R']
variable (f : R →+* R') [IsLocalHom f]

lemma isLocalHom_of_quotient (A : Ideal R) (h : ∀ a ∈ A, f a = 0) :
  IsLocalHom (RingHom.comp (Ideal.Quotient.lift A f h) (Ideal.Quotient.mk A)) := sorry
