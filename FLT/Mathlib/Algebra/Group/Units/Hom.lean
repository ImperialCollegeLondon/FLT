import Mathlib
import Mathlib.Algebra.Group.Units.Hom

variable {R R' : Type*} [CommRing R] [CommRing R']

instance isLocalHom_of_quotient (f : R →+* R') [IsLocalHom f] (A : Ideal R') :
    IsLocalHom (RingHom.comp (Ideal.Quotient.mk A) f) :=
  sorry
