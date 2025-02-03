import Mathlib
import Mathlib.RingTheory.LocalRing.Defs

variable {R R' : Type*} [CommRing R] [CommRing R']

instance isLocalRing_of_quotient [IsLocalRing R] (A : Ideal R) : IsLocalRing (R ⧸ A) :=
  sorry
