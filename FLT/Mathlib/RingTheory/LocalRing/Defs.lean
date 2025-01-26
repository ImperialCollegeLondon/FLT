import Mathlib
import Mathlib.RingTheory.LocalRing.Defs

variable {R : Type*} [CommRing R] [IsLocalRing R]

lemma isLocalRing_of_quotient (A : Ideal R) : IsLocalRing (R ⧸ A) := sorry
