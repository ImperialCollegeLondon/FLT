import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

class IsCompleteRing (R) [CommRing R] (I : Ideal R) : Prop where
  cond : (sorry : Prop)

abbrev IsCompleteLocalRing (R) [CommRing R] [LocalRing R] :=
  IsCompleteRing R (LocalRing.maximalIdeal R)
