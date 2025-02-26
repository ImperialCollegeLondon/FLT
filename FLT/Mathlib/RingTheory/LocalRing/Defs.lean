import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic

variable {R : Type*} [CommRing R] [IsLocalRing R]

instance isLocalRing_of_quotient (I : Ideal R) [Nontrivial (R ⧸ I)] :
    IsLocalRing (R ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
