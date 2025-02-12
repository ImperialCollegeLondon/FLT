import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Order.Notation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Quotient
import FLT.Mathlib.RingTheory.Ideal.Lattice

variable {R : Type*} [CommRing R] [IsLocalRing R]

instance isLocalRing_of_quotient (I : Ideal R) [I.NeqTop]
    : IsLocalRing (R ⧸ I) where
  exists_pair_ne := by
    have ho : ∃ x, x ∉ I := by sorry
    use 0
    use algebraMap _ _ ho.choose
    sorry
  isUnit_or_isUnit_of_add_one := by
    sorry
