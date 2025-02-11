import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Order.Notation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Quotient

variable {R R' : Type*} [CommRing R] [CommRing R']

instance isLocalRing_of_quotient [instLocalRing : IsLocalRing R] (A : Ideal R) (ht : A ≠ ⊤)
    : IsLocalRing (R ⧸ A) where
  exists_pair_ne := by
    have ho : ∃ x, x ∉ A := by sorry
    use 0
    use algebraMap _ _ ho.choose
    sorry
  isUnit_or_isUnit_of_add_one := by
    sorry
