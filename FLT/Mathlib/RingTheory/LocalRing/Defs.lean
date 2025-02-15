import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Defs

variable {R : Type*} [CommRing R] [IsLocalRing R]

instance isLocalRing_of_quotient (I : Ideal R) [Nontrivial (R ⧸ I)] :
    IsLocalRing (R ⧸ I) where
  exists_pair_ne := exists_pair_ne (R ⧸ I)
  isUnit_or_isUnit_of_add_one {a b} h := by
    induction a using Quotient.inductionOn
    rename_i a₀
    obtain ha | hb := IsLocalRing.isUnit_or_isUnit_of_add_one (show a₀ + (1 - a₀) = 1 by ring)
    · left
      exact RingHom.isUnit_map (Ideal.Quotient.mk I) ha
    · right
      rw [eq_sub_of_add_eq' h]
      exact RingHom.isUnit_map (Ideal.Quotient.mk I) hb
