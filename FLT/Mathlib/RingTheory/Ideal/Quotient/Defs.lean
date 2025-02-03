import Mathlib.RingTheory.Ideal.Quotient.Defs

namespace Ideal

variable {R : Type*} [CommRing R] {A B : Ideal R}

def ringHomOfQuot_of_le (h : A ≤ B) : R ⧸ A →+* R ⧸ B :=
    Ideal.Quotient.lift A (Ideal.Quotient.mk B) (by
      rintro a ain
      rw [Quotient.eq_zero_iff_mem]
      aesop
    )

end Ideal
