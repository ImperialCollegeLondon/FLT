import Mathlib.RingTheory.Ideal.Lattice

namespace Ideal

variable {R : Type*} [CommRing R] {A B : Ideal R}

def mem_of_le_of_mem (h : A ≤ B) {a : R} (ain : a ∈ A) : a ∈ B :=
  sorry

end Ideal
