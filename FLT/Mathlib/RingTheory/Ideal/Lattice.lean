import Mathlib.RingTheory.Ideal.Lattice

namespace Ideal

variable {R : Type*} [CommRing R]

class NeqTop (I : Ideal R) : Prop where
  neq_top : I ≠ ⊤

end Ideal
