import Mathlib

universe u

variable (A : Type*) [CommRing A]

variable (G : Type*) [Group G]

variable (W : Type*) [AddCommMonoid W] [Module A W]

def Subrepresentation := Representation A G W -- TODO(jlcontreras): change this

namespace Representation

instance : Lattice (Subrepresentation A G W) := sorry

instance : Top (Subrepresentation A G W) := sorry

instance : Bot (Subrepresentation A G W) := sorry

end Representation
