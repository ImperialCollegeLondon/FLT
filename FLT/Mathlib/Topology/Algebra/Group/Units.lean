import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)
