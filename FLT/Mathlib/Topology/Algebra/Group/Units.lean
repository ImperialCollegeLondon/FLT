import Mathlib.Algebra.Group.Submonoid.Units
import Mathlib

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) := by
  sorry -- needs FLT#

lemma Submonoid.units_isCompact {M : Type*} [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    [T2Space M] {U : Submonoid M} (hU : IsCompact (U : Set M)) : IsCompact (U.units : Set Mˣ) := by
  sorry -- needs FLT#
