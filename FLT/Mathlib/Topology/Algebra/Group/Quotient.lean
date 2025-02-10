import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.Topology.Algebra.Module.Quotient
import FLT.Mathlib.Topology.Algebra.Module.Equiv

-- this proof doesn't work for multiplicative groups so should be
-- refactored so that it does, and then toadditive'd.
-- It should also really be using `comap` not `map` to conform with
-- mathlib library decisions.
-- FLT#341
def QuotientAddGroup.continuousAddEquiv (G H : Type*) [AddCommGroup G] [AddCommGroup H] [TopologicalSpace G]
    [TopologicalSpace H] (G' : AddSubgroup G) (H' : AddSubgroup H) [G'.Normal] [H'.Normal]
    (e : G ≃ₜ+ H) (h : AddSubgroup.map e G' = H') :
    G ⧸ G' ≃ₜ+ H ⧸ H' :=
  (Submodule.Quotient.continuousLinearEquiv _ _ (AddSubgroup.toIntSubmodule G')
    (AddSubgroup.toIntSubmodule H') e.toIntContinuousLinearEquiv
      (congrArg AddSubgroup.toIntSubmodule h)).toContinuousAddEquiv
