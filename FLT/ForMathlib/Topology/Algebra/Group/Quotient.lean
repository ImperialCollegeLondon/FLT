import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.ForMathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.ForMathlib.Topology.Algebra.Module.Quotient
import FLT.ForMathlib.Topology.Algebra.Module.Equiv

def QuotientAddGroup.continuousAddEquiv (G H : Type*) [AddCommGroup G] [AddCommGroup H] [TopologicalSpace G]
    [TopologicalSpace H] (G' : AddSubgroup G) (H' : AddSubgroup H) [G'.Normal] [H'.Normal]
    (e : G ≃ₜ+ H) (h : AddSubgroup.map e G' = H') :
    G ⧸ G' ≃ₜ+ H ⧸ H' :=
  (Submodule.Quotient.continuousLinearEquiv _ _ (AddSubgroup.toIntSubmodule G')
    (AddSubgroup.toIntSubmodule H') e.toIntContinuousLinearEquiv
      (congrArg AddSubgroup.toIntSubmodule h)).toContinuousAddEquiv
