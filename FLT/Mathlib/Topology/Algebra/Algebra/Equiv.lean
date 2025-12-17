import Mathlib.Topology.Algebra.Algebra.Equiv

-- upstream if the community like it; not sure I need it any more though.
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ContinuousAlgEquiv.2EtoContinuousAddEquiv/near/564239498

variable {R A B : Type*} [CommSemiring R] [Semiring A] [TopologicalSpace A]
    [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B] (e : A ≃A[R] B)

def ContinuousAlgEquiv.toContinuousAddEquiv (e : A ≃A[R] B) : A ≃ₜ+ B := {
  __ := e
}
