import Mathlib

variable {R : Type*} [Ring R] [TopologicalSpace R] [TopologicalRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in
class TopologicalModule [TopologicalSpace M] where
  smul_cont : ∀ r : R, Continuous (X := M) (Y := M) (fun m ↦ r • m)
