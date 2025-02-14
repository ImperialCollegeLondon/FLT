import Mathlib

class TopologicalModule
  (R : Type*) [Ring R] [TopologicalSpace R] [TopologicalRing R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M] where
  smul_continuous : Continuous (X := R × M) (Y := M) fun ⟨r, m⟩ ↦ r • m
