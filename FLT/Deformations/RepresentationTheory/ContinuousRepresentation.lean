import Mathlib

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]

variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]

variable (R M) in
class TopologicalModule where
  smul_cont := ∀ r : R, Continuous (fun (m : M) ↦ r • m)

variable [TopologicalModule R M] [Module.Free R M] [Module.Finite R M]

instance linearMapTopology : TopologicalSpace (M →ₗ[R] M) := sorry

structure ContinuousRepresentation extends (Representation R G M) where
  isCont := Continuous toFun
