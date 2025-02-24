import Mathlib
import FLT.Deformation.ContinuousRepresentation.TopologicalModule

variable {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]

variable [TopologicalModule R M] [Module.Free R M] [Module.Finite R M]

instance linearMapTopology : TopologicalSpace (M →ₗ[R] M) := sorry

variable (R G M) in
structure ContinuousRepresentation extends (Representation R G M) where
  isCont := Continuous toFun

instance : CoeOut (ContinuousRepresentation R G M) (Representation R G M) where
  coe ρ := ρ.1
