import Mathlib
import FLT.Deformation.ContinuousRepresentation.TopologicalModule

variable {R : Type*} [Ring R] [TopologicalSpace R] [TopologicalRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable [Module.Free R M] [Module.Finite R M]

variable (R M) in
def freeFiniteModuleProductTopology : TopologicalSpace M :=
  let ι := Module.Free.ChooseBasisIndex R M
  let ψ := Module.Free.repr R M
  .generateFrom <| setOf fun (V : Set M) ↦ ∃ (b : ι → Set R),
      (∀ i, IsOpen (b i)) ∧
      (V = ψ ⁻¹' setOf fun (coord : ι →₀ R) ↦ ∀ i, coord i ∈ b i)

variable [TopologicalSpace M] (h_topo : IsOpen (X := M) = (freeFiniteModuleProductTopology R M).IsOpen)

def freeFiniteModuleProductTopology_topologicalModule : TopologicalModule R M where
  smul_cont r := sorry
