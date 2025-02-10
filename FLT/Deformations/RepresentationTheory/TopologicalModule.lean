import Mathlib

variable {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable (R M) in
class TopologicalModule [TopologicalSpace M] where
  smul_cont : ∀ r : R, Continuous (X := M) (Y := M) (fun m ↦ r • m)

variable [Module.Free R M] [Module.Finite R M]

variable (R M) in
def productTopology : TopologicalSpace M :=
  let ι := Module.Free.ChooseBasisIndex R M
  let ψ := Module.Free.repr R M
  .generateFrom <| setOf fun (V : Set M) ↦ ∃ (b : ι → Set R),
      (∀ i, IsOpen (b i)) ∧
      (V = ψ ⁻¹' setOf fun (coord : ι →₀ R) ↦ ∀ i, coord i ∈ b i)

variable [TopologicalSpace M] (h_topo : IsOpen (X := M) = (productTopology R M).IsOpen)

def productTopology_topologicalModule : TopologicalModule R M where
  smul_cont r := sorry
