import Mathlib
import FLT.Deformation.ContinuousRepresentation.TopologicalModule

-- TODO(jlcontreras): change this, instread of doing it manually use the natural topology in
--  (ChooseBasisIndex) → R
--   [is_prod_topo : Nonempty (W ≃ₜ (Module.Free.ChooseBasisIndex A W → A))]
def freeFiniteModuleProductTopology
  (R : Type*) [Ring R] [TopologicalSpace R] [TopologicalRing R]
  (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] : TopologicalSpace M :=
  let ι := Module.Free.ChooseBasisIndex R M
  let ψ := Module.Free.repr R M
  .generateFrom <| setOf fun (V : Set M) ↦ ∃ (b : ι → Set R),
      (∀ i, IsOpen (b i)) ∧
      (V = ψ ⁻¹' setOf fun (coord : ι →₀ R) ↦ ∀ i, coord i ∈ b i)

variable {R : Type*} [Ring R] [TopologicalSpace R] [TopologicalRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

def freeFiniteModuleProductTopology_topologicalModule
    : @TopologicalModule R _ _ _ M _ _ (freeFiniteModuleProductTopology R M) := sorry
