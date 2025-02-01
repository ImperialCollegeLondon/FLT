import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans  <| induced_mono hσ)
         (inf_le_right.trans  <| induced_mono hτ)

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)):
    DenseRange (Pi.map f) := by
  rw [DenseRange, Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)
