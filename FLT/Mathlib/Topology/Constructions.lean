import Mathlib.Topology.Constructions
import FLT.Mathlib.Data.Set.Function

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans  <| induced_mono hσ)
         (inf_le_right.trans  <| induced_mono hτ)

theorem DenseRange.codRestrict_comp {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {α : Type*} {g : Y → Z} {f : α → Y} (hf : DenseRange f) (cg : Continuous g) :
    DenseRange <| (Set.range g).codRestrict g (fun _ => by simp) ∘ f :=
  DenseRange.comp (Set.codRestrict_range_surjective g).denseRange hf (by fun_prop)
