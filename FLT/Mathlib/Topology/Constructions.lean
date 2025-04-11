import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import FLT.Mathlib.Data.Set.Function
import FLT.Mathlib.Algebra.Algebra.Pi

theorem TopologicalSpace.prod_mono {α β : Type*} {σ₁ σ₂ : TopologicalSpace α}
    {τ₁ τ₂ : TopologicalSpace β} (hσ : σ₁ ≤ σ₂) (hτ : τ₁ ≤ τ₂) :
    @instTopologicalSpaceProd α β σ₁ τ₁ ≤ @instTopologicalSpaceProd α β σ₂ τ₂ :=
  le_inf (inf_le_left.trans  <| induced_mono hσ)
         (inf_le_right.trans  <| induced_mono hτ)

theorem DenseRange.codRestrict_comp {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {α : Type*} {g : Y → Z} {f : α → Y} (hf : DenseRange f) (cg : Continuous g) :
    DenseRange <| (Set.range g).codRestrict g (fun _ => by simp) ∘ f :=
  DenseRange.comp (Set.codRestrict_range_surjective g).denseRange hf (by fun_prop)

theorem Continuous.piSemialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J}
    [(j : J) → TopologicalSpace (g j)] [(i : I) → TopologicalSpace (f i)]
    (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (h : ∀ i, Continuous (p i)) :
    Continuous (Pi.semialgHomPi f g p) := by
  show Continuous (fun (x : (j : J) → g j) w ↦ (p w) (x (r w)))
  fun_prop
