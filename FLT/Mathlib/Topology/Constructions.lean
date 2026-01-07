import Mathlib.Topology.Constructions
import FLT.Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Set.Restrict

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
  change Continuous (fun (x : (j : J) → g j) w ↦ (p w) (x (r w)))
  fun_prop
