/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard, Salvatore Mercuri, Pietro Monticone
-/
module

public import Mathlib.Topology.Constructions
public import FLT.Mathlib.Algebra.Algebra.Pi

/-!
# Constructions

Material destined for Mathlib.
-/

@[expose] public section

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

open Topology in
/-- A map on `X × D` with `D` discrete is continuous as soon as all its slices `x ↦ g (x, d)`
are continuous. -/
lemma continuous_of_discreteTopology_snd {X D Y : Type*} [TopologicalSpace X]
    [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y] {g : X × D → Y}
    (hg : ∀ d, Continuous fun x ↦ g (x, d)) : Continuous g := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt]
  rintro ⟨x, d⟩
  rw [nhds_prod_eq, nhds_discrete D, Filter.prod_pure]
  exact Filter.tendsto_map'_iff.mp ((hg d).tendsto x)
