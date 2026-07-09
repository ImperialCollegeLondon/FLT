/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ContinuousCohomology.Basic
public import Mathlib.Tactic.Group

@[expose] public section

open CategoryTheory ContinuousMap

namespace ContinuousCohomology

universe u

variable {R : Type*} {G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ## The kernel of `d¹` is the continuous 1-cocycles

The degree-`1` differential of the homogeneous cochain complex is, on the underlying cochains,
`(d² f)(g₀, g₁, g₂) = f(g₁, g₂) - f(g₀, g₂) + f(g₀, g₁)` — see
`d_one_two_apply`, which holds by
`rfl`. We show that an element of `.X 1` lies in `ker d¹` iff its inhomogeneous cochain
`c = f 1` satisfies the cocycle identity `c (g * h) = c g + ρ(g) (c h)`. This part is valid for
an arbitrary representation `X`. -/

variable {X : Action (TopModuleCat R) G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Multiplicativity of the action: `ρ(a) (ρ(b) x) = ρ(a * b) x`. -/
lemma ρ_hom_ρ_hom (a b : G) (x : X.V) :
    (X.ρ a).hom ((X.ρ b).hom x) = (X.ρ (a * b)).hom x := by
  rw [map_mul]; rfl

variable (X) in
/-- The continuous `1`-cocycles `Z¹(G, X)`, as a `R`-submodule of the inhomogeneous cochains
`C(G, X)`: continuous functions `c` with `c (g * h) = c g + ρ(g) (c h)`. -/
def oneCocycles : Submodule R C(G, X.V) where
  carrier := {c | ∀ g h : G, c (g * h) = c g + (X.ρ g).hom (c h)}
  zero_mem' g h := by simp
  add_mem' {a b} ha hb g h := by
    simp only [ContinuousMap.add_apply, ha g h, hb g h, map_add]; abel
  smul_mem' r a ha g h := by
    simp only [ContinuousMap.smul_apply, ha g h, map_smul, smul_add]

omit [IsTopologicalGroup G] in
@[simp] lemma mem_oneCocycles {c : C(G, X.V)} :
    c ∈ oneCocycles X ↔ ∀ g h : G, c (g * h) = c g + (X.ρ g).hom (c h) := Iff.rfl
