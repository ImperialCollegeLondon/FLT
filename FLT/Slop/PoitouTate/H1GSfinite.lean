/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Instances.ZMod
public import FLT.Slop.PoitouTate.actionof
public import FLT.Slop.PoitouTate.phipmap

/-!
# `p`-finiteness from Mazur's condition `Φ_p`

This file completes the proof, for a **compact** (e.g. profinite) group `G` satisfying Mazur's
finiteness condition `Φ_p` (`MazurFinite`), that `Z¹_cont(G, S)` is **finite** for every finite
discrete `𝔽_p`-vector space `S` with a continuous `G`-action
(`finite_oneCocycles_of_mazurFinite`).

Two ingredients:
* **Layer 3** (`finite_oneCocycles_of_trivial_action`): for an *open* subgroup `N` acting
  *trivially* on `S`, the cocycles `Z¹(N, S) = Hom_cont(N, S)` are finite. Picking an
  `𝔽_p`-basis
  `S ≅ 𝔽_p^d`, a cocycle's `i`-th coordinate is a continuous homomorphism `N → ℤ/p`, and
  these
  jointly determine it; finiteness of each coordinate space is exactly `Φ_p`.
* **Layer 2** (`finite_oneCocycles_of_finite_quotient`, from `InfRes`): the inflation–restriction
  squeeze. Taking `N₀` to be the (open, normal) pointwise stabilizer of `S`, which acts trivially
  on
  *all* of `S`, the squeeze reduces `Z¹(G, S)` to `Z¹(G/N₀, S)` (finite: `G/N₀` and `S`
  finite) and
  `Z¹(N₀, S)` (Layer 3).

Notably this needs **no composition-series dévissage**: the `𝔽_p`-basis decomposition in Layer 3
already performs the reduction to `ℤ/p` coefficients.

Current state: this file defines `MazurFinite` (the condition `Φ_p`) and states the
`p`-finiteness proposition with `sorry`; the two ingredient lemmas described above are TODO.
-/

@[expose] public noncomputable section

open CategoryTheory TopModuleCat ContinuousMap

/-- **Mazur's finiteness condition `Φ_p`** (Mazur, *Deforming Galois representations*, §1.1):
every open subgroup `N ≤ G` admits only finitely many continuous homomorphisms to `ℤ/p`.
The full absolute Galois group of a number field fails this (infinitely many `ℤ/p`-extensions
as the ramification set varies), but `G_{F,S}` satisfies it by Hermite–Minkowski — cf. the
`Φ_p` discussion in `GKSDefn.lean`. -/
class MazurFinite (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  finite_continuousMonoidHom (N : Subgroup G) (hN : IsOpen (N : Set G)) :
    Finite (ContinuousMonoidHom N (Multiplicative (ZMod p)))

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {p : ℕ} [Fact p.Prime]

/-! ### The `p`-finiteness Proposition -/

variable [CompactSpace G]

theorem finite_oneCocycles_of_mazurFinite [MazurFinite p G]
    {S : Type u} [AddCommGroup S] [Module (ZMod p) S] [Finite S] [TopologicalSpace S]
    [DiscreteTopology S] [DistribMulAction G S] [ContinuousSMul G S] :
    Finite (oneCocycles (actionOf G ℤ S)) := sorry

end ContinuousCohomology
