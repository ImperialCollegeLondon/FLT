/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import FLT.KnownIn1980s.MoretBailly.RationalPoints
public import FLT.Assumptions.KnownIn1980s
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!

# Moret-Bailly's theorem: points on curves with prescribed local behaviour

Let `T` be a smooth geometrically connected curve over a number field `k`.
Moret-Bailly's theorem produces points of `T` over finite Galois extensions
`L/k` with precisely controlled local behaviour: at each place `v` in a
finite set one may prescribe a finite Galois extension `M_v/k_v` and a
nonempty open `Gal(M_v/k_v)`-stable region `Ω_v ⊆ T(M_v)`, and the theorem
gives `L/k` Galois, linearly disjoint from any given finite Galois extension
`K_avoid/k`, and `P ∈ T(L)` such that all completions of `L` above `v` are
isomorphic to `M_v` and `P` lands in `Ω_v`. This is the engine of
*potential modularity*: applied to a twisted modular curve over `ℚ`, it
produces a totally real field `F` and an elliptic curve `E/F` linking a
given mod `ℓ` Galois representation to an induced (hence modular) mod `p`
one.

The statement follows from Théorème 1.3 of [L. Moret-Bailly, *Groupes de
Picard et problèmes de Skolem. II*, Ann. Sci. École Norm. Sup. (4) 22
(1989), no. 2, 181-194] by classical arguments; this precise form is the
variant used by Taylor in his potential modularity arguments. See
`moret-bailly-statement.tex` at the root of this repository for a detailed
account of the statement, an outline of the proof, and the prerequisites a
formalization of the proof would need.

## Implementation notes

* `T(M)` with its `v`-adic topology is `T.pointsOver K M`, from
  `FLT.KnownIn1980s.MoretBailly.RationalPoints`. The hypothesis
  `IsModuleTopology Kv M` pins the topology of `M` to the canonical one;
  without it, openness of `Ω` would be meaningless.
* `LocalCondition.Satisfies` avoids mentioning the places of `L`:
  via `Kv ⊗[K] L ≅ ∏_{w ∣ v} L_w`, the condition
  `∃ n, Nonempty ((Kv ⊗[K] L) ≃ₐ[Kv] (Fin n → M))` says exactly that all
  completions of `L` above `v` are `Kv`-isomorphic to `M`, and
  `∀ σ : L →ₐ[K] M, σ_* P ∈ Ω` says exactly that `P` lands in `Ω` under
  every identification `T(L_w) = T(M)`.
* Moret-Bailly produces points which are moreover integral away from a
  finite set of places; the FLT application does not need this, so
  integrality is discarded.

-/

@[expose] public section

open AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct

universe u

namespace MoretBailly

variable (K : Type u) [Field K]
  (Kv : Type u) [Field Kv] [TopologicalSpace Kv] [Algebra K Kv]
  (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of K))]

/-- A *local condition* on a `K`-scheme `T` at a place of the number field
`K` with completion `Kv`: a finite Galois extension `M/Kv`, together with a
nonempty open `Gal(M/Kv)`-stable subset `Ω ⊆ T(M)`. -/
structure LocalCondition : Type (u + 1) where
  /-- The prescribed finite Galois extension of the completion `Kv`. -/
  M : Type u
  [instFieldM : Field M]
  [instAlgebraKvM : Algebra Kv M]
  [instAlgebraKM : Algebra K M]
  [instTowerM : IsScalarTower K Kv M]
  [instFiniteDimensionalM : FiniteDimensional Kv M]
  [instGaloisM : IsGalois Kv M]
  [instTopologicalSpaceM : TopologicalSpace M]
  [instModuleTopologyM : IsModuleTopology Kv M]
  /-- The prescribed region of `T(M)` in which the global point must land. -/
  omega : Set (T.pointsOver K M)
  nonempty : omega.Nonempty
  isOpen : IsOpen omega
  /-- `omega` is stable under the action of `Gal(M/Kv)` on `T(M)` by
  post-composition. -/
  invariant : ∀ (σ : M ≃ₐ[Kv] M), ∀ P ∈ omega,
    Scheme.pointsOver.map T K (σ.toAlgHom.restrictScalars K) P ∈ omega

attribute [instance] LocalCondition.instFieldM LocalCondition.instAlgebraKvM
  LocalCondition.instAlgebraKM LocalCondition.instTowerM
  LocalCondition.instFiniteDimensionalM LocalCondition.instGaloisM
  LocalCondition.instTopologicalSpaceM LocalCondition.instModuleTopologyM

variable {K Kv T}

/-- `(L, P)` *satisfies* the local condition `(M, Ω)` at a place `v` if all
completions of `L` above `v` are `Kv`-isomorphic to `M`, and the image of
`P` in `T(M)` lies in `Ω` under every identification. See the module
docstring for why this is expressed via `Kv ⊗[K] L` and `σ : L →ₐ[K] M`. -/
def LocalCondition.Satisfies (D : LocalCondition K Kv T)
    (L : Type u) [Field L] [Algebra K L] (P : T.pointsOver K L) : Prop :=
  (∃ n : ℕ, Nonempty ((Kv ⊗[K] L) ≃ₐ[Kv] (Fin n → D.M))) ∧
  ∀ σ : L →ₐ[K] D.M, Scheme.pointsOver.map T K σ P ∈ D.omega

end MoretBailly

variable (k : Type u) [Field k] [NumberField k]
  (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
  (K_avoid : IntermediateField k K) [IsGalois k K_avoid] [FiniteDimensional k K_avoid]
  (T : Scheme.{u}) [T.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [GeometricallyConnected (T ↘ Spec (.of k))]
  (Sf : Finset (HeightOneSpectrum (𝓞 k))) (Sinf : Finset (InfinitePlace k))
  (Cf : (v : HeightOneSpectrum (𝓞 k)) → MoretBailly.LocalCondition k (v.adicCompletion k) T)
  (Cinf : (v : InfinitePlace k) → MoretBailly.LocalCondition k v.Completion T)

/-- **Moret-Bailly's theorem**, in the refined form used in potential
modularity arguments: given a smooth, separated, quasi-compact,
geometrically connected curve `T` over a number field `k`, a finite Galois
extension `K_avoid` of `k` inside a fixed algebraic closure `K`, and local
conditions at finite sets `Sf`, `Sinf` of finite and infinite places of `k`,
there are a finite Galois extension `L/k` inside `K`, linearly disjoint from
`K_avoid`, and a point `P ∈ T(L)` satisfying all the local conditions. -/
def MoretBaillyTheorem : Prop :=
  ∃ (L : IntermediateField k K) (P : T.pointsOver k L),
    FiniteDimensional k L ∧ IsGalois k L ∧ L.LinearDisjoint K_avoid ∧
    (∀ v ∈ Sf, (Cf v).Satisfies L P) ∧ (∀ v ∈ Sinf, (Cinf v).Satisfies L P)

set_option linter.unusedSectionVars false in
/-- Moret-Bailly's theorem follows from Théorème 1.3 of [L. Moret-Bailly,
*Groupes de Picard et problèmes de Skolem. II*, Ann. Sci. École Norm. Sup.
(4) 22 (1989), no. 2, 181-194] by classical pre-1990 arguments (Krasner's
lemma, the Chebotarev density theorem, the Riemann hypothesis for curves
over finite fields, and a Galois closure argument). The deduction is written
out in `moret-bailly-statement.tex` at the root of this repository. -/
theorem moretBailly : MoretBaillyTheorem k K K_avoid T Sf Sinf Cf Cinf :=
  knownin1980s
