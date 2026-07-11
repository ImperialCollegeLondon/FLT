/-
Copyright (c) 2026 Richard Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Richard Hill
-/
module

public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.CupProduct
public import FLT.Mathlib.RepresentationTheory.Smooth.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# The local Tate duality pairing

Let `K` be a nonarchimedean local field of characteristic zero and let `M` be a finite discrete
module over the absolute Galois group `Gal(K̄/K)` of `K`. This file constructs the local Tate
duality pairing on the continuous group cohomology of `Gal(K̄/K)`, as the cup product induced by
the evaluation pairing of `M` with its dual `M^∨ = Hom(M, K̄ˣ)`.

## Main definitions

* `ContRepresentation.multiplicative K`: the continuous representation of `Gal(K̄/K)` on the
  multiplicative group `K̄ˣ` of the algebraic closure, written additively and carrying the
  discrete topology.
* `LocalGaloisRep.dual K M ρ`: the dual `M^∨ = Hom(M, K̄ˣ)` of a local Galois representation
  `ρ` on `M`, i.e. the internal hom of `M` into the multiplicative representation, with
  `Gal(K̄/K)` acting by conjugation.
* `pair₀ K M ρ`: the evaluation pairing `m ↦ (φ ↦ φ m)` of `M` with `M^∨`, as an intertwining
  map from `ρ` into the internal hom of the dual and the multiplicative representation.
* `pairing K M ρ i j hij`: the local Tate duality pairing
  `Hⁱ(Gal(K̄/K), M) × Hʲ(Gal(K̄/K), M^∨) → H²(Gal(K̄/K), K̄ˣ)` for `i + j = 2`, defined as the
  cup product on continuous cohomology induced by `pair₀`.

## TODO

* Prove that the pairing is perfect (local Tate duality): `pairing_isPerfect1` and
  `pairing_isPerfect2`.
-/

@[expose] public section

universe u

variable (K M : Type u) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [TopologicalSpace M] [AddCommGroup M] [DiscreteTopology M]
  [Finite M] (ρ : ContRepresentation ℤ (Field.absoluteGaloisGroup K) M)
  [hρ : Representation.Smooth.IsSmooth ρ.toRepresentation]

open TopRep

/-- The group `(AlgebraicClosure K)ˣ`, written additively, carries the discrete topology. -/
instance instTopologicalSpaceAdditiveUnitsAlgebraicClosure :
    TopologicalSpace (Additive (AlgebraicClosure K)ˣ) := ⊥

instance : DiscreteTopology (Additive (AlgebraicClosure K)ˣ) := ⟨rfl⟩

open Additive

/-- The continuous representation of the absolute Galois group of `K` on the multiplicative
group `(AlgebraicClosure K)ˣ` of its algebraic closure, written additively, given by the
natural Galois action. -/
noncomputable def ContRepresentation.multiplicative :
    ContRepresentation ℤ (Field.absoluteGaloisGroup K) (Additive (AlgebraicClosure K)ˣ) where
  toMonoidHom.toFun g := {
    toFun x := ofMul (g • toMul x)
    map_add' := by simp
    map_smul' := by simp
    cont := by tauto
  }
  toMonoidHom.map_one' := rfl
  toMonoidHom.map_mul' x y := by ext; simp

/-- The dual `M^∨ = Hom(M, K̄ˣ)` of a local Galois representation `ρ` on `M`: the topological
representation on the continuous linear maps from `M` to the (additively written) multiplicative
representation, with the Galois group acting by conjugation. -/
noncomputable abbrev LocalGaloisRep.dual : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  iHom (.of ρ) (.of (ContRepresentation.multiplicative K))

open ContinuousLinearMap.CompactOpen ContRepresentation in
/-- The evaluation pairing `m ↦ (φ ↦ φ m)` of a local Galois representation with its dual, as
an intertwining map from `ρ` into the internal hom of the dual and the multiplicative
representation. -/
noncomputable def pair₀ : ρ →ⁱL ContRepresentation.linHom (LocalGaloisRep.dual K M ρ).ρ
    (ContRepresentation.multiplicative K) := {
  toFun := evalCLM
  map_add' m m' := by ext φ; simp
  map_smul' c m := by ext φ; simp
  cont := continuous_of_discreteTopology
  isIntertwining' g := by
    ext m φ
    have h1 : ∀ x, ContRepresentation.multiplicative K g
        (ContRepresentation.multiplicative K g⁻¹ x) = x := fun x ↦ by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    simp [h1] }

open ContinuousLinearMap.CompactOpen in
/-- The local Tate duality pairing `Hⁱ(Gal(K̄/K), M) × Hʲ(Gal(K̄/K), M^∨) → H²(Gal(K̄/K), K̄ˣ)`
for `i + j = 2`: the cup product on continuous group cohomology induced by the evaluation
pairing `pair₀`. -/
noncomputable def pairing (i j : ℕ) (hij : 2 = i + j) :
    continuousCohomology i (.of ρ) ⟶ TopModuleCat.linHom (k := ℤ)
      (continuousCohomology j (LocalGaloisRep.dual K M ρ)) (continuousCohomology 2
      (.of (ContRepresentation.multiplicative K))) :=
  ContinuousCohomology.cup _ _ _ (pair₀ K M ρ)
    (ContRepresentation.continuous_pair_of_discrete (pair₀ K M ρ)) i j 2 hij

lemma pairing_isPerfect1 (i j : ℕ) (hij : 2 = i + j) :
    ∀ x : continuousCohomology i (.of ρ), x ≠ 0 →
      ∃ y : continuousCohomology j (LocalGaloisRep.dual K M ρ),
      pairing K M ρ i j hij x y ≠ 0 := by
  sorry

lemma pairing_isPerfect2 (i j : ℕ) (hij : 2 = i + j) :
    ∀ y : continuousCohomology j (LocalGaloisRep.dual K M ρ), y ≠ 0 →
      ∃ x : continuousCohomology i (.of ρ),
      pairing K M ρ i j hij x y ≠ 0 := by
  sorry
