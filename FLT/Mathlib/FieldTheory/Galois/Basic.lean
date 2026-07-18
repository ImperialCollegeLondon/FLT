/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import FLT.Mathlib.LinearAlgebra.Dimension.IsQuadraticExtension

import Mathlib.RingTheory.Norm.Transitivity

/-!
# The Galois theory of separable quadratic extensions

Material for `Mathlib.FieldTheory.Galois.Basic`: a separable quadratic extension `L/K` has
exactly two automorphisms; trace and norm via the nontrivial automorphism; the quadratic
character of `Aut(M/K)` attached to a normal subextension `K ⊆ L ⊆ M`.
-/

@[expose] public section

open Algebra.IsQuadraticExtension

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L]

-- Let `M` be a field extension of `L`, for example `L` itself or a separable closure of `K`.
variable (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- For a normal subextension `K ⊆ L ⊆ M`, a `K`-automorphism `σ` of `M` fixes `L` pointwise
if and only if its restriction to `L` (`AlgEquiv.restrictNormal`) is the identity. -/
theorem forall_apply_algebraMap_iff_restrictNormal_eq_one (σ : M ≃ₐ[K] M) :
    (∀ x : L, σ (algebraMap L M x) = algebraMap L M x) ↔ σ.restrictNormal L = 1 := by
  simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply, ← AlgEquiv.restrictNormal_commutes]
  exact forall_congr' fun x ↦ (FaithfulSMul.algebraMap_injective L M).eq_iff

/-- The bundled form of `forall_apply_algebraMap_iff_restrictNormal_eq_one`, in terms of
`AlgEquiv.restrictNormalHom` rather than the underlying `AlgEquiv.restrictNormal`. -/
theorem restrictNormalHom_eq_one_iff (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictNormalHom L σ = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x :=
  (forall_apply_algebraMap_iff_restrictNormal_eq_one K L M σ).symm

variable [Algebra.IsSeparable K L]

-- Note that mathlib already knows the basic facts about this situation: `L/K` is
-- finite (`Module.Finite` from `Algebra.IsQuadraticExtension`), normal
-- (`Algebra.IsQuadraticExtension.normal`) and hence Galois
-- (`Algebra.IsQuadraticExtension.isGalois`), with cyclic Galois group
-- (`Algebra.IsQuadraticExtension.isCyclic`) of order 2 (`IsGalois.card_aut_eq_finrank`
-- plus `Algebra.IsQuadraticExtension.finrank_eq_two`).

/-- A separable quadratic extension has exactly two automorphisms. -/
theorem Algebra.IsQuadraticExtension.card_algEquiv : Nat.card (L ≃ₐ[K] L) = 2 :=
  (IsGalois.card_aut_eq_finrank K L).trans (finrank_eq_two K L)

/-- A separable quadratic extension has a nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.exists_algEquiv_ne_one : ∃ σ : L ≃ₐ[K] L, σ ≠ 1 :=
  ((Nat.card_eq_two_iff' 1).mp (card_algEquiv K L)).exists

/-- The only automorphisms of a separable quadratic extension are the identity and any given
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (φ : L ≃ₐ[K] L) : φ = 1 ∨ φ = σ := by
  rcases eq_or_ne φ 1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (((Nat.card_eq_two_iff' 1).mp (card_algEquiv K L)).unique h1 hσ)

/-- The nontrivial automorphism of a separable quadratic extension is an involution. -/
theorem Algebra.IsQuadraticExtension.algEquiv_mul_self {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) : σ * σ = 1 :=
  (algEquiv_eq_one_or_eq K L hσ (σ * σ)).resolve_right fun h ↦ absurd (mul_eq_left.mp h) hσ

/-- An element fixed by a nontrivial automorphism — hence, `Gal(L/K)` having order two, by all of
`Gal(L/K)` — lies in the base field. -/
theorem Algebra.IsQuadraticExtension.mem_range_algebraMap_of_apply_eq {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) {x : L} (hx : σ x = x) : x ∈ Set.range (algebraMap K L) := by
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  intro φ
  rcases algEquiv_eq_one_or_eq K L hσ φ with rfl | rfl
  · exact AlgEquiv.one_apply x
  · exact hx

open Classical in
/-- The automorphism group of a separable quadratic extension consists of the identity and one
nontrivial element. -/
theorem Algebra.IsQuadraticExtension.univ_algEquiv {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) :
    (Finset.univ : Finset (L ≃ₐ[K] L)) = {1, σ} :=
  (Finset.eq_univ_of_forall fun φ ↦ by simpa using algEquiv_eq_one_or_eq K L hσ φ).symm

/-- The nontrivial automorphism of a separable quadratic extension moves every element
lying outside the base field. -/
theorem Algebra.IsQuadraticExtension.algEquiv_apply_ne {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {x : L}
    (hx : x ∉ Set.range (algebraMap K L)) : σ x ≠ x :=
  fun heq ↦ hx (mem_range_algebraMap_of_apply_eq K L hσ heq)

/-- The nontrivial automorphism of a separable quadratic extension sends a square root
`α ∉ K` of an element of `K` to `-α`. -/
theorem Algebra.IsQuadraticExtension.algEquiv_apply_eq_neg_of_sq_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    {α : L} {d : K} (hαK : α ∉ Set.range (algebraMap K L)) (hα : α ^ 2 = algebraMap K L d) :
    σ α = -α := by
  have hσα : σ α ≠ α := algEquiv_apply_ne K L hσ hαK
  have h1 : (σ α - α) * (σ α + α) = 0 := by
    have hσ2 : (σ α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    linear_combination hσ2
  exact eq_neg_of_add_eq_zero_left
    ((mul_eq_zero.mp h1).resolve_left fun h ↦ hσα (sub_eq_zero.mp h))

open Classical in
/-- The quadratic character of `Aut(M/K)` attached to a separable quadratic subextension
`K ⊆ L ⊆ M`: it sends `σ` to `1` if `σ` fixes `L` pointwise, and to `-1` otherwise.

Since `L/K` is normal, every `K`-automorphism of `M` maps `L` to `L`, and multiplicativity
(`map_mul'`) follows because restriction to `L` is a homomorphism to the order 2 group
`Gal(L/K)`. Taking `M = L` gives the quadratic character of `Gal(L/K)` itself; if `M/K` is
normal then this character is the composite of the restriction `Aut(M/K) → Gal(L/K)` with the
unique isomorphism `Gal(L/K) ≃ {±1}`, and in particular is surjective
(`quadraticCharacter_surjective`). -/
noncomputable def quadraticCharacter : (M ≃ₐ[K] M) →* ℤˣ where
  toFun σ := if ∀ x : L, σ (algebraMap L M x) = algebraMap L M x then 1 else -1
  map_one' := by simp
  map_mul' σ τ := by
    -- "Fixes `L` pointwise" means "restricts to `1`" on `L`; restriction is multiplicative
    -- (`restrictNormalHom`), so the claim reduces to the sign map of the order-2 `Gal(L/K)`.
    obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
    have h := fun x : Gal(M/K) ↦ algEquiv_eq_one_or_eq K L hσ₀ (AlgEquiv.restrictNormalHom L x)
    rcases h σ with ha | ha <;>
    rcases h τ with hb | hb <;>
    simp only [← restrictNormalHom_eq_one_iff, map_mul, ha, hb] <;>
    simp [algEquiv_mul_self K L hσ₀, hσ₀]

theorem quadraticCharacter_eq_one_iff (σ : M ≃ₐ[K] M) :
    quadraticCharacter K L M σ = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  simp only [quadraticCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- If `M/K` is normal (for example `M = L`, or `M` a separable closure of `K`) then the
nontrivial element of `Gal(L/K)` extends to an automorphism of `M`, so the quadratic character
of `Aut(M/K)` attached to `L/K` is surjective. -/
theorem quadraticCharacter_surjective [Normal K M] :
    Function.Surjective (quadraticCharacter K L M) := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · -- The nontrivial element of `Gal(L/K)` lifts to some `τ ∈ Aut(M/K)` because `M/K` is normal;
    -- `τ` does not fix `L` pointwise, so `χ(τ) ≠ 1`, hence `χ(τ) = -1`.
    obtain ⟨σ₀, hσ₀⟩ := exists_algEquiv_ne_one K L
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (E := M) σ₀
    refine ⟨τ, (Int.units_eq_one_or _).resolve_left fun heq ↦ hσ₀ ?_⟩
    exact hτ.symm ▸ (restrictNormalHom_eq_one_iff K L M τ).mpr
      ((quadraticCharacter_eq_one_iff K L M τ).mp heq)

end

end
