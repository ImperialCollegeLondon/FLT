/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import FLT.Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Valued.ValuedField

/-! # Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued K ℤᵐ⁰` instance but no canonical base with which to embed this into
`NNReal`.
-/

open Multiplicative WithZero

open scoped Topology

namespace Valued.WithZeroMulInt

open Set Filter in
/-- In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ ofAdd (-1 : ℤ)`. -/
theorem tendsto_zero_pow_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤᵐ⁰]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) :
    Tendsto (fun (n : ℕ) => x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_setOf_eq, map_pow, eventually_atTop]
  have h_lt : ofAdd (-1 : ℤ) < (1 : ℤᵐ⁰) := by
     rw [← coe_one, coe_lt_coe, ← ofAdd_zero, ofAdd_lt]; linarith
  intro γ _
  let γ' := Units.map MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom γ
  suffices ∃ a, ∀ b ≥ a, v x ^ b < γ' by sorry
  by_cases hγ' : γ'.val ≤ 1
  · let m := - toAdd (unitsWithZeroEquiv γ') + 1 |>.toNat
    refine ⟨m, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    replace hγ' : 0 ≤ -toAdd (unitsWithZeroEquiv γ') + 1 := by
      rw [← coe_unitsWithZeroEquiv_eq_units_val, ←coe_one, coe_le_coe, ← toAdd_le, toAdd_one] at hγ'
      linarith
    apply lt_of_le_of_lt <| pow_le_pow_left₀ zero_le' hx m
    rw [← coe_unitsWithZeroEquiv_eq_units_val, ← coe_pow, coe_lt_coe, ← ofAdd_nsmul,
      nsmul_eq_mul, Int.toNat_of_nonneg hγ', mul_neg, mul_one, neg_add_rev, neg_neg, ofAdd_add,
      ofAdd_neg, ofAdd_toAdd, mul_lt_iff_lt_one_right', Left.inv_lt_one_iff, ← ofAdd_zero, ofAdd_lt]
    exact zero_lt_one
  · refine ⟨1, fun b hb => lt_of_le_of_lt
      (pow_le_pow_of_le_one zero_le' (le_trans hx <| le_of_lt h_lt) hb) ?_⟩
    apply pow_one (v x) ▸ lt_trans (lt_of_le_of_lt hx h_lt) (lt_of_not_ge hγ')

open Filter in
theorem exists_pow_lt_of_le_neg_one {K : Type*} [Ring K] [Valued K ℤᵐ⁰]
    {x : K} (hx : v x ≤ ofAdd (-1 : ℤ)) (γ : ℤᵐ⁰ˣ) :
    ∃ n, v x ^ n < γ := by
  simp_rw [← map_pow]
  let ⟨n, hn⟩ := eventually_atTop.1 <|
     ((hasBasis_nhds_zero _ _).tendsto_right_iff ).1 (tendsto_zero_pow_of_le_neg_one hx) γ trivial
  exact ⟨n, by simpa using hn n le_rfl⟩

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

theorem irreducible_valuation_le_ofAdd_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp only [hy, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ge_iff_le]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

/- Note: this is copied directly from the mathlib result
`Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField` with a relaxation
on some of the hypotheses on `K`. The proof is unchanged. -/
lemma finite_quotient_maximalIdeal_pow_of_finite_residueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_ideal_quotient
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

/-- The ring of integers `𝒪[K]` of a `ℤᵐ⁰`-valued field `K` with finite residue
field has a finite covering by elements of the basis of uniformity of `K`, whenever
`𝒪[K]` is a discrete valuation ring. -/
theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] {γ : ℤᵐ⁰ˣ}
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out : Set 𝒪[K])
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem Quotient.out (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

set_option backward.isDefEq.respectTransparency false in
/-- The ring of integers `𝒪[K]` of a complete `ℤᵐ⁰`-valued field `K` with finite residue
field is compact, whenever `𝒪[K]` is a discrete valuation ring. -/
theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]] (h : Finite 𝓀[K]) :
    CompactSpace 𝒪[K] where
  isCompact_univ :=
    isCompact_iff_isCompact_univ.1 <|
      isCompact_iff_totallyBounded_isComplete.2
        ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 <| fun _ _ =>
          finite_cover_of_uniformity_basis h, (isClosed_integer K).isComplete⟩

end Valued.WithZeroMulInt
