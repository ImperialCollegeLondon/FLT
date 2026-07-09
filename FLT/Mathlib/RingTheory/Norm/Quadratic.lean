/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
public import FLT.Mathlib.FieldTheory.Galois.Basic

/-!
# Trace and norm in a separable quadratic extension

Proposed new Mathlib file `Mathlib.RingTheory.Norm.Quadratic`: trace and norm via the
nontrivial automorphism of a separable quadratic extension.
-/

@[expose] public section

open Algebra.IsQuadraticExtension

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_algEquiv K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem Algebra.IsQuadraticExtension.algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (x : L) : algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_algEquiv K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- The trace of `b + aθ` in a separable quadratic extension is `a·tr(θ) + 2b`. -/
theorem Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_ofNat, algebraMap_trace_eq_add K L hσ, AlgEquiv.commutes]
  ring

/-- The norm of `b + aθ` in a separable quadratic extension is `b² + ab·tr(θ) + a²·N(θ)`. -/
theorem Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_pow, algebraMap_trace_eq_add K L hσ,
    algebraMap_norm_eq_mul K L hσ, AlgEquiv.commutes]
  ring

/-- If `θ` generates a separable quadratic extension of `K` — that is, lies outside `K` — and
`t`, `n` denote its trace and norm, so that `θ² = tθ - n`, then the discriminant `t² - 4n` of
the minimal polynomial of `θ` is nonzero. (Over the nontrivial automorphism `σ` it equals
`(θ - σθ)²` with `σθ ≠ θ`. In characteristic 2 the statement says `t ≠ 0`: separable quadratic
extensions are Artin–Schreier extensions.) -/
theorem Algebra.IsQuadraticExtension.discrim_ne_zero {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  intro h0
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact algEquiv_apply_ne K L hσ hθ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm

/-- A square root `α ∉ K` of `d ∈ K` has trace `0` and norm `-d`: the nontrivial automorphism
sends `α` to `-α`. -/
theorem Algebra.IsQuadraticExtension.trace_eq_zero_and_norm_eq_neg_of_sq_eq {α : L} {d : K}
    (hαK : α ∉ Set.range (algebraMap K L)) (hα : α ^ 2 = algebraMap K L d) :
    Algebra.trace K L α = 0 ∧ Algebra.norm K α = -d := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  have hσα : σ α ≠ α := algEquiv_apply_ne K L hσ hαK
  have hσαα : σ α = -α := by
    have hσ2 : (σ α) ^ 2 = α ^ 2 := by rw [← map_pow, hα, AlgEquiv.commutes]
    have h1 : (σ α - α) * (σ α + α) = 0 := by linear_combination hσ2
    exact eq_neg_of_add_eq_zero_left
      ((mul_eq_zero.mp h1).resolve_left fun h ↦ hσα (sub_eq_zero.mp h))
  constructor
  · apply FaithfulSMul.algebraMap_injective K L
    rw [algebraMap_trace_eq_add K L hσ, hσαα, map_zero, add_neg_cancel]
  · apply FaithfulSMul.algebraMap_injective K L
    rw [algebraMap_norm_eq_mul K L hσ, hσαα, map_neg, ← hα]
    ring

end

end
