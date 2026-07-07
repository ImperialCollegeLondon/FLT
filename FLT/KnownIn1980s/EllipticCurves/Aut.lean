/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!

# Automorphisms of an elliptic curve with `j ∉ {0, 1728}`

Let `E` be an elliptic curve over a field `K`. Over a field, isomorphisms of Weierstrass curves
are exactly the admissible changes of variables `WeierstrassCurve.VariableChange K`, acting via
`•`; the automorphisms of `E` are therefore the `C : VariableChange K` with `C • E = E`. This file
proves the classical fact (Silverman, *The Arithmetic of Elliptic Curves*, III.10) that if
`j(E) ∉ {0, 1728}` then the only automorphisms of `E` are `±1`, uniformly in the characteristic.

## Main definitions and statements

* `WeierstrassCurve.negVariableChange E` : the automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)`
  of `E`, as an admissible change of variables `⟨-1, 0, -a₁, -a₃⟩`.
* `WeierstrassCurve.eq_one_or_eq_negVariableChange_of_smul_eq` : if `j(E) ∉ {0, 1728}` then any
  `C : VariableChange K` with `C • E = E` equals `1` or `negVariableChange E`.

## Implementation notes

The proof is broken into pieces. `j ∉ {0, 1728}` is equivalent to `c₄ ≠ 0` and `c₆ ≠ 0`
(`c₆_ne_zero_of_j_ne_1728`). From the transformation laws of `c₄` and `c₆` one gets `u² = 1`
(`u_eq_one_or_eq_neg_one`), which reduces everything to the case `u = 1`. There
`r = 0` follows from the transformation laws of `b₄`, `b₆`, `b₈` (`r_eq_zero_of_u_eq_one`,
splitting on whether `6 = 0`), and then `s`, `t` are read off from those of `a₁`, `a₃`, `a₄`, `a₆`
(`eq_one_or_eq_negVariableChange_of_u_eq_one`, where the `negVariableChange` value can occur only
in characteristic `2`).

-/

@[expose] public section

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-! ### The negation automorphism -/

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange K :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := rfl

lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  rw [variableChange_def]
  ext <;>
    simp only [negVariableChange, Units.val_neg, Units.val_one, inv_neg, inv_one] <;>
    ring

lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp only [VariableChange.mul_def, VariableChange.one_def, negVariableChange, Units.val_neg,
    Units.val_one]
  ext
  · rw [neg_one_mul, neg_neg]
  · ring
  · ring
  · ring

lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_right E.negVariableChange_mul_self

/-- Base change commutes with the negation automorphism: mapping `[-1]` on `W` through a ring
homomorphism `φ` gives `[-1]` on `W.map φ`. -/
lemma negVariableChange_map {A B : Type*} [Field A] [Field B] (W : WeierstrassCurve A)
    (φ : A →+* B) : W.negVariableChange.map φ = (W.map φ).negVariableChange := by
  ext <;> simp [negVariableChange]

/-! ### `Aut(E) = {±1}` for `j ∉ {0, 1728}`

Throughout, `C • E = E` is an automorphism of `E`; the nonvanishing of `c₄` and `c₆` encodes
`j ∉ {0, 1728}`. -/

/-- If `c₆ ≠ 0` (i.e. `j ≠ 1728`), then in characteristic `2` the invariant `a₁` is nonzero:
otherwise `c₄ = a₁⁴` would vanish. -/
lemma a₁_ne_zero_of_two_eq_zero (hc4 : E.c₄ ≠ 0) (h2 : (2 : K) = 0) : E.a₁ ≠ 0 := by
  intro ha
  apply hc4
  have hc4eq : E.c₄ = E.b₂ ^ 2 - 24 * E.b₄ := rfl
  rw [hc4eq]
  simp only [b₂, b₄, ha]
  linear_combination (8 * E.a₂ ^ 2 - 24 * E.a₄) * h2

/-- The negation automorphism is nontrivial when `c₄ ≠ 0`: in characteristic `≠ 2` it has
`u = -1 ≠ 1`, and in characteristic `2` it has `s = -a₁ ≠ 0`. -/
lemma negVariableChange_ne_one (hc4 : E.c₄ ≠ 0) : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · refine E.a₁_ne_zero_of_two_eq_zero hc4 h2 ?_
    have hs : E.negVariableChange.s = (1 : VariableChange K).s := by rw [h]
    simpa [negVariableChange, VariableChange.one_def, neg_eq_zero] using hs
  · apply h2
    have hu : E.negVariableChange.u = (1 : VariableChange K).u := by rw [h]
    rw [negVariableChange_u, VariableChange.one_def] at hu
    have hv : (-1 : K) = 1 := by simpa using congrArg Units.val hu
    linear_combination -hv

/-- An automorphism `C` of `E` with `C.u = 1` has no `x`-translation: `C.r = 0`. Splitting on
whether `6 = 0`, this uses `c₄ ≠ 0` in characteristic `2` or `3` and `c₆ ≠ 0` otherwise. -/
lemma r_eq_zero_of_u_eq_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hu : C.u = 1) (hCE : C • E = E) : C.r = 0 := by
  have eb4 := congrArg WeierstrassCurve.b₄ hCE
  rw [variableChange_b₄, hu, inv_one, Units.val_one, one_pow, one_mul] at eb4
  have eb6 := congrArg WeierstrassCurve.b₆ hCE
  rw [variableChange_b₆, hu, inv_one, Units.val_one, one_pow, one_mul] at eb6
  have eb8 := congrArg WeierstrassCurve.b₈ hCE
  rw [variableChange_b₈, hu, inv_one, Units.val_one, one_pow, one_mul] at eb8
  by_contra hr0
  rcases eq_or_ne (6 : K) 0 with h6 | h6
  · -- characteristic `2` or `3`: `b₂ = 0`, hence `c₄ = 0`.
    apply hc4
    have hb2 : E.b₂ = 0 := by
      have hq4 : C.r * E.b₂ = 0 := by linear_combination eb4 - C.r ^ 2 * h6
      exact (mul_eq_zero.mp hq4).resolve_left hr0
    have h24 : (24 : K) = 0 := by
      have h46 : (24 : K) = 4 * 6 := by norm_num
      rw [h46, h6, mul_zero]
    have hc4eq : E.c₄ = E.b₂ ^ 2 - 24 * E.b₄ := rfl
    rw [hc4eq, hb2, h24]; ring
  · -- otherwise `2 ≠ 0`, `3 ≠ 0`: `b₆ = 0`, hence `c₆ = 0`.
    have h63 : (6 : K) = 2 * 3 := by norm_num
    have h2 : (2 : K) ≠ 0 := fun hh => h6 (by rw [h63, hh, zero_mul])
    have h3 : (3 : K) ≠ 0 := fun hh => h6 (by rw [h63, hh, mul_zero])
    apply hc6
    have hb2 : E.b₂ = -6 * C.r := by
      have : C.r * E.b₂ = C.r * (-6 * C.r) := by linear_combination eb4
      exact mul_left_cancel₀ hr0 this
    have hb4 : E.b₄ = C.r ^ 2 := by
      have : 2 * C.r * E.b₄ = 2 * C.r * C.r ^ 2 := by linear_combination eb6 - C.r ^ 2 * hb2
      exact mul_left_cancel₀ (mul_ne_zero h2 hr0) this
    have hb6 : E.b₆ = 0 := by
      have : 3 * C.r * E.b₆ = 3 * C.r * 0 := by
        linear_combination eb8 - 3 * C.r ^ 2 * hb4 - C.r ^ 3 * hb2
      exact mul_left_cancel₀ (mul_ne_zero h3 hr0) this
    have hc6eq : E.c₆ = -E.b₂ ^ 3 + 36 * E.b₂ * E.b₄ - 216 * E.b₆ := rfl
    rw [hc6eq, hb2, hb4, hb6]; ring

/-- An automorphism `C` of `E` with `C.u = 1` is either the identity or `negVariableChange E`.
After `r_eq_zero_of_u_eq_one`, the `a₁` and `a₃` laws give `2s = 2t = 0`; in characteristic `≠ 2`
this forces `s = t = 0`, and in characteristic `2` the `a₄`, `a₆` laws pin `(s, t)` down to either
`(0, 0)` or `(-a₁, -a₃)`. -/
lemma eq_one_or_eq_negVariableChange_of_u_eq_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hu : C.u = 1) (hCE : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  have hr : C.r = 0 := E.r_eq_zero_of_u_eq_one hc4 hc6 hu hCE
  obtain ⟨e1, e2, e3, e4, e6⟩ := WeierstrassCurve.ext_iff.mp hCE
  rw [variableChange_a₁, hu, inv_one, Units.val_one, one_mul] at e1
  rw [variableChange_a₂, hu, inv_one, Units.val_one, one_pow, one_mul] at e2
  rw [variableChange_a₃, hu, inv_one, Units.val_one, one_pow, one_mul] at e3
  rw [variableChange_a₄, hu, inv_one, Units.val_one, one_pow, one_mul] at e4
  rw [variableChange_a₆, hu, inv_one, Units.val_one, one_pow, one_mul] at e6
  have hs2 : 2 * C.s = 0 := by linear_combination e1
  have ht2 : 2 * C.t = 0 := by linear_combination e3 - E.a₁ * hr
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- characteristic `2`: `a₁ ≠ 0`, `s ∈ {0, -a₁}`, and `t` follows.
    have ha1 : E.a₁ ≠ 0 := E.a₁_ne_zero_of_two_eq_zero hc4 h2
    have hq2 : C.s * (E.a₁ + C.s) = 0 := by linear_combination -e2 + 3 * hr
    have hq4 : C.s * E.a₃ + C.t * E.a₁ = 0 := by
      linear_combination -e4 + (2 * E.a₂ - C.s * E.a₁ + 3 * C.r) * hr - C.s * C.t * h2
    rcases (mul_eq_zero.mp hq2).imp id eq_neg_of_add_eq_zero_right with hs | hs
    · -- `s = 0`, forcing `t = 0`: `C = 1`.
      have ht : C.t = 0 := by
        have : C.t * E.a₁ = 0 := by linear_combination hq4 - E.a₃ * hs
        exact (mul_eq_zero.mp this).resolve_right ha1
      left
      rw [VariableChange.one_def]
      exact VariableChange.ext hu hr hs ht
    · -- `s = -a₁`, forcing `t = -a₃`: `C = negVariableChange E`.
      have ht : C.t = -E.a₃ := by
        have : E.a₁ * (C.t + E.a₃) = 0 := by
          linear_combination hq4 - E.a₃ * hs + E.a₁ * E.a₃ * h2
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left ha1)
      have hu1neg : (1 : Kˣ) = -1 :=
        Units.ext (by rw [Units.val_one, Units.val_neg, Units.val_one]; linear_combination h2)
      right
      exact VariableChange.ext (hu.trans hu1neg) hr hs ht
  · -- characteristic `≠ 2`: `s = t = 0`, so `C = 1`.
    have hs : C.s = 0 := (mul_eq_zero.mp hs2).resolve_left h2
    have ht : C.t = 0 := (mul_eq_zero.mp ht2).resolve_left h2
    left
    rw [VariableChange.one_def]
    exact VariableChange.ext hu hr hs ht

/-- The `u`-coefficient of an automorphism `C` of `E` (with `c₄, c₆ ≠ 0`) satisfies `u² = 1`:
the `c₄` and `c₆` laws give `u⁴ = u⁶ = 1`. -/
lemma u_eq_one_or_eq_neg_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hCE : C • E = E) : C.u = 1 ∨ C.u = -1 := by
  have hu4 : (C.u : K) ^ 4 = 1 := by
    have h := congrArg WeierstrassCurve.c₄ hCE
    rw [variableChange_c₄, Units.val_inv_eq_inv_val] at h
    have h1 : ((C.u : K)⁻¹) ^ 4 = 1 := mul_right_cancel₀ hc4 (h.trans (one_mul E.c₄).symm)
    rwa [inv_pow, inv_eq_one] at h1
  have hu6 : (C.u : K) ^ 6 = 1 := by
    have h := congrArg WeierstrassCurve.c₆ hCE
    rw [variableChange_c₆, Units.val_inv_eq_inv_val] at h
    have h1 : ((C.u : K)⁻¹) ^ 6 = 1 := mul_right_cancel₀ hc6 (h.trans (one_mul E.c₆).symm)
    rwa [inv_pow, inv_eq_one] at h1
  have hu2 : (C.u : K) * (C.u : K) = 1 := by
    have h64 : (C.u : K) ^ 6 = (C.u : K) ^ 4 * ((C.u : K) * (C.u : K)) := by ring
    rw [hu6, hu4, one_mul] at h64
    exact h64.symm
  rcases mul_self_eq_one_iff.mp hu2 with h | h
  · exact Or.inl (Units.val_eq_one.mp h)
  · exact Or.inr (Units.ext (by rw [Units.val_neg, Units.val_one]; exact h))

/-- If `j(E) ≠ 1728` then `c₆(E) ≠ 0`, since `c₆ = 0` forces `1728·Δ = c₄³`, i.e. `j = 1728`. -/
lemma c₆_ne_zero_of_j_ne_1728 [E.IsElliptic] (hj : E.j ≠ 1728) : E.c₆ ≠ 0 := by
  intro h
  apply hj
  have hcr : E.c₄ ^ 3 = 1728 * (E.Δ' : K) := by
    have hh := E.c_relation
    rw [h, ← coe_Δ'] at hh
    linear_combination -hh
  rw [j, Units.val_inv_eq_inv_val, hcr, mul_left_comm, inv_mul_cancel₀ E.Δ'.ne_zero, mul_one]

/-- If `c₄ ≠ 0` and `c₆ ≠ 0` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`. This is the form of `Aut(E) = {±1}` phrased via `c₄, c₆` (equivalent to
`j ∉ {0, 1728}` for an elliptic curve, see `eq_one_or_eq_negVariableChange_of_smul_eq`). -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hC : C • E = E) : C = 1 ∨ C = E.negVariableChange := by
  rcases E.u_eq_one_or_eq_neg_one hc4 hc6 hC with hu | hu
  · exact E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hu hC
  · -- Reduce `u = -1` to `u = 1` by composing with the involution `negVariableChange E`.
    have hDu : (E.negVariableChange * C).u = 1 := by
      have hmul : (E.negVariableChange * C).u = E.negVariableChange.u * C.u := rfl
      rw [hmul, negVariableChange_u, hu, neg_one_mul, neg_neg]
    have hDE : (E.negVariableChange * C) • E = E := by
      rw [mul_smul, hC, negVariableChange_smul_self]
    have hCeq : C = E.negVariableChange * (E.negVariableChange * C) := by
      rw [← mul_assoc, negVariableChange_mul_self, one_mul]
    rcases E.eq_one_or_eq_negVariableChange_of_u_eq_one hc4 hc6 hDu hDE with h | h
    · right; rw [hCeq, h, mul_one]
    · left; rw [hCeq, h, negVariableChange_mul_self]

/-- If `j(E) ∉ {0, 1728}` then the only admissible changes of variables fixing `E` are `1` and
`negVariableChange E`; that is, `Aut(E) = {±1}`. -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq [E.IsElliptic] (hj₀ : E.j ≠ 0)
    (hj₁₇₂₈ : E.j ≠ 1728) {C : VariableChange K} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange :=
  E.eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero (fun h => hj₀ (E.j_eq_zero h))
    (E.c₆_ne_zero_of_j_ne_1728 hj₁₇₂₈) hC

end WeierstrassCurve
