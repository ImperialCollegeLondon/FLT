/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic

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

/-! ### API

A general construction, independent of elliptic curves: a group with exactly two elements is
isomorphic to `Multiplicative (ZMod 2)`. -/

section API

/-- A group `G` with exactly two elements — the identity `1` and a distinguished element `g ≠ 1`,
every element being equal to one of the two — is isomorphic to `Multiplicative (ZMod 2)`, via the
isomorphism sending `g` to `Multiplicative.ofAdd 1`. The generator `g` and the exhaustion `key` are
taken as explicit data (rather than a bare `Nat.card G = 2`) so the isomorphism is computable. -/
def mulEquivMultiplicativeZModTwo {G : Type*} [Group G] [DecidableEq G] (g : G) (hg : g ≠ 1)
    (key : ∀ x : G, x = 1 ∨ x = g) : G ≃* Multiplicative (ZMod 2) :=
  have hgg : g * g = 1 := (key (g * g)).resolve_right fun h ↦ hg (mul_eq_right.mp h)
  have keyM : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hM1 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide
  have hMM : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
    decide
  { toFun x := if x = 1 then 1 else Multiplicative.ofAdd 1
    invFun x := if x = 1 then 1 else g
    left_inv x := by rcases key x with h | h <;> subst h <;> simp [hg, hM1]
    right_inv x := by rcases keyM x with h | h <;> subst h <;> simp [hg, hM1]
    map_mul' a b := by
      rcases key a with ha | ha <;> rcases key b with hb | hb <;> subst ha <;> subst hb <;>
        simp [hg, hgg, hMM] }

end API

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
  simp [variableChange_def, negVariableChange]
  ring_nf

lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

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

/-- In characteristic `2`, a curve with `Δ ≠ 0` has `a₁ ≠ 0` or `a₃ ≠ 0`: otherwise `a₁ = a₃ = 0`
makes the partial derivative `∂/∂y = 2y + a₁x + a₃` vanish identically, so `Δ = 0`. -/
lemma a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero (hΔ : E.Δ ≠ 0) (h2 : (2 : K) = 0) :
    E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hΔ (by rw [Δ, b₈, b₆, b₄, b₂, h.1, h.2]; grobner)

/-- The negation automorphism is nontrivial for a curve with `Δ ≠ 0`: in characteristic `≠ 2` it
has `u = -1 ≠ 1`, and in characteristic `2` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since a curve
with `Δ ≠ 0` in characteristic `2` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one (hΔ : E.Δ ≠ 0) : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · have ha1 : E.a₁ = 0 := by
      simpa [negVariableChange, VariableChange.one_def, neg_eq_zero]
        using congrArg VariableChange.s h
    have ha3 : E.a₃ = 0 := by
      simpa [negVariableChange, VariableChange.one_def, neg_eq_zero]
        using congrArg VariableChange.t h
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · refine h2 ?_
    have hv : (-1 : K) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange K ↦ (C.u : K)) h
    linear_combination -hv

/-- An automorphism `C` of `E` with `C.u = 1` has no `x`-translation: `C.r = 0`. Splitting on
whether `6 = 0`, this uses `c₄ ≠ 0` in characteristic `2` or `3` and `c₆ ≠ 0` otherwise. -/
lemma r_eq_zero_of_u_eq_one (hc6 : E.c₆ ≠ 0) {C : VariableChange K}
    (hu : C.u = 1) (hCE : C • E = E) : C.r = 0 := by
  have eb4 := congrArg WeierstrassCurve.b₄ hCE
  have eb6 := congrArg WeierstrassCurve.b₆ hCE
  have eb8 := congrArg WeierstrassCurve.b₈ hCE
  simp only [variableChange_b₄, variableChange_b₆, variableChange_b₈, hu, inv_one, Units.val_one,
    one_pow, one_mul] at eb4 eb6 eb8
  rw [c₆] at hc6
  grobner

/-- An automorphism `C` of `E` with `C.u = 1` is either the identity or `negVariableChange E`.
After `r_eq_zero_of_u_eq_one`, the `a₁` and `a₃` laws give `2s = 2t = 0`; in characteristic `≠ 2`
this forces `s = t = 0`, and in characteristic `2` the `a₄`, `a₆` laws pin `(s, t)` down to either
`(0, 0)` or `(-a₁, -a₃)`. -/
lemma eq_one_or_eq_negVariableChange_of_u_eq_one (hc4 : E.c₄ ≠ 0) (hc6 : E.c₆ ≠ 0)
    {C : VariableChange K} (hu : C.u = 1) (hCE : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  have hr : C.r = 0 := E.r_eq_zero_of_u_eq_one hc6 hu hCE
  obtain ⟨e1, e2, e3, e4, -⟩ := WeierstrassCurve.ext_iff.mp hCE
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, hu,
    inv_one, Units.val_one, one_pow, one_mul] at e1 e2 e3 e4
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · -- characteristic `2`: `a₁ ≠ 0` (else `c₄ = a₁⁴ = 0`); the `a₂`, `a₄` laws force `(s, t)` to be
    -- `(0, 0)` or `(-a₁, -a₃)`, the latter being `negVariableChange` since `-1 = 1`.
    have ha1 : E.a₁ ≠ 0 := by rw [c₄, b₂, b₄] at hc4; grobner
    have hq2 : C.s * (E.a₁ + C.s) = 0 := by linear_combination -e2 + 3 * hr
    have hq4 : C.s * E.a₃ + C.t * E.a₁ = 0 := by
      linear_combination -e4 + (2 * E.a₂ - C.s * E.a₁ + 3 * C.r) * hr - C.s * C.t * h2
    rcases (mul_eq_zero.mp hq2).imp id eq_neg_of_add_eq_zero_right with hs | hs
    · have ht : C.t = 0 :=
        (mul_eq_zero.mp
          (show C.t * E.a₁ = 0 by linear_combination hq4 - E.a₃ * hs)).resolve_right ha1
      exact Or.inl (by rw [VariableChange.one_def]; exact VariableChange.ext hu hr hs ht)
    · have ht : C.t = -E.a₃ := eq_neg_of_add_eq_zero_left
        ((mul_eq_zero.mp (show E.a₁ * (C.t + E.a₃) = 0 by
          linear_combination hq4 - E.a₃ * hs + E.a₁ * E.a₃ * h2)).resolve_left ha1)
      have hu1neg : (1 : Kˣ) = -1 :=
        Units.ext (by rw [Units.val_one, Units.val_neg, Units.val_one]; linear_combination h2)
      exact Or.inr (VariableChange.ext (hu.trans hu1neg) hr hs ht)
  · -- characteristic `≠ 2`: `2s = 2t = 0`, so `s = t = 0` and `C = 1`.
    have hs : C.s = 0 :=
      (mul_eq_zero.mp (show 2 * C.s = 0 by linear_combination e1)).resolve_left h2
    have ht : C.t = 0 :=
      (mul_eq_zero.mp (show 2 * C.t = 0 by linear_combination e3 - E.a₁ * hr)).resolve_left h2
    exact Or.inl (by rw [VariableChange.one_def]; exact VariableChange.ext hu hr hs ht)

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
    linear_combination hu6 - (C.u : K) ^ 2 * hu4
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
      rw [show (E.negVariableChange * C).u = E.negVariableChange.u * C.u from rfl,
        negVariableChange_u, hu, neg_one_mul, neg_neg]
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
  E.eq_one_or_eq_negVariableChange_of_smul_eq_of_c₄_ne_zero (fun h ↦ hj₀ (E.j_eq_zero h))
    (E.c₆_ne_zero_of_j_ne_1728 hj₁₇₂₈) hC

/-! ### The automorphism group -/

open MulAction in
/-- The automorphism group of a Weierstrass curve `E` over a field: the admissible changes of
variables fixing `E`, i.e. the stabiliser of `E` under the action of `VariableChange K`. -/
def autGroup : Subgroup (VariableChange K) := stabilizer (VariableChange K) E

lemma mem_autGroup {C : VariableChange K} : C ∈ E.autGroup ↔ C • E = E := Iff.rfl

/-- Two admissible changes of variables agree iff their four coefficients do; this makes equality
of changes of variables decidable over a field with decidable equality. -/
instance {R : Type*} [CommRing R] [DecidableEq R] : DecidableEq (VariableChange R) :=
  fun _ _ ↦ decidable_of_iff _ VariableChange.ext_iff.symm

open MulAction in
/-- **`Aut(E) ≅ ℤ/2` for `j(E) ∉ {0, 1728}`.** The automorphism group of `E` is `{±1}`, so it is
isomorphic to `Multiplicative (ZMod 2)`: it has exactly two elements — `1` and `negVariableChange E`
(`eq_one_or_eq_negVariableChange_of_smul_eq`), distinct by `negVariableChange_ne_one`. The
isomorphism sends `negVariableChange E` to `Multiplicative.ofAdd 1`. -/
def autGroupMulEquiv [DecidableEq K] [E.IsElliptic] (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) :
    E.autGroup ≃* Multiplicative (ZMod 2) :=
  mulEquivMultiplicativeZModTwo ⟨E.negVariableChange, E.negVariableChange_smul_self⟩
    (fun h ↦ E.negVariableChange_ne_one E.isUnit_Δ.ne_zero (congrArg Subtype.val h))
    fun C ↦ (E.eq_one_or_eq_negVariableChange_of_smul_eq hj₀ hj₁₇₂₈
      (E.mem_autGroup.mp C.2)).imp Subtype.ext Subtype.ext

end WeierstrassCurve
