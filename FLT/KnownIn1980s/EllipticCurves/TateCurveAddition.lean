/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction
public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib

import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Analysis.Real.Cardinality
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!

# The formal chord law for the Tate curve coordinates

`TateCurve.weierstrass_equation` (in `TateCurveConstruction`) proves that the formal
coordinates `X(u, q), Y(u, q) ∈ ℚ(u)⟦q⟧` of the Tate uniformisation satisfy the
Weierstrass equation of the Tate curve. This file proves the *addition law* at the same
formal level: writing `X₁ = X(u₁), X₂ = X(u₂), X₃ = X(u₁u₂)` (and similarly `Y`) for the
images of the universal series `X, Y` under the coefficient embeddings
`ℚ(u) → ℚ(u₁, u₂)` sending `u` to `u₁`, `u₂`, `u₁u₂` respectively, we prove the two
polynomial identities of Silverman's proof of ATAEC V.3.1(c):

* `TateCurve.chord_x` :
  `(X₁ - X₂)²·X₃ = (Y₁ - Y₂)² + (Y₁ - Y₂)(X₁ - X₂) - (X₁ + X₂)(X₁ - X₂)²`
* `TateCurve.chord_y` :
  `(X₁ - X₂)·Y₃ = -((Y₂ - Y₁) + (X₂ - X₁))·X₃ - (Y₁X₂ - Y₂X₁)`

in `ℚ(u₁, u₂)⟦q⟧`, where `ℚ(u₁, u₂)` is implemented as the iterated rational function
field `RatFunc (RatFunc ℚ)` with `u₁` the inner and `u₂` the outer variable. For a pair
of nonsingular points with `X₁ ≠ X₂` these are exactly the coordinates of the sum in
mathlib's affine group law (`WeierstrassCurve.Affine.addX`/`addY` with `a₁ = 1`,
`a₂ = a₃ = 0`), which is how they are consumed (after descent to a general coefficient
field in `TateCurveAdditionDescent` and evaluation over a nonarchimedean local field in
`TateCurveUniformisation`).

## Strategy

The same complex-analytic strategy as `TateCurveConstruction`, with the addition theorem
for the Weierstrass `℘`-function (`PeriodPair.weierstrassP_add_sq` and its derivative
`PeriodPair.derivWeierstrassP_add_sq`, proven in
`FLT.KnownIn1980s.EllipticCurves.MaybeMathlib`) replacing the differential
equation:

1. *The analytic chord law* (`analytic_chord_x`, `analytic_chord_y`): for complex
   `q, u₁, u₂` with `0 < ‖q‖ < ‖uᵢ‖ < 1` and `‖q‖ < ‖u₁u₂‖`, the values
   `XAn uᵢ q, YAn uᵢ q, XAn (u₁u₂) q, YAn (u₁u₂) q` satisfy the two identities: choose
   `τ, z₁, z₂` with `e τ = q`, `e zᵢ = uᵢ` (so `e (z₁ + z₂) = u₁u₂` by `e_add`),
   substitute the `q`-expansions of `℘, ℘'` at `z₁, z₂, z₁ + z₂` into the addition
   theorem, and simplify (the analytic-algebra lemmas `analytic_chord_x_algebra`,
   `analytic_chord_y_algebra`).
2. *Rearrangement*: `hasSum_X_eval`/`hasSum_Y_eval` apply verbatim at each of the three
   points `u₁, u₂, u₁u₂` (each is a single transcendental complex number in the
   annulus), presenting the values as the evaluations of the formal series at
   algebraically independent pairs `(u₁, u₂)`.
3. *Descent*: a two-variable extension of `eq_zero_of_forall_hasSum_zero`: an element of
   `ℚ(u₁, u₂)` vanishing at an infinite set of `u₁`'s, and for each at an infinite set
   of `u₂`'s, is zero (iterating the univariate finitely-many-roots argument through
   `RatFunc.num`/`denom`); the supply of algebraically independent pairs in the required
   polydisc region has full cardinality since each algebraic dependence locus is
   countable.
-/

@[expose] public section

open scoped PowerSeries

open Complex TateCurve.Blueprint

open scoped Topology PeriodPair

noncomputable section

namespace TateCurve

/-! ### The two-variable coefficient field `ℚ(u₁, u₂)` and the three embeddings -/

/-- The two-variable rational function field `ℚ(u₁, u₂)`, implemented as
`RatFunc (RatFunc ℚ)`: `u₁` is the inner variable (`TateCurve.u₁`), `u₂` the outer
(`TateCurve.u₂`). -/
abbrev RatFunc₂ : Type := RatFunc (RatFunc ℚ)

/-- The inner variable `u₁ ∈ ℚ(u₁, u₂)`. -/
def u₁ : RatFunc₂ := algebraMap (RatFunc ℚ) RatFunc₂ RatFunc.X

/-- The outer variable `u₂ ∈ ℚ(u₁, u₂)`. -/
def u₂ : RatFunc₂ := RatFunc.X

theorem transcendental_u₂ : Transcendental (RatFunc ℚ) u₂ := RatFunc.transcendental_X

theorem u₁_ne_zero : u₁ ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap (RatFunc ℚ) RatFunc₂).injective).mpr RatFunc.X_ne_zero

theorem u₂_ne_zero : u₂ ≠ 0 := RatFunc.X_ne_zero

/-- `u₁u₂` is transcendental over `ℚ(u₁)` (embedded as constants): otherwise
`u₂ = u₁⁻¹·(u₁u₂)` would be algebraic over it. -/
theorem transcendental_u₁_mul_u₂ : Transcendental (RatFunc ℚ) (u₁ * u₂) := by
  intro halg
  apply transcendental_u₂
  have hu1inv : IsAlgebraic (RatFunc ℚ) u₁⁻¹ := by
    rw [show (u₁⁻¹ : RatFunc₂) = algebraMap (RatFunc ℚ) RatFunc₂ RatFunc.X⁻¹ from by
      rw [u₁, ← map_inv₀]]
    exact isAlgebraic_algebraMap _
  have : IsAlgebraic (RatFunc ℚ) (u₁⁻¹ * (u₁ * u₂)) := hu1inv.mul halg
  rwa [← mul_assoc, inv_mul_cancel₀ u₁_ne_zero, one_mul] at this

/-- `u₂` is transcendental over `ℚ` (from transcendence over the larger field `ℚ(u₁)`). -/
theorem transcendental_u₂_ℚ : Transcendental ℚ u₂ :=
  fun halg => transcendental_u₂ (halg.tower_top (RatFunc ℚ))

/-- `u₁u₂` is transcendental over `ℚ`. -/
theorem transcendental_u₁u₂_ℚ : Transcendental ℚ (u₁ * u₂) :=
  fun halg => transcendental_u₁_mul_u₂ (halg.tower_top (RatFunc ℚ))

/-- The coefficient embedding `ℚ(u) → ℚ(u₁, u₂)`, `u ↦ u₁`: the algebra map to the
constants. -/
def emb₁ : RatFunc ℚ →+* RatFunc₂ :=
  algebraMap (RatFunc ℚ) RatFunc₂

/-- The coefficient embedding `ℚ(u) → ℚ(u₁, u₂)`, `u ↦ u₂`. -/
def emb₂ : RatFunc ℚ →+* RatFunc₂ where
  toFun r := (RatFunc.algEquivOfTranscendental u₂ transcendental_u₂_ℚ r : RatFunc₂)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_zero' := by simp
  map_add' := by intro x y; simp

/-- The coefficient embedding `ℚ(u) → ℚ(u₁, u₂)`, `u ↦ u₁u₂` (legal since `u₁u₂` is
transcendental over `ℚ`). -/
def emb₃ : RatFunc ℚ →+* RatFunc₂ where
  toFun r := (RatFunc.algEquivOfTranscendental (u₁ * u₂) transcendental_u₁u₂_ℚ r : RatFunc₂)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_zero' := by simp
  map_add' := by intro x y; simp

@[simp] theorem emb₁_ratFuncX : emb₁ RatFunc.X = u₁ := rfl

@[simp] theorem emb₂_ratFuncX : emb₂ RatFunc.X = u₂ := by
  change (RatFunc.algEquivOfTranscendental u₂ transcendental_u₂_ℚ RatFunc.X : RatFunc₂) = u₂
  rw [RatFunc.algEquivOfTranscendental_apply]
  simp

@[simp] theorem emb₃_ratFuncX : emb₃ RatFunc.X = u₁ * u₂ := by
  change (RatFunc.algEquivOfTranscendental (u₁ * u₂) transcendental_u₁u₂_ℚ RatFunc.X : RatFunc₂)
    = u₁ * u₂
  rw [RatFunc.algEquivOfTranscendental_apply]
  simp

/-! ### The six coordinate series and the chord law -/

/-- `X₁ = X(u₁, q) ∈ ℚ(u₁, u₂)⟦q⟧`. -/
def X₁ : RatFunc₂⟦X⟧ := (TateCurve.X).map emb₁

/-- `X₂ = X(u₂, q)`. -/
def X₂ : RatFunc₂⟦X⟧ := (TateCurve.X).map emb₂

/-- `X₃ = X(u₁u₂, q)`. -/
def X₃ : RatFunc₂⟦X⟧ := (TateCurve.X).map emb₃

/-- `Y₁ = Y(u₁, q)`. -/
def Y₁ : RatFunc₂⟦X⟧ := (TateCurve.Y).map emb₁

/-- `Y₂ = Y(u₂, q)`. -/
def Y₂ : RatFunc₂⟦X⟧ := (TateCurve.Y).map emb₂

/-- `Y₃ = Y(u₁u₂, q)`. -/
def Y₃ : RatFunc₂⟦X⟧ := (TateCurve.Y).map emb₃

/-! ### The analytic chord identities

For complex `u₁, u₂, q` with `0 < ‖q‖ < ‖uᵢ‖ < 1` and `‖q‖ < ‖u₁u₂‖`, the analytic
functions `XAn`, `YAn` satisfy the two chord identities, obtained by substituting the
`q`-expansions of `℘, ℘'` at `z₁, z₂, z₁ + z₂` into the addition theorem (and, for the
`y`-identity, its derivative together with the differential equation at `z₁, z₂`). -/

private theorem analytic_chord_x_algebra (x1 x2 x3 y1 y2 c P1 P2 P3 D1 D2 : ℂ) (hc : c ≠ 0)
    (hP1 : P1 = c ^ 2 * (1 / 12 + x1)) (hP2 : P2 = c ^ 2 * (1 / 12 + x2))
    (hP3 : P3 = c ^ 2 * (1 / 12 + x3)) (hD1 : D1 = c ^ 3 * (x1 + 2 * y1))
    (hD2 : D2 = c ^ 3 * (x2 + 2 * y2))
    (hAdd : (P3 + P1 + P2) * (P1 - P2) ^ 2 = (D1 - D2) ^ 2 / 4) :
    (x1 - x2) ^ 2 * x3 = (y1 - y2) ^ 2 + (y1 - y2) * (x1 - x2) - (x1 + x2) * (x1 - x2) ^ 2 := by
  subst hP1 hP2 hP3 hD1 hD2
  apply mul_left_cancel₀ (pow_ne_zero 6 hc)
  linear_combination hAdd

private theorem analytic_chord_y_algebra (x1 x2 x3 y1 y2 y3 g2 g3 c P1 P2 P3 D1 D2 D3 : ℂ)
    (hc : c ≠ 0) (hne : x1 ≠ x2)
    (hP1 : P1 = c ^ 2 * (1 / 12 + x1)) (hP2 : P2 = c ^ 2 * (1 / 12 + x2))
    (hP3 : P3 = c ^ 2 * (1 / 12 + x3)) (hD1 : D1 = c ^ 3 * (x1 + 2 * y1))
    (hD2 : D2 = c ^ 3 * (x2 + 2 * y2)) (hD3 : D3 = c ^ 3 * (x3 + 2 * y3))
    (hAdd : (P3 + P1 + P2) * (P1 - P2) ^ 2 = (D1 - D2) ^ 2 / 4)
    (hDeriv : D3 * (P1 - P2) ^ 2 = (D1 - D2) * (6 * P1 ^ 2 - g2 / 2) / 2 - D1 * (P1 - P2) ^ 2
                - 2 * (P3 + P1 + P2) * (P1 - P2) * D1)
    (hDE1 : D1 ^ 2 = 4 * P1 ^ 3 - g2 * P1 - g3) (hDE2 : D2 ^ 2 = 4 * P2 ^ 3 - g2 * P2 - g3) :
    (x2 - x1) * y3 = -((y2 - y1) + (x2 - x1)) * x3 - (y1 * x2 - y2 * x1) := by
  subst hP1 hP2 hP3 hD1 hD2 hD3
  have ha : x1 - x2 ≠ 0 := sub_ne_zero.mpr hne
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hc6 : c ^ 6 ≠ 0 := pow_ne_zero 6 hc
  have hc7 : c ^ 7 ≠ 0 := pow_ne_zero 7 hc
  have ha2 : (x1 - x2) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hA : (1 / 4 + x1 + x2 + x3) * (x1 - x2) ^ 2 = ((x1 - x2) + 2 * (y1 - y2)) ^ 2 / 4 := by
    apply mul_left_cancel₀ hc6
    linear_combination hAdd
  have hx3 : x3 = (((x1 - x2) + 2 * (y1 - y2)) ^ 2 / 4 - (1 / 4 + x1 + x2) * (x1 - x2) ^ 2)
      / (x1 - x2) ^ 2 := by
    rw [eq_div_iff ha2]; linear_combination hA
  have hg2 : g2 = (4 * c ^ 6 * ((1 / 12 + x1) ^ 3 - (1 / 12 + x2) ^ 3)
      - c ^ 6 * ((x1 + 2 * y1) ^ 2 - (x2 + 2 * y2) ^ 2)) / (c ^ 2 * (x1 - x2)) := by
    rw [eq_div_iff (mul_ne_zero hc2 ha)]; linear_combination hDE1 - hDE2
  have hy3 : y3 = ((c ^ 3 * (x1 + 2 * y1) - c ^ 3 * (x2 + 2 * y2))
        * (6 * (c ^ 2 * (1 / 12 + x1)) ^ 2 - g2 / 2) / 2
        - c ^ 3 * (x1 + 2 * y1) * (c ^ 2 * (1 / 12 + x1) - c ^ 2 * (1 / 12 + x2)) ^ 2
        - 2 * (c ^ 2 * (1 / 12 + x3) + c ^ 2 * (1 / 12 + x1) + c ^ 2 * (1 / 12 + x2))
          * (c ^ 2 * (1 / 12 + x1) - c ^ 2 * (1 / 12 + x2)) * c ^ 3 * (x1 + 2 * y1)
        - c ^ 7 * x3 * (x1 - x2) ^ 2) / (2 * c ^ 7 * (x1 - x2) ^ 2) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hc7) ha2)]
    linear_combination hDeriv
  rw [hy3, hx3, hg2]
  field_simp
  ring

/-- Shared setup for the analytic chord identities: choose `τ, z₁, z₂` with `e τ = q`,
`e zᵢ = uᵢ`, `0 < im zᵢ < im τ` and `0 < im (z₁ + z₂) < im τ`, and read off the
`q`-expansions of `℘, ℘'` at `z₁, z₂, z₁ + z₂` together with the addition theorem, its
derivative, and the differential equation at `z₁, z₂`. -/
private theorem chord_analytic_data {u₁ u₂ q : ℂ} (h0 : 0 < ‖q‖)
    (h11 : ‖q‖ < ‖u₁‖) (h12 : ‖u₁‖ < 1) (h21 : ‖q‖ < ‖u₂‖) (h22 : ‖u₂‖ < 1)
    (h3 : ‖q‖ < ‖u₁ * u₂‖) :
    ∃ (P1 P2 P3 D1 D2 D3 g2 g3 : ℂ),
      P1 = (2 * (Real.pi : ℂ) * I) ^ 2 * (1 / 12 + XAn u₁ q) ∧
      P2 = (2 * (Real.pi : ℂ) * I) ^ 2 * (1 / 12 + XAn u₂ q) ∧
      P3 = (2 * (Real.pi : ℂ) * I) ^ 2 * (1 / 12 + XAn (u₁ * u₂) q) ∧
      D1 = (2 * (Real.pi : ℂ) * I) ^ 3 * (XAn u₁ q + 2 * YAn u₁ q) ∧
      D2 = (2 * (Real.pi : ℂ) * I) ^ 3 * (XAn u₂ q + 2 * YAn u₂ q) ∧
      D3 = (2 * (Real.pi : ℂ) * I) ^ 3 * (XAn (u₁ * u₂) q + 2 * YAn (u₁ * u₂) q) ∧
      (P3 + P1 + P2) * (P1 - P2) ^ 2 = (D1 - D2) ^ 2 / 4 ∧
      (D3 * (P1 - P2) ^ 2 = (D1 - D2) * (6 * P1 ^ 2 - g2 / 2) / 2 - D1 * (P1 - P2) ^ 2
        - 2 * (P3 + P1 + P2) * (P1 - P2) * D1) ∧
      D1 ^ 2 = 4 * P1 ^ 3 - g2 * P1 - g3 ∧ D2 ^ 2 = 4 * P2 ^ 3 - g2 * P2 - g3 := by
  have hq0 : q ≠ 0 := norm_pos_iff.mp h0
  have hu10 : u₁ ≠ 0 := norm_pos_iff.mp (h0.trans h11)
  have hu20 : u₂ ≠ 0 := norm_pos_iff.mp (h0.trans h21)
  have hq1 : ‖q‖ < 1 := h11.trans h12
  have him : ∀ {v : ℂ}, 0 < ‖v‖ → ‖v‖ < 1 →
      0 < (Complex.log v / (2 * (Real.pi : ℂ) * I)).im := fun hv0 hv1 ↦ by
    rw [log_div_two_pi_I_im]
    exact div_pos (neg_pos.2 ((Real.log_neg_iff hv0).2 hv1)) (by positivity)
  have hlt : ∀ {v w : ℂ}, 0 < ‖w‖ → ‖w‖ < ‖v‖ →
      (Complex.log v / (2 * (Real.pi : ℂ) * I)).im
        < (Complex.log w / (2 * (Real.pi : ℂ) * I)).im := fun hw0 hwv ↦ by
    rw [log_div_two_pi_I_im, log_div_two_pi_I_im]
    exact div_lt_div_of_pos_right (neg_lt_neg (Real.log_lt_log hw0 hwv)) (by positivity)
  set τ := Complex.log q / (2 * (Real.pi : ℂ) * I) with hτdef
  set z₁ := Complex.log u₁ / (2 * (Real.pi : ℂ) * I) with hz1def
  set z₂ := Complex.log u₂ / (2 * (Real.pi : ℂ) * I) with hz2def
  have hτim : 0 < τ.im := him h0 hq1
  have hz1im : 0 < z₁.im := him (h0.trans h11) h12
  have hz2im : 0 < z₂.im := him (h0.trans h21) h22
  have hz1τ : z₁.im < τ.im := hlt h0 h11
  have hz2τ : z₂.im < τ.im := hlt h0 h21
  have hz12im : 0 < (z₁ + z₂).im := by rw [Complex.add_im]; linarith
  have hz12τ : (z₁ + z₂).im < τ.im := by
    have key : Real.log ‖q‖ < Real.log ‖u₁‖ + Real.log ‖u₂‖ := by
      rw [← Real.log_mul (norm_ne_zero_iff.mpr hu10) (norm_ne_zero_iff.mpr hu20), ← norm_mul]
      exact Real.log_lt_log h0 h3
    rw [Complex.add_im, hz1def, hz2def, hτdef, log_div_two_pi_I_im, log_div_two_pi_I_im,
        log_div_two_pi_I_im, ← add_div]
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  have heτ : e τ = q := e_log_div_two_pi_I hq0
  have hez1 : e z₁ = u₁ := e_log_div_two_pi_I hu10
  have hez2 : e z₂ = u₂ := e_log_div_two_pi_I hu20
  have he12 : e (z₁ + z₂) = u₁ * u₂ := by rw [e_add, hez1, hez2]
  have h₁ := notMem_lattice_of_im_between hτim hz1im hz1τ
  have h₂ := notMem_lattice_of_im_between hτim hz2im hz2τ
  have h₁₂ := notMem_lattice_of_im_between hτim hz12im hz12τ
  refine ⟨℘[periodPair τ hτim.ne'] z₁, ℘[periodPair τ hτim.ne'] z₂,
    ℘[periodPair τ hτim.ne'] (z₁ + z₂), ℘'[periodPair τ hτim.ne'] z₁,
    ℘'[periodPair τ hτim.ne'] z₂, ℘'[periodPair τ hτim.ne'] (z₁ + z₂),
    (periodPair τ hτim.ne').g₂, (periodPair τ hτim.ne').g₃,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := weierstrassP_q_expansion τ hτim z₁ hz1im hz1τ; rwa [hez1, heτ] at this
  · have := weierstrassP_q_expansion τ hτim z₂ hz2im hz2τ; rwa [hez2, heτ] at this
  · have := weierstrassP_q_expansion τ hτim (z₁ + z₂) hz12im hz12τ; rwa [he12, heτ] at this
  · have := derivWeierstrassP_q_expansion τ hτim z₁ hz1im hz1τ; rwa [hez1, heτ] at this
  · have := derivWeierstrassP_q_expansion τ hτim z₂ hz2im hz2τ; rwa [hez2, heτ] at this
  · have := derivWeierstrassP_q_expansion τ hτim (z₁ + z₂) hz12im hz12τ; rwa [he12, heτ] at this
  · exact (periodPair τ hτim.ne').weierstrassP_add_sq z₁ h₁ h₂ h₁₂
  · exact (periodPair τ hτim.ne').derivWeierstrassP_add_sq z₁ h₁ h₂ h₁₂
  · exact (periodPair τ hτim.ne').derivWeierstrassP_sq z₁ h₁
  · exact (periodPair τ hτim.ne').derivWeierstrassP_sq z₂ h₂

/-- **The analytic chord law, `x`-coordinate.** -/
private theorem analytic_chord_x {u₁ u₂ q : ℂ} (h0 : 0 < ‖q‖)
    (h11 : ‖q‖ < ‖u₁‖) (h12 : ‖u₁‖ < 1) (h21 : ‖q‖ < ‖u₂‖) (h22 : ‖u₂‖ < 1)
    (h3 : ‖q‖ < ‖u₁ * u₂‖) :
    (XAn u₁ q - XAn u₂ q) ^ 2 * XAn (u₁ * u₂) q =
      (YAn u₁ q - YAn u₂ q) ^ 2 + (YAn u₁ q - YAn u₂ q) * (XAn u₁ q - XAn u₂ q)
        - (XAn u₁ q + XAn u₂ q) * (XAn u₁ q - XAn u₂ q) ^ 2 := by
  obtain ⟨P1, P2, P3, D1, D2, D3, g2, g3, hP1, hP2, hP3, hD1, hD2, _, hAdd, _, _, _⟩ :=
    chord_analytic_data h0 h11 h12 h21 h22 h3
  exact analytic_chord_x_algebra (XAn u₁ q) (XAn u₂ q) (XAn (u₁ * u₂) q) (YAn u₁ q) (YAn u₂ q)
    (2 * (Real.pi : ℂ) * I) P1 P2 P3 D1 D2 Blueprint.two_pi_I_ne_zero hP1 hP2 hP3 hD1 hD2 hAdd

/-- **The analytic chord law, `y`-coordinate** (requires `XAn u₁ q ≠ XAn u₂ q`). -/
private theorem analytic_chord_y {u₁ u₂ q : ℂ} (h0 : 0 < ‖q‖)
    (h11 : ‖q‖ < ‖u₁‖) (h12 : ‖u₁‖ < 1) (h21 : ‖q‖ < ‖u₂‖) (h22 : ‖u₂‖ < 1)
    (h3 : ‖q‖ < ‖u₁ * u₂‖) (hne : XAn u₁ q ≠ XAn u₂ q) :
    (XAn u₂ q - XAn u₁ q) * YAn (u₁ * u₂) q =
      -((YAn u₂ q - YAn u₁ q) + (XAn u₂ q - XAn u₁ q)) * XAn (u₁ * u₂) q
        - (YAn u₁ q * XAn u₂ q - YAn u₂ q * XAn u₁ q) := by
  obtain ⟨P1, P2, P3, D1, D2, D3, g2, g3, hP1, hP2, hP3, hD1, hD2, hD3, hAdd, hDeriv, hDE1, hDE2⟩ :=
    chord_analytic_data h0 h11 h12 h21 h22 h3
  exact analytic_chord_y_algebra (XAn u₁ q) (XAn u₂ q) (XAn (u₁ * u₂) q) (YAn u₁ q) (YAn u₂ q)
    (YAn (u₁ * u₂) q) g2 g3 (2 * (Real.pi : ℂ) * I) P1 P2 P3 D1 D2 D3 Blueprint.two_pi_I_ne_zero hne
    hP1 hP2 hP3 hD1 hD2 hD3 hAdd hDeriv hDE1 hDE2

/-! ### The evaluation ring homomorphism `ε : ℚ(u₁, u₂) → ℂ`

For an algebraically independent pair `(w₁, w₂)` of complex numbers, we build a ring
homomorphism `ε` sending `u₁ ↦ w₁`, `u₂ ↦ w₂`, and show that precomposing with the
three embeddings `emb₁, emb₂, emb₃` recovers the single-variable evaluations at `w₁`,
`w₂`, `w₁w₂`. -/

/-- If `z` is algebraic over `ℚ`, it is algebraic over `ℚ(u)` (viewed in `ℂ` via
`evalAtHom w₁`). -/
private theorem isAlgebraic_ratFunc_of_rat (w₁ : ℂ) (hw₁ : Transcendental ℚ w₁) {z : ℂ}
    (hz : IsAlgebraic ℚ z) :
    letI := (evalAtHom w₁ hw₁).toAlgebra; IsAlgebraic (RatFunc ℚ) z := by
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  obtain ⟨p, hp0, hp⟩ := hz
  refine ⟨p.map (algebraMap ℚ (RatFunc ℚ)),
    (Polynomial.map_ne_zero_iff (algebraMap ℚ (RatFunc ℚ)).injective).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    show (algebraMap (RatFunc ℚ) ℂ).comp (algebraMap ℚ (RatFunc ℚ)) = algebraMap ℚ ℂ from
      RingHom.ext_rat _ _, ← Polynomial.aeval_def]
  exact hp

/-- Ring-hom extensionality for `ℚ(u)`: two ring homs to `ℂ` agreeing on `RatFunc.X`
coincide (they automatically agree on `ℚ`). -/
private theorem ratFunc_ringHom_ext {f g : RatFunc ℚ →+* ℂ} (hX : f RatFunc.X = g RatFunc.X) :
    f = g := by
  refine IsFractionRing.ringHom_ext (A := Polynomial ℚ) fun p => ?_
  suffices h : f.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ))
      = g.comp (algebraMap (Polynomial ℚ) (RatFunc ℚ)) from congrFun (congrArg DFunLike.coe h) p
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have hval := congrFun (congrArg DFunLike.coe
      (RingHom.ext_rat (f.comp (algebraMap ℚ (RatFunc ℚ))) (g.comp (algebraMap ℚ (RatFunc ℚ))))) a
    simp only [RingHom.comp_apply] at hval ⊢
    rwa [show (algebraMap (Polynomial ℚ) (RatFunc ℚ)) (Polynomial.C a)
        = algebraMap ℚ (RatFunc ℚ) a from by
      rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ), Polynomial.algebraMap_eq]]
  · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
    exact hX

/-- The evaluation ring homomorphism `ε : ℚ(u₁, u₂) → ℂ` for an algebraically
independent pair `(w₁, w₂)`. -/
private noncomputable def evalε (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) :
    RatFunc₂ →+* ℂ :=
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  (RatFunc.liftAlgHom (Polynomial.aeval w₂) (by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    exact hw₂ ⟨p, nonZeroDivisors.ne_zero hp, h0⟩)).toRingHom

private theorem evalε_algebraMap (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) (r : RatFunc ℚ) :
    evalε w₁ w₂ hw₁ hw₂ (algebraMap (RatFunc ℚ) RatFunc₂ r) = evalAtHom w₁ hw₁ r := by
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  change (RatFunc.liftAlgHom (Polynomial.aeval w₂) _ : RatFunc₂ →ₐ[RatFunc ℚ] ℂ)
      (algebraMap (RatFunc ℚ) RatFunc₂ r) = evalAtHom w₁ hw₁ r
  rw [AlgHom.commutes, RingHom.algebraMap_toAlgebra]

private theorem evalε_ratFuncX (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) :
    evalε w₁ w₂ hw₁ hw₂ RatFunc.X = w₂ := by
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  change (RatFunc.liftAlgHom (Polynomial.aeval w₂) _ : RatFunc₂ →ₐ[RatFunc ℚ] ℂ) RatFunc.X = w₂
  rw [RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X]
  simp

/-- `w₂` is transcendental over `ℚ` (from independence). -/
private theorem transcendental_snd (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) :
    Transcendental ℚ w₂ :=
  fun halg => hw₂ (isAlgebraic_ratFunc_of_rat w₁ hw₁ halg)

/-- `w₁w₂` is transcendental over `ℚ` (from independence). -/
private theorem transcendental_prod (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂)
    (hw10 : w₁ ≠ 0) : Transcendental ℚ (w₁ * w₂) := by
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  intro halg
  apply hw₂
  have h1 := isAlgebraic_ratFunc_of_rat w₁ hw₁ halg
  have h2 : IsAlgebraic (RatFunc ℚ) w₁⁻¹ := by
    have hh : (w₁⁻¹ : ℂ) = algebraMap (RatFunc ℚ) ℂ (RatFunc.X⁻¹) := by
      rw [RingHom.algebraMap_toAlgebra, map_inv₀, evalAtHom_ratFuncX]
    rw [hh]; exact isAlgebraic_algebraMap _
  have h3 := h2.mul h1
  rwa [← mul_assoc, inv_mul_cancel₀ hw10, one_mul] at h3

private theorem evalε_comp_emb₁ (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) :
    (evalε w₁ w₂ hw₁ hw₂).comp emb₁ = evalAtHom w₁ hw₁ := by
  ext r
  exact evalε_algebraMap w₁ w₂ hw₁ hw₂ r

private theorem evalε_comp_emb₂ (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) :
    (evalε w₁ w₂ hw₁ hw₂).comp emb₂ = evalAtHom w₂ (transcendental_snd w₁ w₂ hw₁ hw₂) := by
  refine ratFunc_ringHom_ext ?_
  rw [RingHom.comp_apply, emb₂_ratFuncX, evalAtHom_ratFuncX]
  exact evalε_ratFuncX w₁ w₂ hw₁ hw₂

private theorem evalε_comp_emb₃ (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) (hw10 : w₁ ≠ 0) :
    (evalε w₁ w₂ hw₁ hw₂).comp emb₃
      = evalAtHom (w₁ * w₂) (transcendental_prod w₁ w₂ hw₁ hw₂ hw10) := by
  refine ratFunc_ringHom_ext ?_
  rw [RingHom.comp_apply, emb₃_ratFuncX, evalAtHom_ratFuncX, map_mul,
    show (u₁ : RatFunc₂) = algebraMap (RatFunc ℚ) RatFunc₂ RatFunc.X from rfl,
    evalε_algebraMap, evalAtHom_ratFuncX, show (u₂ : RatFunc₂) = RatFunc.X from rfl,
    evalε_ratFuncX]


/-- Bridge: `ε` applied to the coefficients of `φ.map emb` sums to the single-variable
value, provided `ε ∘ emb = evalAtHom v`. -/
private theorem hasSum_evalε_coeff_map {w₁ w₂ q : ℂ} (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂)
    {emb : RatFunc ℚ →+* RatFunc₂} {v : ℂ} {hv : Transcendental ℚ v}
    (hcomp : (evalε w₁ w₂ hw₁ hw₂).comp emb = evalAtHom v hv)
    {φ : (RatFunc ℚ)⟦X⟧} {A : ℂ}
    (hφ : HasSum (fun n ↦ evalAt v (PowerSeries.coeff n φ) * q ^ n) A) :
    HasSum (fun n ↦ evalε w₁ w₂ hw₁ hw₂ (PowerSeries.coeff n (φ.map emb)) * q ^ n) A := by
  refine hφ.congr_fun fun n ↦ ?_
  rw [PowerSeries.coeff_map, ← RingHom.comp_apply, hcomp, evalAtHom_apply]

/-! ### Descent to the formal power series ring, two-variable version -/

/-- The transcendental points of the punctured unit disc, over an arbitrary countable
coefficient field, form an infinite set (replay/generalisation of
`TateCurveConstruction.transcendental_punctured_unit_disk_infinite`). -/
private theorem transcendental_punctured_unit_disk_infinite' {K : Type} [Field K] [Countable K]
    [Algebra K ℂ] : ({u : ℂ | Transcendental K u ∧ 0 < ‖u‖ ∧ ‖u‖ < 1} : Set ℂ).Infinite := by
  intro hfin
  have hsub : ((↑) : ℝ → ℂ) '' Set.Ioo 0 1 ⊆
      {u : ℂ | Transcendental K u ∧ 0 < ‖u‖ ∧ ‖u‖ < 1} ∪ {u : ℂ | IsAlgebraic K u} := by
    rintro z ⟨x, ⟨hx0, hx1⟩, rfl⟩
    by_cases htr : Transcendental K (x : ℂ)
    · have hnorm : ‖(x : ℂ)‖ = x := (RCLike.norm_ofReal (K := ℂ) x).trans (abs_of_pos hx0)
      exact .inl ⟨htr, by rw [hnorm]; exact hx0, by rw [hnorm]; exact hx1⟩
    · exact .inr (not_not.mp htr)
  have hIoo : (Set.Ioo (0 : ℝ) 1).Countable :=
    Set.countable_of_injective_of_countable_image
      (fun x _ y _ h ↦ Complex.ofReal_injective h)
      ((hfin.countable.union (Algebraic.countable K ℂ)).mono hsub)
  exact not_le_of_gt Cardinal.aleph0_lt_continuum
    (Cardinal.mk_Ioo_real one_pos ▸ Cardinal.le_aleph0_iff_set_countable.mpr hIoo)

/-- The evaluation `ε(r)` as a quotient of one-variable specialisations. -/
private theorem evalε_eq (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
    (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂) (r : RatFunc₂) :
    evalε w₁ w₂ hw₁ hw₂ r =
      ((RatFunc.num r).map (evalAtHom w₁ hw₁)).eval w₂
        / ((RatFunc.denom r).map (evalAtHom w₁ hw₁)).eval w₂ := by
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  change (RatFunc.liftAlgHom (Polynomial.aeval w₂) _ : RatFunc₂ →ₐ[RatFunc ℚ] ℂ) r = _
  rw [RatFunc.liftAlgHom_apply]
  have key : ∀ p : Polynomial (RatFunc ℚ), (Polynomial.aeval w₂) p
      = (p.map (evalAtHom w₁ hw₁)).eval w₂ := fun p => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      show algebraMap (RatFunc ℚ) ℂ = evalAtHom w₁ hw₁ from RingHom.algebraMap_toAlgebra _]
  rw [key, key]

/-- Two-variable descent for coefficients: an element of `ℚ(u₁, u₂)` vanishing at every
algebraically independent pair in the polydisc is zero. -/
private theorem ratFunc₂_eq_zero (r : RatFunc₂)
    (h : ∀ (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
      (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂),
      0 < ‖w₁‖ → ‖w₁‖ < 1 → 0 < ‖w₂‖ → ‖w₂‖ < 1 → evalε w₁ w₂ hw₁ hw₂ r = 0) :
    r = 0 := by
  rw [← RatFunc.num_eq_zero_iff]
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  refine ratFunc_eq_zero_of_evalAt_eq_zero_on_infinite _
    {w₁ : ℂ | Transcendental ℚ w₁ ∧ 0 < ‖w₁‖ ∧ ‖w₁‖ < 1}
    (transcendental_punctured_unit_disk_infinite' (K := ℚ)) ?_
  rintro w₁ ⟨hw₁, hw₁0, hw₁1⟩
  letI : Algebra (RatFunc ℚ) ℂ := (evalAtHom w₁ hw₁).toAlgebra
  rw [← evalAtHom_apply w₁ hw₁, ← Polynomial.coeff_map]
  suffices hP : (RatFunc.num r).map (evalAtHom w₁ hw₁) = 0 by rw [hP, Polynomial.coeff_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hQne : (RatFunc.denom r).map (evalAtHom w₁ hw₁) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (evalAtHom w₁ hw₁).injective).mpr (RatFunc.denom_ne_zero r)
  have hgood : ({w₂ : ℂ | Transcendental (RatFunc ℚ) w₂ ∧ 0 < ‖w₂‖ ∧ ‖w₂‖ < 1}).Infinite :=
    transcendental_punctured_unit_disk_infinite' (K := RatFunc ℚ)
  have hQfin : {w₂ : ℂ | ((RatFunc.denom r).map (evalAtHom w₁ hw₁)).IsRoot w₂}.Finite :=
    Polynomial.finite_setOf_isRoot hQne
  refine (hgood.sdiff hQfin).mono ?_
  rintro w₂ ⟨⟨hw₂tr, hw₂0, hw₂1⟩, hw₂Q⟩
  have hev := h w₁ w₂ hw₁ hw₂tr hw₁0 hw₁1 hw₂0 hw₂1
  rw [evalε_eq] at hev
  exact (div_eq_zero_iff.mp hev).resolve_right hw₂Q

/-- Two-variable descent for the formal power series ring. -/
private theorem eq_zero₂ (F : RatFunc₂⟦X⟧)
    (hF : ∀ (w₁ w₂ : ℂ) (hw₁ : Transcendental ℚ w₁)
      (hw₂ : letI := (evalAtHom w₁ hw₁).toAlgebra; Transcendental (RatFunc ℚ) w₂),
      0 < ‖w₁‖ → ‖w₁‖ < 1 → 0 < ‖w₂‖ → ‖w₂‖ < 1 →
      ∃ ρ > 0, ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < ρ →
        HasSum (fun n ↦ evalε w₁ w₂ hw₁ hw₂ (PowerSeries.coeff n F) * q ^ n) 0) :
    F = 0 := by
  ext n
  rw [map_zero]
  refine ratFunc₂_eq_zero _ fun w₁ w₂ hw₁ hw₂ ha hb hc hd => ?_
  obtain ⟨ρ, hρ, hsum⟩ := hF w₁ w₂ hw₁ hw₂ ha hb hc hd
  exact congrFun (coeffs_eq_zero_of_hasSum_punctured _ ρ hρ hsum) n

/-- **The formal chord law, `x`-coordinate** (first identity in Silverman's proof of
ATAEC V.3.1(c)): `(X₁ - X₂)²·X₃ = (Y₁ - Y₂)² + (Y₁ - Y₂)(X₁ - X₂) - (X₁ + X₂)(X₁ - X₂)²`
in `ℚ(u₁, u₂)⟦q⟧`. -/
theorem chord_x :
    (X₁ - X₂) ^ 2 * X₃ =
      (Y₁ - Y₂) ^ 2 + (Y₁ - Y₂) * (X₁ - X₂) - (X₁ + X₂) * (X₁ - X₂) ^ 2 := by
  rw [← sub_eq_zero]
  refine eq_zero₂ _ fun w₁ w₂ hw₁ hw₂ hw₁0 hw₁1 hw₂0 hw₂1 => ?_
  refine ⟨‖w₁‖ * ‖w₂‖, by positivity, fun q hq0 hqρ => ?_⟩
  have hw10 : w₁ ≠ 0 := norm_pos_iff.mp hw₁0
  have hqw1 : ‖q‖ < ‖w₁‖ := hqρ.trans (by nlinarith [hw₂1, hw₁0])
  have hqw2 : ‖q‖ < ‖w₂‖ := hqρ.trans (by nlinarith [hw₁1, hw₂0])
  have hqw12 : ‖q‖ < ‖w₁ * w₂‖ := by rw [norm_mul]; exact hqρ
  have hw121 : ‖w₁ * w₂‖ < 1 := by
    rw [norm_mul]; nlinarith [hw₁1, hw₂1, norm_nonneg w₁, norm_nonneg w₂]
  set ε := evalε w₁ w₂ hw₁ hw₂ with hε
  have hX1 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₁) * q ^ n) (XAn w₁ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₁ w₁ w₂ hw₁ hw₂) (hasSum_X_eval hw₁ hq0 hqw1 hw₁1)
  have hX2 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₂) * q ^ n) (XAn w₂ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₂ w₁ w₂ hw₁ hw₂)
      (hasSum_X_eval (transcendental_snd w₁ w₂ hw₁ hw₂) hq0 hqw2 hw₂1)
  have hX3 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₃) * q ^ n) (XAn (w₁ * w₂) q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₃ w₁ w₂ hw₁ hw₂ hw10)
      (hasSum_X_eval (transcendental_prod w₁ w₂ hw₁ hw₂ hw10) hq0 hqw12 hw121)
  have hY1 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₁) * q ^ n) (YAn w₁ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₁ w₁ w₂ hw₁ hw₂) (hasSum_Y_eval hw₁ hq0 hqw1 hw₁1)
  have hY2 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₂) * q ^ n) (YAn w₂ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₂ w₁ w₂ hw₁ hw₂)
      (hasSum_Y_eval (transcendental_snd w₁ w₂ hw₁ hw₂) hq0 hqw2 hw₂1)
  have hY3 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₃) * q ^ n) (YAn (w₁ * w₂) q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₃ w₁ w₂ hw₁ hw₂ hw10)
      (hasSum_Y_eval (transcendental_prod w₁ w₂ hw₁ hw₂ hw10) hq0 hqw12 hw121)
  have hX12 := hasSum_ringHom_sub ε hX1 hX2
  have hY12 := hasSum_ringHom_sub ε hY1 hY2
  have hX12sq : HasSum (fun n ↦ ε (PowerSeries.coeff n ((X₁ - X₂) ^ 2)) * q ^ n)
      ((XAn w₁ q - XAn w₂ q) ^ 2) := by simpa [pow_two] using hasSum_ringHom_mul ε hX12 hX12
  have hY12sq : HasSum (fun n ↦ ε (PowerSeries.coeff n ((Y₁ - Y₂) ^ 2)) * q ^ n)
      ((YAn w₁ q - YAn w₂ q) ^ 2) := by simpa [pow_two] using hasSum_ringHom_mul ε hY12 hY12
  have hLHS := hasSum_ringHom_mul ε hX12sq hX3
  have hRHS := hasSum_ringHom_sub ε (hasSum_ringHom_add ε hY12sq (hasSum_ringHom_mul ε hY12 hX12))
    (hasSum_ringHom_mul ε (hasSum_ringHom_add ε hX1 hX2) hX12sq)
  have hzero : (XAn w₁ q - XAn w₂ q) ^ 2 * XAn (w₁ * w₂) q -
      ((YAn w₁ q - YAn w₂ q) ^ 2 + (YAn w₁ q - YAn w₂ q) * (XAn w₁ q - XAn w₂ q) -
        (XAn w₁ q + XAn w₂ q) * (XAn w₁ q - XAn w₂ q) ^ 2) = 0 :=
    sub_eq_zero.mpr (analytic_chord_x hq0 hqw1 hw₁1 hqw2 hw₂1 hqw12)
  rw [← hzero]
  exact hasSum_ringHom_sub ε hLHS hRHS

private theorem coeff_zero_X :
    PowerSeries.coeff 0 (TateCurve.X) = RatFunc.X / (1 - RatFunc.X) ^ 2 := by
  simp [TateCurve.X]

/-- `X₁ ≠ X₂` in `ℚ(u₁, u₂)⟦q⟧`: otherwise `u₂ = u₁·(…)` would be algebraic over `ℚ(u₁)`.
Used to cancel the factor `X₁ - X₂` in the `y`-coordinate law. -/
private theorem X₁_sub_X₂_ne_zero : (X₁ - X₂ : RatFunc₂⟦X⟧) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hc₀ne : (RatFunc.X / (1 - RatFunc.X) ^ 2 : RatFunc ℚ) ≠ 0 :=
    div_ne_zero RatFunc.X_ne_zero (pow_ne_zero 2 RatFunc.one_sub_X_ne_zero)
  have hemb₂ : emb₂ (RatFunc.X / (1 - RatFunc.X) ^ 2) = u₂ / (1 - u₂) ^ 2 := by
    rw [map_div₀, map_pow, map_sub, map_one, emb₂_ratFuncX]
  have hc : algebraMap (RatFunc ℚ) RatFunc₂ (RatFunc.X / (1 - RatFunc.X) ^ 2)
      = u₂ / (1 - u₂) ^ 2 := by
    have h0 := congrArg (PowerSeries.coeff 0) h
    simp only [X₁, X₂, PowerSeries.coeff_map, coeff_zero_X, hemb₂] at h0
    exact h0
  apply transcendental_u₂
  refine ⟨Polynomial.C (RatFunc.X / (1 - RatFunc.X) ^ 2) * (1 - Polynomial.X) ^ 2
    - Polynomial.X, ?_, ?_⟩
  · intro hp
    apply hc₀ne
    have h0 : (Polynomial.C (RatFunc.X / (1 - RatFunc.X) ^ 2) * (1 - Polynomial.X) ^ 2
        - Polynomial.X : Polynomial (RatFunc ℚ)).eval 0 = 0 := by rw [hp, Polynomial.eval_zero]
    simpa using h0
  · rw [map_sub, map_mul, map_pow, map_sub, map_one, Polynomial.aeval_X, Polynomial.aeval_C, hc]
    have hu₂ne : (1 : RatFunc₂) - u₂ ≠ 0 := RatFunc.one_sub_X_ne_zero
    field_simp
    ring

/-- **The formal chord law, `y`-coordinate** (second identity in Silverman's proof of
ATAEC V.3.1(c)): `(X₂ - X₁)·Y₃ = -((Y₂ - Y₁) + (X₂ - X₁))·X₃ - (Y₁X₂ - Y₂X₁)` in
`ℚ(u₁, u₂)⟦q⟧`. -/
theorem chord_y :
    (X₂ - X₁) * Y₃ = -((Y₂ - Y₁) + (X₂ - X₁)) * X₃ - (Y₁ * X₂ - Y₂ * X₁) := by
  rw [← sub_eq_zero]
  refine (mul_eq_zero.mp (?_ : (X₁ - X₂) * ((X₂ - X₁) * Y₃ -
    (-((Y₂ - Y₁) + (X₂ - X₁)) * X₃ - (Y₁ * X₂ - Y₂ * X₁))) = 0)).resolve_left X₁_sub_X₂_ne_zero
  refine eq_zero₂ _ fun w₁ w₂ hw₁ hw₂ hw₁0 hw₁1 hw₂0 hw₂1 => ?_
  refine ⟨‖w₁‖ * ‖w₂‖, by positivity, fun q hq0 hqρ => ?_⟩
  have hw10 : w₁ ≠ 0 := norm_pos_iff.mp hw₁0
  have hqw1 : ‖q‖ < ‖w₁‖ := hqρ.trans (by nlinarith [hw₂1, hw₁0])
  have hqw2 : ‖q‖ < ‖w₂‖ := hqρ.trans (by nlinarith [hw₁1, hw₂0])
  have hqw12 : ‖q‖ < ‖w₁ * w₂‖ := by rw [norm_mul]; exact hqρ
  have hw121 : ‖w₁ * w₂‖ < 1 := by
    rw [norm_mul]; nlinarith [hw₁1, hw₂1, norm_nonneg w₁, norm_nonneg w₂]
  set ε := evalε w₁ w₂ hw₁ hw₂ with hε
  have hX1 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₁) * q ^ n) (XAn w₁ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₁ w₁ w₂ hw₁ hw₂) (hasSum_X_eval hw₁ hq0 hqw1 hw₁1)
  have hX2 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₂) * q ^ n) (XAn w₂ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₂ w₁ w₂ hw₁ hw₂)
      (hasSum_X_eval (transcendental_snd w₁ w₂ hw₁ hw₂) hq0 hqw2 hw₂1)
  have hX3 : HasSum (fun n ↦ ε (PowerSeries.coeff n X₃) * q ^ n) (XAn (w₁ * w₂) q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₃ w₁ w₂ hw₁ hw₂ hw10)
      (hasSum_X_eval (transcendental_prod w₁ w₂ hw₁ hw₂ hw10) hq0 hqw12 hw121)
  have hY1 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₁) * q ^ n) (YAn w₁ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₁ w₁ w₂ hw₁ hw₂) (hasSum_Y_eval hw₁ hq0 hqw1 hw₁1)
  have hY2 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₂) * q ^ n) (YAn w₂ q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₂ w₁ w₂ hw₁ hw₂)
      (hasSum_Y_eval (transcendental_snd w₁ w₂ hw₁ hw₂) hq0 hqw2 hw₂1)
  have hY3 : HasSum (fun n ↦ ε (PowerSeries.coeff n Y₃) * q ^ n) (YAn (w₁ * w₂) q) :=
    hasSum_evalε_coeff_map hw₁ hw₂ (evalε_comp_emb₃ w₁ w₂ hw₁ hw₂ hw10)
      (hasSum_Y_eval (transcendental_prod w₁ w₂ hw₁ hw₂ hw10) hq0 hqw12 hw121)
  have hX12 := hasSum_ringHom_sub ε hX1 hX2
  have hFy := hasSum_ringHom_sub ε (hasSum_ringHom_mul ε (hasSum_ringHom_sub ε hX2 hX1) hY3)
    (hasSum_ringHom_sub ε
      (hasSum_ringHom_mul ε (hasSum_ringHom_neg ε
        (hasSum_ringHom_add ε (hasSum_ringHom_sub ε hY2 hY1) (hasSum_ringHom_sub ε hX2 hX1))) hX3)
      (hasSum_ringHom_sub ε (hasSum_ringHom_mul ε hY1 hX2) (hasSum_ringHom_mul ε hY2 hX1)))
  have hprod : (XAn w₁ q - XAn w₂ q) * ((XAn w₂ q - XAn w₁ q) * YAn (w₁ * w₂) q -
      (-((YAn w₂ q - YAn w₁ q) + (XAn w₂ q - XAn w₁ q)) * XAn (w₁ * w₂) q -
        (YAn w₁ q * XAn w₂ q - YAn w₂ q * XAn w₁ q))) = 0 := by
    by_cases ha : XAn w₁ q = XAn w₂ q
    · rw [ha, sub_self, zero_mul]
    · rw [sub_eq_zero.mpr (analytic_chord_y hq0 hqw1 hw₁1 hqw2 hw₂1 hqw12 ha), mul_zero]
  rw [← hprod]
  exact hasSum_ringHom_mul ε hX12 hFy

end TateCurve
