/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists

/-!

# Outline: `WeierstrassCurve.exists_variableChange_tateCurve`

This file collects the statements needed to fill the `sorry` in
`WeierstrassCurve.exists_variableChange_tateCurve` (`TateCurve.lean`):
for `E/k` elliptic with split multiplicative reduction over a nonarchimedean local field
`k`, and Tate parameter `E.q = tateParameter E.j`, there is a change of Weierstrass
coordinates taking the Tate curve `E_q := tateCurve E.q` to `E`. This is Silverman, ATAEC
V.5.3.

Everything below is a `sorry`ed statement: this is an outline of the API to be proved, not
a proof. The mathematics splits into two independent halves.

## Half A — `j(tateCurve E.q) = E.j`

The Tate curve of the parameter has the right `j`-invariant. This is the assertion that
`tateParameter` inverts `j ↦ j(tateCurve q)`. It rests on the (hard, classical)
discriminant product formula `Δ(tateCurve q) = q·∏(1-qⁿ)²⁴` (`tateCurve_Δ` below, matching
the formal series `TateCurve.ΔFormal`), plus routine evaluation bookkeeping:

* `tateCurve_c₄` — the easy `c₄`-analogue (`A1`);
* `tateCurve_Δ` — the discriminant product formula (`A2`, the dominant risk);
* `evalInt_subst` — evaluation commutes with formal substitution (`A3`);
* `evalInt_jInv`, `j_tateCurve_q` — assembling `A4`, `A5`.

## Half B — descent from same-`j` to isomorphism over `k`

Two curves over `k` with the same `j ∉ {0, 1728}` are quadratic twists of one another; they
are isomorphic *over `k`* iff the twisting class in `kˣ/(kˣ)²` is trivial. Split
multiplicative reduction of both `E` and `E_q` forces triviality.

* `HasSplitMultiplicativeReduction` for `tateCurve E.q` (`B0`, needs `tateCurve_Δ`);
* `isSquare_twist_of_splitMult` — split + split ⟹ the twist class is a square (`B1`+`B2`);
* `exists_variableChange_of_c₄_c₆` — matching `(c₄, c₆)` up to `(u⁴, u⁶)` ⟹ a variable
  change (`B3`, the field-generic cousin of mathlib's `exists_variableChange_of_j_eq`,
  which is stated only over `[IsSepClosed]`).

The exclusion `j ∉ {0, 1728}` is free: `1 < |E.j|` (`one_lt_valuation_j`) while `|0|, |1728|`
are `≤ 1`, so `c₄(E), c₆(E) ≠ 0`.

See `ExistsVariableChangeTateCurve_Blueprint.md` for the full mathematical discussion,
per-lemma difficulty estimates, and the recommended bottom-up build order.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

/-! ## Evaluation helpers

Small facts about `TateCurve.evalInt` on the open unit disc, used repeatedly below:
evaluation of a constant series and pulling an integer constant out of a product. -/

namespace TateCurve

open PowerSeries

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Evaluation of a constant integral power series `C a` at any point returns `a`. -/
theorem evalInt_C (q : k) (a : ℤ) : evalInt q (C a : ℤ⟦X⟧) = (a : k) := by
  rw [show evalInt q (C a : ℤ⟦X⟧)
        = ∑' n : ℕ, ((coeff n (C a : ℤ⟦X⟧) : ℤ) : k) * q ^ n from rfl,
    tsum_eq_single 0 fun n hn ↦ by rw [coeff_C, if_neg hn]; simp]
  rw [coeff_C, if_pos rfl]; simp

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Evaluation sends `1` to `1`. -/
@[simp] theorem evalInt_one (q : k) : evalInt q (1 : ℤ⟦X⟧) = 1 := by
  rw [← map_one (C : ℤ →+* ℤ⟦X⟧), evalInt_C, Int.cast_one]

/-- Pulling an integer constant `a` out of a product before evaluating, valid on the open
unit disc where `evalInt` is multiplicative. -/
theorem evalInt_C_mul (q : k) (hq : valuation k q < 1) (a : ℤ) (F : ℤ⟦X⟧) :
    evalInt q ((C a : ℤ⟦X⟧) * F) = (a : k) * evalInt q F := by
  rw [evalInt_mul q hq, evalInt_C]

end TateCurve

namespace WeierstrassCurve

/-! ## Half A: `j(tateCurve E.q) = E.j` -/

open TateCurve PowerSeries in
/-- **A1.** The `c₄` of the Tate curve is the evaluation of the formal Eisenstein series
`c₄Formal = 1 + 240·s₃`. Since `c₄ = b₂² - 24b₄` with `b₂ = 1`, `b₄ = 2·tateA₄ q`, this is
`1 - 48·tateA₄ q`; conclude by `evalInt`-linearity from `tateA₄_eq_evalInt`. A finite,
mechanical calculation. -/
theorem tateCurve_c₄ {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ = evalInt q c₄Formal := by
  -- `c₄ = b₂² - 24b₄` with `b₂ = 1`, `b₄ = 2·tateA₄ q`
  have hc : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tateCurve]
    ring
  -- `240 = C 240` and `-5 = C (-5)` as integral series, to expose the constant factors
  have h240 : (240 : ℤ⟦X⟧) = C (240 : ℤ) := by simp
  have h5 : (-5 : ℤ⟦X⟧) = C (-5 : ℤ) := by simp
  -- `evalInt` of the two Eisenstein-type series, both `= const · evalInt q (sInt 3)`
  have hR : evalInt q c₄Formal = 1 + 240 * evalInt q (sInt 3) := by
    rw [c₄Formal, h240, evalInt_add (summable_evalInt q hq 1) (summable_evalInt q hq _),
      evalInt_one, evalInt_C_mul q hq]
    push_cast; ring
  have hL : evalInt q a₄Formal = -5 * evalInt q (sInt 3) := by
    rw [a₄Formal, h5, evalInt_C_mul q hq]; push_cast; ring
  rw [hc, tateA₄_eq_evalInt q hq, hL, hR]; ring

open TateCurve PowerSeries in
/-- **A2 (GAP #1).** The discriminant of the Tate curve is the evaluation of the formal
discriminant `ΔFormal = X·∏(1-Xⁿ)²⁴`. Equivalent to the formal power-series identity
`Δ_Weierstrass ⟨1,0,0,a₄Formal,a₆Formal⟩ = ΔFormal` in `ℤ⟦X⟧`, i.e. the `q`-expansion of
the modular discriminant / Jacobi's product `Δ = η²⁴`. There is no mathlib API for this;
it is the deepest input to the whole development. Everything downstream of `A4` is blocked
on it, as is the valuation part of `B0` (although `B0` needs only the weaker fragment
`constantCoeff_ΔFormal`/`coeff_one_ΔFormal` below). -/
theorem tateCurve_Δ {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = evalInt q ΔFormal :=
  -- Sam has this so leave this sorry
  sorry

open TateCurve PowerSeries in
/-- **A2 fragment.** The constant coefficient of `ΔFormal = X·∏(1-Xⁿ)²⁴` vanishes.
Provable directly from the product, without the full `tateCurve_Δ`; together with
`coeff_one_ΔFormal` this is all that `B0`'s valuation computation needs. -/
theorem constantCoeff_ΔFormal : constantCoeff ΔFormal = 0 :=
  sorry

open TateCurve PowerSeries in
/-- **A2 fragment.** The linear coefficient of `ΔFormal = X·∏(1-Xⁿ)²⁴` is `1` (a unit). -/
theorem coeff_one_ΔFormal : coeff 1 ΔFormal = 1 :=
  sorry

open TateCurve PowerSeries in
/-- **A3.** The convergent avatar of formal substitution: for integral power series and
arguments in the open unit disc, evaluation commutes with `subst`. Proof by the formal-to-
analytic bridge (partial sums of `F ∘ G` converge to `evalInt (evalInt w G) F`); mildly
technical (double series / summability), but self-contained and reusable. -/
theorem evalInt_subst {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (w : k) (hw : valuation k w < 1) (F G : ℤ⟦X⟧)
    (hG0 : constantCoeff G = 0) :
    evalInt (evalInt w G) F = evalInt w (subst G F) := by
  classical
  -- Evaluate into the complete DVR `𝒪[k]`, where the power-series evaluation API applies;
  -- `evalInt` is the coercion to `k` of `PowerSeries.eval₂` at the integer point.
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : IsUniformAddGroup 𝒪[k] := inferInstanceAs (IsUniformAddGroup 𝒪[k].toAddSubgroup)
  have hind : Topology.IsInducing ((↑) : 𝒪[k] → k) := ⟨rfl⟩
  have hφ : Continuous (algebraMap ℤ 𝒪[k]) := continuous_of_discreteTopology
  -- points of the open unit disc are topologically nilpotent in `𝒪[k]`
  have hEval : ∀ (p : k) (hp : valuation k p < 1), HasEval (⟨p, hp.le⟩ : 𝒪[k]) := fun p hp ↦
    hind.tendsto_nhds_iff.mpr (by simpa [Function.comp_def] using tendsto_pow_nhds_zero hp)
  -- the bridge: `evalInt p H` is `eval₂ … ⟨p⟩ H` coerced back to `k`
  have bridge : ∀ (p : k) (hp : valuation k p < 1) (H : ℤ⟦X⟧),
      evalInt p H = ((eval₂ (algebraMap ℤ 𝒪[k]) (⟨p, hp.le⟩ : 𝒪[k]) H : 𝒪[k]) : k) := by
    intro p hp H
    change (∑' n : ℕ, ((coeff n H : ℤ) : k) * p ^ n) = _
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def] using (hasSum_eval₂ hφ (hEval p hp) H).map
      (Subring.subtype 𝒪[k]).toAddMonoidHom continuous_subtype_val
  -- `evalInt w G` lies in the open unit disc, since `constantCoeff G = 0`
  have hlow : ∀ m < 1, coeff m G = 0 := fun m hm ↦ by
    rw [Nat.lt_one_iff.mp hm]; simpa [coeff_zero_eq_constantCoeff] using hG0
  have hv : valuation k (evalInt w G) < 1 :=
    lt_of_le_of_lt (by simpa using valuation_evalInt_le_pow w hw hlow) hw
  -- the substitution/evaluation identity in `𝒪[k]`, from `MvPowerSeries.eval₂_subst`
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hsub : eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) (subst G F)
      = eval₂ (algebraMap ℤ 𝒪[k])
          (eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) G) F := by
    have h := MvPowerSeries.eval₂_subst (R := ℤ) (S := ℤ) (T := 𝒪[k])
      (a := fun _ : Unit ↦ G) (b := fun _ : Unit ↦ (⟨w, hw.le⟩ : 𝒪[k]))
      hG.const (hasEval (hEval w hw)) F
    simpa only [PowerSeries.eval₂, PowerSeries.subst_def] using h
  -- `eval₂ … ⟨w⟩ G` is the disc point `evalInt w G` as an element of `𝒪[k]`
  have hpt : (⟨evalInt w G, hv.le⟩ : 𝒪[k])
      = eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) G :=
    Subtype.ext (bridge w hw G)
  calc evalInt (evalInt w G) F
      = ((eval₂ (algebraMap ℤ 𝒪[k]) (⟨evalInt w G, hv.le⟩ : 𝒪[k]) F : 𝒪[k]) : k) :=
        bridge (evalInt w G) hv F
    _ = ((eval₂ (algebraMap ℤ 𝒪[k])
          (eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) G) F : 𝒪[k]) : k) := by rw [hpt]
    _ = ((eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) (subst G F) : 𝒪[k]) : k) := by rw [hsub]
    _ = evalInt w (subst G F) := (bridge w hw (subst G F)).symm

open TateCurve PowerSeries in
/-- **A4.** `jInv = ΔFormal · invOfUnit (c₄Formal³)` evaluates to `1/j(tateCurve q)`.
From `tateCurve_c₄`, `tateCurve_Δ` and `evalInt_mul`/`evalInt_pow`; the nonvanishing of
`evalInt q (c₄Formal³)` is automatic, as it multiplies `evalInt q (invOfUnit …)` to `1`. -/
theorem evalInt_jInv {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : k) (hq : valuation k q < 1)
    [(tateCurve q).IsElliptic] :
    evalInt q jInv = (tateCurve q).j⁻¹ := by
  -- `c₄Formal³` is a unit series, so its formal inverse really inverts it
  have hinv : c₄Formal ^ 3 * invOfUnit (c₄Formal ^ 3) 1 = 1 := by
    apply mul_invOfUnit
    have hc : constantCoeff c₄Formal = 1 := by
      simp only [c₄Formal, map_add, map_one, map_mul, map_ofNat]
      simp [sInt]
    simp [map_pow, hc]
  -- evaluating the inversion identity shows `evalInt q (invOfUnit …) = (evalInt q c₄Formal³)⁻¹`
  have h1 : evalInt q (c₄Formal ^ 3) * evalInt q (invOfUnit (c₄Formal ^ 3) 1) = 1 := by
    rw [← evalInt_mul q hq, hinv, evalInt_one]
  have hev_inv : evalInt q (invOfUnit (c₄Formal ^ 3) 1) = (evalInt q (c₄Formal ^ 3))⁻¹ :=
    (inv_eq_of_mul_eq_one_right h1).symm
  calc evalInt q jInv
      = evalInt q ΔFormal * evalInt q (invOfUnit (c₄Formal ^ 3) 1) := by
        rw [jInv, evalInt_mul q hq]
    _ = (tateCurve q).Δ * (evalInt q (c₄Formal ^ 3))⁻¹ := by
        rw [hev_inv, ← tateCurve_Δ q hq]
    _ = (tateCurve q).Δ * ((tateCurve q).c₄ ^ 3)⁻¹ := by
        rw [evalInt_pow q hq, ← tateCurve_c₄ q hq]
    _ = (tateCurve q).j⁻¹ := by
        rw [show (tateCurve q).j = (↑((tateCurve q).Δ'⁻¹) : k) * (tateCurve q).c₄ ^ 3 from rfl,
          mul_inv, Units.val_inv_eq_inv_val, inv_inv, coe_Δ']

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- Let `E/k` be elliptic with split multiplicative reduction.
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]

/-- The Tate curve of the Tate parameter is elliptic: its discriminant is nonzero, as
`v(Δ) = v(q) < 1 ≠ 0` (via `tateCurve_Δ` and the `ΔFormal`-fragment lemmas). Needed to speak
of its `j`-invariant and reduction type. -/
instance : (tateCurve E.q).IsElliptic :=
  sorry

open TateCurve in
/-- **A5.** The Tate curve of the Tate parameter has the same `j`-invariant as `E`. Put
`w := E.j⁻¹` (with `|w| < 1` by `one_lt_valuation_j`); then `E.q = evalInt w jInvReverse`
and
`1/j(tateCurve E.q) = evalInt E.q jInv = evalInt (evalInt w jInvReverse) jInv`
`= evalInt w (subst jInvReverse jInv) = evalInt w X = w = E.j⁻¹`
by `evalInt_jInv`, `evalInt_subst` and `jInv_subst_jInvReverse`. Invert both sides. -/
theorem j_tateCurve_q : (tateCurve E.q).j = E.j :=
  sorry

/-! ## Half B: descent `∃ C : VariableChange k, C • tateCurve E.q = E` -/

/-- **B0.** The Tate curve of the Tate parameter itself has split multiplicative reduction.
It is minimal (`c₄` a unit, `v(Δ) = v(q) < 1`), `v(Δ) < 1` (from `tateCurve_Δ`, or just the
`ΔFormal`-fragment lemmas), `v(c₄) = 1` (from `tateCurve_c₄` and `|tateA₄| < 1`), and the
reduction — the nodal cubic `y² + xy = x³` with rational tangents `y = 0`, `y = -x` — is
split. This is where "the Tate curve is *the* split model" is discharged. -/
instance : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[k] :=
  sorry

/-- **B1 + B2 (GAP #2).** For two elliptic curves over `k` with the same `j`-invariant and
*split* multiplicative reduction, the twist class `d := c₄(W₁)·c₆(W₂)/(c₄(W₂)·c₆(W₁))`
relating them is a square in `kˣ`.

`B1` is field algebra: from `j = c₄³/Δ` and `j - 1728 = c₆²/Δ`, equal `j` gives
`d² = c₄(W₁)/c₄(W₂)` and `d³ = c₆(W₁)/c₆(W₂)`.

`B2` is the arithmetic heart of V.5.3: `d ∈ (kˣ)²` says the quadratic twist relating `W₁`
and `W₂` is trivial, forced by *both* curves having split reduction (a nontrivial
quadratic twist of a split-multiplicative curve is non-split, if unramified, or additive,
if ramified). Needs a "reduction type of a quadratic twist" theory not yet in mathlib or
FLT; the residue quadratic of `HasSplitMultiplicativeReduction` is the concrete handle. -/
theorem isSquare_twist_of_splitMult (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] [W₁.HasSplitMultiplicativeReduction 𝒪[k]]
    [W₂.HasSplitMultiplicativeReduction 𝒪[k]] (hj : W₁.j = W₂.j) :
    IsSquare (W₁.c₄ * W₂.c₆ / (W₂.c₄ * W₁.c₆)) :=
  sorry

/-- **B3.** Two elliptic curves over a field whose `(c₄, c₆)` agree up to `(u⁴, u⁶)` for a
unit `u` are related by a variable change (parameter `u`). This is the field-generic cousin
of mathlib's `exists_variableChange_of_j_eq`, which is stated only over `[IsSepClosed]`; it
should be extractable from the normal-form machinery in mathlib's `NormalForms.lean` /
`IsomOfJ.lean`, or admit a short standalone proof by solving for `r, s, t`. -/
theorem exists_variableChange_of_c₄_c₆ (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] (u : kˣ) (h4 : W₂.c₄ = (u : k) ^ 4 * W₁.c₄)
    (h6 : W₂.c₆ = (u : k) ^ 6 * W₁.c₆) :
    ∃ C : VariableChange k, C • W₁ = W₂ :=
  sorry

/-- **Final glue.** Silverman ATAEC V.5.3, restated here to record how the pieces above
combine (the load-bearing declaration is `exists_variableChange_tateCurve` in
`TateCurve.lean`, whose `sorry` this outline is meant to discharge):

* `j_tateCurve_q` gives `j(E_q) = E.j`;
* `isSquare_twist_of_splitMult` (with `B0`'s instance) makes the twist class `d` a square,
  say `d = u²`; then `B1`'s identities give `u⁴ = c₄(E)/c₄(E_q)`, `u⁶ = c₆(E)/c₆(E_q)`;
* `exists_variableChange_of_c₄_c₆` turns that into the variable change. -/
theorem exists_variableChange_tateCurve_of_pieces :
    ∃ C : VariableChange k, C • tateCurve E.q = E := by
  have hj : (tateCurve E.q).j = E.j := j_tateCurve_q E
  have hsq : IsSquare ((tateCurve E.q).c₄ * E.c₆ / (E.c₄ * (tateCurve E.q).c₆)) :=
    isSquare_twist_of_splitMult _ _ hj
  sorry

end WeierstrassCurve
