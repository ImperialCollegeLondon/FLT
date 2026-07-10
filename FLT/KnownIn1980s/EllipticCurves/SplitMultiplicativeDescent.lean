/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib
public import FLT.KnownIn1980s.EllipticCurves.TateParameterOfCurve
public import FLT.KnownIn1980s.EllipticCurves.TateCurveSeries
public import FLT.KnownIn1980s.EllipticCurves.TateCurveSurjectivity
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.FieldTheory.KrullTopology

/-!

# `E ≅ tateCurve E.q`: the Tate uniformisation at the equation level

For `E/k` elliptic with split multiplicative reduction over a nonarchimedean local field `k`,
with Tate parameter `E.q = tateParameter E.j`, there is a change of Weierstrass coordinates
taking the Tate curve `E_q := tateCurve E.q` to `E` (Silverman, ATAEC V.5.3). This file
proves the two halves of that statement that need no characteristic hypothesis, and records
the **characteristic-uniform** descent that finishes it.

## Half A — `j(tateCurve E.q) = E.j` (proved)

The Tate curve of the parameter has the right `j`-invariant: `tateParameter` inverts
`j ↦ j(tateCurve q)`. This rests on the discriminant product formula `tateCurve_Δ_eq_evalInt`
(the `q`-expansion of `Δ = η²⁴`, proved in `TateCurveSeries` — the PR #1099 work) plus routine
evaluation bookkeeping (`evalInt_subst`, `evalInt_jInv`, `j_tateCurve_q`).

## Half B0 — `tateCurve E.q` has split multiplicative reduction (proved)

The Tate curve is minimal (`c₄` a unit, `|Δ| = |q| < 1`) and its reduction is the split nodal
cubic `y² + xy = x³` (tangent-cone quadratic `X² + X = X(X+1)`).

## Descent — from same `j` and both split to `k`-isomorphism (blueprint)

The remaining step reduces to two general facts about quadratic twists, stated below as
**(a)** and **(c)** and *not* yet in the API. Given them, `exists_variableChange_of_splitMult`
and `exists_variableChange_tateCurve` hold with **no** hypothesis on the
characteristic of `k` or of its residue field — unlike the earlier `c₄, c₆`/`IsSquare` route,
which is the Kummer (characteristic `≠ 2`) description of twists and pays a `(2 : k) ≠ 0`,
`(3 : k) ≠ 0`, `IsUnit (2 : 𝒪[k])` toll.

Status of the ingredients (all in FLT PR #1088, branch
`MichaelStollBayreuth:MS_quadratic_twists_1`):

* **Dichotomy** `exists_smul_eq_or_exists_smul_eq_quadraticTwist` — *available*, PR #1088
  `FLT/KnownIn1980s/EllipticCurves/QuadraticTwists/QuadraticTwists.lean:547`.
* **(a)** same `j ∉ {0, 1728}` ⟹ isomorphic over a separable quadratic extension —
  **missing**.
* **(c)** a quadratic twist of a split-multiplicative curve is never split — **missing** as a
  theorem; decomposes into reduction-type-is-a-`k`-isomorphism-invariant (*available*, PR #1088
  `HasSplitMultiplicativeReduction.of_isMinimal_smul`,
  `FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean:425`) and the arithmetic heart
  (proved in *both* residue characteristics inside PR #1088
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`,
  `FLT/KnownIn1980s/EllipticCurves/QuadraticTwists/SplitMultiplicativeReduction.lean:404`, but
  the converse direction used here is not exposed).
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

universe u

namespace WeierstrassCurve

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-! ## Half A: `j(tateCurve E.q) = E.j`

`evalInt q F = ∑' n, (coeff n F) qⁿ` (`TateCurve.evalInt`, `TateParameter`) evaluates an
integral power series on the open unit disc; its algebra (`evalInt_C`, `evalInt_mul`, …) and
the leading-coefficient fragments of `ΔFormal` live in `TateParameter`, and the deep inputs —
the discriminant identity `tateCurve_Δ_eq_evalInt` and the Eisenstein identity
`tateCurve_c₄_eq_evalInt` — in `TateCurveSeries` (the PR #1099 work, imported above). -/

open TateCurve PowerSeries in
/-- **A3.** The convergent avatar of formal substitution: for integral power series and
arguments in the open unit disc, evaluation commutes with `subst`, by the formal-to-analytic
bridge (partial sums of `F ∘ G` converge to `evalInt (evalInt w G) F`). -/
theorem evalInt_subst (w : k) (hw : valuation k w < 1) (F G : ℤ⟦X⟧)
    (hG0 : constantCoeff G = 0) :
    evalInt (evalInt w G) F = evalInt w (subst G F) := by
  classical
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : IsUniformAddGroup 𝒪[k] := inferInstanceAs (IsUniformAddGroup 𝒪[k].toAddSubgroup)
  have hind : Topology.IsInducing ((↑) : 𝒪[k] → k) := ⟨rfl⟩
  have hφ : Continuous (algebraMap ℤ 𝒪[k]) := continuous_of_discreteTopology
  have hEval : ∀ (p : k) (hp : valuation k p < 1), HasEval (⟨p, hp.le⟩ : 𝒪[k]) := fun p hp ↦
    hind.tendsto_nhds_iff.mpr (by simpa [Function.comp_def] using tendsto_pow_nhds_zero hp)
  have bridge : ∀ (p : k) (hp : valuation k p < 1) (H : ℤ⟦X⟧),
      evalInt p H = ((eval₂ (algebraMap ℤ 𝒪[k]) (⟨p, hp.le⟩ : 𝒪[k]) H : 𝒪[k]) : k) := by
    intro p hp H
    change (∑' n : ℕ, ((coeff n H : ℤ) : k) * p ^ n) = _
    refine HasSum.tsum_eq ?_
    simpa [Function.comp_def] using (hasSum_eval₂ hφ (hEval p hp) H).map
      (Subring.subtype 𝒪[k]).toAddMonoidHom continuous_subtype_val
  have hlow : ∀ m < 1, coeff m G = 0 := fun m hm ↦ by
    rw [Nat.lt_one_iff.mp hm]; simpa [coeff_zero_eq_constantCoeff] using hG0
  have hv : valuation k (evalInt w G) < 1 :=
    lt_of_le_of_lt (by simpa using valuation_evalInt_le_pow w hw hlow) hw
  have hG : HasSubst G := HasSubst.of_constantCoeff_zero' hG0
  have hsub : eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) (subst G F)
      = eval₂ (algebraMap ℤ 𝒪[k])
          (eval₂ (algebraMap ℤ 𝒪[k]) (⟨w, hw.le⟩ : 𝒪[k]) G) F := by
    have h := MvPowerSeries.eval₂_subst (R := ℤ) (S := ℤ) (T := 𝒪[k])
      (a := fun _ : Unit ↦ G) (b := fun _ : Unit ↦ (⟨w, hw.le⟩ : 𝒪[k]))
      hG.const (hasEval (hEval w hw)) F
    simpa only [PowerSeries.eval₂, PowerSeries.subst_def] using h
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
/-- **A4.** `jInv = ΔFormal · invOfUnit (c₄Formal³)` evaluates to `1/j(tateCurve q)`. -/
theorem evalInt_jInv (q : k) (hq : valuation k q < 1) [(tateCurve q).IsElliptic] :
    evalInt q jInv = (tateCurve q).j⁻¹ := by
  have hinv : c₄Formal ^ 3 * invOfUnit (c₄Formal ^ 3) 1 = 1 := by
    apply mul_invOfUnit
    have hc : constantCoeff c₄Formal = 1 := by
      simp only [c₄Formal, map_add, map_one, map_mul, map_ofNat]
      simp [sInt]
    simp [map_pow, hc]
  have h1 : evalInt q (c₄Formal ^ 3) * evalInt q (invOfUnit (c₄Formal ^ 3) 1) = 1 := by
    rw [← evalInt_mul q hq, hinv, evalInt_one]
  have hev_inv : evalInt q (invOfUnit (c₄Formal ^ 3) 1) = (evalInt q (c₄Formal ^ 3))⁻¹ :=
    (inv_eq_of_mul_eq_one_right h1).symm
  calc evalInt q jInv
      = evalInt q ΔFormal * evalInt q (invOfUnit (c₄Formal ^ 3) 1) := by
        rw [jInv, evalInt_mul q hq]
    _ = (tateCurve q).Δ * (evalInt q (c₄Formal ^ 3))⁻¹ := by
        rw [hev_inv, ← tateCurve_Δ_eq_evalInt q hq]
    _ = (tateCurve q).Δ * ((tateCurve q).c₄ ^ 3)⁻¹ := by
        rw [evalInt_pow q hq, ← tateCurve_c₄_eq_evalInt q hq]
    _ = (tateCurve q).j⁻¹ := by
        rw [show (tateCurve q).j = (↑((tateCurve q).Δ'⁻¹) : k) * (tateCurve q).c₄ ^ 3 from rfl,
          mul_inv, Units.val_inv_eq_inv_val, inv_inv, coe_Δ']

/-! ### Valuation and integrality of the Tate curve

The reduction-theoretic facts about `tateCurve q` for a parameter `q` in the open unit disc,
feeding `B0`: its coefficients are integral, `|c₄| = 1` (so the equation is minimal), and
`|Δ| = |q| < 1`. -/

/-- The Tate curve of a parameter in the punctured open unit disc has `|Δ| = |q| < 1`
(`valuation_tateCurve_Δ`). -/
theorem valuation_tateCurve_Δ_lt_one (q : k) (hq0 : q ≠ 0) (hq : valuation k q < 1) :
    valuation k (tateCurve q).Δ < 1 :=
  (valuation_tateCurve_Δ q hq0 hq).trans_lt hq

open TateCurve in
/-- The Tate curve of a parameter in the open unit disc is integral: its coefficients
`(1, 0, 0, tateA₄ q, tateA₆ q)` all lie in `𝒪[k]`. -/
theorem isIntegral_tateCurve (q : k) (hq : valuation k q < 1) :
    IsIntegral 𝒪[k] (tateCurve q) :=
  isIntegral_of_exists_lift 𝒪[k]
    ⟨1, by simp [tateCurve]⟩
    ⟨0, by simp [tateCurve]⟩
    ⟨0, by simp [tateCurve]⟩
    ⟨⟨tateA₄ q, (Valuation.mem_integer_iff _ _).mpr ((valuation_tateA₄_le q hq).trans hq.le)⟩,
      rfl⟩
    ⟨⟨tateA₆ q, (Valuation.mem_integer_iff _ _).mpr ((valuation_tateA₆_le q hq).trans hq.le)⟩,
      rfl⟩

-- Let `E/k` be elliptic with split multiplicative reduction.
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]

/-- The Tate curve of the Tate parameter is elliptic: `|Δ| = |q| ≠ 0`
(`tateCurve_Δ_ne_zero`). -/
instance : (tateCurve E.q).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (tateCurve_Δ_ne_zero E.q E.q_ne_zero E.valuation_q_lt_one)⟩

open TateCurve in
/-- **A5.** The Tate curve of the Tate parameter has the same `j`-invariant as `E`: with
`w := E.j⁻¹` (`|w| < 1` by `one_lt_valuation_j`) and `E.q = evalInt w jInvReverse`,
`1/j(tateCurve E.q) = evalInt E.q jInv = evalInt w (subst jInvReverse jInv) = evalInt w X = w
= E.j⁻¹` by `evalInt_jInv`, `evalInt_subst`, `jInv_subst_jInvReverse`. -/
theorem j_tateCurve_q : (tateCurve E.q).j = E.j := by
  have hw : valuation k E.j⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ E.one_lt_valuation_j
  have hq_eq : E.q = evalInt E.j⁻¹ jInvReverse := tateParameter_eq
  refine inv_inj.mp ?_
  rw [← evalInt_jInv E.q E.valuation_q_lt_one, hq_eq,
    evalInt_subst E.j⁻¹ hw jInv jInvReverse constantCoeff_jInvReverse,
    jInv_subst_jInvReverse, evalInt_X]

/-! ## B0: `tateCurve E.q` has split multiplicative reduction -/

open Polynomial IsLocalRing in
/-- **B0.** The Tate curve of the Tate parameter has split multiplicative reduction: it is
minimal (`|c₄| = 1`), has `|Δ| < 1`, and its reduction is the split nodal cubic `y² + xy = x³`
(tangent-cone quadratic `X² + X = X(X + 1)`). -/
instance : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[k] := by
  haveI hInt : IsIntegral 𝒪[k] (tateCurve E.q) :=
    isIntegral_tateCurve E.q E.valuation_q_lt_one
  have hc₄adic :
      (IsDiscreteValuationRing.maximalIdeal 𝒪[k]).valuation k (tateCurve E.q).c₄ = 1 := by
    have hk : valuation k (tateCurve E.q).c₄ = 1 :=
      valuation_tateCurve_c₄ E.q E.valuation_q_lt_one
    rw [← integralModel_c₄_eq 𝒪[k] (tateCurve E.q)] at hk ⊢
    exact adicValuation_eq_one_iff.mpr hk
  have hΔadic :
      (IsDiscreteValuationRing.maximalIdeal 𝒪[k]).valuation k (tateCurve E.q).Δ < 1 := by
    have hk : valuation k (tateCurve E.q).Δ < 1 :=
      valuation_tateCurve_Δ_lt_one E.q E.q_ne_zero E.valuation_q_lt_one
    rw [← integralModel_Δ_eq 𝒪[k] (tateCurve E.q)] at hk ⊢
    exact adicValuation_lt_one_iff.mpr hk
  refine
    { toHasMultiplicativeReduction :=
        { toIsMinimal := isMinimal_of_valuation_c₄_eq_one 𝒪[k] (tateCurve E.q) hc₄adic
          badReduction := hΔadic
          multiplicativeReduction := hc₄adic }
      splitMultiplicativeReduction := ?_ }
  set I := integralModel 𝒪[k] (tateCurve E.q) with hIdef
  set r := algebraMap 𝒪[k] (ResidueField 𝒪[k]) with hr_def
  have res0 : ∀ x : 𝒪[k], valuation k (algebraMap 𝒪[k] k x) < 1 → r x = 0 := by
    intro x hx
    rw [hr_def, ResidueField.algebraMap_eq, residue_eq_zero_iff, mem_maximalIdeal,
      mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  have ha₁ : r I.a₁ = 1 := by
    rw [show I.a₁ = 1 from IsFractionRing.injective 𝒪[k] k
      (by rw [hIdef, integralModel_a₁_eq, map_one]; rfl), map_one]
  have ha₂ : r I.a₂ = 0 := by
    rw [show I.a₂ = 0 from IsFractionRing.injective 𝒪[k] k
      (by rw [hIdef, integralModel_a₂_eq, map_zero]; rfl), map_zero]
  have ha₃ : r I.a₃ = 0 := by
    rw [show I.a₃ = 0 from IsFractionRing.injective 𝒪[k] k
      (by rw [hIdef, integralModel_a₃_eq, map_zero]; rfl), map_zero]
  have ha₄ : r I.a₄ = 0 := res0 _ (by
    rw [hIdef, integralModel_a₄_eq]
    exact (valuation_tateA₄_le E.q E.valuation_q_lt_one).trans_lt E.valuation_q_lt_one)
  have ha₆ : r I.a₆ = 0 := res0 _ (by
    rw [hIdef, integralModel_a₆_eq]
    exact (valuation_tateA₆_le E.q E.valuation_q_lt_one).trans_lt E.valuation_q_lt_one)
  have hpoly : Polynomial.map r
      (C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X
        - C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) = X * (X + C 1) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, map_add, map_sub, map_mul,
      map_pow, map_ofNat, ha₁, ha₂, ha₃, ha₄, ha₆, map_one, map_zero]
    ring
  rw [hpoly]
  exact Splits.X.mul (Splits.X_add_C 1)

/-! ## The characteristic-uniform descent

The remaining step — that two split-multiplicative curves with the same `j` are
`k`-isomorphic — reduces to two general facts about quadratic twists, **(a)** and **(c)**
below, together with the twist dichotomy of `QuadraticTwists`. -/

/-! ### Interface: quadratic-twist facts from FLT PR #1088

The reduction-theoretic inputs to the descent, stated as sorried statements pointing to FLT
PR #1088 (branch `MichaelStollBayreuth:MS_quadratic_twists_1`), so that the descent can be
built on them. Two more inputs already live (sorried) in `QuadraticTwists`: the dichotomy
`exists_smul_eq_or_exists_smul_eq_quadraticTwist`
(PR #1088 `QuadraticTwists/QuadraticTwists.lean:547`) and
`exists_quadraticTwist_hasSplitMultiplicativeReduction`
(PR #1088 `QuadraticTwists/SplitMultiplicativeReduction.lean:404`). -/

/-- **[PR #1088]** `FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean:425`. Split
multiplicative reduction transfers along a `k`-isomorphism of *minimal* models (reduction
type is intrinsic; a split curve is minimal, so this is the isomorphism-invariance used
below). -/
theorem HasSplitMultiplicativeReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve k}
    [IsMinimal 𝒪[k] W₁] [IsMinimal 𝒪[k] W₂] [W₁.IsElliptic] (D : VariableChange k)
    (hD : D • W₁ = W₂) (h₁ : W₁.HasSplitMultiplicativeReduction 𝒪[k]) :
    W₂.HasSplitMultiplicativeReduction 𝒪[k] :=
  sorry

/-- **[PR #1088, converse of `exists_quadraticTwist_hasSplitMultiplicativeReduction`].** A
curve `k`-isomorphic to a quadratic twist of a split-multiplicative curve does not have split
multiplicative reduction — a quadratic twist of a split-multiplicative curve is never split
(twisting by the unramified quadratic extension gives nonsplit multiplicative reduction, a
ramified quadratic twist gives additive reduction; both residue characteristics).

Provable from `exists_quadraticTwist_hasSplitMultiplicativeReduction`
(PR #1088 `QuadraticTwists/SplitMultiplicativeReduction.lean:404`), the residue split criteria
`nodePoly_map_splits_iff_isSquare` (char `≠ 2`, `Reduction.lean:144`) /
`nodePoly_map_splits_iff_of_two_eq_zero` (char `2`, `Reduction.lean:156`), and
`of_isMinimal_smul` above; it is not exposed as a standalone lemma in PR #1088. -/
theorem not_hasSplitMultiplicativeReduction_quadraticTwist (W : WeierstrassCurve k)
    [W.IsElliptic] [W.HasSplitMultiplicativeReduction 𝒪[k]] (L : Type u) [Field L] [Algebra k L]
    [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] (W' : WeierstrassCurve k)
    [W'.IsElliptic] (C : VariableChange k) (hC : C • W' = W.quadraticTwist L) :
    ¬ W'.HasSplitMultiplicativeReduction 𝒪[k] :=
  sorry

-- The negation automorphism `negVariableChange = ⟨-1, 0, -a₁, -a₃⟩`, its stability lemmas
-- (`negVariableChange_smul`, `map_negVariableChange`), and the full classification
-- `smul_eq_self_iff` — `Aut(E) = {±1}` for `c₄, c₆ ≠ 0`, in every characteristic — live in
-- `FLT.KnownIn1980s.EllipticCurves.MaybeMathlib` (imported above).

/-- For `j ∉ {0, 1728}`, the only admissible changes of variables fixing `E` are `1` and
`[-1]`; that is, `Aut(E) = {±1}` (Silverman, AEC III.10.1, in every characteristic). This
is `smul_eq_self_iff` fed the nonvanishing of `c₄` and `c₆`: `j ≠ 0` forces `c₄ ≠ 0` since
`j = Δ'⁻¹c₄³`, and `j ≠ 1728` forces `c₆ ≠ 0` since `c₆ = 0` gives `c₄³ = 1728Δ` by
`c_relation`, whence `j = 1728`. -/
theorem eq_one_or_eq_negVariableChange_of_smul_eq {F : Type*} [Field F] (E : WeierstrassCurve F)
    [E.IsElliptic] (hj₀ : E.j ≠ 0) (hj₁₇₂₈ : E.j ≠ 1728) {C : VariableChange F} (hC : C • E = E) :
    C = 1 ∨ C = E.negVariableChange := by
  have hc₄ : E.c₄ ≠ 0 := by
    intro h0
    exact hj₀ (by rw [show E.j = (↑(E.Δ'⁻¹) : F) * E.c₄ ^ 3 from rfl, h0]; ring)
  have hc₆ : E.c₆ ≠ 0 := by
    intro h0
    have hc₄3 : E.c₄ ^ 3 = 1728 * E.Δ := by linear_combination -E.c_relation + E.c₆ * h0
    exact hj₁₇₂₈ (by
      rw [show E.j = (↑(E.Δ'⁻¹) : F) * E.c₄ ^ 3 from rfl, hc₄3, ← E.coe_Δ', mul_left_comm,
        Units.inv_mul, mul_one])
  exact (smul_eq_self_iff hc₄ hc₆).mp hC

-- Base change preserves ellipticity: `baseChange` is `map` along the `algebraMap`, but the
-- mathlib instance for `map` does not transfer through the definitional unfolding
-- automatically.
instance {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

/-! #### The Galois descent of the field of definition

The isomorphism from **(a)** exists over `Ω := SeparableClosure k`; the two sorries below carry
it down to the (at most separable-quadratic) field of definition. They split the classical
`H¹(Gal(Ω/k), {±1})` argument into (1) *the sign character* — the stabiliser of the isomorphism
under the Galois action is a finite-index subgroup — and (2) *fixed field + descent* — that
subgroup's fixed field is `k` or a separable quadratic extension, over which the isomorphism
descends. This route is **characteristic-uniform**: it never divides by `2`, so it covers equal
characteristic `2` (an Artin–Schreier extension) on the same footing as the Kummer case. -/

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **[Galois-cohomology core — the sign character].** For `j ∉ {0, 1728}`, the stabiliser of the
isomorphism `C` (over `Ω := SeparableClosure k`, from `C • W₁^Ω = W₂^Ω`) under the Galois action
`σ • C = C.map σ` is a subgroup of index `≤ 2`.

For `σ ∈ Gal(Ω/k)`, applying `σ` to `C • W₁^Ω = W₂^Ω` gives `σ(C) • W₁^Ω = W₂^Ω`
(`map_variableChange`, using that `W₁, W₂` are defined over `k`), so `C⁻¹ · σ(C) ∈ Aut(W₁^Ω)`.
By `Aut(E) = {1, [-1]}` (`smul_eq_self_iff`), `σ ↦ (C⁻¹ · σ(C))` is a homomorphism
`ε : Gal(Ω/k) → {±1} ≅ ℤ/2` — a homomorphism because `{1, [-1]}` is defined over `k`, so `Gal`
acts trivially on it — whose kernel is the stabiliser. Hence the stabiliser has index `≤ 2`.
Proved here (on top of `eq_one_or_eq_negVariableChange_of_smul_eq`, the
`Aut = {±1}` lemma) as `ker a` for the sign homomorphism `a`. -/
theorem exists_stabilizer_index_le_two (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    (hj₀ : W₁.j ≠ 0) (hj₁₇₂₈ : W₁.j ≠ 1728) (C : VariableChange (SeparableClosure k))
    (hC : C • W₁.baseChange (SeparableClosure k) = W₂.baseChange (SeparableClosure k)) :
    ∃ H : Subgroup (SeparableClosure k ≃ₐ[k] SeparableClosure k), H.index ≠ 0 ∧ H.index ≤ 2 ∧
      ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        σ ∈ H ↔ C.map σ.toAlgHom.toRingHom = C := by
  set Ω := SeparableClosure k with hΩ
  -- (0) The base changes `W₁^Ω`, `W₂^Ω` are Galois-invariant (their coefficients are in `k`).
  have hWinv : ∀ (W : WeierstrassCurve k) (σ : Ω ≃ₐ[k] Ω),
      (W.baseChange Ω).map σ.toAlgHom.toRingHom = W.baseChange Ω := by
    intro W σ
    have hc : σ.toAlgHom.toRingHom.comp (algebraMap k Ω) = algebraMap k Ω := by
      ext x; simp
    rw [show W.baseChange Ω = W.map (algebraMap k Ω) from rfl, WeierstrassCurve.map_map, hc]
  -- (1) Each Galois conjugate `C.map σ` is again an isomorphism `W₁^Ω → W₂^Ω`.
  have hCσ : ∀ σ : Ω ≃ₐ[k] Ω,
      C.map σ.toAlgHom.toRingHom • W₁.baseChange Ω = W₂.baseChange Ω := by
    intro σ
    have h := map_variableChange (W := W₁.baseChange Ω) (C := C) (φ := σ.toAlgHom.toRingHom)
    rwa [hWinv W₁ σ, hC, hWinv W₂ σ] at h
  -- (2) Hence `a σ := C⁻¹ · (C.map σ)` is an automorphism of `W₁^Ω`.
  have haAut : ∀ σ : Ω ≃ₐ[k] Ω,
      (C⁻¹ * C.map σ.toAlgHom.toRingHom) • W₁.baseChange Ω = W₁.baseChange Ω := by
    intro σ
    rw [mul_smul, hCσ σ, ← hC, inv_smul_smul]
  -- `j ∉ {0, 1728}` transfers to `Ω`.
  have hjeq : (W₁.baseChange Ω).j = algebraMap k Ω W₁.j := by
    change (W₁.map (algebraMap k Ω)).j = _; rw [map_j]
  have hjΩ₀ : (W₁.baseChange Ω).j ≠ 0 := by
    rw [hjeq, ne_eq, map_eq_zero_iff _ (algebraMap k Ω).injective]; exact hj₀
  have hjΩ₁₇₂₈ : (W₁.baseChange Ω).j ≠ 1728 := by
    rw [hjeq]
    have h1728 : (1728 : Ω) = algebraMap k Ω 1728 := by rw [map_ofNat]
    rw [h1728, ne_eq, (algebraMap k Ω).injective.eq_iff]; exact hj₁₇₂₈
  -- (3) By `Aut(W₁^Ω) = {1, [-1]}`, every `a σ` is `1` or `[-1]`.
  have haMem : ∀ σ : Ω ≃ₐ[k] Ω, C⁻¹ * C.map σ.toAlgHom.toRingHom = 1 ∨
      C⁻¹ * C.map σ.toAlgHom.toRingHom = (W₁.baseChange Ω).negVariableChange := fun σ =>
    eq_one_or_eq_negVariableChange_of_smul_eq (W₁.baseChange Ω) hjΩ₀ hjΩ₁₇₂₈ (haAut σ)
  -- (4) Each `a σ` is Galois-fixed, since `{1, [-1]}` is defined over `k`.
  have haFixed : ∀ σ τ : Ω ≃ₐ[k] Ω,
      (C⁻¹ * C.map τ.toAlgHom.toRingHom).map σ.toAlgHom.toRingHom
        = C⁻¹ * C.map τ.toAlgHom.toRingHom := by
    intro σ τ
    rcases haMem τ with h1 | hneg
    · rw [h1]; ext <;> simp [VariableChange.map, VariableChange.one_def]
    · rw [hneg, map_negVariableChange, hWinv W₁ σ]
  -- (5) Therefore `a : Gal(Ω/k) → VariableChange Ω` is a group homomorphism.
  have hmapmul : ∀ (X Y : VariableChange Ω) (φ : Ω →+* Ω),
      (X * Y).map φ = X.map φ * Y.map φ := by
    intro X Y φ; exact map_mul (VariableChange.mapHom (φ := φ)) X Y
  have hmul : ∀ σ τ : Ω ≃ₐ[k] Ω,
      C⁻¹ * C.map (σ * τ).toAlgHom.toRingHom
        = (C⁻¹ * C.map σ.toAlgHom.toRingHom) * (C⁻¹ * C.map τ.toAlgHom.toRingHom) := by
    intro σ τ
    have hcomp : (σ * τ).toAlgHom.toRingHom
        = σ.toAlgHom.toRingHom.comp τ.toAlgHom.toRingHom := by ext x; simp [AlgEquiv.mul_apply]
    have e1 : C.map (σ * τ).toAlgHom.toRingHom
        = (C.map τ.toAlgHom.toRingHom).map σ.toAlgHom.toRingHom := by
      rw [hcomp, VariableChange.map_map]
    rw [e1]
    have e2 : C.map τ.toAlgHom.toRingHom = C * (C⁻¹ * C.map τ.toAlgHom.toRingHom) := by group
    rw [e2, hmapmul, haFixed σ τ]; group
  let a : (Ω ≃ₐ[k] Ω) →* VariableChange Ω :=
    MonoidHom.mk' (fun σ => C⁻¹ * C.map σ.toAlgHom.toRingHom) hmul
  -- (6) The stabiliser is `ker a`, of index `= card (range a)`, and `range a ⊆ {1, [-1]}`.
  have hsub : (a.range : Set (VariableChange Ω))
      ⊆ {1, (W₁.baseChange Ω).negVariableChange} := by
    rintro x hx
    rw [SetLike.mem_coe, MonoidHom.mem_range] at hx
    obtain ⟨σ, rfl⟩ := hx
    exact haMem σ
  have hfin : (a.range : Set (VariableChange Ω)).Finite :=
    Set.Finite.subset ((Set.finite_singleton _).insert _) hsub
  haveI : Finite ↥a.range := hfin.to_subtype
  refine ⟨a.ker, ?_, ?_, fun σ => ?_⟩
  · rw [Subgroup.index_ker]
    haveI : Nonempty ↥a.range := ⟨⟨1, one_mem _⟩⟩
    exact Nat.card_pos.ne'
  · rw [Subgroup.index_ker]
    calc Nat.card a.range
        = (a.range : Set (VariableChange Ω)).ncard := (Nat.card_coe_set_eq _)
      _ ≤ ({1, (W₁.baseChange Ω).negVariableChange} : Set (VariableChange Ω)).ncard :=
          Set.ncard_le_ncard hsub ((Set.finite_singleton _).insert _)
      _ ≤ 2 := by
          have h := Set.ncard_insert_le (1 : VariableChange Ω)
            {(W₁.baseChange Ω).negVariableChange}
          simpa [Set.ncard_singleton] using h
  · rw [MonoidHom.mem_ker]
    change C⁻¹ * C.map σ.toAlgHom.toRingHom = 1 ↔ C.map σ.toAlgHom.toRingHom = C
    rw [inv_mul_eq_one]; exact eq_comm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **[Galois-cohomology core — fixed field and descent].** If the isomorphism `C` over
`Ω := SeparableClosure k` is stabilised by a subgroup `H ≤ Gal(Ω/k)` of index `≤ 2`, then the two
curves are isomorphic over `k` or over a separable quadratic extension.

Take `L := fixedField H`. Since `Ω/k` is Galois (`separableClosure.isGalois`) and `H` has index
`≤ 2`, `[L : k] ≤ 2` and `L/k` is separable (`L ⊆ Ω`). Each coordinate of `C` is `H`-fixed, hence
lies in `fixedField H = L` (`fixedField_fixingSubgroup`), so `C` is the base change of some
`C_L : VariableChange L` with `C_L • W₁^L = W₂^L`. If `L = k` this is the first disjunct; if
`[L : k] = 2` it is the second. -/
theorem exists_isom_of_stabilizer_index_le_two (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] (C : VariableChange (SeparableClosure k))
    (hC : C • W₁.baseChange (SeparableClosure k) = W₂.baseChange (SeparableClosure k))
    (H : Subgroup (SeparableClosure k ≃ₐ[k] SeparableClosure k)) (hHne : H.index ≠ 0)
    (hHi : H.index ≤ 2)
    (hHmem : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      σ ∈ H ↔ C.map σ.toAlgHom.toRingHom = C) :
    (∃ C : VariableChange k, C • W₁ = W₂) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsQuadraticExtension k L)
        (_ : Algebra.IsSeparable k L) (C : VariableChange L),
        C • W₂.baseChange L = W₁.baseChange L := by
  set Ω := SeparableClosure k with hΩ
  haveI : IsGalois k Ω := separableClosure.isGalois k (AlgebraicClosure k)
  haveI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr hHne
  -- The field of definition `L := fixedField H`, and its fixing subgroup contains `H`.
  set L := IntermediateField.fixedField H with hLdef
  have hHle : H ≤ L.fixingSubgroup := (IntermediateField.le_iff_le H L).mp le_rfl
  haveI : L.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_le hHle
  -- `[L : k] ≤ 2`, and `[L:k] ≠ 0` since `L.fixingSubgroup` has finite index.
  have hfr : Module.finrank k L ≤ 2 :=
    (IntermediateField.finrank_eq_fixingSubgroup_index L).le.trans
      ((Subgroup.index_antitone hHle).trans hHi)
  have hfrne : Module.finrank k L ≠ 0 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index L]
    exact Subgroup.FiniteIndex.index_ne_zero
  -- Every coordinate of `C` lies in `L` (it is `H`-fixed).
  have hcoordfix : ∀ x : Ω, (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ H → σ x = x) → x ∈ L := fun x hx =>
    (IntermediateField.mem_fixedField_iff H x).mpr hx
  have hmapfix : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ H →
      σ (C.u : Ω) = (C.u : Ω) ∧ σ C.r = C.r ∧ σ C.s = C.s ∧ σ C.t = C.t := by
    intro σ hσ
    have h := (hHmem σ).mp hσ
    have e := VariableChange.ext_iff.mp h
    exact ⟨congrArg (Units.val ·) e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  have huL : (C.u : Ω) ∈ L := hcoordfix _ fun σ hσ => (hmapfix σ hσ).1
  have hrL : C.r ∈ L := hcoordfix _ fun σ hσ => (hmapfix σ hσ).2.1
  have hsL : C.s ∈ L := hcoordfix _ fun σ hσ => (hmapfix σ hσ).2.2.1
  have htL : C.t ∈ L := hcoordfix _ fun σ hσ => (hmapfix σ hσ).2.2.2
  -- Package `C` as a change of variables `C_L` over `L`.
  have hune : (⟨(C.u : Ω), huL⟩ : L) ≠ 0 :=
    fun h => C.u.ne_zero (by simpa using Subtype.ext_iff.mp h)
  set CL : VariableChange L :=
    ⟨Units.mk0 _ hune, ⟨C.r, hrL⟩, ⟨C.s, hsL⟩, ⟨C.t, htL⟩⟩ with hCLdef
  -- `C_L` base-changes back to `C` along `L ↪ Ω`.
  have hCLmap : CL.map (algebraMap L Ω) = C := by
    rw [hCLdef]
    refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_ <;>
      (simp only [VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
        VariableChange.map_t, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0]; rfl)
  -- Base change `k → L → Ω` factors through `k → Ω`.
  have hbc : ∀ W : WeierstrassCurve k,
      (W.baseChange L).map (algebraMap L Ω) = W.map (algebraMap k Ω) := by
    intro W
    rw [show W.baseChange L = W.map (algebraMap k L) from rfl, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq]
  -- `C_L • W₁^L = W₂^L`, checked after the injective base change to `Ω`.
  have hCLiso : CL • W₁.baseChange L = W₂.baseChange L := by
    apply WeierstrassCurve.map_injective (f := algebraMap L Ω) (algebraMap L Ω).injective
    change (CL • W₁.baseChange L).map (algebraMap L Ω)
      = (W₂.baseChange L).map (algebraMap L Ω)
    rw [← WeierstrassCurve.map_variableChange, hCLmap, hbc W₁, hbc W₂]
    exact hC
  -- Dichotomy on `[L : k]`.
  rcases (Nat.lt_or_ge (Module.finrank k L) 2) with hlt | hge
  · -- `finrank ≤ 1`, so `L = ⊥ = k`: the coordinates lie in `k`, so `C` descends to `k`.
    left
    have hfr1 : Module.finrank k L = 1 := by omega
    have hLbot : L = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfr1
    obtain ⟨u₀, hu₀⟩ := IntermediateField.mem_bot.mp (hLbot ▸ huL)
    obtain ⟨r₀, hr₀⟩ := IntermediateField.mem_bot.mp (hLbot ▸ hrL)
    obtain ⟨s₀, hs₀⟩ := IntermediateField.mem_bot.mp (hLbot ▸ hsL)
    obtain ⟨t₀, ht₀⟩ := IntermediateField.mem_bot.mp (hLbot ▸ htL)
    have hu₀ne : u₀ ≠ 0 := fun h => C.u.ne_zero (by rw [← hu₀, h, map_zero])
    set Ck : VariableChange k := ⟨Units.mk0 u₀ hu₀ne, r₀, s₀, t₀⟩ with hCkdef
    have hCkmap : Ck.map (algebraMap k Ω) = C := by
      rw [hCkdef]
      refine VariableChange.ext (Units.ext ?_) ?_ ?_ ?_ <;>
        simp only [VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
          VariableChange.map_t, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0]
      exacts [hu₀, hr₀, hs₀, ht₀]
    refine ⟨Ck, ?_⟩
    apply WeierstrassCurve.map_injective (f := algebraMap k Ω) (algebraMap k Ω).injective
    change (Ck • W₁).map (algebraMap k Ω) = W₂.map (algebraMap k Ω)
    rw [← WeierstrassCurve.map_variableChange, hCkmap]
    exact hC
  · -- `finrank = 2`: `L` is a separable quadratic extension.
    right
    have hfr2 : Module.finrank k L = 2 := le_antisymm hfr hge
    haveI : Algebra.IsSeparable k L := Algebra.isSeparable_tower_bot_of_isSeparable k L Ω
    haveI : Algebra.IsQuadraticExtension k L := ⟨hfr2⟩
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, CL⁻¹,
      by rw [inv_smul_eq_iff, hCLiso]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The descent of an isomorphism from the separable closure to its field of definition — the
input to **(a)** beyond mathlib's `exists_variableChange_of_j_eq`. Assembled from the two
Galois-cohomology lemmas above (`exists_stabilizer_index_le_two`, the sign character, and
`exists_isom_of_stabilizer_index_le_two`, fixed field + descent), both now proved modulo the
`Aut = {±1}` interface lemma. Characteristic-uniform. -/
theorem exists_isom_baseChange_of_isom_separableClosure (W₁ W₂ : WeierstrassCurve k)
    [W₁.IsElliptic] [W₂.IsElliptic] (hj₀ : W₁.j ≠ 0) (hj₁₇₂₈ : W₁.j ≠ 1728)
    (h : ∃ C : VariableChange (SeparableClosure k),
      C • W₁.baseChange (SeparableClosure k) = W₂.baseChange (SeparableClosure k)) :
    (∃ C : VariableChange k, C • W₁ = W₂) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsQuadraticExtension k L)
        (_ : Algebra.IsSeparable k L) (C : VariableChange L),
        C • W₂.baseChange L = W₁.baseChange L := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨H, hHne, hHi, hHmem⟩ := exists_stabilizer_index_le_two W₁ W₂ hj₀ hj₁₇₂₈ C hC
  exact exists_isom_of_stabilizer_index_le_two W₁ W₂ C hC H hHne hHi hHmem

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **(a).** Two elliptic curves over `k` with the same `j ∉ {0, 1728}` are isomorphic over `k`
or over a *separable quadratic* extension `L/k`. Assembled from mathlib's char-uniform
`exists_variableChange_of_j_eq` (the isomorphism over `SeparableClosure k`) and
`exists_isom_baseChange_of_isom_separableClosure` (the descent to the quadratic field of
definition). The whole descent is now proved modulo the `Aut = {±1}` interface lemma
`eq_one_or_eq_negVariableChange_of_smul_eq`. (Silverman, AEC X.5.) -/
theorem exists_isom_baseChange_of_j_eq (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] (hj₀ : W₁.j ≠ 0) (hj₁₇₂₈ : W₁.j ≠ 1728) (hj : W₁.j = W₂.j) :
    (∃ C : VariableChange k, C • W₁ = W₂) ∨
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsQuadraticExtension k L)
        (_ : Algebra.IsSeparable k L) (C : VariableChange L),
        C • W₂.baseChange L = W₁.baseChange L := by
  refine exists_isom_baseChange_of_isom_separableClosure W₁ W₂ hj₀ hj₁₇₂₈ ?_
  exact exists_variableChange_of_j_eq (E := W₁.baseChange (SeparableClosure k))
    (E' := W₂.baseChange (SeparableClosure k)) (by
      change (W₁.map (algebraMap k (SeparableClosure k))).j
        = (W₂.map (algebraMap k (SeparableClosure k))).j
      rw [map_j, map_j, hj])

/-- `W₂` is a *quadratic-twist form* of `W₁`: `k`-isomorphic to the quadratic twist of `W₁` by
some separable quadratic extension `L/k`. Packaging the extension inside a predicate keeps it
out of the way in the descent (it is unpacked only inside the proofs of `(a′)` and `(c)`). -/
def IsQuadraticTwistForm (W₁ W₂ : WeierstrassCurve k) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : Algebra.IsQuadraticExtension k L)
    (_ : Algebra.IsSeparable k L) (C : VariableChange k), C • W₂ = W₁.quadraticTwist L

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- **(a′).** Same `j ∉ {0, 1728}` ⟹ `k`-isomorphic, or `W₂` is a quadratic-twist form of
`W₁`. Proved from **(a)** and the twist **dichotomy**
`exists_smul_eq_or_exists_smul_eq_quadraticTwist` (PR #1088
`QuadraticTwists/QuadraticTwists.lean:547`); separated out only to feed the descent without
shuffling the extension `L` and its instances by hand (that stays inside this proof). -/
theorem exists_isom_or_isQuadraticTwistForm_of_j_eq (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] (hj₀ : W₁.j ≠ 0) (hj₁₇₂₈ : W₁.j ≠ 1728) (hj : W₁.j = W₂.j) :
    (∃ C : VariableChange k, C • W₁ = W₂) ∨ IsQuadraticTwistForm W₁ W₂ := by
  rcases exists_isom_baseChange_of_j_eq W₁ W₂ hj₀ hj₁₇₂₈ hj with hiso | ⟨L, hF, hA, hQ, hS, ρ, hρ⟩
  · exact Or.inl hiso
  · -- feed the obtained extension and its instances to the dichotomy explicitly (`@`), to
    -- avoid re-synthesising the `CommRing L` diamond
    rcases @exists_smul_eq_or_exists_smul_eq_quadraticTwist k _ W₁ _ L hF hA hQ hS hj₀ hj₁₇₂₈
      W₂ _ ⟨ρ, hρ⟩ with ⟨C, hC⟩ | ⟨C, hC⟩
    · exact Or.inl ⟨C⁻¹, by rw [← hC]; exact inv_smul_smul C W₂⟩
    · exact Or.inr ⟨L, hF, hA, hQ, hS, C, hC⟩

/-- **(c).** A quadratic-twist form of a split-multiplicative curve does not have split
multiplicative reduction. Immediate from `not_hasSplitMultiplicativeReduction_quadraticTwist`
(the PR #1088 arithmetic core, both residue characteristics) after unpacking the twisting
extension from `IsQuadraticTwistForm`. -/
theorem not_hasSplitMultiplicativeReduction_of_isQuadraticTwistForm (W₁ W₂ : WeierstrassCurve k)
    [W₁.IsElliptic] [W₂.IsElliptic] [W₁.HasSplitMultiplicativeReduction 𝒪[k]]
    (h : IsQuadraticTwistForm W₁ W₂) :
    ¬ W₂.HasSplitMultiplicativeReduction 𝒪[k] := by
  obtain ⟨L, hF, hA, hQ, hS, C, hC⟩ := h
  exact @not_hasSplitMultiplicativeReduction_quadraticTwist k _ _ _ _ W₁ _ _ L hF hA hQ hS W₂ _ C hC

/-- **Characteristic-uniform descent.** Two elliptic curves over a nonarchimedean local field
with the same `j`-invariant and both split multiplicative are `k`-isomorphic — with **no**
hypothesis on the characteristic of `k` or its residue field.

Proof: `j ∉ {0, 1728}` (split reduction forces `1 < |j|`, while `|0|, |1728| ≤ 1`). By **(a′)**
they are `k`-isomorphic (done) or `W₂` is a quadratic-twist form of `W₁`; the latter is
impossible because `W₂` is split while a quadratic twist of the split `W₁` is not (**(c)**). -/
theorem exists_variableChange_of_splitMult (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic]
    [W₂.IsElliptic] [W₁.HasSplitMultiplicativeReduction 𝒪[k]]
    [W₂.HasSplitMultiplicativeReduction 𝒪[k]] (hj : W₁.j = W₂.j) :
    ∃ C : VariableChange k, C • W₁ = W₂ := by
  have hj₀ : W₁.j ≠ 0 :=
    (valuation k).ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans W₁.one_lt_valuation_j))
  have hj₁₇₂₈ : W₁.j ≠ 1728 := fun h ↦ absurd (h ▸ W₁.one_lt_valuation_j)
    (not_lt.mpr (by simpa using valuation_intCast_le_one (R := k) 1728))
  rcases exists_isom_or_isQuadraticTwistForm_of_j_eq W₁ W₂ hj₀ hj₁₇₂₈ hj with hiso | htw
  · exact hiso
  · exact absurd ‹W₂.HasSplitMultiplicativeReduction 𝒪[k]›
      (not_hasSplitMultiplicativeReduction_of_isQuadraticTwistForm W₁ W₂ htw)

/-- **Tate's theorem (Silverman, ATAEC V.5.3), characteristic-uniform.** An elliptic curve
`E` with split multiplicative reduction is isomorphic, by a change of Weierstrass
coordinates, to the Tate curve of its Tate parameter — with no characteristic hypothesis.
Feed `j_tateCurve_q` (Half A) to `exists_variableChange_of_splitMult`; the Tate curve is
split multiplicative by `B0`. Downstream, `TateCurve` transports the uniformisation
`tateCurveEquiv` of `tateCurve E.q` along a choice of such a `C` to build `tateEquiv`. -/
theorem exists_variableChange_tateCurve (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    ∃ C : VariableChange k, C • tateCurve E.q = E :=
  exists_variableChange_of_splitMult (tateCurve E.q) E (j_tateCurve_q E)

/-- A choice of change of Weierstrass coordinates taking the Tate curve `E_{q(E)}` to
`E` (Silverman, ATAEC V.5.3). There are exactly two, differing by negation
(`WeierstrassCurve.smul_eq_self_iff`); this fixed choice, for each `E`, is the only
choice in the whole theory. -/
noncomputable def tateVariableChange (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] : VariableChange k :=
  E.exists_variableChange_tateCurve.choose

theorem tateVariableChange_smul (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    E.tateVariableChange • tateCurve E.q = E :=
  E.exists_variableChange_tateCurve.choose_spec

theorem tateVariableChange_inv_smul (E : WeierstrassCurve k) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction 𝒪[k]] :
    E.tateVariableChange⁻¹ • E = tateCurve E.q :=
  inv_smul_eq_iff.mpr E.tateVariableChange_smul.symm

end WeierstrassCurve
