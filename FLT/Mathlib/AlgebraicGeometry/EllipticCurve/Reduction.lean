/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.Algebra.Polynomial.QuadraticDiscriminant
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import FLT.Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

import Mathlib.Tactic.ComputeDegree

/-!
# Complements on reduction of elliptic curves

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`: the node polynomial and
its splitting criteria (answering the discriminant-characterization TODO there), a minimality
criterion via `c₄`, and uniqueness of minimal models (Silverman VII.1.3(b)): split
multiplicative reduction is an isomorphism invariant of minimal models.
-/

@[expose] public section

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

section Reduction

variable (R : Type u) [CommRing R] [Algebra R K]

/-- The **node polynomial** `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose roots are the
slopes of the two tangent directions at the node of a multiplicative reduction; its splitting over
the residue field governs whether the reduction is split (see `HasSplitMultiplicativeReduction`). -/
noncomputable def nodePoly {A : Type*} [CommRing A] (W : WeierstrassCurve A) : Polynomial A :=
  .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The node polynomial base-changed along a ring homomorphism. -/
lemma nodePoly_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    W.nodePoly.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      - .C (φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [nodePoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]

/-- The node polynomial is natural in the coefficient ring: it commutes with base change of the
Weierstrass equation along any ring homomorphism, since every coefficient is a polynomial in the
`aᵢ` and `Polynomial.map` is a ring homomorphism on each. -/
lemma map_nodePoly {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    (W.map φ).nodePoly = W.nodePoly.map φ := by
  simp only [nodePoly, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁, WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_a₂, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_ofNat, map_add, map_sub, map_mul, map_ofNat]

/-- The root of the (base-changed) node polynomial satisfies its defining quadratic relation. -/
lemma aeval_root_nodePoly_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    algebraMap B (AdjoinRoot (W.nodePoly.map φ)) (φ W.c₄) * AdjoinRoot.root (W.nodePoly.map φ) ^ 2
      + algebraMap B (AdjoinRoot (W.nodePoly.map φ)) (φ (W.a₁ * W.c₄))
        * AdjoinRoot.root (W.nodePoly.map φ)
      - algebraMap B (AdjoinRoot (W.nodePoly.map φ))
        (φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) = 0 := by
  have h := congrArg (Polynomial.aeval (AdjoinRoot.root (W.nodePoly.map φ))) (nodePoly_map φ W)
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self] at h
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    using h.symm

/-- The reduced node polynomial, presented as a quadratic with an additive constant term — the
form consumed by the quadratic separability and splitting criteria. -/
lemma nodePoly_map_eq_quadratic {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    W.nodePoly.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      + .C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  rw [nodePoly_map, map_neg, sub_eq_add_neg]

/-- The image of the discriminant identity `splitPolynomial_discrim` under a ring homomorphism,
in the shape produced by the quadratic criteria applied to `nodePoly_map_eq_quadratic`. -/
lemma map_splitPolynomial_discrim {A : Type*} [CommRing A] {B : Type*} [CommRing B] (φ : A →+* B)
    (W : WeierstrassCurve A) :
    φ (W.a₁ * W.c₄) ^ 2 - 4 * φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = φ (-(W.c₄ * W.c₆)) := by
  rw [mul_neg, sub_neg_eq_add, ← map_pow, ← map_ofNat φ 4, ← map_mul, ← map_mul, ← map_add]
  exact congrArg φ W.splitPolynomial_discrim

/-- Under a change of variables `C = (u, r, s, t)`, the node polynomial transforms by the affine
substitution `T ↦ u T + s` and the unit scalar `u⁻⁶` — reflecting that the tangent slopes `λ`
transform as `λ ↦ (λ - s)/u`. In particular its splitting field is unchanged. -/
lemma nodePoly_smul {A : Type*} [CommRing A] (W : WeierstrassCurve A) (C : VariableChange A) :
    (C • W).nodePoly = .C ((↑C.u⁻¹ : A) ^ 6)
      * W.nodePoly.comp (.C (↑C.u : A) * .X + .C C.s) := by
  have e2 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) ^ 2 = (↑C.u⁻¹ : A) ^ 4 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u ^ 2 = C.u⁻¹ ^ 4)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e1 : (↑C.u⁻¹ : A) ^ 6 * (↑C.u : A) = (↑C.u⁻¹ : A) ^ 5 := by
    have := congrArg (Units.val (α := A)) (by group : C.u⁻¹ ^ 6 * C.u = C.u⁻¹ ^ 5)
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have e2p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * (algebraMap A (Polynomial A) ↑C.u) ^ 2
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 4 := by
    rw [← map_pow, ← map_pow, ← map_mul, e2, map_pow]
  have e1p : (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 6 * algebraMap A (Polynomial A) ↑C.u
      = (algebraMap A (Polynomial A) (↑C.u⁻¹ : A)) ^ 5 := by
    rw [← map_pow, ← map_mul, e1, map_pow]
  simp only [nodePoly, c₄, variableChange_a₁, variableChange_a₂, variableChange_b₂,
    variableChange_b₄, variableChange_b₆, Polynomial.mul_comp, Polynomial.add_comp,
    Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, pow_two, mul_add, add_mul,
    mul_sub, sub_mul]
  simp only [Polynomial.C_eq_algebraMap, map_mul, map_pow, map_sub, map_add, map_ofNat]
  linear_combination
    (-(algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
        Polynomial.X ^ 2) * e2p +
    (-(2 * (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄) *
            algebraMap A (Polynomial A) C.s +
          algebraMap A (Polynomial A) W.a₁ *
            (algebraMap A (Polynomial A) W.b₂ ^ 2 - 24 * algebraMap A (Polynomial A) W.b₄)) *
        Polynomial.X) * e1p

/-- **Invariance of the node polynomial's splitting under change of variables.** Since a change of
variables transforms the node polynomial by an affine substitution and a nonzero scalar
(`nodePoly_smul`), whether it splits over a field `k` is unchanged. This is what makes split
multiplicative reduction an isomorphism invariant. -/
lemma nodePoly_map_splits_smul_iff {A : Type*} [CommRing A] {k : Type*} [Field k] (φ : A →+* k)
    (W : WeierstrassCurve A) (C : VariableChange A) :
    ((C • W).nodePoly.map φ).Splits ↔ (W.nodePoly.map φ).Splits := by
  have hu : φ (↑C.u : A) ≠ 0 := (RingHom.isUnit_map φ C.u.isUnit).ne_zero
  have hu6 : φ ((↑C.u⁻¹ : A) ^ 6) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 6 (RingHom.isUnit_map φ C.u⁻¹.isUnit).ne_zero
  rw [nodePoly_smul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_C,
    Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hu6) (Polynomial.Splits.C _)]
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (Polynomial.natDegree_linear hu)).symm

open Polynomial in
/-- **Split criterion (residue characteristic ≠ 2).** Over a field `k` of characteristic `≠ 2`, the
node polynomial splits — i.e. the two tangent directions at the node are `k`-rational — exactly when
its discriminant `-c₄ c₆` (`splitPolynomial_discrim`) is a square in `k`. This is the tool that,
applied to a quadratic twist via the scaling `-c₄' c₆' = (t²-4n)⁵ · (-c₄ c₆)`, turns a nonsplit
reduction into a split one after twisting by the right square class. -/
lemma nodePoly_map_splits_iff_isSquare {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ IsSquare (φ (-(W.c₄ * W.c₆))) := by
  rw [nodePoly_map_eq_quadratic, Polynomial.splits_quadratic_iff hc₄, discrim,
    map_splitPolynomial_discrim]

open Polynomial in
/-- **Split criterion (residue characteristic 2).** Over a field `k` of characteristic `2`, where
the square-class criterion `nodePoly_map_splits_iff_isSquare` fails, the node polynomial splits
exactly when its Artin–Schreier invariant lies in the image of `z ↦ z² + z`. Here `c₄` and `c₆` are
units, and separability (`b² = -c₄ c₆ ≠ 0`, since `4 = 0`) forces the linear coefficient
`a₁ c₄` to be nonzero, so `splits_quadratic_iff_of_two_eq_zero` applies. -/
lemma nodePoly_map_splits_iff_of_two_eq_zero {A : Type*} [CommRing A] {k : Type*} [Field k]
    (h2 : (2 : k) = 0) (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0)
    (hc₆ : φ W.c₆ ≠ 0) :
    (W.nodePoly.map φ).Splits ↔ ∃ z, φ (W.a₁ * W.c₄) ^ 2 * (z ^ 2 + z)
      = φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  have hb : φ (W.a₁ * W.c₄) ≠ 0 := by
    have h4 : (4 : k) = 0 := by linear_combination (2 : k) * h2
    have hAk := map_splitPolynomial_discrim φ W
    intro h0
    refine neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆) ?_
    rw [← map_mul, ← map_neg]
    linear_combination -hAk + φ (W.a₁ * W.c₄) * h0
      + φ W.c₄ * φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) * h4
  rw [nodePoly_map_eq_quadratic, Polynomial.splits_quadratic_iff_of_two_eq_zero h2 hc₄ hb]

variable [IsFractionRing R K]

/-- The integral model of the base change to `K` of an integral Weierstrass curve `W` over `R` is
`W` itself (integral models are unique, as `R → K` is injective). -/
lemma integralModel_baseChange (W : WeierstrassCurve R) [IsIntegral R (W⁄K)] :
    integralModel R (W⁄K) = W := by
  ext <;> apply IsFractionRing.injective R K <;>
    simp only [integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq,
      integralModel_a₆_eq, baseChange, map_a₁,
      map_a₂, map_a₃, map_a₄,
      map_a₆]

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **Split multiplicative reduction is a change-of-variables invariant.** If `W` (over `R`) gives a
curve with split multiplicative reduction over `K`, then so does any `R`-change of variables `C • W`
that still has multiplicative reduction — because the split condition is the splitting of the node
polynomial of the integral model, which is invariant by `nodePoly_map_splits_smul_iff`. -/
theorem HasSplitMultiplicativeReduction.baseChange_smul {W : WeierstrassCurve R}
    (C : VariableChange R) [IsMinimal R (W⁄K)]
    (hW : (W⁄K).HasSplitMultiplicativeReduction R)
    [((C • W)⁄K).HasMultiplicativeReduction R] :
    ((C • W)⁄K).HasSplitMultiplicativeReduction R := by
  have hspl := hW.splitMultiplicativeReduction
  rw [show ((W⁄K).integralModel R) = W from integralModel_baseChange R W] at hspl
  refine { ‹((C • W)⁄K).HasMultiplicativeReduction R› with splitMultiplicativeReduction := ?_ }
  rw [show (((C • W)⁄K).integralModel R) = C • W from integralModel_baseChange R (C • W)]
  exact (nodePoly_map_splits_smul_iff (algebraMap R (IsLocalRing.ResidueField R)) W C).mpr hspl

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- Multiplicative reduction forces `c₄` of the integral model to be a unit: its residue is nonzero
(`valuation c₄ = 1` means `c₄ ∉ maximalIdeal`). -/
lemma residue_integralModel_c₄_ne_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).c₄) ≠ 0 := by
  rw [Ne, residue_eq_zero_iff]
  have hval := ‹E.HasMultiplicativeReduction R›.multiplicativeReduction
  rw [← integralModel_c₄_eq R E, valuation_eq_one_iff_notMem] at hval
  exact hval

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- Multiplicative reduction (bad reduction) means the discriminant of the integral model has zero
residue. -/
lemma residue_integralModel_Δ_eq_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).Δ) = 0 := by
  rw [residue_eq_zero_iff]
  have hval := ‹E.HasMultiplicativeReduction R›.badReduction
  rw [← integralModel_Δ_eq R E, valuation_lt_one_iff_mem] at hval
  exact hval

open IsLocalRing in
/-- Multiplicative reduction forces `c₆` of the integral model to be a unit too: from
`1728 Δ = c₄³ - c₆²` and `Δ ≡ 0`, `c₆² ≡ c₄³ ≢ 0`. -/
lemma residue_integralModel_c₆_ne_zero [E.HasMultiplicativeReduction R] :
    residue R ((E.integralModel R).c₆) ≠ 0 := by
  intro h
  refine residue_integralModel_c₄_ne_zero E R ?_
  have key : residue R ((E.integralModel R).c₆) ^ 2
      = residue R ((E.integralModel R).c₄) ^ 3 - 1728 * residue R ((E.integralModel R).Δ) := by
    have h1 := congrArg (residue R) ((E.integralModel R).c_relation)
    simp only [map_mul, map_sub, map_pow, map_ofNat] at h1
    linear_combination h1
  rw [h, residue_integralModel_Δ_eq_zero E R, mul_zero, sub_zero, zero_pow (by norm_num)] at key
  exact (pow_eq_zero_iff (by norm_num)).mp key.symm

open IsLocalRing in
/-- Nonsplit multiplicative reduction means precisely that the node polynomial of the integral
model does not split over the residue field. -/
lemma not_splits_nodePoly_of_not_hasSplit [E.HasMultiplicativeReduction R]
    (h : ¬ E.HasSplitMultiplicativeReduction R) :
    ¬ ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).Splits :=
  fun hspl ↦ h { ‹E.HasMultiplicativeReduction R› with splitMultiplicativeReduction := hspl }

open IsLocalRing in
/-- The node polynomial over the residue field is a genuine quadratic (leading coefficient `c₄` is a
unit). -/
lemma natDegree_nodePoly_map [E.HasMultiplicativeReduction R] :
    ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).natDegree = 2 := by
  have ha : algebraMap R (ResidueField R) ((E.integralModel R).c₄) ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R
  rw [nodePoly_map_eq_quadratic]
  exact Polynomial.natDegree_quadratic ha

open IsLocalRing in
/-- For nonsplit multiplicative reduction, the node polynomial is irreducible over the residue
field: it is a quadratic that does not split, so (over a field) it has no linear factors. -/
lemma irreducible_nodePoly_map [E.HasMultiplicativeReduction R]
    (h : ¬ E.HasSplitMultiplicativeReduction R) :
    Irreducible ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))) := by
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hns := not_splits_nodePoly_of_not_hasSplit E R h
  have hdeg := natDegree_nodePoly_map E R
  rw [← hP] at hns hdeg
  have hP0 : P ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos P (by rw [hdeg]; norm_num), fun a b hab ↦ ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hna, hnb⟩ := hcon
  have ha0 : a ≠ 0 := fun h0 ↦ hP0 (by rw [hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 ↦ hP0 (by rw [hab, h0, mul_zero])
  have hsum : a.natDegree + b.natDegree = 2 := by rw [← hdeg, hab, Polynomial.natDegree_mul ha0 hb0]
  have hda := Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_ne_zero_of_nonunit ha0 hna)
  have hdb := Polynomial.natDegree_pos_iff_degree_pos.mpr
    (Polynomial.degree_pos_of_ne_zero_of_nonunit hb0 hnb)
  exact hns (hab ▸ (Polynomial.Splits.of_natDegree_le_one (by lia)).mul
    (Polynomial.Splits.of_natDegree_le_one (by lia)))

open IsLocalRing in
/-- For multiplicative reduction the node polynomial is separable over the residue field: its
discriminant is `-c₄ c₆` (`splitPolynomial_discrim`), a unit, so the quadratic-separability
criterion `Polynomial.separable_quadratic_iff` applies. -/
lemma separable_nodePoly_map [E.HasMultiplicativeReduction R] :
    ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))).Separable := by
  have ha : algebraMap R (ResidueField R) (E.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R
  -- Its discriminant is `-c₄ c₆` (`splitPolynomial_discrim`), a unit of the residue field.
  rw [nodePoly_map_eq_quadratic, Polynomial.separable_quadratic_iff ha,
    map_splitPolynomial_discrim, map_neg, map_mul, neg_ne_zero, mul_ne_zero_iff,
    ResidueField.algebraMap_eq]
  exact ⟨residue_integralModel_c₄_ne_zero E R, residue_integralModel_c₆_ne_zero E R⟩

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum in
/-- **Minimality criterion.** An integral Weierstrass equation over `K` whose `c₄` is a unit of `R`
(equivalently, `valuation c₄ = 1`) is already minimal: any change of variables `C` keeping the
equation integral must have `valuation C.u ≥ 1` (else `valuation (C • W).c₄ = valuation C.u⁻⁴ > 1`,
contradicting integrality), so `valuation (C • W).Δ = valuation C.u⁻¹² · valuation W.Δ ≤ valuation
W.Δ`. This is the tool that shows the twist `W` we build is minimal without minimising by hand.

This is the unit-`c₄` case of the Kraus–Laska criterion: the special case "`v(c₄) < 4` or
`v(Δ) < 12` implies minimal" of Silverman, *The Arithmetic of Elliptic Curves*, Remark VII.1.1,
restricted to `v(c₄) = 0`. The hypothesis is stated at the field level — via the adic valuation
of `W.c₄ : K` — to match mathlib's phrasing of `WeierstrassCurve.HasMultiplicativeReduction`,
whose `multiplicativeReduction` field is exactly `(maximalIdeal R).valuation K W.c₄ = 1`. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : valuation K (maximalIdeal R) (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hint
  simpa [variableChange_Δ, map_mul, map_pow] using mul_le_of_le_one_left'
    (pow_le_one' ((pow_le_one_iff (by norm_num)).mp hint) 12)

/-- For a minimal Weierstrass model `W`, no integral change of variables increases the valuation
of the discriminant. -/
theorem valuation_Δ_aux_smul_le {W : WeierstrassCurve K} [hm : IsMinimal R W]
    (D : VariableChange K) (hint : IsIntegral R (D • W)) :
    valuation_Δ_aux R (D • W) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W) :=
  (le_total (valuation_Δ_aux R ((1 : VariableChange K) • W)) (valuation_Δ_aux R (D • W))).elim
    (hm.val_Δ_maximal.2 hint) id

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- Two minimal Weierstrass models related by a change of variables have the same valuation of
the discriminant. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ := by
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁]
  refine le_antisymm (Subtype.coe_le_coe.mpr ?_) (Subtype.coe_le_coe.mpr ?_)
  · have hsub := valuation_Δ_aux_smul_le R D
      (show IsIntegral R (D • W₁) by rw [hD]; infer_instance)
    rwa [hD, one_smul] at hsub
  · have hW₁eq : W₁ = D⁻¹ • W₂ := by rw [← hD, inv_smul_smul]
    have hsub := valuation_Δ_aux_smul_le R D⁻¹
      (show IsIntegral R (D⁻¹ • W₂) by rw [← hW₁eq]; infer_instance)
    rwa [← hW₁eq, one_smul] at hsub

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- The scaling factor of a change of variables between two minimal models of an elliptic curve
has valuation `1`: the valuations of the discriminants agree and differ by a factor `v(u)⁻¹²`. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr W₁.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

/-- A change of variables `D` relating two integral Weierstrass models whose scaling factor `D.u`
is the image of a unit of `R` is itself defined over `R`: `r`, `s`, `t` are integral over `R` —
roots of monic polynomials obtained from the change-of-variables formulas for the
`b₆`/`b₈`/`a₂`/`a₆`-invariants — hence lie in `R` since `R` is integrally closed. -/
theorem exists_variableChange_baseChange_eq_of_smul_eq {W₁ W₂ : WeierstrassCurve K}
    [IsIntegral R W₁] [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
    (hau : algebraMap R K ↑u₀ = ↑D.u) : ∃ C₀ : VariableChange R, C₀.baseChange K = D := by
  have hune : (↑D.u : K) ≠ 0 := D.u.ne_zero
  -- `D.r ∈ R`: a root of the monic quartic `X⁴ - b₄ X² + (-2b₆ - u⁶b₆')X + (u⁸b₈' - b₈)` obtained
  -- as `r·P₃ - P₄` from the `b₆`- and `b₈`-relations.
  have hb₆ : (↑D.u : K) ^ 6 * W₂.b₆
      = W₁.b₆ + 2 * D.r * W₁.b₄ + D.r ^ 2 * W₁.b₂ + 4 * D.r ^ 3 := by
    rw [← hD, variableChange_b₆]
    simp only [Units.val_inv_eq_inv_val]
    field
  have hb₈ : (↑D.u : K) ^ 8 * W₂.b₈
      = W₁.b₈ + 3 * D.r * W₁.b₆ + 3 * D.r ^ 2 * W₁.b₄ + D.r ^ 3 * W₁.b₂ + 3 * D.r ^ 4 := by
    rw [← hD, variableChange_b₈]
    simp only [Units.val_inv_eq_inv_val]
    field
  obtain ⟨rR, hrR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (⟨.X ^ 4 + (.C (-(W₁.integralModel R).b₄) * .X ^ 2
        + .C (-(2 * (W₁.integralModel R).b₆) - (↑u₀ : R) ^ 6 * (W₂.integralModel R).b₆) * .X
        + .C ((↑u₀ : R) ^ 8 * (W₂.integralModel R).b₈ - (W₁.integralModel R).b₈)),
      Polynomial.monic_X_pow_add (by compute_degree!), by
        rw [← Polynomial.aeval_def]
        simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, Polynomial.aeval_X,
          Polynomial.aeval_C]
        rw [integralModel_b₄_eq R W₁, integralModel_b₆_eq R W₁, integralModel_b₈_eq R W₁,
          integralModel_b₆_eq R W₂, integralModel_b₈_eq R W₂, hau]
        linear_combination hb₈ - D.r * hb₆⟩ : _root_.IsIntegral R D.r)
  -- `D.s ∈ R`: a root of the monic quadratic `X² + a₁ X + (u²·a₂' - a₂ - 3r)`.
  have ha₂ : (↑D.u : K) ^ 2 * W₂.a₂ = W₁.a₂ - D.s * W₁.a₁ + 3 * D.r - D.s ^ 2 := by
    rw [← hD, variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val]
    field
  obtain ⟨sR, hsR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (⟨.X ^ 2 + (.C (W₁.integralModel R).a₁ * .X
        + .C ((↑u₀ : R) ^ 2 * (W₂.integralModel R).a₂ - (W₁.integralModel R).a₂ - 3 * rR)),
      Polynomial.monic_X_pow_add (by compute_degree!), by
        rw [← Polynomial.aeval_def]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X,
          Polynomial.aeval_C]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₂_eq R W₂, hau, hrR]
        linear_combination ha₂⟩ : _root_.IsIntegral R D.s)
  -- `D.t ∈ R`: a root of the monic quadratic
  -- `X² + (a₃ + r·a₁) X + (u⁶·a₆' - a₆ - r·a₄ - r²·a₂ - r³)`.
  have ha₆ : (↑D.u : K) ^ 6 * W₂.a₆ = W₁.a₆ + D.r * W₁.a₄ + D.r ^ 2 * W₁.a₂ + D.r ^ 3
      - D.t * W₁.a₃ - D.t ^ 2 - D.r * D.t * W₁.a₁ := by
    rw [← hD, variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val]
    field
  obtain ⟨tR, htR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (⟨.X ^ 2 + (.C ((W₁.integralModel R).a₃ + rR * (W₁.integralModel R).a₁) * .X
        + .C (-((W₁.integralModel R).a₆ + rR * (W₁.integralModel R).a₄
          + rR ^ 2 * (W₁.integralModel R).a₂ + rR ^ 3) + (↑u₀ : R) ^ 6 * (W₂.integralModel R).a₆)),
      Polynomial.monic_X_pow_add (by compute_degree!), by
        rw [← Polynomial.aeval_def]
        simp only [map_add, map_neg, map_mul, map_pow, Polynomial.aeval_X,
          Polynomial.aeval_C]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₃_eq R W₁,
          integralModel_a₄_eq R W₁, integralModel_a₆_eq R W₁, integralModel_a₆_eq R W₂, hau, hrR]
        linear_combination ha₆⟩ : _root_.IsIntegral R D.t)
  exact ⟨⟨u₀, rR, sR, tR⟩, VariableChange.ext (Units.ext hau) hrR hsR htR⟩

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing IsLocalRing in
/-- **Split multiplicative reduction is an isomorphism invariant of minimal models.** If two minimal
Weierstrass models `W₁`, `W₂` of an elliptic curve over `K` are related by a change of variables
(`D • W₁ = W₂`), and `W₁` has split multiplicative reduction, then so does `W₂`.

This is a form of Silverman VII.1.3(b) (uniqueness of minimal models over a discrete valuation
ring): the change `D` has `u ∈ Rˣ` (`valuation_u_eq_one_of_isMinimal_smul`), so it is defined over
`R` (`exists_variableChange_baseChange_eq_of_smul_eq`); then the node polynomial's splitting
transfers by `nodePoly_map_splits_smul_iff`. -/
theorem HasSplitMultiplicativeReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h₁ : W₁.HasSplitMultiplicativeReduction R) :
    W₂.HasSplitMultiplicativeReduction R := by
  -- `D.u` is the image of a unit of `R`, so `D` descends to `C₀ : VariableChange R`.
  have hvu := valuation_u_eq_one_of_isMinimal_smul R D hD
  obtain ⟨u₀, hau⟩ := exists_algebraMap_unit_eq_of_valuation_eq_one R hvu
  obtain ⟨C₀, hDC₀⟩ := exists_variableChange_baseChange_eq_of_smul_eq R D hD u₀ hau
  have hW₂eq : (C₀ • W₁.integralModel R)⁄K = W₂ := by
    rw [show ((C₀ • W₁.integralModel R)⁄K)
        = (C₀ • W₁.integralModel R).map (algebraMap R K) from rfl, ← map_variableChange,
      show C₀.map (algebraMap R K) = D from hDC₀,
      show (W₁.integralModel R).map (algebraMap R K) = W₁ from baseChange_integralModel_eq R W₁, hD]
  -- `W₂` has multiplicative reduction: `v(D.u) = 1` fixes the valuations of `Δ` and `c₄`.
  have hΔeq := valuation_Δ_eq_of_isMinimal_smul R D hD
  have hc₄eq : valuation K (maximalIdeal R) W₂.c₄ = valuation K (maximalIdeal R) W₁.c₄ := by
    rw [← hD, variableChange_c₄, map_mul]
    simp only [Units.val_inv_eq_inv_val, map_pow, map_inv₀, hvu, inv_one, one_pow, one_mul]
  have hmult₂ : W₂.HasMultiplicativeReduction R :=
    { badReduction := by rw [hΔeq]; exact h₁.toHasMultiplicativeReduction.badReduction
      multiplicativeReduction := by
        rw [hc₄eq]; exact h₁.toHasMultiplicativeReduction.multiplicativeReduction }
  refine { hmult₂ with splitMultiplicativeReduction := ?_ }
  have hint₂ : W₂.integralModel R = C₀ • W₁.integralModel R := by
    apply map_injective (IsFractionRing.injective R K)
    change ((W₂.integralModel R)⁄K) = ((C₀ • W₁.integralModel R)⁄K)
    exact (baseChange_integralModel_eq R W₂).trans hW₂eq.symm
  rw [hint₂]
  exact (nodePoly_map_splits_smul_iff (algebraMap R (ResidueField R)) (W₁.integralModel R) C₀).mpr
    h₁.splitMultiplicativeReduction

end Reduction

end WeierstrassCurve

end
