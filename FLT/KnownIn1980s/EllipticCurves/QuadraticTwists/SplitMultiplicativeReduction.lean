/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.LiftSeparableExtension
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Multiplicative reduction becomes split after a quadratic twist

Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of integers
of a nonarchimedean local field), and let `E` be an elliptic curve over `K` with multiplicative
reduction. This file proves that if the reduction is *nonsplit*, then the quadratic twist of `E`
(`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists`) by the unramified quadratic
extension of `K` (`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.LiftSeparableExtension`) has
*split* multiplicative reduction: the reduction of the twist is the same nodal cubic with the
Galois action on the two tangent directions at the node twisted into triviality.

## Main definitions and statements

* `WeierstrassCurve.nodePoly` : the node polynomial `c₄ T² + a₁c₄ T - κ`
  (`κ = 54b₆ - 3b₂b₄ + a₂c₄`), whose roots are the slopes of the two tangent directions at the
  node of a multiplicative reduction; its splitting over the residue field governs whether the
  reduction is split.
* `WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul` : split multiplicative
  reduction is an isomorphism invariant of minimal models (a form of Silverman VII.1.3(b),
  uniqueness of minimal models over a discrete valuation ring).
* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction` : over the fraction
  field of a discrete valuation ring, an elliptic curve with nonsplit multiplicative reduction
  has a quadratic twist with split multiplicative reduction.

The file starts with the quadratic separability and splitting criteria over a field
(`Polynomial.separable_quadratic_iff`, `Polynomial.splits_quadratic_iff`,
`Polynomial.splits_quadratic_iff_of_two_eq_zero`), which feed the analysis of the node
polynomial over the residue field.

## TODO

* Behaviour of reduction types under twisting in general: over the fraction field of a DVR, an
  unramified quadratic twist preserves good and multiplicative reduction (exchanging split and
  nonsplit), while a ramified quadratic twist of a curve with good or multiplicative reduction
  has additive reduction (at least in residue characteristic ≠ 2).
* Compatibility with the Tate curve (`FLT.KnownIn1980s.EllipticCurves.TateCurve`): for `E` with
  nonsplit multiplicative reduction over a nonarchimedean local field, the Galois representation
  of `E` is the unramified quadratic twist of the Tate-curve representation of its split twist.
  This is the main FLT-facing application of this file together with
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.§1 and VII.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)
-/

@[expose] public section

/-! ### Quadratic polynomials: separability and splitting criteria -/

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, add_zero, mul_one, Nat.cast_ofNat, map_ofNat]
  ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (b² - 4 a c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit combination of `P` and its derivative. -/
theorem sq_derivative_quadratic_sub_mul {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (b ^ 2 - 4 * a * c) := by
  rw [derivative_quadratic]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A polynomial of degree at most `2` over a field splits as soon as it has a root: the root
splits off a linear factor and the cofactor is linear. -/
theorem Splits.of_natDegree_le_two_of_isRoot {k : Type*} [Field k] {p : k[X]}
    (hdeg : p.natDegree ≤ 2) {x : k} (hx : p.IsRoot x) : p.Splits := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact .zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
  have hq0 : q ≠ 0 := fun h ↦ hp0 (by rw [hq, h, mul_zero])
  have hqdeg : q.natDegree ≤ 1 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero x) hq0, natDegree_X_sub_C] at hdeg
    lia
  rw [hq]
  exact (Splits.of_natDegree_le_one (natDegree_X_sub_C x).le).mul (.of_natDegree_le_one hqdeg)

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
its discriminant `b² - 4 a c` is nonzero. The `←` direction holds in every characteristic: by the
Bézout identity `sq_derivative_quadratic_sub_mul`, a nonzero (hence invertible) discriminant
exhibits `P` and `P'` as coprime. The `→` direction argues that if the discriminant vanishes then
`P ∣ (P')²`, forcing the coprimality witness `P` to be a unit, contradicting `deg P = 2`. -/
theorem separable_quadratic_iff {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ b ^ 2 - 4 * a * c ≠ 0 := by
  set P := C a * X ^ 2 + C b * X + C c with hP
  have hid : derivative P ^ 2 - 4 * C a * P = C (b ^ 2 - 4 * a * c) :=
    sq_derivative_quadratic_sub_mul a b c
  constructor
  · intro hsep hdisc
    rw [hdisc, map_zero] at hid
    have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
    exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
      (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
  · intro hdisc
    rw [separable_def]
    have hdinv : C (b ^ 2 - 4 * a * c)⁻¹ * C (b ^ 2 - 4 * a * c) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hdisc, C_1]
    exact ⟨-(C (b ^ 2 - 4 * a * c)⁻¹ * 4 * C a), C (b ^ 2 - 4 * a * c)⁻¹ * derivative P,
      by linear_combination C (b ^ 2 - 4 * a * c)⁻¹ * hid + hdinv⟩

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root
(`Splits.of_natDegree_le_two_of_isRoot`). This is the characteristic-free core of the split
criterion. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hp0 : p ≠ 0 := fun h ↦ by simp [h] at hdeg
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by simp [degree_eq_natDegree hp0, hdeg])
    rw [hp] at hx
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine Splits.of_natDegree_le_two_of_isRoot hdeg.le (x := x) ?_
    rw [hp, IsRoot]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when its discriminant `b² - 4 a c` is a square: it splits iff it has a root
(`splits_quadratic_iff_exists_root`), and completing the square
(`discrim_eq_sq_of_quadratic_eq_zero` / `exists_quadratic_eq_zero`) matches roots with square roots
of the discriminant. This is the split-multiplicative-reduction criterion; compare
`separable_quadratic_iff` (separable ↔ discriminant nonzero). -/
theorem splits_quadratic_iff {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by linear_combination hx)]; ring⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
    exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a *separable* quadratic `a X² + b X + c` (`a, b ≠ 0`)
splits exactly when its Artin–Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`,
written division-free as `∃ z, b² (z² + z) = a c`. (Substitute `z = a x / b` in a root `x`.) In
residue characteristic `2` this replaces the square-class criterion `splits_quadratic_iff`, since
there `b² - 4 a c = b²`, so separability already forces `b ≠ 0`. -/
theorem splits_quadratic_iff_of_two_eq_zero {k : Type*} [Field k] (h2 : (2 : k) = 0)
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a * x / b, ?_⟩
    field_simp
    linear_combination hx - c * h2
  · rintro ⟨z, hz⟩
    refine ⟨b * z / a, ?_⟩
    field_simp
    linear_combination hz + a * c * h2

end Polynomial

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-! ### Multiplicative reduction becomes split after a quadratic twist -/

section Reduction

-- Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of
-- integers of a nonarchimedean local field). The instances are introduced in stages, as needed.
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

open Polynomial in
/-- **Twisting flips the square class (residue characteristic ≠ 2).** Combining the split criterion
`nodePoly_map_splits_iff_isSquare` with the coefficient scaling of the quadratic twist
(`c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`), the node polynomial of `W.quadraticTwistOf t n`
splits over a field `k` of characteristic `≠ 2` exactly when `D · (-c₄ c₆)` is a square there, where
`D = t² - 4n`. Thus twisting multiplies the square class governing splitting by `D`: it converts a
nonsplit reduction into a split one precisely when `D` and `-c₄ c₆` lie in the same square class. -/
lemma nodePoly_quadraticTwistOf_map_splits_iff {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (t n : A) (hc₄ : φ W.c₄ ≠ 0)
    (hD : φ (t ^ 2 - 4 * n) ≠ 0) :
    ((W.quadraticTwistOf t n).nodePoly.map φ).Splits
      ↔ IsSquare (φ ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆))) := by
  have key : ∀ s y : k, s ≠ 0 → (IsSquare (s ^ 2 * y) ↔ IsSquare y) := fun s y hs ↦
    ⟨fun ⟨w, hw⟩ ↦ ⟨w / s, by field_simp; linear_combination hw⟩,
      fun ⟨w, hw⟩ ↦ ⟨s * w, by rw [hw]; ring⟩⟩
  have hc₄' : φ (W.quadraticTwistOf t n).c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero 2 hD) hc₄
  rw [nodePoly_map_splits_iff_isSquare φ (W.quadraticTwistOf t n) hc₄',
    show -((W.quadraticTwistOf t n).c₄ * (W.quadraticTwistOf t n).c₆)
        = ((t ^ 2 - 4 * n) ^ 2) ^ 2 * ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆)) from by
      rw [c₄_quadraticTwistOf, c₆_quadraticTwistOf]; ring,
    map_mul, map_pow,
    key _ _ (show φ ((t ^ 2 - 4 * n) ^ 2) ≠ 0 by rw [map_pow]; exact pow_ne_zero 2 hD)]

/-- The `R`-model twist base-changes to the twist over `K`: for `E` integral over `R`, twisting its
integral model by `t, n : R` and base-changing to `K` equals twisting `E` by the images
`(algebraMap R K t, algebraMap R K n)`. Together with the coefficient laws this is the bridge from
the `K`-twist `E.quadraticTwist L` to a genuine `R`-model whose reduction can be computed. -/
theorem baseChange_integralModel_quadraticTwistOf [IsIntegral R E] (t n : R) :
    ((E.integralModel R).quadraticTwistOf t n)⁄K
      = E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n) := by
  change ((E.integralModel R).quadraticTwistOf t n).map (algebraMap R K) = _
  rw [quadraticTwistOf_map, show (E.integralModel R).map (algebraMap R K) = E
    from baseChange_integralModel_eq R E]

variable [IsFractionRing R K]

/-- The integral model of the base change to `K` of an integral Weierstrass curve `W` over `R` is
`W` itself (integral models are unique, as `R → K` is injective). -/
lemma integralModel_baseChange (W : WeierstrassCurve R) [IsIntegral R (W⁄K)] :
    integralModel R (W⁄K) = W := by
  ext <;> apply IsFractionRing.injective R K <;>
    simp only [integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq, integralModel_a₄_eq,
      integralModel_a₆_eq, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆]

variable [IsDomain R]

/-- The base change of the twisted integral model has nonzero discriminant: its `Δ` is
`(t'² - 4n')⁶ · Δ` (`Δ_quadraticTwistOf`), and both factors are nonzero. -/
theorem Δ_baseChange_quadraticTwistOf_ne_zero [E.IsElliptic] [IsIntegral R E] (t' n' : R)
    (hD : t' ^ 2 - 4 * n' ≠ 0) :
    ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ ≠ 0 := by
  have hΔint : (E.integralModel R).Δ ≠ 0 := fun h0 ↦
    E.isUnit_Δ.ne_zero (by rw [← integralModel_Δ_eq R E, h0, map_zero])
  rw [show ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ
    = algebraMap R K ((E.integralModel R).quadraticTwistOf t' n').Δ from map_Δ _ _,
    Δ_quadraticTwistOf, Ne, map_eq_zero_iff _ (IsFractionRing.injective R K), mul_eq_zero]
  exact not_or.mpr ⟨pow_ne_zero 6 hD, hΔint⟩

-- From here on, `R` is a discrete valuation ring.
variable [IsDiscreteValuationRing R]

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
  have hpos : ∀ a : Polynomial (ResidueField R), a ≠ 0 → ¬ IsUnit a → 0 < a.natDegree := by
    intro a ha0 hau
    by_contra hc
    refine hau (Polynomial.isUnit_iff_degree_eq_zero.mpr ?_)
    rw [Polynomial.degree_eq_natDegree ha0, Nat.le_zero.mp (Nat.not_lt.mp hc), Nat.cast_zero]
  have hP0 : P ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos P (by rw [hdeg]; norm_num), fun a b hab ↦ ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hna, hnb⟩ := hcon
  have ha0 : a ≠ 0 := fun h0 ↦ hP0 (by rw [hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 ↦ hP0 (by rw [hab, h0, mul_zero])
  have hsum : a.natDegree + b.natDegree = 2 := by rw [← hdeg, hab, Polynomial.natDegree_mul ha0 hb0]
  have hda := hpos a ha0 hna
  have hdb := hpos b hb0 hnb
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
W.Δ`. This is the tool that shows the twist `W` we build is minimal without minimising by hand. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [hint : IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using hint, fun C hC _ ↦ ?_⟩⟩
  have hCi : IsIntegral R (C • W) := hC
  simp only [← Subtype.coe_le_coe, one_smul, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  set v := valuation K (maximalIdeal R) with hv
  set y := v ((C.u⁻¹ : Kˣ) : K) with hy
  -- From integrality, `valuation (C • W).c₄ = y⁴ · valuation W.c₄ = y⁴ ≤ 1`, hence `y ≤ 1`.
  have huc : v ((C • W).c₄) ≤ 1 := by
    rw [← integralModel_c₄_eq R (C • W)]; exact valuation_le_one (maximalIdeal R) _
  rw [variableChange_c₄, map_mul, map_pow, ← hy, hc₄, mul_one] at huc
  have hy1 : y ≤ 1 := by
    by_contra hgt
    exact absurd (one_lt_pow₀ (lt_of_not_ge hgt) (by norm_num)) (not_lt.mpr huc)
  -- Therefore `valuation (C • W).Δ = y¹² · valuation W.Δ ≤ valuation W.Δ`.
  rw [variableChange_Δ, map_mul, map_pow, ← hy]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hy1)

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- **The twist by a unit discriminant keeps multiplicative reduction.** If `E` has multiplicative
reduction and `D = t² - 4n` is a unit of `R` (residue `≠ 0`), then the base change of the `R`-model
twist `(E.integralModel R).quadraticTwistOf t n` again has multiplicative reduction: its
`c₄ = D² · c₄` is a unit (so the model is minimal and the reduction multiplicative) and its
`Δ = D⁶ · Δ` still has positive valuation. -/
theorem hasMultiplicativeReduction_baseChange_quadraticTwistOf [E.HasMultiplicativeReduction R]
    (t n : R) (hD : residue R (t ^ 2 - 4 * n) ≠ 0) :
    (((E.integralModel R).quadraticTwistOf t n)⁄K).HasMultiplicativeReduction R := by
  set W := (E.integralModel R).quadraticTwistOf t n with hW
  have hWint : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  -- `residue W.c₄ = residue D² · residue (E.integralModel R).c₄ ≠ 0`, `residue W.Δ = 0`.
  have hc₄res : residue R W.c₄ ≠ 0 := by
    rw [hW, c₄_quadraticTwistOf, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hD) (residue_integralModel_c₄_ne_zero E R)
  have hΔres : residue R W.Δ = 0 := by
    rw [hW, Δ_quadraticTwistOf, map_mul, map_pow, residue_integralModel_Δ_eq_zero E R, mul_zero]
  -- Convert to the valuation conditions on the base change `W⁄K`.
  have hc₄val : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).c₄ = 1 := by
    rw [show (W⁄K).c₄ = algebraMap R K W.c₄ from map_c₄ W (algebraMap R K)]
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem.mpr
      fun hmem ↦ hc₄res ((residue_eq_zero_iff W.c₄).mpr hmem)
  have hΔval : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).Δ < 1 := by
    rw [show (W⁄K).Δ = algebraMap R K W.Δ from map_Δ W (algebraMap R K)]
    exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem W.Δ).mpr
      ((residue_eq_zero_iff W.Δ).mp hΔres)
  have : IsMinimal R (W⁄K) := isMinimal_of_valuation_c₄_eq_one R (W⁄K) hc₄val
  exact { badReduction := hΔval, multiplicativeReduction := hc₄val }

open IsLocalRing in
/-- **Norm and the residue field.** For a finite free algebra `B` over a local ring `A`, the norm of
the reduction of `x` is the reduction of the norm. This is the norm analogue of
`Algebra.trace_quotient_mk`; the proof is identical, using `RingHom.map_det` in place of the matrix
trace map. -/
theorem norm_quotient_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.norm (A ⧸ maximalIdeal A)
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) x)
      = Ideal.Quotient.mk (maximalIdeal A) (Algebra.norm A x) := by
  classical
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let b : Module.Basis (Module.Free.ChooseBasisIndex A B) A B := Module.Free.chooseBasis A B
  rw [Algebra.norm_eq_matrix_det (basisQuotient b), Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply,
    ← map_mul, basisQuotient_repr]

/-- **Rank-2 Cayley–Hamilton.** Every element `θ` of a free rank-2 `A`-algebra `B` satisfies its
characteristic polynomial `X² - (trace θ) X + (norm θ)`: this is Cayley–Hamilton
(`Algebra.aeval_self_charpoly_lmul`) applied to left multiplication by `θ`, whose characteristic
polynomial is `X² - trace X + norm` in rank two (`Matrix.charpoly_fin_two`). -/
theorem sq_sub_trace_mul_self_add_norm {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] (h2 : Module.finrank A B = 2) (θ : B) :
    θ ^ 2 - algebraMap A B (Algebra.trace A B θ) * θ + algebraMap A B (Algebra.norm A θ) = 0 := by
  classical
  set b : Module.Basis (Fin 2) A B := Module.finBasisOfFinrankEq A B h2 with hb
  have hcp : (Algebra.lmul A B θ).charpoly
      = Polynomial.X ^ 2 - Polynomial.C (Algebra.trace A B θ) * Polynomial.X
        + Polynomial.C (Algebra.norm A θ) := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul A B θ) b, ← Algebra.leftMulMatrix_apply,
      Matrix.charpoly_fin_two, ← Algebra.trace_eq_matrix_trace b, ← Algebra.norm_eq_matrix_det b]
  have hCH := Algebra.aeval_self_charpoly_lmul (R := A) (M := B) θ
  rw [hcp] at hCH
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    using hCH

open IsLocalRing in
/-- Transport of the rank-2 Cayley–Hamilton identity `θ² - t·θ + n = 0` (`t`, `n` the trace and
norm of `θ`, `sq_sub_trace_mul_self_add_norm`) through an isomorphism of residue fields: the image
of the residue of `θ` satisfies the corresponding relation in the residues of `t` and `n`. -/
theorem sq_sub_trace_mul_self_add_norm_residue {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Free R S] [Module.Finite R S]
    (hSrank : Module.finrank R S = 2) {k' : Type u} [CommRing k']
    [Algebra (ResidueField R) k'] (resIso : ResidueField S ≃ₐ[ResidueField R] k') (θ : S) :
    resIso (residue S θ) ^ 2
      - algebraMap (ResidueField R) k' (residue R (Algebra.trace R S θ)) * resIso (residue S θ)
      + algebraMap (ResidueField R) k' (residue R (Algebra.norm R θ)) = 0 := by
  have htower : ∀ r : R, algebraMap (ResidueField R) (ResidueField S) (residue R r)
      = residue S (algebraMap R S r) := fun r ↦ by
    simp only [← ResidueField.algebraMap_residue]
  have h0 := congrArg (fun x ↦ resIso (residue S x)) (sq_sub_trace_mul_self_add_norm hSrank θ)
  simp only [map_sub, map_add, map_mul, map_pow, map_zero, ← htower, resIso.commutes] at h0
  exact h0

/-- An element satisfying a monic quadratic relation with coefficients in `A` is integral. -/
theorem isIntegral_of_sq_add_mul_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b : A) (h : x ^ 2 + algebraMap A B a * x + algebraMap A B b = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C a * Polynomial.X + Polynomial.C b), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

/-- An element satisfying a monic quartic relation (with no cubic term) with coefficients in `A`
is integral. -/
theorem isIntegral_of_pow_four_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b c : A)
    (h : x ^ 4 + algebraMap A B a * x ^ 2 + algebraMap A B b * x + algebraMap A B c = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 4 + (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X
    + Polynomial.C c), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

/-- For a minimal Weierstrass model `W`, no integral change of variables increases the valuation
of the discriminant. -/
theorem valuation_Δ_aux_smul_le {W : WeierstrassCurve K} [hm : IsMinimal R W]
    (D : VariableChange K) (hint : IsIntegral R (D • W)) :
    valuation_Δ_aux R (D • W) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W) := by
  rcases le_total (valuation_Δ_aux R ((1 : VariableChange K) • W)) (valuation_Δ_aux R (D • W))
    with h | h
  · exact hm.val_Δ_maximal.2 hint h
  · exact h

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
/-- An element of the fraction field of a discrete valuation ring with valuation `1` is the image
of a unit. -/
theorem exists_algebraMap_unit_eq_of_valuation_eq_one {x : K}
    (hx : valuation K (maximalIdeal R) x = 1) : ∃ u : Rˣ, algebraMap R K ↑u = x := by
  obtain ⟨u₀, hu₀⟩ := associated_of_valuation_eq (A := R) (K := K) x 1 (by rw [map_one]; exact hx)
  have h1 : algebraMap R K ↑u₀ * x = 1 := by rw [← Algebra.smul_def]; exact hu₀
  have h2 : algebraMap R K ↑u₀ * algebraMap R K ↑u₀⁻¹ = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact ⟨u₀⁻¹, mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h2.trans h1.symm)⟩

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
    field_simp
  have hb₈ : (↑D.u : K) ^ 8 * W₂.b₈
      = W₁.b₈ + 3 * D.r * W₁.b₆ + 3 * D.r ^ 2 * W₁.b₄ + D.r ^ 3 * W₁.b₂ + 3 * D.r ^ 4 := by
    rw [← hD, variableChange_b₈]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨rR, hrR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_pow_four_add_eq_zero (x := D.r) (-(W₁.integralModel R).b₄)
      (-(2 * (W₁.integralModel R).b₆) - (↑u₀ : R) ^ 6 * (W₂.integralModel R).b₆)
      ((↑u₀ : R) ^ 8 * (W₂.integralModel R).b₈ - (W₁.integralModel R).b₈) (by
        simp only [map_sub, map_neg, map_mul, map_pow, map_ofNat]
        rw [integralModel_b₄_eq R W₁, integralModel_b₆_eq R W₁, integralModel_b₈_eq R W₁,
          integralModel_b₆_eq R W₂, integralModel_b₈_eq R W₂, hau]
        linear_combination hb₈ - D.r * hb₆))
  -- `D.s ∈ R`: a root of the monic quadratic `X² + a₁ X + (u²·a₂' - a₂ - 3r)`.
  have ha₂ : (↑D.u : K) ^ 2 * W₂.a₂ = W₁.a₂ - D.s * W₁.a₁ + 3 * D.r - D.s ^ 2 := by
    rw [← hD, variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨sR, hsR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_mul_add_eq_zero (x := D.s) (W₁.integralModel R).a₁
      ((↑u₀ : R) ^ 2 * (W₂.integralModel R).a₂ - (W₁.integralModel R).a₂ - 3 * rR) (by
        simp only [map_sub, map_mul, map_pow, map_ofNat]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₂_eq R W₂, hau, hrR]
        linear_combination ha₂))
  -- `D.t ∈ R`: a root of the monic quadratic
  -- `X² + (a₃ + r·a₁) X + (u⁶·a₆' - a₆ - r·a₄ - r²·a₂ - r³)`.
  have ha₆ : (↑D.u : K) ^ 6 * W₂.a₆ = W₁.a₆ + D.r * W₁.a₄ + D.r ^ 2 * W₁.a₂ + D.r ^ 3
      - D.t * W₁.a₃ - D.t ^ 2 - D.r * D.t * W₁.a₁ := by
    rw [← hD, variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  obtain ⟨tR, htR⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (isIntegral_of_sq_add_mul_add_eq_zero (x := D.t)
      ((W₁.integralModel R).a₃ + rR * (W₁.integralModel R).a₁)
      (-((W₁.integralModel R).a₆ + rR * (W₁.integralModel R).a₄
        + rR ^ 2 * (W₁.integralModel R).a₂ + rR ^ 3) + (↑u₀ : R) ^ 6 * (W₂.integralModel R).a₆) (by
        simp only [map_add, map_neg, map_mul, map_pow]
        rw [integralModel_a₁_eq R W₁, integralModel_a₂_eq R W₁, integralModel_a₃_eq R W₁,
          integralModel_a₄_eq R W₁, integralModel_a₆_eq R W₁, integralModel_a₆_eq R W₂, hau, hrR]
        linear_combination ha₆))
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
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
    change ((W₂.integralModel R)⁄K) = ((C₀ • W₁.integralModel R)⁄K)
    exact (baseChange_integralModel_eq R W₂).trans hW₂eq.symm
  rw [hint₂]
  exact (nodePoly_map_splits_smul_iff (algebraMap R (ResidueField R)) (W₁.integralModel R) C₀).mpr
    h₁.splitMultiplicativeReduction

open IsLocalRing in
/-- If the residue of an integral element `θ` of `S` does not come from the residue field of `R`,
then `θ` does not come from `K` either: an element of `K` integral over the integrally closed `R`
lies in `R`, and residues are compatible. -/
theorem notMem_range_algebraMap_of_residue_notMem {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsLocalHom (algebraMap R S)] {L : Type u} [Field L]
    [Algebra K L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] {θ : S}
    (hθ : residue S θ ∉ Set.range (algebraMap (ResidueField R) (ResidueField S))) :
    algebraMap S L θ ∉ Set.range (algebraMap K L) := by
  rintro ⟨a, ha⟩
  have haint : _root_.IsIntegral R a := by
    have h1 : _root_.IsIntegral R (algebraMap S L θ) :=
      _root_.IsIntegral.map (IsScalarTower.toAlgHom R S L) (Algebra.IsIntegral.isIntegral θ)
    rw [← ha] at h1
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (FaithfulSMul.algebraMap_injective K L)).mp h1
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp haint
  refine hθ ⟨residue R r, ?_⟩
  rw [show algebraMap (ResidueField R) (ResidueField S) (residue R r)
    = residue S (algebraMap R S r) by simp only [← ResidueField.algebraMap_residue]]
  congr 1
  apply IsFractionRing.injective S L
  rw [← ha, ← hr, ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R K L]

open IsLocalRing in
/-- If the root of the reduced node polynomial `P̄` (assumed irreducible) satisfies a monic
quadratic relation `X² - t·X + n` over the residue field, then comparing with the defining
relation of `P̄` (`aeval_root_nodePoly_map`) and using the linear independence of `1` and the root
(`AdjoinRoot.eq_zero_of_mul_root_add_eq_zero`) yields the relations `φc₄·t + φ(a₁c₄) = 0` and
`φc₄·n + φκ = 0` (φ = residue, `κ = 54b₆ - 3b₂b₄ + a₂c₄`). -/
theorem nodePoly_map_root_relations [E.HasMultiplicativeReduction R]
    (hirr : Irreducible ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))))
    {t n : ResidueField R}
    (hρ : AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))) ^ 2
        - algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) t
          * AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))
        + algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) n
        = 0) :
    residue R (E.integralModel R).c₄ * t
        + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0
      ∧ residue R (E.integralModel R).c₄ * n
        + residue R (54 * (E.integralModel R).b₆
          - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
          + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0 := by
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hρ2 : algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) (E.integralModel R).c₄) * (AdjoinRoot.root P) ^ 2
        + algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) ((E.integralModel R).a₁ * (E.integralModel R).c₄))
          * (AdjoinRoot.root P)
        - algebraMap (ResidueField R) (AdjoinRoot P) (algebraMap R (ResidueField R)
          (54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
            + (E.integralModel R).a₂ * (E.integralModel R).c₄)) = 0 :=
    aeval_root_nodePoly_map (algebraMap R (ResidueField R)) (E.integralModel R)
  obtain ⟨hA, hB⟩ := AdjoinRoot.eq_zero_of_mul_root_add_eq_zero hPdeg2.ge
    (a := residue R (E.integralModel R).c₄ * t
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄))
    (b := -(residue R (E.integralModel R).c₄ * n
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄))) (by
    simp only [IsLocalRing.ResidueField.algebraMap_eq, map_add, map_mul, map_neg] at hρ2 ⊢
    linear_combination hρ2
      - algebraMap (ResidueField R) (AdjoinRoot P) (residue R (E.integralModel R).c₄) * hρ)
  rw [neg_eq_zero] at hB
  exact ⟨hA, hB⟩

open IsLocalRing in
/-- The key identity `φc₄ · φ(t'² - 4n') = -φc₆` of the twisting datum `(t', n')`: if its residues
satisfy the trace and norm relations cut out by the node polynomial
(`κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄`), then the discriminant identity `splitPolynomial_discrim` turns
them into this identity. -/
theorem residue_c₄_mul_residue_eq_neg_c₆ [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    residue R (E.integralModel R).c₄ * residue R (t' ^ 2 - 4 * n')
      = -residue R (E.integralModel R).c₆ := by
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hRid : ((E.integralModel R).a₁ * c₄') ^ 2 + 4 * c₄' * κ'
      = -(c₄' * (E.integralModel R).c₆) := by
    rw [hκ', hc₄']
    exact splitPolynomial_discrim (E.integralModel R)
  have hdisc := congrArg (residue R) hRid
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hdisc
  apply mul_left_cancel₀ (residue_integralModel_c₄_ne_zero E R)
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination hdisc
    + (residue R c₄' * residue R t' - residue R (E.integralModel R).a₁ * residue R c₄') * hA
    - 4 * residue R c₄' * hB

open IsLocalRing in
/-- The residue characteristic `2` case of `nodePoly_quadraticTwistOf_map_splits_of_residue`:
the Artin–Schreier split condition (`nodePoly_map_splits_iff_of_two_eq_zero`) holds with `z = 0`,
because `φ κ_W = 0`. Indeed `κ_W = D³κ - D²·n·a₁²·c₄` (`kappa_quadraticTwistOf`), and
`φκ = -φc₄·φn` (`hB`), `φa₁ = -φt'` (`hA`), `φD = φt'²` (as `4 = 0`), so
`φκ_W = -φD²·φc₄·φn·(φD + φa₁²) = -φD²·φc₄·φn·(2·φt'²) = 0`. -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero
    [E.HasMultiplicativeReduction R] (t' n' : R) (h2 : (2 : ResidueField R) = 0)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  -- `D = t'²-4n'` has nonzero residue (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
  have hc₄map : algebraMap R (ResidueField R) (E.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hc₄0
  set D := t' ^ 2 - 4 * n' with hDdef
  have h4 : (4 : ResidueField R) = 0 := by
    rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, mul_zero]
  have hDmap : algebraMap R (ResidueField R) D ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hDne
  have hDt : residue R D = residue R t' ^ 2 := by
    rw [hDdef, map_sub, map_mul, map_pow, map_ofNat, h4, zero_mul, sub_zero]
  have hWc₄ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hDmap) hc₄map
  have hWc₆ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₆ ≠ 0 := by
    rw [c₆_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 3 hDmap)
      (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
  have hta : residue R (E.integralModel R).a₁ = -residue R t' := by
    rcases mul_eq_zero.mp (show residue R c₄'
        * (residue R t' + residue R (E.integralModel R).a₁) = 0 by linear_combination hA)
      with hz | hz
    · exact absurd hz hc₄0
    · linear_combination hz
  have hκW_eq : 54 * ((E.integralModel R).quadraticTwistOf t' n').b₆
      - 3 * ((E.integralModel R).quadraticTwistOf t' n').b₂
          * ((E.integralModel R).quadraticTwistOf t' n').b₄
      + ((E.integralModel R).quadraticTwistOf t' n').a₂
          * ((E.integralModel R).quadraticTwistOf t' n').c₄
      = D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄' := by
    rw [hDdef, hκ', hc₄']
    exact kappa_quadraticTwistOf (E.integralModel R) t' n'
  have hWc₄eq : ((E.integralModel R).quadraticTwistOf t' n').c₄ = D ^ 2 * c₄' := by
    rw [c₄_quadraticTwistOf, ← hDdef, hc₄']
  have hκW0 : algebraMap R (ResidueField R)
      (D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄') = 0 := by
    simp only [map_sub, map_mul, map_pow, ResidueField.algebraMap_eq, hDt, hta]
    linear_combination (residue R t') ^ 6 * hB
      - (residue R t') ^ 6 * residue R n' * residue R c₄' * h2
  rw [nodePoly_map_splits_iff_of_two_eq_zero h2 (algebraMap R (ResidueField R))
    ((E.integralModel R).quadraticTwistOf t' n') hWc₄ hWc₆]
  refine ⟨0, ?_⟩
  rw [hκW_eq, hWc₄eq, show (0 : ResidueField R) ^ 2 + 0 = 0 from by ring, mul_zero, hκW0,
    neg_zero, mul_zero]

open IsLocalRing in
/-- If the residues of `(t', n')` satisfy the trace and norm relations cut out by the node
polynomial, then the node polynomial of the quadratic twist of the integral model by `(t', n')`
splits over the residue field: the key identity `φc₄ · φ(t'² - 4n') = -φc₆`
(`residue_c₄_mul_residue_eq_neg_c₆`) reduces this to a square-class computation for residue
characteristic `≠ 2`, and to an Artin–Schreier computation for residue characteristic `2`
(`nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero`). -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  rcases ne_or_eq (2 : ResidueField R) 0 with h2 | h2
  · -- Residue characteristic `≠ 2`: split ↔ `IsSquare (φ((t'²-4n')·-(c₄c₆)))`, which `hkey` shows
    -- equals `IsSquare (φc₆²)`.
    have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
    have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
      residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
    have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
    have : NeZero (2 : ResidueField R) := ⟨h2⟩
    rw [nodePoly_quadraticTwistOf_map_splits_iff (algebraMap R (ResidueField R))
      (E.integralModel R) t' n' (by rw [ResidueField.algebraMap_eq]; exact hc₄0)
      (by rw [ResidueField.algebraMap_eq]; exact hDne)]
    refine ⟨residue R (E.integralModel R).c₆, ?_⟩
    apply mul_left_cancel₀ hc₄0
    rw [ResidueField.algebraMap_eq]
    simp only [map_mul, map_neg]
    linear_combination
      (-(residue R (E.integralModel R).c₄ * residue R (E.integralModel R).c₆)) * hkey
  · exact nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero E R t' n' h2 hA hB

open IsLocalRing in
/-- Packaging `nodePoly_quadraticTwistOf_map_splits_of_residue`: if the base change of the twisted
integral model has multiplicative reduction and the residues of `(t', n')` satisfy the trace and
norm relations, then the reduction is *split* multiplicative. -/
theorem hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    [hW : (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasMultiplicativeReduction R]
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
  refine { hW with splitMultiplicativeReduction := ?_ }
  rw [show (((E.integralModel R).quadraticTwistOf t' n')⁄K).integralModel R
    = (E.integralModel R).quadraticTwistOf t' n' from integralModel_baseChange R _]
  exact nodePoly_quadraticTwistOf_map_splits_of_residue E R t' n' hA hB

variable [E.IsElliptic]

open IsLocalRing in
/-- If `E` has multiplicative reduction which is not split, then `E` has a quadratic twist with
split multiplicative reduction — namely the twist by the unramified quadratic extension of `K`:
the reduction of the twist is the same nodal cubic with the Galois action on the two tangent
directions at the node twisted into triviality.

Mathlib's reduction-type predicates apply to a specific Weierstrass equation and require it to
be minimal, while our chosen model `E.quadraticTwist L` of the twist need not be; so the
conclusion is phrased via the minimal model `(E.quadraticTwist L).minimal R`. (Being split
multiplicative is intrinsic, so any other minimal model would do.)

The nonsplitness hypothesis `h` cannot be dropped: if `E` already has split multiplicative
reduction then *no* quadratic twist of `E` has split multiplicative reduction, since the
unramified quadratic twist has nonsplit multiplicative reduction and ramified quadratic twists
have additive reduction. -/
theorem exists_quadraticTwist_hasSplitMultiplicativeReduction [E.HasMultiplicativeReduction R]
    (h : ¬E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L),
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  classical
  -- The node polynomial reduced to the residue field `k`; nonsplitness makes it irreducible
  -- (`irreducible_nodePoly_map`), and multiplicative reduction makes it separable
  -- (`separable_nodePoly_map`). Its root field `k' = k[X]/(P)` is therefore a separable
  -- quadratic extension of `k`.
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hirr : Irreducible P := irreducible_nodePoly_map E R h
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hk'rank : Module.finrank (ResidueField R) (AdjoinRoot P) = 2 :=
    AdjoinRoot.finrank_eq_natDegree.trans hPdeg2
  have : FiniteDimensional (ResidueField R) (AdjoinRoot P) := .of_finrank_eq_succ hk'rank
  have : Algebra.IsSeparable (ResidueField R) (AdjoinRoot P) :=
    AdjoinRoot.isSeparable_of_separable (separable_nodePoly_map E R)
  -- Lift `k'` to the unramified quadratic extension `L/K` (`LiftSeparableExtension`).
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hLrank, ⟨resIso⟩⟩ :=
    exists_unramified_extension_of_residueField (R := R) (K := K) (AdjoinRoot P)
  have : Algebra.IsQuadraticExtension K L := ⟨hLrank.trans hk'rank⟩
  refine ⟨L, ‹Field L›, ‹Algebra K L›, ‹Algebra.IsQuadraticExtension K L›,
    ‹Algebra.IsSeparable K L›, ?_⟩
  -- `S = 𝒪_L` is the integral closure of `R` in `L` (now that `Frac S = L` is proved), so `L` is
  -- the base-change localization of `S`, and `R`-trace/norm are compatible with `K`-trace/norm.
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R K L S
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  have hSrank : Module.finrank R S = 2 :=
    (IsIntegralClosure.rank R K L S).trans (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨θ', hθ'res⟩ := IsLocalRing.residue_surjective (resIso.symm (AdjoinRoot.root P))
  -- Via `resIso`, `root P` satisfies the Cayley–Hamilton relation `X² - φ(t')·X + φ(n')` of `θ'`
  -- (`sq_sub_trace_mul_self_add_norm_residue`); comparing with the defining relation of `P` gives
  -- the residue relations `φc₄·φt' = -φ(a₁c₄)` and `φc₄·φn' = -φκ` (`nodePoly_map_root_relations`).
  have hρ1 := sq_sub_trace_mul_self_add_norm_residue R hSrank resIso θ'
  rw [hθ'res, resIso.apply_symm_apply] at hρ1
  obtain ⟨hA, hB⟩ := nodePoly_map_root_relations E R hirr hρ1
  set t' := Algebra.trace R S θ' with ht'
  set n' := Algebra.norm R θ' with hn'
  -- `root P ∉ k` (its minimal polynomial has degree 2), so `θ'̄ = resIso⁻¹(root P) ∉ k` and, since
  -- `R` is integrally closed, `algebraMap S L θ' ∉ K` — the twist by `θ'` is nontrivial.
  have hθ' : algebraMap S L θ' ∉ Set.range (algebraMap K L) :=
    notMem_range_algebraMap_of_residue_notMem R (by
      rw [hθ'res]
      exact fun hmem ↦ AdjoinRoot.root_notMem_range_algebraMap hPdeg2.ge
        (resIso.symm.apply_mem_range_algebraMap_iff.mp hmem))
  -- Trace/norm land in `K`, giving the connection to the `R`-model `W = quadraticTwistOf t' n'`.
  have htr : Algebra.trace K L (algebraMap S L θ') = algebraMap R K t' :=
    Algebra.trace_localization R (nonZeroDivisors R) θ'
  have hnr : Algebra.norm K (algebraMap S L θ') = algebraMap R K n' :=
    Algebra.norm_localization R (nonZeroDivisors R) θ'
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ'
  rw [quadraticTwistBy, htr, hnr, ← baseChange_integralModel_quadraticTwistOf E R t' n'] at hC
  -- `D = t'²-4n'` is a unit (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`), so `W⁄K`
  -- has multiplicative reduction; the relations `hA`, `hB` make it split
  -- (`nodePoly_quadraticTwistOf_map_splits_of_residue`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  have hWmult := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hDne
  have hWsplit := hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue E R t' n' hA hB
  -- `hWsplit : (W⁄K).HasSplitMultiplicativeReduction R` with `W⁄K` minimal and
  -- `hC : C • E.quadraticTwist L = W⁄K`. Split multiplicativity transfers to the chosen minimal
  -- model `(E.quadraticTwist L).minimal R`, which is another minimal model of
  -- `E.quadraticTwist L` (`of_isMinimal_smul`).
  have : IsMinimal R (((E.integralModel R).quadraticTwistOf t' n')⁄K) := hWmult.toIsMinimal
  have hD : (((E.quadraticTwist L).exists_isMinimal R).choose * C⁻¹)
      • (((E.integralModel R).quadraticTwistOf t' n')⁄K) = (E.quadraticTwist L).minimal R := by
    rw [mul_smul, ← hC, inv_smul_smul]; rfl
  have : (((E.integralModel R).quadraticTwistOf t' n')⁄K).IsElliptic :=
    ⟨(Δ_baseChange_quadraticTwistOf_ne_zero E R t' n' fun h0 ↦
      hDne (by rw [h0, map_zero])).isUnit⟩
  exact HasSplitMultiplicativeReduction.of_isMinimal_smul R _ hD hWsplit

end Reduction

end WeierstrassCurve

end
