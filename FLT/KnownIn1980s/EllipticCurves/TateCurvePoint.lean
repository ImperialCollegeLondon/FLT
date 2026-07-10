/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveEquation
public import FLT.Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Tate curve `E_q`: the uniformisation point map `tateCurvePoint`

The point map `tateCurvePoint : kˣ → E_q(k)`, `u ↦ (X(u, q), Y(u, q))` for `u ∉ qᶻ`, `qᶻ ↦ O`
(`WeierstrassCurve.tateCurvePoint`), together with its structural lemmas: it depends only on the
class mod `qᶻ` (`tateCurvePoint_eq`), its kernel is `qᶻ` (`tateCurvePoint_eq_zero_iff`), parameter
inversion is negation (`tateX_inv`, `tateY_inv`, `tateCurvePoint_inv`), and it takes infinitely many
values (`exists_tateCurvePoint_notMem`).

Third of the files split out of `TateCurveUniformisation`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

open scoped Classical in
/-- The point of `E_q(k)` attached to a unit `u ∈ kˣ` by Tate's uniformisation: the affine
point `(X(u, q), Y(u, q))` when `u` is not a power of `q`, and the point at infinity `O`
(the class of `qᶻ`) otherwise. This descends to `tateCurveEquiv` below. -/
noncomputable def WeierstrassCurve.tateCurvePoint (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : ((tateCurve (q : k))⁄k).Point :=
  if hu : u ∈ Subgroup.zpowers q then .zero
  else .some (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) (tateCurve_nonsingular q hq u hu)

/-- `tateCurvePoint` only depends on the class of `u` in `kˣ/qᶻ`: on the point at
infinity the two membership conditions agree, and on affine points the coordinate series
are `qᶻ`-invariant (`tateX_zpow_mul_left`, `tateY_zpow_mul_left`). -/
theorem WeierstrassCurve.tateCurvePoint_eq (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (h : u⁻¹ * v ∈ Subgroup.zpowers q) :
    tateCurvePoint q hq u = tateCurvePoint q hq v := by
  obtain ⟨m, hm⟩ := h
  have hm' : q ^ m = u⁻¹ * v := hm
  have hv : v = q ^ m * u := by
    rw [hm', mul_comm u⁻¹ v, inv_mul_cancel_right]
  subst hv
  have hXeq : tateX ((q ^ m * u : kˣ) : k) (q : k) = tateX (u : k) (q : k) := by
    push_cast
    exact tateX_zpow_mul_left q m u
  have hYeq : tateY ((q ^ m * u : kˣ) : k) (q : k) = tateY (u : k) (q : k) := by
    push_cast
    exact tateY_zpow_mul_left q m u
  simp only [tateCurvePoint]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m) h1) h2
  · exact absurd
      ((Subgroup.mul_mem_cancel_left _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) m)).mp h2) h1
  · simp only [hXeq, hYeq]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The only power of `q` in the annulus `|q| < |·| ≤ 1` is `1` itself. -/
theorem TateCurve.notMem_zpowers_of_annulus (q w : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (w : k)) (h₂ : valuation k (w : k) ≤ 1)
    (hw1 : (w : k) ≠ 1) : w ∉ Subgroup.zpowers q := by
  rintro ⟨m, rfl⟩
  have hvq : valuation k ((q ^ m : kˣ) : k) = valuation k (q : k) ^ m := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  rcases lt_trichotomy m 0 with hm | hm | hm
  · -- negative exponents leave the closed unit ball
    rw [hvq] at h₂
    have h1q : 1 < (valuation k (q : k))⁻¹ :=
      (one_lt_inv₀ (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr (Units.ne_zero q)))).mpr
        hq
    have : (1 : ValueGroupWithZero k) < valuation k (q : k) ^ m := by
      calc (1 : ValueGroupWithZero k) < (valuation k (q : k))⁻¹ := h1q
        _ = (valuation k (q : k))⁻¹ ^ 1 := (pow_one _).symm
        _ ≤ (valuation k (q : k))⁻¹ ^ (-m).toNat :=
            pow_le_pow_right' h1q.le (by omega)
        _ = valuation k (q : k) ^ m := by
            rw [inv_pow, ← zpow_natCast, ← zpow_neg,
              Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -m), neg_neg]
    exact absurd h₂ (not_le.mpr this)
  · exact hw1 (by rw [hm]; simp)
  · -- positive exponents drop below `|q|`
    rw [hvq] at h₁
    have : valuation k (q : k) ^ m ≤ valuation k (q : k) := by
      calc valuation k (q : k) ^ m = valuation k (q : k) ^ m.toNat := by
            rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m)]
        _ ≤ valuation k (q : k) ^ 1 :=
            pow_le_pow_right_of_le_one' hq.le (by omega)
        _ = valuation k (q : k) := pow_one _
    exact absurd h₁ (not_lt.mpr this)


/-! ### Stage 1: negation -/

/-- The tail-summability workhorse for the two-sided coordinate series: for `|q| < 1`,
`u ≠ 0` and exponents `1 ≤ i`, the series `∑ₙ (qⁿ⁺¹u)ⁱ/(1 - qⁿ⁺¹u)ʲ` converges. After
discarding the finitely many indices with `|qⁿ⁺¹u| ≥ 1` (`summable_nat_add_iff`), the
denominators are isosceles-trivial (`Valuation.map_one_sub_of_lt`) and the terms are
bounded by `C·|q|ⁿ` with `C = |u|·|q|^(N+1)`, which is the constant-carrying
summability criterion. -/
theorem TateCurve.summable_pow_div_tail (q u : k) (hq : valuation k q < 1) (hu : u ≠ 0)
    (i j : ℕ) (hi : 1 ≤ i) :
    Summable fun n : ℕ ↦ (q ^ (n + 1) * u) ^ i / (1 - q ^ (n + 1) * u) ^ j := by
  rcases eq_or_ne q 0 with rfl | hq0
  · refine summable_zero.congr fun n ↦ ?_
    rw [zero_pow (Nat.succ_ne_zero n), zero_mul, zero_pow (by omega : i ≠ 0), zero_div]
  · have hvq : valuation k q ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
    have hvu : valuation k u ≠ 0 := (valuation k).ne_zero_iff.mpr hu
    obtain ⟨N, hN⟩ := exists_pow_lt hq (Units.mk0 (valuation k u)⁻¹ (inv_ne_zero hvu))
    have hδ : valuation k u * valuation k q ^ N < 1 :=
      mul_pow_lt hvu (by rw [mul_one]; exact hN)
    rw [← summable_nat_add_iff N]
    refine summable_of_valuation_le_const_mul_pow
      (C := valuation k u * valuation k q ^ (N + 1))
      (mul_ne_zero hvu (pow_ne_zero _ hvq)) hq _ fun n ↦ ?_
    have hx : valuation k (q ^ (n + N + 1) * u) =
        valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n := by
      rw [map_mul, map_pow, show n + N + 1 = N + 1 + n from by omega, pow_add,
        mul_comm _ (valuation k u), ← mul_assoc]
    have hxlt : valuation k (q ^ (n + N + 1) * u) < 1 := by
      rw [hx]
      calc valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n
          ≤ valuation k u * valuation k q ^ (N + 1) * 1 :=
            mul_le_mul' le_rfl (pow_le_one' hq.le n)
        _ = valuation k u * (valuation k q ^ N * valuation k q) := by
            rw [mul_one, pow_succ]
        _ = valuation k u * valuation k q ^ N * valuation k q := by rw [mul_assoc]
        _ ≤ valuation k u * valuation k q ^ N * 1 := mul_le_mul' le_rfl hq.le
        _ = valuation k u * valuation k q ^ N := mul_one _
        _ < 1 := hδ
    rw [map_div₀, map_pow, map_pow, (valuation k).map_one_sub_of_lt hxlt, one_pow,
      div_one]
    calc valuation k (q ^ (n + N + 1) * u) ^ i
        ≤ valuation k (q ^ (n + N + 1) * u) ^ 1 :=
          pow_le_pow_right_of_le_one' hxlt.le hi
      _ = valuation k (q ^ (n + N + 1) * u) := pow_one _
      _ = valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n := hx

/-- The two-sided `x`-coordinate series converges for every `u ∈ kˣ` when `|q| < 1`
(including `u ∈ qᶻ`, where the singular term takes the junk value `0`): both tails are
instances of `summable_pow_div_tail`, the negative one after the inversion identity
`div_one_sub_sq_inv`. -/
theorem TateCurve.summable_tateX_int (q u : kˣ) (hq : valuation k (q : k) < 1) :
    Summable fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2 := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := fun n ↦ by
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  refine Summable.of_add_one_of_neg_add_one ?_ ?_
  · exact (summable_pow_div_tail (q : k) (u : k) hq hu0 1 2 le_rfl).congr fun n ↦ by
      rw [pow_one, hcoe n]
  · refine (summable_pow_div_tail (q : k) ((u : k)⁻¹) hq (inv_ne_zero hu0) 1 2
      le_rfl).congr fun n ↦ ?_
    rw [pow_one, zpow_neg, hcoe n,
      div_one_sub_sq_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
        (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Units.ne_zero q))) hu0),
      mul_inv, inv_inv]

/-- The two-sided `y`-coordinate series converges for every `u ∈ kˣ` when `|q| < 1`;
as `summable_tateX_int`, with the negative tail entering through the antisymmetry
`sq_div_one_sub_cube_inv`. -/
theorem TateCurve.summable_tateY_int (q u : kˣ) (hq : valuation k (q : k) < 1) :
    Summable fun n : ℤ ↦
      ((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3 := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := fun n ↦ by
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  refine Summable.of_add_one_of_neg_add_one ?_ ?_
  · exact (summable_pow_div_tail (q : k) (u : k) hq hu0 2 3 (by omega)).congr fun n ↦ by
      rw [hcoe n]
  · refine ((summable_pow_div_tail (q : k) ((u : k)⁻¹) hq (inv_ne_zero hu0) 1 3
      le_rfl).neg).congr fun n ↦ ?_
    rw [pow_one, zpow_neg, hcoe n,
      sq_div_one_sub_cube_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
        (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Units.ne_zero q))) hu0),
      mul_inv, inv_inv]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `X(u⁻¹, q) = X(u, q)`: the `x`-coordinate series is even. Reindex the two-sided
sum by `n ↦ -n` (which needs no summability) and apply `div_one_sub_sq_inv`
termwise. True with junk values for all `q, u`. -/
theorem WeierstrassCurve.tateX_inv (q u : k) :
    tateX u⁻¹ q = tateX u q := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [inv_zero]
  · simp only [tateX]
    congr 1
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ ↦ q ^ n * u⁻¹ / (1 - q ^ n * u⁻¹) ^ 2)]
    refine tsum_congr fun n ↦ ?_
    simp only [Equiv.neg_apply]
    rcases eq_or_ne (q ^ n) 0 with h | h
    · rw [zpow_neg, h, inv_zero]
      simp
    · rw [zpow_neg, ← mul_inv]
      exact (TateCurve.div_one_sub_sq_inv (mul_ne_zero h hu)).symm

/-- `Y(u⁻¹, q) = -Y(u, q) - X(u, q)`: inversion of the parameter is negation on the
curve `y² + xy = x³ + a₄x + a₆` (whose negation is `(x, y) ↦ (x, -y - x)`). Reindex
by `n ↦ -n`, apply `sq_div_one_sub_cube_inv` termwise (producing the combination
`-fY(n) - fX(n)` of the two coordinate integrands), and split the sum using the
`ℤ`-summability of both series. -/
theorem WeierstrassCurve.tateY_inv (q u : kˣ) (hq : valuation k (q : k) < 1) :
    tateY ((u : k)⁻¹) (q : k) =
      -tateY (u : k) (q : k) - tateX (u : k) (q : k) := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hX := TateCurve.summable_tateX_int q u hq
  have hY := TateCurve.summable_tateY_int q u hq
  have hterm : ∀ n : ℤ,
      ((q : k) ^ (-n) * (u : k)⁻¹) ^ 2 / (1 - (q : k) ^ (-n) * (u : k)⁻¹) ^ 3 =
      -(((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3 +
        (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2) := by
    intro n
    have hqn : (q : k) ^ n ≠ 0 := zpow_ne_zero _ (Units.ne_zero q)
    rw [zpow_neg, ← mul_inv,
      TateCurve.sq_div_one_sub_cube_inv (v := ((q : k) ^ n * (u : k))⁻¹)
        (inv_ne_zero (mul_ne_zero hqn hu0)),
      inv_inv]
    rcases eq_or_ne (1 - (q : k) ^ n * (u : k)) 0 with h1 | h1
    · rw [h1]
      simp
    · field_simp
      ring
  simp only [tateY, tateX]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ ↦
    ((q : k) ^ n * (u : k)⁻¹) ^ 2 / (1 - (q : k) ^ n * (u : k)⁻¹) ^ 3)]
  rw [tsum_congr fun n ↦ by simpa only [Equiv.neg_apply] using hterm n]
  rw [tsum_neg, Summable.tsum_add hY hX]
  ring

/-! ### The three pillars: additivity, kernel (= free injectivity), surjectivity

Following Silverman's proof of ATAEC V.3.1(c), the isomorphism
`WeierstrassCurve.tateCurveEquiv : kˣ/qᶻ ≃+ E_q(k)` (assembled in
`FLT.KnownIn1980s.EllipticCurves.TateCurve`) rests on three statements about
`tateCurvePoint`, of which the kernel computation is definitional and yields injectivity
for free, and the other two are the genuine mathematical content. -/

/-- `tateCurvePoint q hq u = O` if and only if `u ∈ qᶻ`: affine points are never `O`, so
the kernel of Tate's uniformisation is `qᶻ` *by construction*. This is why injectivity of
the uniformisation is free once additivity (`tateCurvePoint_mul`) is known — no
theta-function machinery is needed; cf. Silverman's proof of ATAEC V.3.1(c), where the
kernel is described as "apparent from its very definition". -/
theorem WeierstrassCurve.tateCurvePoint_eq_zero_iff (q : kˣ)
    (hq : valuation k (q : k) < 1) {u : kˣ} :
    tateCurvePoint q hq u = 0 ↔ u ∈ Subgroup.zpowers q := by
  constructor
  · intro h
    by_contra hu
    rw [tateCurvePoint, dif_neg hu] at h
    exact Affine.Point.some_ne_zero _ h
  · intro hu
    rw [tateCurvePoint, dif_pos hu]
    rfl

/-- Parameter inversion is negation on the curve: `φ(u⁻¹) = -φ(u)`. On `qᶻ` both sides
are `O`; off `qᶻ` this is Stage 1 (`tateX_inv`, `tateY_inv`), since negation on
`y² + xy = x³ + a₄x + a₆` is `(x, y) ↦ (x, -y - x)`. -/
theorem WeierstrassCurve.tateCurvePoint_inv (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : tateCurvePoint q hq u⁻¹ = -tateCurvePoint q hq u := by
  by_cases hu : u ∈ Subgroup.zpowers q
  · rw [tateCurvePoint, dif_pos (inv_mem hu), tateCurvePoint, dif_pos hu]
    exact (Affine.Point.neg_zero).symm
  · have hu' : u⁻¹ ∉ Subgroup.zpowers q := fun h ↦ hu (by simpa using inv_mem h)
    have hX : tateX ((u⁻¹ : kˣ) : k) (q : k) = tateX (u : k) (q : k) := by
      rw [Units.val_inv_eq_inv_val]
      exact tateX_inv (q : k) (u : k)
    have hY : tateY ((u⁻¹ : kˣ) : k) (q : k) =
        -tateY (u : k) (q : k) - tateX (u : k) (q : k) := by
      rw [Units.val_inv_eq_inv_val]
      exact tateY_inv q u hq
    have hnegY : ((tateCurve (q : k))⁄k).toAffine.negY (tateX (u : k) (q : k))
        (tateY (u : k) (q : k)) = -tateY (u : k) (q : k) - tateX (u : k) (q : k) := by
      simp only [Affine.negY, WeierstrassCurve.baseChange, tateCurve,
        Algebra.algebraMap_self, WeierstrassCurve.map_id]
      ring
    rw [tateCurvePoint, dif_neg hu', tateCurvePoint, dif_neg hu, Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hX, by rw [hY, hnegY]⟩

/-- The valuation of the `x`-coordinate near the identity: `|X(1 + t, q)| = |t|⁻²` for
`0 < |t| < 1`. The leading term `u/(1-u)² = (1+t)/t²` of the annulus expansion dominates
the tail, which is `O(|q|)`, ultrametrically. This is how one sees that Tate's
uniformisation takes infinitely many distinct values
(`exists_tateCurvePoint_notMem` below), which feeds the auxiliary-element trick in
`tateCurvePoint_mul`; cf. the end of Silverman's proof of ATAEC V.3.1(c). -/
theorem WeierstrassCurve.valuation_tateX_one_add (q : kˣ) (hq : valuation k (q : k) < 1)
    {t : k} (ht0 : t ≠ 0) (ht : valuation k t < 1) :
    valuation k (tateX (1 + t) (q : k)) = ((valuation k t)⁻¹) ^ 2 := by
  have hv1 : valuation k (1 + t) = 1 := by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k)) (by simpa using ht)
  have hu0 : (1 : k) + t ≠ 0 := fun h ↦ by
    rw [h, map_zero] at hv1
    exact zero_ne_one hv1
  have hvt : valuation k t ≠ 0 := (valuation k).ne_zero_iff.mpr ht0
  set u : kˣ := Units.mk0 (1 + t) hu0 with hu_def
  have hvu : valuation k (u : k) = 1 := hv1
  have h₁ : valuation k (q : k) < valuation k (u : k) := by rw [hvu]; exact hq
  have h₂ : valuation k (u : k) ≤ 1 := le_of_eq hvu
  -- the tail of the annulus expansion is summable and `O(|q|)`
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [hvu, inv_one, mul_one]
    exact hq
  have htails : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N :=
    ((TateCurve.evalBounded_XField_tail q u h₂).summable hρ1).congr fun n ↦ by
      rw [PowerSeries.coeff_mk]
  have htail : valuation k (∑' N : ℕ, (∑ d ∈ N.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N)
      ≤ valuation k (q : k) := by
    refine valuation_tsum_le htails fun N ↦ ?_
    rcases N with - | N
    · simp
    · have h1u : (1 : ValueGroupWithZero k) ≤ (valuation k (u : k))⁻¹ := by
        rw [hvu, inv_one]
      have hS : valuation k (∑ d ∈ (N + 1).divisors,
          ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) ≤ 1 := by
        refine (valuation k).map_sum_le fun d _ ↦ ?_
        refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
          ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
        · rw [map_mul, map_pow]
          calc valuation k ((d : ℕ) : k) * valuation k (u : k) ^ d
              ≤ 1 * 1 := mul_le_mul' (valuation_natCast_le_one d) (pow_le_one' h₂ d)
            _ = 1 := one_mul 1
        · rw [map_mul, map_pow, map_inv₀, hvu, inv_one, one_pow, mul_one]
          exact valuation_natCast_le_one d
        · rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
          exact valuation_natCast_le_one _
      rw [map_mul, map_pow]
      calc valuation k (∑ d ∈ (N + 1).divisors,
            ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) *
            valuation k (q : k) ^ (N + 1)
          ≤ 1 * valuation k (q : k) ^ (N + 1) := mul_le_mul' hS le_rfl
        _ = valuation k (q : k) ^ (N + 1) := one_mul _
        _ ≤ valuation k (q : k) ^ 1 := pow_le_pow_right_of_le_one' hq.le (by omega)
        _ = valuation k (q : k) := pow_one _
  -- the leading term has valuation exactly `|t|⁻²`
  have hlead : valuation k ((u : k) / (1 - (u : k)) ^ 2) = ((valuation k t)⁻¹) ^ 2 := by
    have h1mu : (1 : k) - (u : k) = -t := by
      rw [hu_def, Units.val_mk0]
      ring
    rw [map_div₀, map_pow, h1mu, Valuation.map_neg, hvu, inv_pow, one_div]
  -- the leading term dominates
  have hone_le : (1 : ValueGroupWithZero k) ≤ ((valuation k t)⁻¹) ^ 2 := by
    have h1 : (1 : ValueGroupWithZero k) ≤ (valuation k t)⁻¹ :=
      ((one_lt_inv₀ (zero_lt_iff.mpr hvt)).mpr ht).le
    calc (1 : ValueGroupWithZero k) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ ((valuation k t)⁻¹) ^ 2 := pow_le_pow_left' h1 2
  have hlt : valuation k (∑' N : ℕ, (∑ d ∈ N.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N)
      < valuation k ((u : k) / (1 - (u : k)) ^ 2) := by
    rw [hlead]
    exact lt_of_le_of_lt htail (lt_of_lt_of_le hq hone_le)
  rw [show (1 : k) + t = (u : k) from rfl, tateX_eq_annulus q u hq h₁ h₂,
    (valuation k).map_add_eq_of_lt_left hlt, hlead]

/-- Tate's uniformisation takes infinitely many distinct values: it misses any finite
set of points. The points `φ(1 + q^(m+1))`, `m : ℕ`, are pairwise distinct, since their
`x`-coordinates have pairwise distinct valuations `|q|^{-2(m+1)}`
(`valuation_tateX_one_add`). This is the input to the auxiliary-element trick
(`TateCurve.map_mul_of_generic`) in `tateCurvePoint_mul`. -/
theorem WeierstrassCurve.exists_tateCurvePoint_notMem (q : kˣ)
    (hq : valuation k (q : k) < 1) {S : Set ((tateCurve (q : k))⁄k).Point}
    (hS : S.Finite) : ∃ w : kˣ, tateCurvePoint q hq w ∉ S := by
  have hq0 : (q : k) ≠ 0 := q.ne_zero
  have hvq0 : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
  -- the powers `q^(m+1)` lie in the punctured open unit disc
  have hpow : ∀ m : ℕ, valuation k ((q : k) ^ (m + 1)) < 1 := fun m ↦ by
    rw [map_pow]
    calc valuation k (q : k) ^ (m + 1) ≤ valuation k (q : k) ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
      _ < 1 := hq
  have hpow0 : ∀ m : ℕ, (q : k) ^ (m + 1) ≠ 0 := fun m ↦ pow_ne_zero _ hq0
  -- the units `1 + q^(m+1)`
  have hv1 : ∀ m : ℕ, valuation k ((1 : k) + (q : k) ^ (m + 1)) = 1 := fun m ↦ by
    simpa using (valuation k).map_add_eq_of_lt_left (x := (1 : k)) (by simpa using hpow m)
  have hne : ∀ m : ℕ, (1 : k) + (q : k) ^ (m + 1) ≠ 0 := fun m h ↦ by
    have h1 := hv1 m
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  set w : ℕ → kˣ := fun m ↦ Units.mk0 _ (hne m) with hw_def
  have hwmem : ∀ m : ℕ, w m ∉ Subgroup.zpowers q := fun m ↦ by
    refine TateCurve.notMem_zpowers_of_annulus q (w m) hq ?_ ?_ ?_
    · rw [show valuation k ((w m : k)) = 1 from hv1 m]
      exact hq
    · exact le_of_eq (hv1 m)
    · rw [hw_def, Units.val_mk0]
      intro h
      exact hpow0 m (by linear_combination h)
  -- pairwise distinct `x`-valuations, hence pairwise distinct points
  have hval : ∀ m : ℕ, valuation k (tateX ((w m : k)) (q : k)) =
      ((valuation k (q : k))⁻¹) ^ (2 * (m + 1)) := fun m ↦ by
    rw [hw_def, Units.val_mk0, valuation_tateX_one_add q hq (hpow0 m) (hpow m), map_pow,
      ← inv_pow, ← pow_mul, mul_comm (m + 1) 2]
  have hinj : Function.Injective fun m : ℕ ↦ tateCurvePoint q hq (w m) := by
    have hone_lt : (1 : ValueGroupWithZero k) < (valuation k (q : k))⁻¹ :=
      (one_lt_inv₀ (zero_lt_iff.mpr hvq0)).mpr hq
    intro m m' hmm'
    by_contra hne'
    have hmm : tateCurvePoint q hq (w m) = tateCurvePoint q hq (w m') := hmm'
    have hXeq : tateX ((w m : k)) (q : k) = tateX ((w m' : k)) (q : k) := by
      rw [tateCurvePoint, dif_neg (hwmem m), tateCurvePoint, dif_neg (hwmem m')] at hmm
      exact ((Affine.Point.some.injEq _ _ _ _ _ _).mp hmm).1
    have hvv := congrArg (valuation k) hXeq
    rw [hval m, hval m'] at hvv
    rcases lt_trichotomy m m' with h | h | h
    · exact absurd hvv (ne_of_lt (pow_lt_pow_right₀ hone_lt (by omega)))
    · exact hne' h
    · exact absurd hvv.symm (ne_of_lt (pow_lt_pow_right₀ hone_lt (by omega)))
  by_contra h
  refine Set.infinite_range_of_injective hinj
    (hS.subset (Set.range_subset_iff.mpr fun m ↦ ?_))
  by_contra hm
  exact h ⟨w m, hm⟩

/-- Two off-lattice parameters with the same `x`-coordinate map to equal or opposite
points: on a Weierstrass curve, affine points sharing an `x`-coordinate are equal or
negatives of each other (`WeierstrassCurve.Affine.Y_eq_of_X_eq`). This is how the
`X(u) = X(v)` degeneration is excluded in the auxiliary-element trick of
`tateCurvePoint_mul`: a `w` with `φ(w) ∉ {±P}` for the relevant `P` automatically has
`X(w)` different from the relevant `x`-coordinates. -/
theorem WeierstrassCurve.tateCurvePoint_eq_or_eq_neg (q : kˣ)
    (hq : valuation k (q : k) < 1) {x y : kˣ} (hx : x ∉ Subgroup.zpowers q)
    (hy : y ∉ Subgroup.zpowers q)
    (hX : tateX (x : k) (q : k) = tateX (y : k) (q : k)) :
    tateCurvePoint q hq y = tateCurvePoint q hq x ∨
      tateCurvePoint q hq y = -tateCurvePoint q hq x := by
  have hEx := tateCurve_equation q hq x hx
  have hEy := tateCurve_equation q hq y hy
  have hYY := Affine.Y_eq_of_X_eq hEy hEx hX.symm
  rw [tateCurvePoint, dif_neg hy, tateCurvePoint, dif_neg hx]
  rcases hYY with h | h
  · exact Or.inl (by simp only [Affine.Point.some.injEq]; exact ⟨hX.symm, h⟩)
  · refine Or.inr ?_
    rw [Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hX.symm, h⟩
