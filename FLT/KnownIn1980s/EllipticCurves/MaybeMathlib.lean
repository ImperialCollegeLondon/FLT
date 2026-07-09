/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Material destined for Mathlib

Generic lemmas developed for the Tate-curve formalisation that are not specific to it and
should eventually be upstreamed to Mathlib. Each section is annotated with the base Mathlib
file it is intended to land in; the section can be lifted there essentially verbatim (only the
imports need reconciling with that file's existing import closure).

Not collected here: `ValuativeRel.valuation_tsum_le`, which lives in
`FLT.Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology` because it depends on the
`T2Space` / `IsLinearTopology` instances proved in that file (and would land in the
corresponding base file `Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`).
-/

@[expose] public section

/-! ## → `Mathlib.Algebra.Group.Basic` -/

/-- Upgrading a generically additive map to a globally additive one: if
`f (a * b) = f a + f b` holds off a bad set of pairs, and for every pair an auxiliary
`w` exists making the three pairs `(a * b, w)`, `(a, b * w)`, `(b, w)` good, then
additivity holds everywhere, by cancellation of `f w`. -/
theorem map_mul_of_generic {G H : Type*} [CommGroup G] [AddCommGroup H]
    (f : G → H) (Bad : Set (G × G))
    (hmul : ∀ a b : G, (a, b) ∉ Bad → f (a * b) = f a + f b)
    (hgen : ∀ a b : G, ∃ w : G, (a * b, w) ∉ Bad ∧ (a, b * w) ∉ Bad ∧ (b, w) ∉ Bad)
    (a b : G) : f (a * b) = f a + f b := by
  obtain ⟨w, h1, h2, h3⟩ := hgen a b
  have key : f (a * b) + f w = f a + f b + f w := by
    rw [← hmul _ _ h1, mul_assoc a b w, hmul _ _ h2, hmul _ _ h3, ← add_assoc]
  exact add_right_cancel key

/-! ## → `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic` -/

/-- Translating by a power of `g` does not change membership in `zpowers g`. -/
@[simp]
theorem Subgroup.zpow_mul_mem_zpowers_iff {G : Type*} [CommGroup G] (g w : G) (j : ℤ) :
    g ^ j * w ∈ Subgroup.zpowers g ↔ w ∈ Subgroup.zpowers g := by
  refine ⟨fun h ↦ ?_, fun h ↦ mul_mem (zpow_mem (mem_zpowers g) j) h⟩
  have := mul_mem (zpow_mem (Subgroup.mem_zpowers g) (-j)) h
  rwa [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul] at this

/-! ## → `Mathlib.Algebra.GroupWithZero.Units.Basic` -/

/-- The coercion `Mˣ → M` applied to `g ^ j * w`. -/
@[simp]
theorem Units.val_zpow_mul {M : Type*} [DivisionRing M] (g w : Mˣ) (j : ℤ) :
    ((g ^ j * w : Mˣ) : M) = (g : M) ^ j * (w : M) := by
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

/-! ## → `Mathlib.Algebra.Polynomial.Cardinal` (or `Mathlib.Algebra.Polynomial.Basic`) -/

namespace Polynomial

/-- The polynomial ring over a countable semiring is countable. -/
instance instCountable {R : Type*} [Semiring R] [Countable R] : Countable R[X] := by
  rw [← Cardinal.mk_le_aleph0_iff]
  calc Cardinal.mk R[X] ≤ max (Cardinal.mk R) Cardinal.aleph0 := cardinalMk_le_max
    _ ≤ Cardinal.aleph0 := max_le Cardinal.mk_le_aleph0 le_rfl

end Polynomial

/-! ## → `Mathlib.FieldTheory.RatFunc.AsPolynomial`

`instCountable` here depends on `Polynomial.instCountable` from the section above. -/

namespace RatFunc

variable {K : Type*} [Field K]

/-- The rational-function variable `X` is not equal to `1`. -/
theorem X_ne_one : (RatFunc.X : RatFunc K) ≠ 1 := fun h ↦ by
  have h2 : (Polynomial.X : Polynomial K) = 1 := RatFunc.algebraMap_injective K
    (by rw [RatFunc.algebraMap_X, map_one]; exact h)
  simpa using congrArg Polynomial.natDegree h2

/-- In the field of rational functions, `1 - X` is nonzero. -/
theorem one_sub_X_ne_zero : (1 : RatFunc K) - RatFunc.X ≠ 0 := by
  have h1 : (1 : RatFunc K) - RatFunc.X
      = algebraMap (Polynomial K) (RatFunc K) (1 - Polynomial.X) := by
    rw [map_sub, map_one, RatFunc.algebraMap_X]
  rw [h1, Ne, ← map_zero (algebraMap (Polynomial K) (RatFunc K))]
  intro h
  have h2 : (1 : Polynomial K) - Polynomial.X = 0 :=
    IsFractionRing.injective (Polynomial K) (RatFunc K) h
  have h3 : (Polynomial.X : Polynomial K) = 1 := by linear_combination -h2
  simpa [Polynomial.coeff_X_one, Polynomial.coeff_one] using
    congrArg (fun p => Polynomial.coeff p 1) h3

/-- The field of rational functions over a countable field is countable. -/
instance instCountable [Countable K] : Countable (RatFunc K) :=
  Function.Surjective.countable
    (f := fun p : Polynomial K × (nonZeroDivisors (Polynomial K)) =>
      IsLocalization.mk' (RatFunc K) p.1 p.2)
    (fun r => by
      obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial K)) r
      exact ⟨(p, q), h⟩)

end RatFunc

/-! ## → `Mathlib.RingTheory.PowerSeries.Basic`

Evaluating power-series coefficients through a ring homomorphism `ε : S →+* ℂ`: if the
sequences `ε (coeff n φ) * qⁿ` and `ε (coeff n ψ) * qⁿ` have sums, then so do the sequences
for `φ + ψ`, `-φ`, `φ - ψ` and `φ * ψ` (Cauchy product). The `mul` case uses that unconditional
summation over `ℂ` is absolute (`Summable.norm`), so the target is kept at `ℂ`; a more general
statement over an `RCLike` (or finite-dimensional real normed) field would carry the extra
`FiniteDimensional ℝ _` typeclass. Needs the analysis imports above, so an upstream home might
instead be an analysis-side file such as `Mathlib.Analysis.Normed.Ring.InfiniteSum`. -/

section PowerSeriesEval

open scoped PowerSeries

variable {S : Type*} [CommRing S]

theorem hasSum_ringHom_add (ε : S →+* ℂ) {q : ℂ} {φ ψ : S⟦X⟧} {P Q : ℂ}
    (hφ : HasSum (fun n ↦ ε (PowerSeries.coeff n φ) * q ^ n) P)
    (hψ : HasSum (fun n ↦ ε (PowerSeries.coeff n ψ) * q ^ n) Q) :
    HasSum (fun n ↦ ε (PowerSeries.coeff n (φ + ψ)) * q ^ n) (P + Q) := by
  refine (hφ.add hψ).congr_fun fun n ↦ ?_
  simp only [map_add, add_mul]

theorem hasSum_ringHom_neg (ε : S →+* ℂ) {q : ℂ} {φ : S⟦X⟧} {P : ℂ}
    (hφ : HasSum (fun n ↦ ε (PowerSeries.coeff n φ) * q ^ n) P) :
    HasSum (fun n ↦ ε (PowerSeries.coeff n (-φ)) * q ^ n) (-P) := by
  refine hφ.neg.congr_fun fun n ↦ ?_
  simp only [map_neg, neg_mul]

theorem hasSum_ringHom_sub (ε : S →+* ℂ) {q : ℂ} {φ ψ : S⟦X⟧} {P Q : ℂ}
    (hφ : HasSum (fun n ↦ ε (PowerSeries.coeff n φ) * q ^ n) P)
    (hψ : HasSum (fun n ↦ ε (PowerSeries.coeff n ψ) * q ^ n) Q) :
    HasSum (fun n ↦ ε (PowerSeries.coeff n (φ - ψ)) * q ^ n) (P - Q) := by
  simpa [sub_eq_add_neg] using hasSum_ringHom_add ε hφ (hasSum_ringHom_neg ε hψ)

theorem hasSum_ringHom_mul (ε : S →+* ℂ) {q : ℂ} {φ ψ : S⟦X⟧} {P Q : ℂ}
    (hφ : HasSum (fun n ↦ ε (PowerSeries.coeff n φ) * q ^ n) P)
    (hψ : HasSum (fun n ↦ ε (PowerSeries.coeff n ψ) * q ^ n) Q) :
    HasSum (fun n ↦ ε (PowerSeries.coeff n (φ * ψ)) * q ^ n) (P * Q) := by
  have hprod := hasSum_sum_range_mul_of_summable_norm hφ.summable.norm hψ.summable.norm
  rw [hφ.tsum_eq, hψ.tsum_eq] at hprod
  refine hprod.congr_fun fun n ↦ ?_
  rw [PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ (ε (PowerSeries.coeff k φ) * q ^ k) * (ε (PowerSeries.coeff l ψ) * q ^ l)),
    map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [map_mul, ← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

end PowerSeriesEval

/-! ## → `Mathlib.NumberTheory.Bernoulli` -/

theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, bernoulli'_five]

/-! ## → `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`

Depends on `bernoulli'_six` from the section above. -/

section RiemannZeta

open Complex

open Real in
/-- The value `ζ(6) = π⁶/945` (companion to Mathlib's `riemannZeta_four`). -/
theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 * ((3 : ℕ) : ℂ)) = 6 by norm_num] at h
  rw [h, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  norm_num [Nat.factorial]
  ring

end RiemannZeta

/-! ## → `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` -/

/-!

# The addition theorem for the Weierstrass `℘`-function

Material destined for Mathlib. Let `L` be a pair of periods, `Λ` its lattice, and `℘`,
`℘'` the associated Weierstrass functions (`Mathlib.Analysis.SpecialFunctions.Elliptic.
Weierstrass`). This file proves:

* `PeriodPair.deriv_derivWeierstrassP` : `℘''(z) = 6℘(z)² - g₂/2` away from `Λ`, together
  with the third and fourth derivatives `iteratedDeriv_three_weierstrassP`,
  `iteratedDeriv_four_weierstrassP` obtained by differentiating it;
* `PeriodPair.weierstrassP_add_sq` — **the addition theorem** in polynomial form: for
  `z₁, z₂, z₁ + z₂ ∉ Λ`,

  `(℘(z₁+z₂) + ℘(z₁) + ℘(z₂))·(℘(z₁) - ℘(z₂))² = (℘'(z₁) - ℘'(z₂))²/4`;

* `PeriodPair.derivWeierstrassP_add_sq` — its `z₁`-derivative, expressing
  `℘'(z₁+z₂)·(℘(z₁) - ℘(z₂))²` polynomially in `℘(z₁±...), ℘', g₂`.

The polynomial form requires no `℘(z₁) ≠ ℘(z₂)` hypothesis; dividing by
`(℘(z₁) - ℘(z₂))²` when it is nonzero recovers the classical formula
`℘(z₁+z₂) = ¼((℘'z₁-℘'z₂)/(℘z₁-℘z₂))² - ℘z₁ - ℘z₂`.

## Proof strategy

Both main results follow the strategy of mathlib's `PeriodPair.derivWeierstrassP_sq`
(the differential equation): the defect of the identity, extended by `0` on its polar
locus, is meromorphic and doubly periodic; multiplying by a suitable power of a local
uniformiser exhibits it as analytic with high-order vanishing at each pole candidate
(a finite computation with `iteratedDeriv` and the lattice sums
`PeriodPair.sumInvPow`/`PeriodPair.G`); hence the defect is entire, bounded (periodicity
plus compactness of a fundamental domain), constant by Liouville, and `0` by evaluation.

For the addition theorem with `z₂ ∉ Λ` fixed, the polar locus in `z₁` is
`Λ ∪ (Λ - z₂)`:

* at `Λ` (reduce to `0` by periodicity), the defect times `z₁⁶` is analytic, and its
  first seven Taylor coefficients vanish — a computation using the expansions
  `℘ = ℘[L-0] + z⁻²`, `℘' = ℘'[L-0] - 2z⁻³`, the values
  `iteratedDeriv_weierstrassPExcept_self` (Eisenstein numbers `G`), the derivatives of
  `z₁ ↦ ℘(z₁+z₂)` at `0` up to order 4 (this is where `deriv_derivWeierstrassP` enters),
  the vanishing of odd `G`'s, and finally the differential equation at `z₂`;
* at `Λ - z₂` (reduce to `-z₂` by periodicity), the defect times `(z₁+z₂)²` is analytic
  and vanishes to order 3 — a computation using only the evenness of `℘` and oddness
  of `℘'` at `-z₂`. In particular no two-torsion hypothesis on `z₂` is needed.
-/

open Filter
open scoped Topology Nat

noncomputable section

/-- **Liouville's theorem for lattice-periodic functions**: a `ℂ`-differentiable function
`f : E → F` on a finite-dimensional complex normed space `E`, invariant under translation by a
`ℤ`-lattice `Λ`, takes the same value at any two points; in particular it is constant. Specialised
to `E = F = ℂ` and a rank-2 lattice this is Liouville's first theorem for elliptic functions. -/
theorem Differentiable.eq_of_zLattice_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} (hf : Differentiable ℂ f) (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hper : ∀ w ∈ Λ, ∀ z, f (z + w) = f z) (x y : E) : f x = f y :=
  hf.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic Λ _ hf.continuous
      (fun z w hw ↦ hper w hw z)).isBounded x y

namespace PeriodPair

variable (L : PeriodPair)

/-! ### Shared infrastructure for the Liouville arguments

Both main results are proved by the same template: a defect, extended by `0` on its polar locus,
is meromorphic and lattice-periodic; multiplying by a uniformiser of the right order clears the
pole once enough Taylor coefficients vanish (`analyticAt_of_mul_uniformiser`), so the defect is
entire; being entire and doubly periodic it is constant (`Differentiable.eq_of_zLattice_periodic`),
and vanishing at one point makes it `0`. -/

/-- (Implementation) `f` is analytic at `x` once a uniformiser `u` of order `k` clears the pole:
if `f · u` is analytic at `x` and its first `k + 1` Taylor coefficients there vanish, then the
order of `f` at `x` is positive, so (given `f x = 0`) `f` is analytic at `x`. -/
private lemma analyticAt_of_mul_uniformiser {f u : ℂ → ℂ} {x : ℂ} {k : ℕ}
    (hf : MeromorphicAt f x) (hu : MeromorphicAt u x) (hzero : f x = 0)
    (horder : meromorphicOrderAt u x = k) (hfu : AnalyticAt ℂ (f * u) x)
    (hvanish : ∀ i < k + 1, iteratedDeriv i (f * u) x = 0) : AnalyticAt ℂ f x := by
  refine .of_meromorphicOrderAt_pos (one_pos.trans_le ?_) hzero
  suffices ((k : ℤ) + 1 : WithTop ℤ) ≤ meromorphicOrderAt (f * u) x by
    rw [meromorphicOrderAt_mul hf hu, horder] at this
    rw [← WithTop.add_le_add_iff_right (z := (k : WithTop ℤ)) (by simp)]
    simpa [-add_le_add_iff_left_of_ne_top, add_comm] using! this
  rw [AnalyticAt.meromorphicOrderAt_eq hfu]
  exact ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfu).mpr fun i hi ↦ hvanish i hi)

/-! ### The second derivative: `℘'' = 6℘² - g₂/2`

The defect `deriv ℘' - 6℘² + g₂/2` has, at each lattice point, a pole of order at most
`2` (the `z⁻⁴`-terms of `deriv ℘'` and `6℘²` cancel); multiplied by `z²` it is analytic
with a triple zero at `0` — the constant term is `-12℘[L-0](0) = 0`, the linear term is
`-12·℘[L-0]'(0) = -24·G₃ = 0`, and the quadratic term is `g₂ - 60·G₄ = 0` by definition
of `g₂`. So the defect is entire, doubly periodic, hence zero.
-/

section SecondDerivative

/-- (Implementation) The defect of the second-derivative identity `℘'' = 6℘² - g₂/2`,
extended by `0` on the lattice. We show it is constantly zero:
see `PeriodPair.deriv_derivWeierstrassP`. -/
private def relation₂ (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice then 0 else deriv ℘'[L] z - 6 * ℘[L] z ^ 2 + L.g₂ / 2

/-- (Implementation) Away from `0`, `deriv ℘'[L] z = deriv ℘'[L-0] z + 6/z⁴`. -/
private lemma deriv_derivWeierstrassP_eq {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = deriv ℘'[L - (0 : ℂ)] z + 6 / z ^ 4 := by
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (zero_mem _)
  have hfun : ℘'[L] = fun w ↦ ℘'[L - (0 : ℂ)] w - 2 / w ^ 3 := by
    funext w
    have := L.derivWeierstrassPExcept_sub (0 : L.lattice) w
    simpa using this.symm
  have hEx : HasDerivAt ℘'[L - (0 : ℂ)] (deriv ℘'[L - (0 : ℂ)] z) z :=
    (L.analyticOnNhd_derivWeierstrassPExcept 0 z (fun h ↦ hz h.1)).differentiableAt.hasDerivAt
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  have hdiv : HasDerivAt (fun w : ℂ ↦ 2 / w ^ 3)
      ((0 * z ^ 3 - 2 * (3 * z ^ 2)) / (z ^ 3) ^ 2) z :=
    (hasDerivAt_const z (2 : ℂ)).div hpow (pow_ne_zero 3 hz0)
  have hderiv : HasDerivAt ℘'[L]
      (deriv ℘'[L - (0 : ℂ)] z - (0 * z ^ 3 - 2 * (3 * z ^ 2)) / (z ^ 3) ^ 2) z := by
    rw [hfun]; exact hEx.sub hdiv
  rw [hderiv.deriv]
  field_simp
  ring

/-- (Implementation) `deriv ℘'[L]` is lattice-periodic. -/
private lemma deriv_derivWeierstrassP_add_coe (x : ℂ) (l : L.lattice) :
    deriv ℘'[L] (x + l) = deriv ℘'[L] x := by
  rw [← deriv_comp_add_const ℘'[L] (l : ℂ) x]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards with w using L.derivWeierstrassP_add_coe w l

@[local fun_prop]
private lemma meromorphic_deriv_derivWeierstrassP : Meromorphic (deriv ℘'[L]) :=
  fun x ↦ (L.meromorphic_derivWeierstrassP x).deriv

@[local fun_prop]
private lemma meromorphic_relation₂ : Meromorphic L.relation₂ := by
  have : Meromorphic fun z ↦ deriv ℘'[L] z - 6 * ℘[L] z ^ 2 + L.g₂ / 2 := by fun_prop
  refine fun x ↦ (this _).congr ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds _)] with w hw hw'
  rw [relation₂, if_neg (by simp_all)]

private lemma relation₂_mul_id_pow_two_eventuallyEq :
    (L.relation₂ * id ^ 2) =ᶠ[nhds 0] fun z ↦
      deriv ℘'[L - (0 : ℂ)] z * z ^ 2
        - 6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) * z ^ 2
        - 12 * ℘[L - (0 : ℂ)] z + L.g₂ / 2 * z ^ 2 := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds _] with z hz
  by_cases hz0 : z = 0
  · subst hz0; simp [relation₂]
  have hzL : z ∉ L.lattice := fun h ↦ hz ⟨h, hz0⟩
  have hP : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
    have := L.weierstrassPExcept_add (0 : L.lattice) z
    simpa using this.symm
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq, relation₂, if_neg hzL]
  rw [L.deriv_derivWeierstrassP_eq hzL, hP]
  field_simp
  ring

@[local fun_prop]
private lemma analyticAt_relation₂_mul_id_pow_two :
    AnalyticAt ℂ (L.relation₂ * id ^ 2) 0 := by
  refine .congr ?_ L.relation₂_mul_id_pow_two_eventuallyEq.symm
  fun_prop

attribute [local fun_prop] AnalyticAt.contDiffAt in
private lemma analyticAt_relation₂_zero : AnalyticAt ℂ L.relation₂ 0 := by
  have horder : meromorphicOrderAt ((id : ℂ → ℂ) ^ 2) 0 = 2 := by
    have he : ((id : ℂ → ℂ) ^ 2) = ((· - (0 : ℂ)) ^ 2 : ℂ → ℂ) := by ext z; simp
    rw [he]; simpa using meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := 2)
  refine analyticAt_of_mul_uniformiser (by fun_prop) (by fun_prop) (by simp [relation₂])
    horder (by fun_prop) fun i hi₁ ↦ ?_
  rw [L.relation₂_mul_id_pow_two_eventuallyEq.iteratedDeriv_eq]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_weierstrassPExcept_self]
  interval_cases i <;>
    simp [Finset.sum_range_succ, deriv_derivWeierstrassPExcept_self, weierstrassPExcept_zero,
      L.G_eq_zero_of_odd 3 (by decide), g₂, sumInvPow_zero, show (3 : ℕ)! = 6 from rfl]
  ring

@[local simp]
private lemma relation₂_add_coe (x : ℂ) (l : L.lattice) :
    L.relation₂ (x + l) = L.relation₂ x := by
  simp only [relation₂, weierstrassP_add_coe, L.deriv_derivWeierstrassP_add_coe]
  congr 1
  simpa using (L.lattice.toAddSubgroup.add_mem_cancel_right (y := x) l.2)

@[local simp]
private lemma relation₂_sub_coe (x : ℂ) (l : L.lattice) :
    L.relation₂ (x - l) = L.relation₂ x := by
  rw [← L.relation₂_add_coe _ l, sub_add_cancel]

private lemma analyticAt_relation₂ (x : ℂ) : AnalyticAt ℂ L.relation₂ x := by
  by_cases hx : x ∈ L.lattice
  · lift x to L.lattice using hx
    have := L.analyticAt_relation₂_zero
    rw [← sub_self x.1] at this
    convert! this.comp (f := (· - x.1)) (by fun_prop)
    ext a
    simp
  · have : AnalyticAt ℂ (fun z ↦ deriv ℘'[L] z - 6 * ℘[L] z ^ 2 + L.g₂ / 2) x := by
      have h1 := L.analyticOnNhd_derivWeierstrassP _ hx
      have h2 := L.analyticOnNhd_weierstrassP _ hx
      fun_prop
    apply this.congr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with x hx
    simp_all [relation₂]

private lemma relation₂_eq_zero : L.relation₂ = 0 := by
  ext x
  refine (Differentiable.eq_of_zLattice_periodic
    (fun x ↦ (L.analyticAt_relation₂ x).differentiableAt) L.lattice
    (fun w hw z ↦ by lift w to L.lattice using hw; simp) x 0).trans (if_pos (by simp))

/-- The second derivative of the Weierstrass `℘`-function:
`℘''(z) = 6℘(z)² - g₂/2` away from the lattice. -/
theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have := congr($(L.relation₂_eq_zero) z)
  simp only [relation₂, if_neg hz, Pi.zero_apply] at this
  linear_combination this

/-- `℘'' = 6℘² - g₂/2`, in iterated-derivative form. -/
theorem iteratedDeriv_two_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    iteratedDeriv 2 ℘[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_weierstrassP]
  exact L.deriv_derivWeierstrassP hz

/-- `℘''' = 12℘℘'`: differentiate `℘'' = 6℘² - g₂/2` on the open set `Λᶜ`. -/
theorem iteratedDeriv_three_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    iteratedDeriv 3 ℘[L] z = 12 * ℘[L] z * ℘'[L] z := by
  rw [iteratedDeriv_succ]
  have heq : iteratedDeriv 2 ℘[L] =ᶠ[𝓝 z] fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2 := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.iteratedDeriv_two_weierstrassP hw
  rw [heq.deriv_eq]
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    rw [← congr_fun L.deriv_weierstrassP z]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun w ↦ 6 * ℘[L] w ^ 2 - L.g₂ / 2)
      (6 * (2 * ℘[L] z ^ (2 - 1) * ℘'[L] z)) z :=
    ((hP.pow 2).const_mul 6).sub_const _
  rw [hd.deriv]
  ring

/-- `℘⁗ = 12℘'² + 12℘·(6℘² - g₂/2)`: differentiate `℘''' = 12℘℘'` on `Λᶜ`. -/
theorem iteratedDeriv_four_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    iteratedDeriv 4 ℘[L] z =
      12 * ℘'[L] z ^ 2 + 12 * ℘[L] z * (6 * ℘[L] z ^ 2 - L.g₂ / 2) := by
  rw [iteratedDeriv_succ]
  have heq : iteratedDeriv 3 ℘[L] =ᶠ[𝓝 z] fun w ↦ 12 * ℘[L] w * ℘'[L] w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.iteratedDeriv_three_weierstrassP hw
  rw [heq.deriv_eq]
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    rw [← congr_fun L.deriv_weierstrassP z]
    exact (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hP' : HasDerivAt ℘'[L] (deriv ℘'[L] z) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun w ↦ 12 * ℘[L] w * ℘'[L] w)
      (12 * ℘'[L] z * ℘'[L] z + 12 * ℘[L] z * deriv ℘'[L] z) z :=
    (hP.const_mul 12).mul hP'
  rw [hd.deriv, L.deriv_derivWeierstrassP hz]
  ring

end SecondDerivative

/-! ### The addition theorem -/

section Addition

variable {z₂ : ℂ}

/-- (Implementation) The defect of the addition theorem for `℘` at translation `z₂`,
as a function of `z₁`, extended by `0` on its polar locus `Λ ∪ (Λ - z₂)`. For
`z₂ ∉ Λ` it is constantly zero: see `PeriodPair.weierstrassP_add_sq`. -/
private def addRelation (z₂ : ℂ) (z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice ∨ z + z₂ ∈ L.lattice then 0 else
    (℘[L] (z + z₂) + ℘[L] z + ℘[L] z₂) * (℘[L] z - ℘[L] z₂) ^ 2
      - (℘'[L] z - ℘'[L] z₂) ^ 2 / 4

/-- (Implementation) `z ↦ ℘(z + c)` is meromorphic. -/
private lemma meromorphic_wP_add (c : ℂ) : Meromorphic (fun z ↦ ℘[L] (z + c)) :=
  fun x ↦ (L.meromorphic_weierstrassP (x + c)).comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

@[local fun_prop]
private lemma meromorphic_addRelation : Meromorphic (L.addRelation z₂) := by
  intro x
  have h1 : MeromorphicAt (fun z ↦ ℘[L] (z + z₂)) x := L.meromorphic_wP_add z₂ x
  have h2 : MeromorphicAt ℘[L] x := L.meromorphic_weierstrassP x
  have h3 : MeromorphicAt ℘'[L] x := L.meromorphic_derivWeierstrassP x
  refine ((((h1.add h2).add (.const (℘[L] z₂) x)).mul
    ((h2.sub (.const (℘[L] z₂) x)).pow 2)).sub
    (((h3.sub (.const (℘'[L] z₂) x)).pow 2).div (.const 4 x))).congr ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds x),
    mem_nhdsWithin_of_mem_nhds ((continuous_add_const z₂).continuousAt.preimage_mem_nhds
      (L.compl_lattice_sdiff_singleton_mem_nhds (x + z₂)))] with w hw hw' hw''
  simp only [Set.mem_preimage] at hw''
  have hwx : w ≠ x := hw
  rw [addRelation, if_neg (show ¬(w ∈ L.lattice ∨ w + z₂ ∈ L.lattice) from
    not_or.mpr ⟨fun h ↦ hw' ⟨h, hwx⟩, fun h ↦ hw'' ⟨h, fun e ↦ hwx (add_right_cancel e)⟩⟩)]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]

@[local simp]
private lemma addRelation_add_coe (x : ℂ) (l : L.lattice) :
    L.addRelation z₂ (x + l) = L.addRelation z₂ x := by
  unfold addRelation
  rw [show x + (l : ℂ) + z₂ = x + z₂ + l from by ring, L.lattice.add_mem_iff_left l.2,
    L.lattice.add_mem_iff_left l.2]
  simp only [weierstrassP_add_coe, derivWeierstrassP_add_coe]

@[local simp]
private lemma addRelation_sub_coe (x : ℂ) (l : L.lattice) :
    L.addRelation z₂ (x - l) = L.addRelation z₂ x := by
  rw [← L.addRelation_add_coe _ l, sub_add_cancel]

/-- (Implementation) Pole-clearing at `0` (locus `Λ`). -/
private lemma addRelation_mul_id_pow_six_eventuallyEq (hz₂ : z₂ ∉ L.lattice) :
    (L.addRelation z₂ * id ^ 6) =ᶠ[nhds 0] fun z ↦
      ((℘[L] (z + z₂) + ℘[L] z₂) * z ^ 2 + ℘[L - (0 : ℂ)] z * z ^ 2 + 1)
        * ((℘[L - (0 : ℂ)] z - ℘[L] z₂) * z ^ 2 + 1) ^ 2
        - ((℘'[L - (0 : ℂ)] z - ℘'[L] z₂) * z ^ 3 - 2) ^ 2 / 4 := by
  have hz2mem : {z : ℂ | z + z₂ ∉ L.lattice} ∈ nhds (0 : ℂ) :=
    (continuous_add_const z₂).continuousAt.preimage_mem_nhds
      (L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hz₂))
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0, hz2mem] with z hz hz2L
  by_cases hz0 : z = 0
  · subst hz0
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq, addRelation, weierstrassPExcept_zero]
    norm_num
  have hzL : z ∉ L.lattice := fun h ↦ hz ⟨h, hz0⟩
  have hPz : ℘[L] z = ℘[L - (0 : ℂ)] z + 1 / z ^ 2 := by
    have := L.weierstrassPExcept_add (0 : L.lattice) z; simpa using this.symm
  have hP'z : ℘'[L] z = ℘'[L - (0 : ℂ)] z - 2 / z ^ 3 := by
    have := L.derivWeierstrassPExcept_sub (0 : L.lattice) z; simpa using this.symm
  simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
  rw [addRelation, if_neg (not_or.mpr ⟨hzL, hz2L⟩), hPz, hP'z]
  field_simp
  ring

/-- (Implementation) Derivatives of `z ↦ ℘(z + z₂)` at `0` are those of `℘` at `z₂`. -/
private lemma iteratedDeriv_wP_add_zero (n : ℕ) :
    iteratedDeriv n (fun z ↦ ℘[L] (z + z₂)) 0 = iteratedDeriv n ℘[L] z₂ := by
  simp [iteratedDeriv_comp_add_const]

/-- (Implementation) `z ↦ ℘(z + z₂)` is analytic at `0` when `z₂ ∉ Λ`. -/
private lemma analyticAt_wP_add_zero (hz₂ : z₂ ∉ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] (z + z₂)) 0 :=
  (L.analyticOnNhd_weierstrassP z₂ hz₂).comp_of_eq (by fun_prop) (zero_add z₂)

private lemma analyticAt_addRelation_mul_id_pow_six (hz₂ : z₂ ∉ L.lattice) :
    AnalyticAt ℂ (L.addRelation z₂ * id ^ 6) 0 := by
  refine .congr ?_ (L.addRelation_mul_id_pow_six_eventuallyEq hz₂).symm
  have hA := L.analyticAt_wP_add_zero hz₂
  fun_prop

attribute [local fun_prop] AnalyticAt.contDiffAt in
private lemma analyticAt_addRelation_zero (hz₂ : z₂ ∉ L.lattice) :
    AnalyticAt ℂ (L.addRelation z₂) 0 := by
  have hA := L.analyticAt_wP_add_zero hz₂
  have hAC : ∀ n : WithTop ℕ∞, ContDiffAt ℂ n (fun z ↦ ℘[L] (z + z₂)) 0 := fun _ ↦ hA.contDiffAt
  have hDE : ℘'[L] z₂ ^ 2 = 4 * ℘[L] z₂ ^ 3 - 60 * L.G 4 * ℘[L] z₂ - 140 * L.G 6 := by
    have := L.derivWeierstrassP_sq z₂ hz₂; simpa [g₂, g₃] using this
  have e0 : iteratedDeriv 0 ℘[L] z₂ = ℘[L] z₂ := rfl
  have e1 : iteratedDeriv 1 ℘[L] z₂ = ℘'[L] z₂ := by
    rw [iteratedDeriv_one, congr_fun L.deriv_weierstrassP]
  have e2 : iteratedDeriv 2 ℘[L] z₂ = 6 * ℘[L] z₂ ^ 2 - L.g₂ / 2 :=
    L.iteratedDeriv_two_weierstrassP hz₂
  have e3 : iteratedDeriv 3 ℘[L] z₂ = 12 * ℘[L] z₂ * ℘'[L] z₂ :=
    L.iteratedDeriv_three_weierstrassP hz₂
  have e4 : iteratedDeriv 4 ℘[L] z₂ =
      12 * ℘'[L] z₂ ^ 2 + 12 * ℘[L] z₂ * (6 * ℘[L] z₂ ^ 2 - L.g₂ / 2) :=
    L.iteratedDeriv_four_weierstrassP hz₂
  have horder : meromorphicOrderAt ((id : ℂ → ℂ) ^ 6) 0 = 6 := by
    have he : ((id : ℂ → ℂ) ^ 6) = ((· - (0 : ℂ)) ^ 6 : ℂ → ℂ) := by ext z; simp
    rw [he]; simpa using meromorphicOrderAt_pow_id_sub_const (x := (0 : ℂ)) (n := 6)
  refine analyticAt_of_mul_uniformiser (by fun_prop) (by fun_prop) (by simp [addRelation])
    horder (L.analyticAt_addRelation_mul_id_pow_six hz₂) fun i hi₁ ↦ ?_
  rw [(L.addRelation_mul_id_pow_six_eventuallyEq hz₂).iteratedDeriv_eq]
  simp_rw [pow_succ (_ + _), pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_div_const, iteratedDeriv_derivWeierstrassPExcept_self,
    iteratedDeriv_weierstrassPExcept_self, L.iteratedDeriv_wP_add_zero]
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4,
      weierstrassPExcept_zero, sumInvPow_zero, L.G_eq_zero_of_odd 3 (by decide),
      L.G_eq_zero_of_odd 5 (by decide), g₂, Nat.choose, Nat.factorial,
      Nat.choose_self] <;>
    push_cast <;>
    ring_nf
  linear_combination 180 * hDE

/-- (Implementation) Pole-clearing at `-z₂` (locus `Λ - z₂`). -/
private lemma addRelation_mul_add_sq_eventuallyEq (hz₂ : z₂ ∉ L.lattice) :
    (L.addRelation z₂ * fun z ↦ (z + z₂) ^ 2) =ᶠ[nhds (-z₂)] fun z ↦
      (℘[L - (0 : ℂ)] (z + z₂) * (z + z₂) ^ 2 + 1) * (℘[L] z - ℘[L] z₂) ^ 2
        + ((℘[L] z + ℘[L] z₂) * (℘[L] z - ℘[L] z₂) ^ 2 - (℘'[L] z - ℘'[L] z₂) ^ 2 / 4)
          * (z + z₂) ^ 2 := by
  have hnegz₂ : -z₂ ∉ L.lattice := fun h ↦ hz₂ (by simpa using neg_mem h)
  have hmem2 : (fun z : ℂ ↦ z + z₂) ⁻¹' (↑L.lattice \ {0})ᶜ ∈ nhds (-z₂) :=
    (continuous_add_const z₂).continuousAt.preimage_mem_nhds
      (by simpa using L.compl_lattice_sdiff_singleton_mem_nhds 0)
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hnegz₂, hmem2] with z hz1 hz2
  simp only [Set.mem_preimage] at hz2
  have hzL : z ∉ L.lattice := hz1
  by_cases hz0 : z + z₂ = 0
  · have hze : z = -z₂ := by linear_combination hz0
    subst hze
    simp only [Pi.mul_apply, neg_add_cancel, addRelation, weierstrassPExcept_zero,
      weierstrassP_neg]
    norm_num
  have hz2L : z + z₂ ∉ L.lattice := fun h ↦ hz2 ⟨h, hz0⟩
  have hP : ℘[L] (z + z₂) = ℘[L - (0 : ℂ)] (z + z₂) + 1 / (z + z₂) ^ 2 := by
    have := L.weierstrassPExcept_add (0 : L.lattice) (z + z₂); simpa using this.symm
  simp only [Pi.mul_apply]
  rw [addRelation, if_neg (not_or.mpr ⟨hzL, hz2L⟩), hP]
  field_simp
  ring

private lemma iteratedDeriv_wPExcept_add_negZ2 (n : ℕ) :
    iteratedDeriv n (fun z ↦ ℘[L - (0 : ℂ)] (z + z₂)) (-z₂) = iteratedDeriv n ℘[L - (0 : ℂ)] 0 := by
  simp [iteratedDeriv_comp_add_const]

private lemma iteratedDeriv_add_sq_negZ2 (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ (z + z₂) ^ 2) (-z₂) = iteratedDeriv n (· ^ 2 : ℂ → ℂ) 0 := by
  have h := congrFun (iteratedDeriv_comp_add_const n (· ^ 2 : ℂ → ℂ) z₂) (-z₂)
  simpa using h

private lemma analyticAt_addRelation_mul_add_sq (hz₂ : z₂ ∉ L.lattice) :
    AnalyticAt ℂ (L.addRelation z₂ * fun z ↦ (z + z₂) ^ 2) (-z₂) := by
  have hnegz₂ : -z₂ ∉ L.lattice := fun h ↦ hz₂ (by simpa using neg_mem h)
  refine .congr ?_ (L.addRelation_mul_add_sq_eventuallyEq hz₂).symm
  have hP := L.analyticOnNhd_weierstrassP (-z₂) hnegz₂
  have hP' := L.analyticOnNhd_derivWeierstrassP (-z₂) hnegz₂
  have hEx : AnalyticAt ℂ (fun z ↦ ℘[L - (0 : ℂ)] (z + z₂)) (-z₂) :=
    (L.analyticAt_weierstrassPExcept 0).comp_of_eq (by fun_prop) (by simp)
  fun_prop

attribute [local fun_prop] AnalyticAt.contDiffAt in
private lemma analyticAt_addRelation_negZ2 (hz₂ : z₂ ∉ L.lattice) :
    AnalyticAt ℂ (L.addRelation z₂) (-z₂) := by
  have hnegz₂ : -z₂ ∉ L.lattice := fun h ↦ hz₂ (by simpa using neg_mem h)
  have hPc : ∀ n : WithTop ℕ∞, ContDiffAt ℂ n ℘[L] (-z₂) :=
    fun _ ↦ (L.analyticOnNhd_weierstrassP (-z₂) hnegz₂).contDiffAt
  have hP'c : ∀ n : WithTop ℕ∞, ContDiffAt ℂ n ℘'[L] (-z₂) :=
    fun _ ↦ (L.analyticOnNhd_derivWeierstrassP (-z₂) hnegz₂).contDiffAt
  have hExc : ∀ n : WithTop ℕ∞, ContDiffAt ℂ n (fun z ↦ ℘[L - (0 : ℂ)] (z + z₂)) (-z₂) :=
    fun _ ↦ ((L.analyticAt_weierstrassPExcept 0).comp_of_eq (by fun_prop) (by simp)).contDiffAt
  have p0 : iteratedDeriv 0 ℘[L] (-z₂) = ℘[L] z₂ := by simp
  have p1 : iteratedDeriv 1 ℘[L] (-z₂) = -℘'[L] z₂ := by
    rw [iteratedDeriv_one, congr_fun L.deriv_weierstrassP]; simp
  have p2 : iteratedDeriv 2 ℘[L] (-z₂) = 6 * ℘[L] z₂ ^ 2 - L.g₂ / 2 := by
    rw [L.iteratedDeriv_two_weierstrassP hnegz₂]; simp
  have q0 : iteratedDeriv 0 ℘'[L] (-z₂) = -℘'[L] z₂ := by simp
  have q1 : iteratedDeriv 1 ℘'[L] (-z₂) = 6 * ℘[L] z₂ ^ 2 - L.g₂ / 2 := by
    rw [iteratedDeriv_one, L.deriv_derivWeierstrassP hnegz₂]; simp
  have h3 : iteratedDeriv 3 ℘[L] (-z₂) = iteratedDeriv 2 ℘'[L] (-z₂) := by
    rw [iteratedDeriv_succ', L.deriv_weierstrassP]
  have q2 : iteratedDeriv 2 ℘'[L] (-z₂) = -(12 * ℘[L] z₂ * ℘'[L] z₂) := by
    rw [← h3, L.iteratedDeriv_three_weierstrassP hnegz₂]
    simp only [weierstrassP_neg, derivWeierstrassP_neg]; ring
  have horder : meromorphicOrderAt (fun z : ℂ ↦ (z + z₂) ^ 2) (-z₂) = 2 := by
    have he : (fun z : ℂ ↦ (z + z₂) ^ 2) = ((· - -z₂) ^ 2 : ℂ → ℂ) := by
      ext z; simp [sub_neg_eq_add]
    rw [he]; simpa using meromorphicOrderAt_pow_id_sub_const (x := (-z₂ : ℂ)) (n := 2)
  refine analyticAt_of_mul_uniformiser (by fun_prop) (by fun_prop) (by simp [addRelation])
    horder (L.analyticAt_addRelation_mul_add_sq hz₂) fun i hi₁ ↦ ?_
  rw [(L.addRelation_mul_add_sq_eventuallyEq hz₂).iteratedDeriv_eq]
  simp_rw [pow_succ (_ - _), pow_zero, one_mul]
  simp (discharger := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_fun_sub,
    iteratedDeriv_fun_mul, iteratedDeriv_const, iteratedDeriv_div_const,
    iteratedDeriv_fun_pow_zero, iteratedDeriv_weierstrassPExcept_self,
    L.iteratedDeriv_wPExcept_add_negZ2, iteratedDeriv_add_sq_negZ2]
  interval_cases i <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, q0, q1, q2,
      weierstrassPExcept_zero, sumInvPow_zero, g₂, Nat.choose, Nat.factorial,
      Nat.choose_self] <;>
    push_cast <;>
    ring_nf

private lemma analyticAt_addRelation (hz₂ : z₂ ∉ L.lattice) (x : ℂ) :
    AnalyticAt ℂ (L.addRelation z₂) x := by
  by_cases hx : x ∈ L.lattice
  · have key : (fun z ↦ L.addRelation z₂ (z - x)) = L.addRelation z₂ := by
      ext a; exact L.addRelation_sub_coe a ⟨x, hx⟩
    rw [← key]
    exact (L.analyticAt_addRelation_zero hz₂).comp_of_eq (by fun_prop) (by ring)
  by_cases hx2 : x + z₂ ∈ L.lattice
  · have key : (fun z ↦ L.addRelation z₂ (z - (x + z₂))) = L.addRelation z₂ := by
      ext a; exact L.addRelation_sub_coe a ⟨x + z₂, hx2⟩
    rw [← key]
    exact (L.analyticAt_addRelation_negZ2 hz₂).comp_of_eq (by fun_prop) (by ring)
  · have hnx : x ∉ L.lattice := hx
    have hnx2 : x + z₂ ∉ L.lattice := hx2
    have hAx : AnalyticAt ℂ (fun z ↦ ℘[L] (z + z₂)) x :=
      (L.analyticOnNhd_weierstrassP (x + z₂) hnx2).comp_of_eq (by fun_prop) rfl
    have hP := L.analyticOnNhd_weierstrassP x hnx
    have hP' := L.analyticOnNhd_derivWeierstrassP x hnx
    have hsmooth : AnalyticAt ℂ (fun z ↦ (℘[L] (z + z₂) + ℘[L] z + ℘[L] z₂)
        * (℘[L] z - ℘[L] z₂) ^ 2 - (℘'[L] z - ℘'[L] z₂) ^ 2 / 4) x := by fun_prop
    have hopen : IsOpen {w : ℂ | w ∉ L.lattice ∧ w + z₂ ∉ L.lattice} := by
      rw [Set.setOf_and]
      exact (L.isClosed_lattice.isOpen_compl).inter
        ((continuous_add_const z₂).isOpen_preimage _ L.isClosed_lattice.isOpen_compl)
    apply hsmooth.congr
    filter_upwards [hopen.mem_nhds ⟨hnx, hnx2⟩] with w hw
    rw [addRelation, if_neg (show ¬(w ∈ L.lattice ∨ w + z₂ ∈ L.lattice) from
      not_or.mpr ⟨hw.1, hw.2⟩)]

private lemma addRelation_eq_zero (hz₂ : z₂ ∉ L.lattice) : L.addRelation z₂ = 0 := by
  ext x
  refine (Differentiable.eq_of_zLattice_periodic
    (fun x ↦ (L.analyticAt_addRelation hz₂ x).differentiableAt) L.lattice
    (fun w hw z ↦ by lift w to L.lattice using hw; simp) x 0).trans (if_pos (by simp))

/-- **The addition theorem for the Weierstrass `℘`-function**, in polynomial form: for
`z₁, z₂, z₁ + z₂` off the lattice,

`(℘(z₁+z₂) + ℘(z₁) + ℘(z₂)) · (℘(z₁) - ℘(z₂))² = (℘'(z₁) - ℘'(z₂))² / 4`.

No `℘(z₁) ≠ ℘(z₂)` hypothesis is needed in this form; dividing by `(℘(z₁) - ℘(z₂))²`
when nonzero recovers the classical
`℘(z₁+z₂) = ¼((℘'(z₁)-℘'(z₂))/(℘(z₁)-℘(z₂)))² - ℘(z₁) - ℘(z₂)`. -/
theorem weierstrassP_add_sq (z₁ : ℂ) (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice)
    (h₁₂ : z₁ + z₂ ∉ L.lattice) :
    (℘[L] (z₁ + z₂) + ℘[L] z₁ + ℘[L] z₂) * (℘[L] z₁ - ℘[L] z₂) ^ 2
      = (℘'[L] z₁ - ℘'[L] z₂) ^ 2 / 4 := by
  have := congr($(L.addRelation_eq_zero h₂) z₁)
  simp only [addRelation, if_neg (not_or.mpr ⟨h₁, h₁₂⟩), Pi.zero_apply] at this
  linear_combination this

/-- The `z₁`-derivative of the addition theorem: the polynomial identity determining
`℘'(z₁+z₂)·(℘(z₁)-℘(z₂))²`. Obtained by differentiating `weierstrassP_add_sq` in `z₁`
on the open set where it holds, using `℘'' = 6℘² - g₂/2`. -/
theorem derivWeierstrassP_add_sq (z₁ : ℂ) (h₁ : z₁ ∉ L.lattice) (h₂ : z₂ ∉ L.lattice)
    (h₁₂ : z₁ + z₂ ∉ L.lattice) :
    ℘'[L] (z₁ + z₂) * (℘[L] z₁ - ℘[L] z₂) ^ 2
      = (℘'[L] z₁ - ℘'[L] z₂) * (6 * ℘[L] z₁ ^ 2 - L.g₂ / 2) / 2
        - ℘'[L] z₁ * (℘[L] z₁ - ℘[L] z₂) ^ 2
        - 2 * (℘[L] (z₁ + z₂) + ℘[L] z₁ + ℘[L] z₂) * (℘[L] z₁ - ℘[L] z₂) * ℘'[L] z₁ := by
  -- The addition identity holds on the open set where `z, z + z₂ ∉ Λ`, so its two sides
  -- (as functions of `z₁`) agree near `z₁`, hence have equal derivatives.
  have hEq : (fun z ↦ (℘[L] (z + z₂) + ℘[L] z + ℘[L] z₂) * (℘[L] z - ℘[L] z₂) ^ 2)
      =ᶠ[𝓝 z₁] fun z ↦ (℘'[L] z - ℘'[L] z₂) ^ 2 / 4 := by
    have hmem2 : {z : ℂ | z + z₂ ∉ L.lattice} ∈ 𝓝 z₁ :=
      (continuous_add_const z₂).continuousAt.preimage_mem_nhds
        (L.isClosed_lattice.isOpen_compl.mem_nhds h₁₂)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds h₁, hmem2] with z hz hz'
    exact L.weierstrassP_add_sq z hz h₂ hz'
  have hP1 : HasDerivAt ℘[L] (℘'[L] z₁) z₁ := by
    rw [← congr_fun L.deriv_weierstrassP z₁]
    exact (L.analyticOnNhd_weierstrassP z₁ h₁).differentiableAt.hasDerivAt
  have hP12 : HasDerivAt ℘[L] (℘'[L] (z₁ + z₂)) (z₁ + z₂) := by
    rw [← congr_fun L.deriv_weierstrassP (z₁ + z₂)]
    exact (L.analyticOnNhd_weierstrassP (z₁ + z₂) h₁₂).differentiableAt.hasDerivAt
  have hP1' : HasDerivAt ℘'[L] (6 * ℘[L] z₁ ^ 2 - L.g₂ / 2) z₁ := by
    rw [← L.deriv_derivWeierstrassP h₁]
    exact (L.analyticOnNhd_derivWeierstrassP z₁ h₁).differentiableAt.hasDerivAt
  have hA : HasDerivAt (fun z ↦ ℘[L] (z + z₂)) (℘'[L] (z₁ + z₂)) z₁ :=
    hP12.comp_add_const z₁ z₂
  have hF : HasDerivAt (fun z ↦ (℘[L] (z + z₂) + ℘[L] z + ℘[L] z₂) * (℘[L] z - ℘[L] z₂) ^ 2)
      ((℘'[L] (z₁ + z₂) + ℘'[L] z₁) * (℘[L] z₁ - ℘[L] z₂) ^ 2
        + (℘[L] (z₁ + z₂) + ℘[L] z₁ + ℘[L] z₂)
          * (2 * (℘[L] z₁ - ℘[L] z₂) ^ (2 - 1) * ℘'[L] z₁)) z₁ :=
    ((hA.add hP1).add_const (℘[L] z₂)).mul ((hP1.sub_const (℘[L] z₂)).pow 2)
  have hG : HasDerivAt (fun z ↦ (℘'[L] z - ℘'[L] z₂) ^ 2 / 4)
      (2 * (℘'[L] z₁ - ℘'[L] z₂) ^ (2 - 1) * (6 * ℘[L] z₁ ^ 2 - L.g₂ / 2) / 4) z₁ :=
    ((hP1'.sub_const (℘'[L] z₂)).pow 2).div_const 4
  have key := hEq.deriv_eq
  rw [hF.deriv, hG.deriv] at key
  linear_combination key

end Addition

end PeriodPair
