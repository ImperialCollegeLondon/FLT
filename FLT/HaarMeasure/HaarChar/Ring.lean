/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.HaarMeasure.HaarChar.AddEquiv
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.MeasureTheory.Group.Pointwise

open scoped NNReal Set Pointwise

namespace ContinuousAddEquiv

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

-- TODO move to Mathlib/Topology/Algebra/ContinuousMonoidHom.lean
initialize_simps_projections ContinuousAddEquiv (toFun → apply, invFun → symm_apply)

/-- The additive homeomorphism from a topological ring to itself,
induced by left multiplication by a unit.
-/
@[simps apply]
def mulLeft (r : Rˣ) : R ≃ₜ+ R where
  toFun x := r * x
  invFun y := r⁻¹ * y
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := left_distrib ↑r x₁ x₂
  continuous_toFun := continuous_mul_left _
  continuous_invFun := continuous_mul_left _

/-- The additive homeomorphism from a topological ring to itself,
induced by right multiplication by a unit.
-/
@[simps apply]
def mulRight (r : Rˣ) : R ≃ₜ+ R where
  toFun x := x * r
  invFun y := y * r⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := right_distrib x₁ x₂ r
  continuous_toFun := continuous_mul_right _
  continuous_invFun := continuous_mul_right _

open Pointwise in
@[simp]
lemma preimage_mulLeft_smul (r : Rˣ) (s : Set R) :
    ContinuousAddEquiv.mulLeft r ⁻¹' (r • s) = s := by ext; simp [Set.mem_smul_set, Units.smul_def]

end ContinuousAddEquiv

namespace MeasureTheory

variable {G : Type*} [Group G] (A B : Set G)

open Measure

--set_option trace.Meta.Tactic.fun_prop true
attribute [fun_prop] Units.continuous_val
attribute [fun_prop] Units.continuous_coe_inv

variable {R : Type*} [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

variable (R) in
@[nolint unusedHavesSuffices] -- this can be removed when the proof is complete;
-- if you remove it beforehand, check the linter is happy!
lemma ringHaarChar_continuous :
    Continuous (fun (u : Rˣ) ↦ addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)) := by
  /-
    Fix a Haar measure $\mu$ on $R$ and a continuous real-valued function f
  on $R$ with compact support and such that $\int f(x) d\mu(x)\not=0$.
   -/
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(R, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero : ∫ x, f x ∂addHaar ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  /-
    Then $u \mapsto \int f(ux) d\mu(x)$ is a continuous function
  of $R\to\R$ (because a continuous function with compact support is uniformly
   continuous) and thus gives a continuous function $R^\times\to\R$.
   Thus the function $u\mapsto (\int f(ux) d\mu(x))/(\int f(x)d\mu(x))$ is
   a continuous function from $R^\times$ to $\R$ taking values in $\R_{>0}$.
   Hence $\delta_R$ is continuous, from `mulEquivHaarChar_mul_integral`
   in the AddEquiv file
  -/
  rw[continuous_iff_continuousAt]
  intro u₀
  obtain ⟨K, hK, hu₀⟩ := exists_compact_mem_nhds (↑u₀⁻¹ : R)
  let g (u : Rˣ) (x : R) := f (u * x)
  let s := (fun (u : Rˣ) ↦ (↑u⁻¹ : R)) ⁻¹' K
  have hs : s ∈ nhds u₀ := ContinuousAt.preimage_mem_nhds (by fun_prop) (by exact hu₀)
  have h_comp : IsCompact (K * (tsupport f)) := by exact hK.mul f_comp
  have : ContinuousOn (fun u : Rˣ ↦ ∫ x, g u x ∂addHaar) s := by
    apply continuousOn_integral_of_compact_support h_comp (by fun_prop)
    intro p x hps hx
    unfold g
    apply image_eq_zero_of_notMem_tsupport
    contrapose! hx
    refine ⟨(↑p⁻¹ : R) , hps, p * x, hx, by simp⟩
  refine ContinuousOn.continuousAt ?_ hs



/-- `ringHaarChar : Rˣ →ₜ* ℝ≥0` is the function sending a unit of
a locally compact topological ring `R` to the positive real factor
which left multiplication by the unit scales additive Haar measure by.
-/
@[simps (isSimp := false)]
noncomputable def ringHaarChar : Rˣ →ₜ* ℝ≥0 where
  toFun r := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r)
  map_one' := by convert addEquivAddHaarChar_refl (G := R); ext; simp
  map_mul' φ ψ := by
    rw [mul_comm]
    convert addEquivAddHaarChar_trans (G := R); ext; simp [mul_assoc]
  continuous_toFun := ringHaarChar_continuous R

lemma ringHaarChar_mul_integral
    (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {f : R → ℝ} (hf : Measurable f) (u : Rˣ) :
    (ringHaarChar u) * ∫ (r : R), f (u * r) ∂μ = ∫ a, f a ∂μ := by
  symm
  convert addEquivAddHaarChar_smul_integral_map μ (ContinuousAddEquiv.mulLeft u) (f := f) using 1
  simp only [ringHaarChar_toFun, NNReal.smul_def, smul_eq_mul, mul_eq_mul_left_iff,
    NNReal.coe_eq_zero]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp

open Pointwise in
lemma ringHaarChar_mul_volume (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {X : Set R} (u : Rˣ) :
    μ (u • X) = ringHaarChar u * μ X := by
  rw [ringHaarChar_toFun, addEquivAddHaarChar_smul_preimage _ (ContinuousAddEquiv.mulLeft u)]
  simp


open Pointwise ENNReal in
lemma ringHaarChar_eq_of_measure_smul_eq_mul {μ : Measure R} [IsAddHaarMeasure μ] [μ.Regular]
    {s : Set R} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) {r : ℝ≥0} {u : Rˣ}
    (hμgs : μ (u • s) = r * μ s) : ringHaarChar u = r := by
  rw [ringHaarChar_mul_volume μ u, ENNReal.mul_left_inj hs₀ hs] at hμgs
  assumption_mod_cast

variable (R) in
/-- The kernel of the `ringHaarChar : Rˣ → ℝ≥0`, namely the units
of a locally compact topological ring such that left multiplication
by them does not change additive Haar measure.
-/
noncomputable def ringHaarChar_ker := MonoidHom.ker (ringHaarChar : Rˣ →ₜ* ℝ≥0).toMonoidHom

section prod

variable {S : Type*} [Ring S] [TopologicalSpace S]
  [IsTopologicalRing S] [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]

-- this is true in general, but the proof is easier if we assume
-- `SecondCountableTopologyEither R S` because then if R and S are equipped with the Borel
-- sigma algebra, the product sigma algebra on R × S is also the Borel sigma algebra.
lemma ringHaarChar_prod (u : Rˣ) (v : Sˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar (MulEquiv.prodUnits.symm (u, v)) = ringHaarChar u * ringHaarChar v :=
  addEquivAddHaarChar_prodCongr (ContinuousAddEquiv.mulLeft u) (ContinuousAddEquiv.mulLeft v)

lemma ringHaarChar_prod' (uv : (R × S)ˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar uv =
    ringHaarChar (MulEquiv.prodUnits uv).1 * ringHaarChar (MulEquiv.prodUnits uv).2 :=
  ringHaarChar_prod (MulEquiv.prodUnits uv).1 (MulEquiv.prodUnits uv).2

end prod

section pi

variable {ι : Type*} {A : ι → Type*} [Π i, Ring (A i)] [Π i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)]

lemma ringHaarChar_pi [Fintype ι] (u : Π i, (A i)ˣ) :
    letI : MeasurableSpace (Π i, A i) := borel _
    haveI : BorelSpace (Π i, A i) := ⟨rfl⟩
    ringHaarChar (MulEquiv.piUnits.symm u) = ∏ i, ringHaarChar (u i) :=
  addEquivAddHaarChar_piCongrRight (fun i ↦ ContinuousAddEquiv.mulLeft (u i))

end pi

section restrictedproduct

open scoped RestrictedProduct

variable {ι : Type*} {A : ι → Type*} [Π i, Ring (A i)] [Π i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)]
    {C : (i : ι) → Subring (A i)}
    [hCopen : Fact (∀ (i : ι), IsOpen (C i : Set (A i)))]
    [hCcompact : ∀ i, CompactSpace (C i)]

lemma ringHaarChar_restrictedProduct (u : (Πʳ i, [A i, C i])ˣ) :
    letI : MeasurableSpace (Πʳ i, [A i, C i]) := borel _
    haveI : BorelSpace (Πʳ i, [A i, C i]) := ⟨rfl⟩
    ringHaarChar u = ∏ᶠ i, ringHaarChar (MulEquiv.restrictedProductUnits C u i) := by
  sorry -- FLT#554

end restrictedproduct

end MeasureTheory
