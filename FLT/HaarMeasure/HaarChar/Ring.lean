/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.HaarMeasure.HaarChar.AddEquiv

open scoped NNReal

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
  map_add' x₁ x₂ := left_distrib (↑r) x₁ x₂
  continuous_toFun := continuous_mul_left _
  continuous_invFun := continuous_mul_left _

end ContinuousAddEquiv

namespace MeasureTheory

open Measure

variable {R : Type*} [Ring R] [MeasurableSpace R] [TopologicalSpace R] [BorelSpace R]
  [IsTopologicalRing R] [LocallyCompactSpace R]

variable (R) in
lemma ringHaarChar_continuous :
    Continuous (fun (u : Rˣ) ↦ addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)) := by
  /-
    Fix a Haar measure $\mu$ on $R$ and a continuous real-valued function
  on $R$ with compact support and such that $\int f(x) d\mu(x)\not=0$.
  Then $u \mapsto \int f(ux) d\mu(x)$ is a continuous function
  of $R\to\R$ (because a continuous function with compact support is uniformly
   continuous) and thus gives a continuous function $R^\times\to\R$.
   Thus the function $u\mapsto (\int f(ux) d\mu(x))/(\int f(x)d\mu(x))$ is
   a continuous function from $R^\times$ to $\R$ taking values in $\R_{>0}$.
   Hence $\delta_R$ is continuous, from `mulEquivHaarChar_mul_integral`
   in the AddEquiv file
   -/
  sorry -- FLT#task008

/-- `ringHaarChar : Rˣ →ₜ* ℝ≥0` is the function sending a unit of
a locally compact topological ring `R` to the positive real factor
which left multiplication by the unit scales additive Haar measure by.
-/
@[simps]
noncomputable def ringHaarChar : Rˣ →ₜ* ℝ≥0 where
  toFun r := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r)
  map_one' := by convert addEquivAddHaarChar_refl (G := R); ext; simp
  map_mul' φ ψ := by
    rw [mul_comm]
    convert addEquivAddHaarChar_trans (G := R); ext; simp [mul_assoc]
  continuous_toFun := ringHaarChar_continuous R

lemma ringHaarChar_mul_integral (μ : Measure R) [IsAddHaarMeasure μ]
    {f : R → ℝ} (hf : Measurable f) (u : Rˣ) :
    (ringHaarChar u) * ∫ (r : R), f (u * r) ∂μ = ∫ a, f a ∂μ := sorry -- FLT#task006
    -- addEquivAddHaarChar_mul_integral

open Pointwise in
lemma ringHaarChar_mul_volume (μ : Measure R) [IsAddHaarMeasure μ]
    {X : Set R} (hf : MeasurableSet X) (u : Rˣ) :
    μ (u • X) = ringHaarChar u * μ X := sorry -- FLT#task007

variable (R) in
/-- The kernel of the `ringHaarChar : Rˣ → ℝ≥0`, namely the units
of a locally compact topological ring such that left multiplication
by them does not change additive Haar measure.
-/
noncomputable def ringHaarChar_ker := MonoidHom.ker (ringHaarChar : Rˣ →ₜ* ℝ≥0).toMonoidHom

end MeasureTheory
