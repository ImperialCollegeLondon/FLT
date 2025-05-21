/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.HaarMeasure.HaarChar.AddEquiv
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.MeasureTheory.Group.Pointwise

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

open Measure

variable {R : Type*} [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

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
  sorry -- FLT#516

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
    {X : Set R} (hf : MeasurableSet X) (u : Rˣ) :
    μ (u • X) = ringHaarChar u * μ X := by
  simp [ringHaarChar_toFun,
    addEquivAddHaarChar_smul_preimage _ (hf.const_smul _) (ContinuousAddEquiv.mulLeft u)]

variable (R) in
/-- The kernel of the `ringHaarChar : Rˣ → ℝ≥0`, namely the units
of a locally compact topological ring such that left multiplication
by them does not change additive Haar measure.
-/
noncomputable def ringHaarChar_ker := MonoidHom.ker (ringHaarChar : Rˣ →ₜ* ℝ≥0).toMonoidHom

section units

variable {R S : Type*} [Monoid R] [Monoid S]

-- do we want these next three definitions?
/-- The canonical map `Rˣ → Sˣ → (R × S)ˣ`. -/
def _root_.Units.prod (u : Rˣ) (v : Sˣ) : (R × S)ˣ where
  val := (u, v)
  inv := ((u⁻¹ : Rˣ), (v⁻¹ : Sˣ))
  val_inv := by simp
  inv_val := by simp

/-- The canonical projection (R × S)ˣ → Rˣ as a group homomorphism. -/
def _root_.Units.fst : (R × S)ˣ →* Rˣ :=  Units.map (MonoidHom.fst R S)

/-- The canonical projection (R × S)ˣ → Sˣ as a group homomorphism. -/
def _root_.Units.snd : (R × S)ˣ →* Sˣ :=  Units.map (MonoidHom.snd R S)

end units
section prod

variable {S : Type*} [Ring S] [TopologicalSpace S]
  [IsTopologicalRing S] [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]

-- this is true in general, but the proof is easier if we assume
-- `SecondCountableTopologyEither R S` because then if R and S are equipped with the Borel
-- sigma algebra, the product sigma algebra on R × S is also the Borel sigma algebra.
lemma ringHaarChar_prod (u : Rˣ) (v : Sˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar (u.prod v) = ringHaarChar u * ringHaarChar v :=
  addEquivAddHaarChar_prodCongr (ContinuousAddEquiv.mulLeft u) (ContinuousAddEquiv.mulLeft v)

lemma ringHaarChar_prod' (uv : (R × S)ˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar uv = ringHaarChar uv.fst * ringHaarChar uv.snd :=
  ringHaarChar_prod uv.fst uv.snd

-- right now I think we're supposed to state them like this :-/
example (u : Rˣ) (v : Sˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar (MulEquiv.prodUnits.symm (u, v)) = ringHaarChar u * ringHaarChar v :=
  ringHaarChar_prod u v

-- right now I think we're supposed to state them like this :-/
example (uv : (R × S)ˣ) :
    letI : MeasurableSpace (R × S) := borel (R × S)
    haveI : BorelSpace (R × S) := ⟨rfl⟩
    ringHaarChar uv =
    ringHaarChar (MulEquiv.prodUnits uv).1 * ringHaarChar (MulEquiv.prodUnits uv).2 :=
  ringHaarChar_prod' uv

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

end MeasureTheory
