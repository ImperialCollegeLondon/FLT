/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.HaarMeasure.HaarChar.AddEquiv
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.MeasureTheory.Group.Pointwise
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

open scoped NNReal

namespace ContinuousAddEquiv

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The additive homeomorphism from a topological ring to itself,
induced by left multiplication by a unit.
-/
@[simps apply]
def mulLeft (r : Rˣ) : R ≃ₜ+ R where
  toFun x := r * x
  invFun y := r⁻¹ * y
  left_inv x := by simp
  right_inv y := by simp
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

lemma ringHaarChar_continuous :
    Continuous (fun (u : Rˣ) ↦ addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)) := by
  suffices
    hf : Continuous (fun (u : Rˣ) ↦ (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) : ℝ)) from
    continuous_induced_rng.mpr hf
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(R, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero : ∫ x, f x ∂addHaar ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  have h (u : Rˣ) :=
      addEquivAddHaarChar_smul_integral_map addHaar (ContinuousAddEquiv.mulLeft u) (f := f)
  conv at h => ext; rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [ContinuousAddEquiv.mulLeft_apply, NNReal.smul_def, smul_eq_mul] at h
  let g (u : Rˣ) (x : R) := f (u * x)
  have int_g_ne_zero (u : Rˣ) : ∫ (x : R), g u x ∂addHaar ≠ 0 := by
    have hu := h u
    contrapose! hu
    simp [g, hu, int_f_ne_zero.symm]
  rw [← funext (fun u ↦ div_eq_of_eq_mul (int_g_ne_zero u) (h u).symm)]
  refine Continuous.div continuous_const ?_ (fun u ↦ int_g_ne_zero u)
  rw [continuous_iff_continuousAt]
  intro u₀
  obtain ⟨K, hK, hu₀⟩ := exists_compact_mem_nhds (↑u₀⁻¹ : R)
  let s := (fun (u : Rˣ) ↦ (↑u⁻¹ : R)) ⁻¹' K
  refine ContinuousOn.continuousAt ?_
    (ContinuousAt.preimage_mem_nhds (by fun_prop) (by exact hu₀) : s ∈ nhds u₀)
  apply continuousOn_integral_of_compact_support (hK.mul f_comp) (by fun_prop)
  intro p x hps hx
  unfold g
  apply image_eq_zero_of_notMem_tsupport
  contrapose! hx
  exact ⟨(↑p⁻¹ : R) , hps, p * x, hx, by simp⟩

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
  continuous_toFun := ringHaarChar_continuous

lemma ringHaarChar_mul_integral
    (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {f : R → ℝ} (hf : Measurable f) (u : Rˣ) :
    (ringHaarChar u) * ∫ (r : R), f (u * r) ∂μ = ∫ a, f a ∂μ := by
  symm
  convert (addEquivAddHaarChar_smul_integral_map μ (ContinuousAddEquiv.mulLeft u) (f := f)).symm
    using 1
  simp only [ringHaarChar_toFun, NNReal.smul_def, smul_eq_mul, mul_eq_mul_left_iff,
    NNReal.coe_eq_zero]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp

open Pointwise in
lemma ringHaarChar_mul_volume (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {X : Set R} (u : Rˣ) :
    μ (u • X) = ringHaarChar u * μ X := by
  rw [ringHaarChar_toFun, (addEquivAddHaarChar_smul_preimage _ (ContinuousAddEquiv.mulLeft u)).symm]
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
lemma ringHaarChar_prod (u : Rˣ) (v : Sˣ) [MeasurableSpace (R × S)] [BorelSpace (R × S)] :
    ringHaarChar (MulEquiv.prodUnits.symm (u, v)) = ringHaarChar u * ringHaarChar v :=
  addEquivAddHaarChar_prodCongr (ContinuousAddEquiv.mulLeft u) (ContinuousAddEquiv.mulLeft v)

lemma ringHaarChar_prod' (uv : (R × S)ˣ) [MeasurableSpace (R × S)] [BorelSpace (R × S)] :
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
    ringHaarChar u = ∏ᶠ i, ringHaarChar (MulEquiv.restrictedProductUnits u i) := by
  set u := MulEquiv.restrictedProductUnits u
  apply addEquivAddHaarChar_restrictedProductCongrRight (C := (C · |>.toAddSubgroup))
    (ContinuousAddEquiv.mulLeft <| u ·)
  refine Filter.Eventually.and u.coe_prop u⁻¹.coe_prop |>.mono fun i ⟨hu, hv⟩ ↦ ⟨?_, ?_, ?_⟩
  · exact fun _ ↦ (C i).mul_mem ((C i).mem_units_iff _ |>.mp hu).1
  · exact Set.injOn_of_injective (ContinuousAddEquiv.injective _)
  · exact fun c hc ↦ ⟨(u i)⁻¹ * c, (C i).mul_mem ((C i).mem_units_iff _ |>.mp hv).1 hc, by simp⟩

end restrictedproduct

section ModuleFinite

variable {K R : Type*} [Field K] [Ring R] [Algebra K R] [Module.Finite K R]
    [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology K R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [IsTopologicalRing K] [LocallyCompactSpace K]
    (t : Kˣ)

/-- The Borel measurable space instance on Fin n → K. A local instance. -/
local instance : MeasurableSpace (Fin (Module.finrank K R) → K) :=
  borel (Fin (Module.finrank K R) → K)

local instance : BorelSpace (Fin (Module.finrank K R) → K) where
  measurable_eq := rfl

theorem ringHaarChar_ModuleFinite :
    ringHaarChar (Units.map (algebraMap K R).toMonoidHom t) =
    ringHaarChar (R := (Fin (Module.finrank K R) → K))
      (Units.map (algebraMap K (Fin (Module.finrank K R) → K)).toMonoidHom t) := by
  apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    ((IsModuleTopology.Module.Basis.equivFun_homeo _ _).toContinuousAddEquiv)
  intro x
  -- this would not be needed if `mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv`
  -- ate a ContinuousMulEquivClass instead of a ContinuousMulEquiv.
  -- Unfortunately there's no such class :-(
  change (IsModuleTopology.Module.Basis.equivFun_homeo K R) _ =
    (ContinuousAddEquiv.mulLeft ((Units.map ↑(algebraMap K (Fin (Module.finrank K R) → K))) t))
    ((IsModuleTopology.Module.Basis.equivFun_homeo K R) x)
  simp [← Algebra.smul_def]

variable [MeasurableSpace K] [BorelSpace K]

theorem ringHaarChar_ModuleFinite_unit :
    ringHaarChar (Units.map (algebraMap K R).toMonoidHom t) =
    (ringHaarChar t) ^ (Module.finrank K R) := by
  rw [ringHaarChar_ModuleFinite]
  simpa using ringHaarChar_pi (ι := Fin (Module.finrank K R))
      (A := fun _ : Fin (Module.finrank K R) => K) (fun (i : Fin (Module.finrank K R)) ↦ t)


end ModuleFinite

end MeasureTheory
