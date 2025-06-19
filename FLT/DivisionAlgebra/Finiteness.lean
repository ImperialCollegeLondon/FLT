/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ludwig Monnerjahn, Hannah Scholz
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.Group.Subgroup.Pointwise
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Algebra.Central.Defs
import Mathlib.Tactic.LinearCombination'
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.Ring
import FLT.HaarMeasure.HaarChar.AdeleRing

/-

# Fujisaki's lemma

We prove a lemma which Voight (in his quaternion algebra book) attributes to Fujisaki:
if `D` is a finite-dimensional division algebra over a number field `K`
and if `U ⊆ (D ⊗[K] 𝔸_K^infty)ˣ` is a compact open subgroup then the double coset
space `Dˣ \ (D ⊗[K] 𝔸_K^infty)ˣ / U` is finite.

-/

suppress_compilation

open IsDedekindDomain MeasureTheory

open scoped NumberField TensorProduct

variable (K : Type*) [Field K] [NumberField K]
variable (D : Type*) [DivisionRing D] [Algebra K D] [FiniteDimensional K D]

namespace NumberField.AdeleRing.DivisionAlgebra

set_option quotPrecheck false in
/-- `D_𝔸` is notation for `D ⊗[K] 𝔸_K`. -/
notation "D_𝔸" => (D ⊗[K] AdeleRing (𝓞 K) K)

open scoped TensorProduct.RightActions

variable [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)]

/-- The inclusion Dˣ → D_𝔸ˣ as a group homomorphism. -/
noncomputable abbrev incl : Dˣ →* D_𝔸ˣ :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

namespace Aux

lemma existsE : ∃ E : Set (D_𝔸), IsCompact E ∧
    ∀ φ : D_𝔸 ≃ₜ+ D_𝔸, addEquivAddHaarChar φ = 1 → ∃ e₁ ∈ E, ∃ e₂ ∈ E,
    e₁ ≠ e₂ ∧ φ e₁ - φ e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  sorry

/-- An auxiliary set E used in the proof of Fukisaki's lemma. -/
def E : Set D_𝔸 := (existsE K D).choose

lemma E_compact : IsCompact (E K D) := (existsE K D).choose_spec.1

lemma E_noninjective_left {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    x * e₁ - x * e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  (existsE K D).choose_spec.2 (ContinuousAddEquiv.mulLeft x) h

lemma E_noninjective_right {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    e₁ * x⁻¹ - e₂ * x⁻¹  ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  let φ : D_𝔸 ≃ₜ+ D_𝔸 := ContinuousAddEquiv.mulRight x⁻¹
  have hφ : addEquivAddHaarChar φ = 1 := sorry
  exact (existsE K D).choose_spec.2 φ hφ

open scoped Pointwise in
/-- An auxiliary set X used in the proof of Fukisaki's lemma. Defined as E - E. -/
def X : Set D_𝔸 := E K D - E K D

open scoped Pointwise in
/-- An auxiliary set Y used in the proof of Fukisaki's lemma. Defined as X * X. -/
def Y : Set D_𝔸 := X K D * X K D

lemma X_compact : IsCompact (X K D) := by
  simpa only [Set.image_prod, Set.image2_sub] using (IsCompact.image_of_continuousOn
    ((E_compact K D).prod (E_compact K D)) ((continuous_fst.sub continuous_snd).continuousOn))

lemma Y_compact : IsCompact (Y K D) := by
  simpa only [Set.image_prod, Set.image2_mul] using (IsCompact.image_of_continuousOn
    ((X_compact K D).prod (X_compact K D)) ((continuous_fst.mul continuous_snd).continuousOn))

lemma X_meets_kernel {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ x ∈ X K D, ∃ d ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ), β * x = d := by
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_left K D hβ
  refine ⟨e1 - e2, by simpa only using (Set.sub_mem_sub he1 he2), ?_⟩
  obtain ⟨b1, rfl⟩ : IsUnit b := by
    simp_rw [← mul_sub_left_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
    have h1 : ↑β * (e1 - e2) ≠ 0 := by
      simpa only [ne_eq, not_not, Units.mul_right_eq_zero] using (sub_ne_zero_of_ne noteq)
    simp only [isUnit_iff_ne_zero, ne_eq]
    rintro rfl
    simp only [← hb, TensorProduct.zero_tmul, ne_eq, not_true_eq_false] at h1
  exact ⟨incl K D b1, ⟨b1, rfl⟩, by simpa [mul_sub] using hb.symm⟩

lemma X_meets_kernel' {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ x ∈ X K D, ∃ d ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ), x * β⁻¹ = d := by
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_right K D hβ
  refine ⟨e1 - e2, by simpa only using (Set.sub_mem_sub he1 he2), ?_⟩
  obtain ⟨b1, rfl⟩ : IsUnit b := by
    simp_rw [← mul_sub_right_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
    have h1 : (e1 - e2) * ↑β⁻¹ ≠ 0 := by
      simpa only [ne_eq, Units.mul_left_eq_zero] using (sub_ne_zero_of_ne noteq)
    simp only [isUnit_iff_ne_zero, ne_eq]
    rintro rfl
    simp only [← hb, TensorProduct.zero_tmul, ne_eq, not_true_eq_false] at h1
  exact ⟨incl K D b1, ⟨b1, rfl⟩, by simpa [sub_mul] using hb.symm⟩

/-- An auxiliary set T used in the proof of Fukisaki's lemma. Defined as Y ∩ Dˣ. -/
def T : Set D_𝔸ˣ := ((↑) : D_𝔸ˣ → D_𝔸) ⁻¹' (Y K D) ∩ Set.range ((incl K D : Dˣ → D_𝔸ˣ))

-- Need something saying D ⊆ D_𝔸 is discrete

lemma T_finite : Set.Finite (T K D) := by
  have h : Set.Finite ((Y K D) ∩ (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)))
      := by
    apply IsCompact.finite
    · refine IsCompact.inter_right (Y_compact K D) ?_

      -- Subgroup.isClosed_of_discrete
      sorry
    · -- follows form D being discrete

      sorry
  have h1 : Units.val '' T K D ⊆ (Y K D) ∩
      (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
    rintro _ ⟨t, ⟨ht1, d, rfl⟩, rfl⟩
    exact ⟨ht1, d, rfl⟩
  exact Set.Finite.of_finite_image (Set.Finite.subset h h1) (Function.Injective.injOn Units.ext)

open scoped Pointwise in
/-- An auxiliary set C used in the proof of Fukisaki's lemma. Defined as T⁻¹X × X. -/
def C : Set (D_𝔸 × D_𝔸) := ((((↑) : D_𝔸ˣ → D_𝔸) '' (T K D)⁻¹) * X K D) ×ˢ X K D

lemma C_compact : IsCompact (C K D) := by
  refine IsCompact.prod ?_ (X_compact K D)
  simpa only [Set.image_prod, Set.image2_mul] using
    (IsCompact.image_of_continuousOn (IsCompact.prod (IsCompact.image_of_continuousOn
    (IsCompact.inv (Set.Finite.isCompact (T_finite K D))) (Continuous.comp_continuousOn'
    (Units.continuous_val) (continuousOn_id' (T K D)⁻¹)))
    (X_compact K D)) ((continuous_fst.mul continuous_snd).continuousOn))

lemma antidiag_mem_C {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ b ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ),
    ∃ ν ∈ ringHaarChar_ker D_𝔸,
    β = b * ν ∧ ((ν : D_𝔸), ((ν⁻¹ : D_𝔸ˣ) : D_𝔸)) ∈ C K D := by
  obtain ⟨x1, hx1, b1, ⟨b1, rfl⟩, eq1⟩ := X_meets_kernel K D hβ
  obtain ⟨x2, hx2, b2, ⟨b2, rfl⟩, eq2⟩ := X_meets_kernel' K D hβ
  obtain ⟨x1, rfl⟩ : IsUnit x1 := ⟨↑β⁻¹ * incl K D b1,
    ((Units.eq_inv_mul_iff_mul_eq β).mpr eq1).symm⟩
  obtain ⟨x2, rfl⟩ : IsUnit x2 := ⟨incl K D b2 * β, ((Units.mul_inv_eq_iff_eq_mul β).mp eq2).symm⟩
  have h : x2 * x1 ∈ T K D := ⟨by simpa only [Y] using (Set.mul_mem_mul hx2 hx1), b2 * b1,
    by simpa using Units.eq_iff.mp (id (Eq.symm (by simpa [mul_assoc] using
    (Mathlib.Tactic.LinearCombination'.mul_pf eq2 eq1))))⟩
  refine ⟨incl K D b1, by simp only [Set.mem_range, exists_apply_eq_apply],  x1⁻¹, ?_,
    eq_mul_inv_of_mul_eq (Units.eq_iff.mp eq1), ?_, hx1⟩
  · rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq (Units.eq_iff.mp eq1))))]
    exact (Subgroup.mul_mem_cancel_right (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K)) hβ).mpr
      ((Subgroup.inv_mem_iff (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))).mpr
      (NumberField.AdeleRing.units_mem_ringHaarCharacter_ker K D b1))
  · obtain ⟨t, ht, ht1⟩ := exists_eq_right'.mpr h
    simp_rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq ht1)))]
    exact Set.mem_mul.mpr ⟨↑t⁻¹, Set.mem_image_of_mem Units.val ht, x2, hx2, rfl⟩

end Aux

lemma compact_quotient : CompactSpace (_root_.Quotient (QuotientGroup.rightRel
      ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) := sorry

end NumberField.AdeleRing.DivisionAlgebra

section FiniteAdeleRing

variable [FiniteDimensional K D]

-- Instance to help speed up instance synthesis
instance : NonUnitalNonAssocRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance : NonAssocSemiring (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

variable [Algebra.IsCentral K D]

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

open scoped TensorProduct.RightActions in
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) := by
  sorry

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If `D` is a finite-dimensional division algebra over a number field `K`
then the double coset space `Dˣ \ (D ⊗ 𝔸_K^infty)ˣ / U` is finite for any compact open subgroup `U`
of `(D ⊗ 𝔸_F^infty)ˣ`.
-/

open scoped TensorProduct.RightActions in
def map₁ (U : Subgroup (Dfx K D)) : (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) →
    (Doset.Quotient (Set.range (incl₁ K D)) U) :=
  fun x => Quotient.mk'' x.out

lemma map₁_surjective (U : Subgroup (Dfx K D)) : Function.Surjective (map₁ K D U) := by
  refine Set.range_eq_univ.mp ?_
  ext x
  constructor
  · exact fun a ↦ trivial
  · intro hx
    refine Set.mem_range.mpr ?_
    refine Quotient.exists.mpr ?_
    simp_rw [map₁]
    obtain ⟨a, ha⟩ := Quot.exists_rep x
    use a
    have : Quot.mk (⇑(Doset.setoid (Set.range ⇑(incl₁ K D)) ↑U)) a = Quotient.mk'' a := by rfl
    simp_rw [←ha, this]
    -- so tedious

    sorry
    /-
    obtain ⟨b, hb⟩ := Quot.exists_rep x
    have : ∃ a : Dfx K D, (⟦a⟧ : Quotient (QuotientGroup.rightRel (incl₁ K D).range)).out = b := by
      -- this may not be true??... .out is really messing with me here
      sorry
    obtain ⟨a, ha⟩ := this
    use a
    simp_rw [ha]
    exact hb
    -/

  -- I think I need to adapt map₁ so that I am not use a choice function

open scoped TensorProduct.RightActions in
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (Doset.Quotient (Set.range (incl₁ K D)) U) := by
  haveI := NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D
  have := finite_cover_nhds (X := _root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range))
    (U := fun (x : _root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) => {x})
    (by
      intro x


      simp only
      rw [@mem_nhds_iff]
      use {x}
      refine ⟨(fun ⦃a⦄ ↦ congrArg fun ⦃a⦄ ↦ a), ?_, rfl⟩
      -- I dont remember if this is the discrete side or not
      -- maybe? not sure if I have the correct set up for the map U
      sorry
    )
  obtain ⟨t, ht⟩ := this
  haveI : Finite (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) := by
    exact Set.finite_univ_iff.mp (by simpa only [← ht] using Set.toFinite (⋃ x ∈ t, {x}))
  exact Finite.of_surjective (map₁ K D U) (map₁_surjective K D U)

end FiniteAdeleRing
