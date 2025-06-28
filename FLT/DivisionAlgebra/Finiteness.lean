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

theorem Doset.finite {G : Type*} [Group G] (H K : Subgroup G) :
    Finite (Quotient (H : Set G) K) ↔ ∃ I : Finset (Quotient (H : Set G) K), Set.univ = ⋃ i : I,
    quotToDoset H K i.1 := by
  constructor
  · intro I
    refine Finset.exists.mpr ⟨Set.univ, Set.finite_univ, ?_⟩
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Subtype.exists, Set.Finite.mem_toFinset, exists_const,
      true_iff]
    exact Set.mem_iUnion.mp (by rw [(Doset.union_quotToDoset H K)]; exact trivial)
  · intro ⟨I, hI⟩
    refine Set.finite_univ_iff.mp ?_
    have : ⋃ (i : I), {i.1} = Set.univ := by
      contrapose hI
      rw [eq_comm, ← ne_eq]
      apply (Set.ne_univ_iff_exists_notMem (⋃ (i : I), {i.1})).mp at hI
      obtain ⟨i, hi⟩ := hI
      refine (Set.ne_univ_iff_exists_notMem (⋃ i : I, quotToDoset H K i.1)).mpr ⟨i.out, ?_⟩
      simp only [Set.mem_iUnion, Subtype.exists, exists_prop, not_exists, not_and]
      contrapose hi
      simp only [Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Finset.setOf_mem,
        Finset.mem_coe, not_not]
      simp only [not_forall, Classical.not_imp, not_not, exists_prop] at hi
      obtain ⟨x, hx1, hx2⟩ := hi
      have : i = x := by
        simpa using (mk_eq_of_doset_eq (doset_eq_of_mem hx2))
      simpa only [this] using hx1
    simp only [← this, Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Finset.setOf_mem,
      Finset.finite_toSet]

-- I guess I could generalise this?
open scoped TensorProduct.RightActions in
lemma Cover_descended (U : Subgroup (Dfx K D)) : ⋃ (q : Doset.Quotient ↑(incl₁ K D).range ↑U),
      Quot.mk (α := Dfx K D) ((QuotientGroup.rightRel (incl₁ K D).range)) ''
      (Doset.doset (Quotient.out q : Dfx K D) (Set.range (incl₁ K D)) (U : Set (Dfx K D))) =
      Set.univ := by
    have Cover_Dfx := Doset.union_quotToDoset ((incl₁ K D).range) U
    refine Eq.symm (Set.Subset.antisymm ?_ fun ⦃a⦄ a ↦ trivial)
    intro x hx
    simp only [MonoidHom.coe_range, Set.mem_iUnion, Set.mem_image]
    obtain ⟨y, hy⟩ := Quot.exists_rep x
    have ⟨i, hi⟩ : ∃ i : Doset.Quotient ↑(incl₁ K D).range ↑U,
       y ∈ Doset.doset (Quotient.out i) (Set.range ⇑(incl₁ K D)) ↑U  := by
      contrapose Cover_Dfx
      refine (Set.ne_univ_iff_exists_notMem (⋃ q, Doset.doset (Quotient.out q)
        (Set.range ⇑(incl₁ K D)) ↑U)).mpr ?_
      exact ⟨y, by simpa using Cover_Dfx⟩
    exact ⟨i, y, hi, hy⟩

local instance : SMul (Dfx K D) (Dfx K D) where
  smul := HMul.hMul

open scoped TensorProduct.RightActions
local instance : ContinuousConstSMul (Dfx K D) (Dfx K D) where
  continuous_const_smul a := by
    simp only [smul_eq_mul]
    exact continuous_mul_left a

-- this can definitely be generalised
lemma doset_isOpen (U : Subgroup (Dfx K D)) (hU : IsOpen (U : Set (Dfx K D))) :
    (∀ (i : Doset.Quotient (Set.range ⇑(incl₁ K D)) ↑U), IsOpen (Quot.mk
      ⇑(QuotientGroup.rightRel (incl₁ K D).range) '' Doset.doset (Quotient.out i)
      (Set.range ⇑(incl₁ K D)) ↑U)) := by
  intro i
  rw [isOpen_coinduced]
  have : (Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) ⁻¹'
      (Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) ''
      Doset.doset (Quotient.out i) (Set.range ⇑(incl₁ K D)) ↑U)) =
      (Doset.doset (Quotient.out i) (Set.range ⇑(incl₁ K D)) ↑U) := by
    ext x
    constructor
    · intro ⟨a, ha1, ha2⟩
      simp_rw [Doset.mem_doset] at ⊢ ha1
      obtain ⟨m, ⟨m', hm'⟩, n, hn, eq⟩ := ha1
      -- from here
      obtain ⟨⟨q, q', hq'⟩, hq⟩ : ∃ q : Set.range ⇑(incl₁ K D), x = q * a := by
        obtain ⟨q, hq⟩  : ∃ q, (incl₁ K D) q * x = a := by
          obtain ⟨⟨o', ⟨o, ho⟩⟩, ho'⟩ := Quotient.eq.mp ha2
          exact ⟨o, by simpa [ho] using ho'⟩
        refine ⟨⟨(incl₁ K D) q⁻¹, ⟨q⁻¹, rfl⟩⟩, eq_inv_mul_of_mul_eq hq⟩
      -- to here
      -- is repeated below (marked again)... this is either a result in mathlib I could not find
      -- or is something I can generalise and pull out
      refine ⟨q * m, ⟨q' * m', by simp only [map_mul, hm', hq']⟩, n, hn, ?_⟩
      simp_rw [mul_assoc, hq, eq]
      nth_rw 3 [← mul_assoc]
    · intro hx
      use x
  simpa only [this] using (IsOpen.mul_left hU)

lemma FinCover_ascended (U : Subgroup (Dfx K D))
    (t : Finset (Doset.Quotient (Set.range ⇑(incl₁ K D)) ↑U)) (ht : Set.univ ⊆ ⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) '' Doset.doset (Quotient.out i)
    (Set.range ⇑(incl₁ K D)) ↑U) : ⋃ q : t, Doset.doset (Quotient.out q.1)
    (Set.range ⇑(incl₁ K D)) ↑U =
    Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem (⋃ q : { x // x ∈ t },
    Doset.doset (Quotient.out q.1) (Set.range ⇑(incl₁ K D)) ↑U)).mp ht
  refine (Set.ne_univ_iff_exists_notMem (⋃ i ∈ t,
    Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) '' Doset.doset (Quotient.out i)
    (Set.range ⇑(incl₁ K D)) ↑U)).mpr ⟨Quot.mk (⇑(QuotientGroup.rightRel (incl₁ K D).range)) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and, ne_eq]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, Subtype.exists, exists_prop, not_exists, not_and, not_forall,
    Classical.not_imp, not_not]
  simp only [ne_eq, not_not] at hx
  refine ⟨y, hy, ?_⟩
  have : Doset.doset q (Set.range (incl₁ K D)) U =
      Doset.doset (Quotient.out y) (Set.range ⇑(incl₁ K D)) ↑U := by
    exact Doset.doset_eq_of_mem (H := (incl₁ K D).range) (K := U) hq
  rw [← this]
  apply Doset.mem_doset.mpr
  -- from here 2
  obtain ⟨a, ha⟩ : ∃ a : Set.range ⇑(incl₁ K D), x = a * q := by
    obtain ⟨a, ha⟩  : ∃ a, (incl₁ K D) a * x = q := by
      obtain ⟨⟨a', ⟨a, ha⟩⟩, ha'⟩ := (Quotient.eq).mp hx
      refine ⟨a, by simpa [ha] using ha'⟩
    refine ⟨⟨(incl₁ K D) a⁻¹, ⟨a⁻¹, rfl⟩⟩, eq_inv_mul_of_mul_eq ha⟩
  -- to here 2
  refine ⟨a.1, ?_⟩
  simp only [Subtype.coe_prop, SetLike.mem_coe, true_and]
  exact ⟨1, Subgroup.one_mem U, by simpa using ha⟩

open scoped TensorProduct.RightActions in
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (Doset.Quotient (Set.range (incl₁ K D)) U) := by
  have ToFinCover :=  isCompact_iff_finite_subcover.mp
    (ι := (Doset.Quotient (Set.range (incl₁ K D)) U))
    (U := fun q ↦ Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) ''
    Doset.doset (Quotient.out q) (Set.range ⇑(incl₁ K D)) U) (isCompact_univ_iff.mpr
    (NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D))
  have ⟨t, FinCover_descended⟩ := ToFinCover (doset_isOpen K D U hU)
    (Cover_descended K D U ▸ Set.Subset.rfl)
  apply (Doset.finite ((incl₁ K D).range) U).mpr
  exact ⟨t, Eq.symm (FinCover_ascended K D U t FinCover_descended)⟩

end FiniteAdeleRing
