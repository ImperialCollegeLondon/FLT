/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
public import FLT.Mathlib.MeasureTheory.Group.ModularCharacter
public import FLT.HaarMeasure.FiniteAdeleRing
public import Mathlib

/-! # The Petersson inner product on quaternion modular forms. -/

@[expose] public section

attribute [-simp] RingHom.toMonoidHom_eq_coe

suppress_compilation

open IsQuaternionAlgebra.NumberField IsDedekindDomain

open scoped FLT

variable {F R : Type*} [Field F] [NumberField F] [CommRing R] [Algebra R ℂ]
variable {D : Type*} [DivisionRing D] [Algebra F D] [WithRigidification F D]


namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

open scoped TensorProduct NumberField Adele

local notation "𝓓ˣ" => MonoidHom.range (WithRigidification.unitsIncl F D)
local notation "𝓕ˣ" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F]))))
local notation "𝔸ˣ" F =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]))))

local notation "ιD" => WithRigidification.unitsIncl F D
local notation "ι𝔸" => Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))
local notation "ℙ(" K ")" => HeightOneSpectrum (𝓞 K)
local notation "𝒪_[" K ", " v "]" => HeightOneSpectrum.adicCompletionIntegers K v

variable (ℒ : LocalLevelStruct F R) (v : ℙ(F)) (hv : ℒ.χ v = 1) (g : GL₂(v.adicCompletion F))

lemma LevelStruct.star_χA (ℒ : LevelStruct F R) (u) :
    starRingEnd ℂ (algebraMap R ℂ (ℒ.χA u)) = (algebraMap R ℂ (ℒ.χA u))⁻¹ := by
  refine (Complex.inv_eq_conj ?_).symm
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.mp (ℒ.isOfFinOrder_χA_apply u)
  refine (Real.rpow_left_inj (z := n) (by simp) (by simp) (by simpa using hn.ne')).mp ?_
  simp [← norm_pow, ← map_pow, e]

/-- The summand appearing in the Petersson inner product. -/
def LevelStruct.innerSummand (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) (a : Dˣ＼GL₂(𝔸 F)／ℒ.UA) : ℂ :=
  (ℒ.ΔIndex D a : ℂ)⁻¹ *
  Quotient.lift (fun i ↦ starRingEnd ℂ (f.1 i) * g.1 i) (by
    intro x y e
    obtain ⟨_, ⟨d, rfl⟩, u, hu, rfl⟩ := DoubleCoset.rel_iff.mp e
    lift u to ℒ.UA using hu
    simp [mul_assoc, Algebra.smul_def, LevelStruct.star_χA]
    field [(((Group.isUnit u).map ℒ.χA).map _).ne_zero]) a

lemma LevelStruct.starRingEnd_innerSummand (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) (a : Dˣ＼GL₂(𝔸 F)／ℒ.UA) :
    starRingEnd ℂ (ℒ.innerSummand f g a) = ℒ.innerSummand g f a := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  simp [innerSummand, mul_comm]

@[simp]
lemma LevelStruct.innerSummand_add_left (ℒ : LevelStruct F R)
    (f₁ f₂ g : ℒ.form D ℂ) :
    ℒ.innerSummand (f₁ + f₂) g = ℒ.innerSummand f₁ g + ℒ.innerSummand f₂ g := by
  ext a
  rw [Pi.add_apply]
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  simp [innerSummand, add_mul, mul_add]

@[simp]
lemma LevelStruct.innerSummand_smul_left (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) (z : ℂ) :
    ℒ.innerSummand (z • f) g = starRingEnd ℂ z • ℒ.innerSummand f g := by
  ext a
  rw [Pi.smul_apply]
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  simp [innerSummand]
  ring

instance : MeasurableSpace 𝔸ᶠ[F] := borel _
instance : BorelSpace 𝔸ᶠ[F] := ⟨rfl⟩

open FiniteAdeleRing

instance : IsClosed (X := GL₂(𝔸ᶠ[F])) (𝔸ˣ F) :=
  RestrictedProduct.isClosed_unitsMap_matrix ..

instance : PolishSpace GL₂(𝔸ᶠ[F]) := polish_of_locally_compact_second_countable _

variable (F) in
/-- The haar measure on `GL₂(𝔸ᶠ[F])` that gives `Π GL₂(𝒪ᵥ)` measure one. -/
def haarQuot : MeasureTheory.Measure (GL₂(𝔸ᶠ[F]) ⧸ 𝔸ˣ F) :=
  MeasureTheory.Measure.haarMeasure ⟨⟨(GL2.maximalCompact F).map (QuotientGroup.mk' (𝔸ˣ F)),
    GL2.maximalCompact.isCompact.image continuous_quotient_mk'⟩, by
    rw [IsOpen.interior_eq]
    · simp
    · exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ GL2.maximalCompact.isOpen⟩

instance : (haarQuot F).IsHaarMeasure := by delta haarQuot; infer_instance
instance : (haarQuot F).Regular := by delta haarQuot; infer_instance

instance : IsUnimodularGroup (GL₂(𝔸ᶠ[F]) ⧸ 𝔸ˣ F) := inferInstance

omit [Algebra R ℂ] in
lemma haarQuot_mul_relIndex (ℒ ℒ' : LevelStruct F R) (h : ℒ ≤ ℒ') :
    haarQuot F (ℒ.U.map (QuotientGroup.mk' (𝔸ˣ F))) * (ℒ.UA.relIndex ℒ'.UA) =
      haarQuot F (ℒ'.U.map (QuotientGroup.mk' (𝔸ˣ F))) := by
  rw [mul_comm]
  convert MeasureTheory.relIndex_mul_measure _ _ (haarQuot F)
  · simp [Subgroup.relIndex_map_map]
  · rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, Subgroup.relIndex_map_map]
    simp only [QuotientGroup.ker_mk', ne_eq]
    exact Subgroup.relIndex_ne_zero
  · exact (QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ ℒ.isOpen_U).measurableSet
  · exact Subgroup.map_mono h.1

variable [IsQuaternionAlgebra F D]

/-- The Petersson inner product of two complex valued automorphic forms of a given level.

We later show that this is independent of the level. -/
protected noncomputable
def LevelStruct.inner (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) : ℂ :=
    (haarQuot F (ℒ.U.map (QuotientGroup.mk' (𝔸ˣ F)))).toNNReal *
      ∑ a : Dˣ＼GL₂(𝔸 F)／ℒ.UA, ℒ.innerSummand f g a

variable [NumberField.IsTotallyReal F] [IsQuaternionAlgebra.IsTotallyDefinite F D]

omit [Algebra R ℂ] in
lemma LevelStruct.sum_filter_map_eq_ΔIndex_div_ΔIndex
    (ℒ ℒ' : LevelStruct F R) (h : ℒ ≤ ℒ') (g : Dˣ＼GL₂(𝔸 F)／ℒ'.UA)
    [DecidableEq (Dˣ＼GL₂(𝔸 F)／ℒ'.UA)] :
    ∑ a : Dˣ＼GL₂(𝔸 F)／ℒ.UA with DoubleCoset.map _ _ _ _ (.id _) le_rfl
        (UA_mono h) a = g, LevelStruct.ΔIndex D ℒ' g / LevelStruct.ΔIndex D ℒ a =
    ℒ.UA.relIndex ℒ'.UA := by
  classical
  let φ : Dˣ＼GL₂(𝔸 F)／ℒ.UA → Dˣ＼GL₂(𝔸 F)／ℒ'.UA := DoubleCoset.map _ _ _ _ (.id _) le_rfl
    (UA_mono h)
  change ∑ a with φ a = g, ℒ'.ΔIndex D g / ℒ.ΔIndex D a = ℒ.UA.relIndex ℒ'.UA
  convert DoubleCoset.sum_filter_map_eq_relIndex_eq_relIndex _ _ _ (UA_mono h) g with x hx
  obtain ⟨x, rfl⟩ := DoubleCoset.mk_surjective _ _ x
  conv_rhs => simp only [DoubleCoset.mk, Quotient.mk'', Quotient.lift_mk]
  obtain rfl : DoubleCoset.mk _ _ x = g := by simpa [-MonoidHom.coe_range] using hx
  have := ℒ.isFiniteRelIndex_Δ (D := D)
  rw [← LevelStruct.ΔIndex_mul_relIndex _ _ h,
    Nat.mul_div_cancel_left _ (by exact Subgroup.relIndex_ne_zero.pos),
    ← Subgroup.inf_relIndex_right, eq_comm, ← Subgroup.inf_relIndex_right]
  congr 1
  dsimp [LevelStruct.Δ]
  rw [inf_inf_inf_comm, inf_idem, inf_assoc]

lemma LevelStruct.inner_eq_of_map_le_map
    {R' : Type*} [CommRing R'] [Algebra R' ℂ]
    (ℒ : LevelStruct F R) (ℒ' : LevelStruct F R')
    (hUV : ℒ.map (algebraMap R ℂ) ≤ ℒ'.map (algebraMap R' ℂ))
    (f g : ℒ'.form D ℂ) :
    ℒ'.inner f g = ℒ.inner
      ⟨f.1, by grw [← form_map (R' := ℂ), hUV]; exact (form_map _).ge f.2⟩
      ⟨g.1, by grw [← form_map (R' := ℂ), hUV]; exact (form_map _).ge g.2⟩ := by
  classical
  symm
  let φ : Dˣ＼GL₂(𝔸 F)／ℒ.UA → Dˣ＼GL₂(𝔸 F)／ℒ'.UA := DoubleCoset.map _ _ _ _ (.id _) le_rfl
    (sup_le_sup hUV.1 le_rfl)
  dsimp only [LevelStruct.inner]
  rw [← Finset.sum_fiberwise _ φ]
  rw [← haarQuot_mul_relIndex _ _ hUV]
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_natCast, NNReal.coe_mul, NNReal.coe_natCast,
    Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  congr 1 with x
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
  trans ∑ i with φ i = ⟦x⟧, (ΔIndex D ℒ i : ℂ)⁻¹ * (starRingEnd ℂ (f.1 x) * g.1 x)
  · refine Finset.sum_congr rfl fun y hy ↦ ?_
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
    obtain ⟨_, ⟨d, rfl⟩, u, hu, rfl⟩ :=
      (DoubleCoset.eq _ _ _ _).mp ((Finset.mem_filter_univ _).mp hy:)
    have Hf := ℒ'.apply_mul_eq_χA_smul _ f.2 ⟨u, hu⟩ y
    have Hg := ℒ'.apply_mul_eq_χA_smul _ g.2 ⟨u, hu⟩ y
    dsimp at Hf Hg
    simp [mul_assoc, innerSummand, Hf, Hg, ℒ'.star_χA, Algebra.smul_def,
      -mul_eq_mul_left_iff, mul_left_comm _ (starRingEnd ℂ _),
      (((Group.isUnit ⟨u, hu⟩).map ℒ'.χA).map _).ne_zero]
  · suffices ∑ y with φ y = ⟦x⟧, (ΔIndex D ℒ y : ℂ)⁻¹ =
        (ℒ.UA.relIndex ℒ'.UA) * (ΔIndex D ℒ' ⟦x⟧ : ℂ)⁻¹ by
      rw [← Finset.sum_mul]; dsimp [innerSummand]; simp_rw [← mul_assoc]; erw [← this]; simp; grind
    have H : ℒ'.ΔIndex D ⟦x⟧ ≠ 0 :=
      have := ℒ'.isFiniteRelIndex_Δ (D := D); Subgroup.relIndex_ne_zero
    refine mul_left_injective₀ (b := (ℒ'.ΔIndex D  ⟦x⟧ : ℂ)) (by simpa) ?_
    dsimp only
    rw [mul_assoc, inv_mul_cancel₀ (by simpa), Finset.sum_mul, mul_one,
      ← LevelStruct.sum_filter_map_eq_ΔIndex_div_ΔIndex (D := D) _ _ hUV (DoubleCoset.mk _ _ x)]
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    obtain ⟨a, rfl⟩ := DoubleCoset.mk_surjective _ _ a
    rw [Nat.cast_div, div_eq_inv_mul]
    · rfl
    · rw [← (@Finset.mem_filter_univ ..).mp ha]
      erw [DoubleCoset.map_mk]
      rw [← ΔIndex_mul_relIndex _ _ hUV]
      exact ⟨_, rfl⟩
    · have := ℒ.isFiniteRelIndex_Δ (D := D); simpa using! Subgroup.relIndex_ne_zero

lemma LevelStruct.inner_eq_of_le
    (ℒ ℒ' : LevelStruct F R)
    (hUV : ℒ ≤ ℒ')
    (f g : ℒ'.form D ℂ) :
    ℒ'.inner f g = ℒ.inner ⟨f.1, form_anti hUV f.2⟩ ⟨g.1, form_anti hUV g.2⟩ :=
  LevelStruct.inner_eq_of_map_le_map ℒ ℒ' (by gcongr) f g

lemma LevelStruct.inner_eq {R' : Type*} [CommRing R'] [Algebra R' ℂ]
    (ℒ : LevelStruct F R) (ℒ' : LevelStruct F R')
    (f g : WeightTwoAutomorphicForm F D ℂ)
    (hfℒ : f ∈ ℒ.form D ℂ) (hgℒ : g ∈ ℒ.form D ℂ)
    (hfℒ' : f ∈ ℒ'.form D ℂ) (hgℒ' : g ∈ ℒ'.form D ℂ) :
    ℒ.inner ⟨f, hfℒ⟩ ⟨g, hgℒ⟩ = ℒ'.inner ⟨f, hfℒ'⟩ ⟨g, hgℒ'⟩ := by
  let ℒℂ := ℒ.map (algebraMap R ℂ)
  let ℒ'ℂ := ℒ'.map (algebraMap R' ℂ)
  suffices ℒℂ.inner ⟨f, (ℒ.form_map (R' := ℂ)).ge hfℒ⟩ ⟨g, (ℒ.form_map (R' := ℂ)).ge hgℒ⟩ =
      ℒ'ℂ.inner ⟨f, (ℒ'.form_map (R' := ℂ)).ge hfℒ'⟩ ⟨g, (ℒ'.form_map (R' := ℂ)).ge hgℒ'⟩ by
    convert this using 1
    · exact LevelStruct.inner_eq_of_map_le_map _ _ le_rfl _ _
    · exact LevelStruct.inner_eq_of_map_le_map _ _ le_rfl _ _
  rw [LevelStruct.inner_eq_of_le (ℒℂ ⊓ ℒ'ℂ) ℒℂ inf_le_left,
    LevelStruct.inner_eq_of_le (ℒℂ ⊓ ℒ'ℂ) ℒ'ℂ inf_le_right]

instance (ℒ ℒ' : LevelStruct F R) [ℒ.IsSufficientlySmall D] : (ℒ ⊓ ℒ').IsSufficientlySmall D :=
  .of_le _ _ inf_le_left

instance (ℒ ℒ' : LevelStruct F R) [ℒ'.IsSufficientlySmall D] : (ℒ ⊓ ℒ').IsSufficientlySmall D :=
  .of_le _ _ inf_le_right

attribute [instance] LevelStruct.isFiniteRelIndex_Δ

instance : InnerProductSpace.Core ℂ (WeightTwoAutomorphicForm F D ℂ) where
  inner f g := (f.levelStruct ℂ ⊓ g.levelStruct ℂ).inner
    ⟨f, LevelStruct.form_anti inf_le_left (f.mem_form _)⟩
    ⟨g, LevelStruct.form_anti inf_le_right (g.mem_form _)⟩
  conj_inner_symm f g := by
    rw! [inf_comm]; simp [LevelStruct.inner, LevelStruct.starRingEnd_innerSummand]
  re_inner_nonneg f := by
    rw! [inf_idem]
    dsimp [-MonoidHom.coe_range, LevelStruct.inner, LevelStruct.innerSummand]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.re_sum, Complex.inv_re,
      Complex.natCast_re, Complex.normSq_natCast, div_self_mul_self', Complex.inv_im,
      Complex.natCast_im, neg_zero, zero_div, zero_mul, sub_zero, Complex.ofReal_im, Complex.im_sum,
      Complex.mul_im, add_zero]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ ↦ mul_nonneg (by positivity) ?_)
    obtain ⟨x, rfl⟩ := DoubleCoset.mk_surjective _ _ x
    simp [DoubleCoset.mk, Quotient.mk'', ← pow_two, add_nonneg, sq_nonneg]
  add_left f₁ f₂ g := by
    let ℒ := levelStruct ℂ (f₁ + f₂) ⊓ levelStruct ℂ g ⊓ levelStruct ℂ f₁ ⊓ levelStruct ℂ f₂
    rw [ℒ.inner_eq_of_le _ (by aesop (add unsafe inf_le_of_left_le)),
      ℒ.inner_eq_of_le (f₁.levelStruct ℂ ⊓ _) (by aesop (add unsafe inf_le_of_left_le)),
      ℒ.inner_eq_of_le (f₂.levelStruct ℂ ⊓ _) (by aesop (add unsafe inf_le_of_left_le))]
    dsimp only [LevelStruct.inner]
    simp_rw [← mul_add, ← Finset.sum_add_distrib, ← Pi.add_apply (ℒ.innerSummand _ _),
      ← ℒ.innerSummand_add_left]
    rfl
  smul_left f g r := by
    let ℒ := levelStruct ℂ (r • f) ⊓ levelStruct ℂ f ⊓ levelStruct ℂ g
    rw [ℒ.inner_eq_of_le _ (by aesop (add unsafe inf_le_of_left_le)),
      ℒ.inner_eq_of_le (levelStruct ℂ f ⊓ _) (by aesop (add unsafe inf_le_of_left_le))]
    dsimp only [LevelStruct.inner]
    rw [mul_left_comm, Finset.mul_sum _ _ (starRingEnd ℂ r)]
    simp_rw [← smul_eq_mul, ← Pi.smul_apply _ (ℒ.innerSummand _ _), ← ℒ.innerSummand_smul_left]
    rfl
  definite f H := by
    rw! [inf_idem] at H
    have := congr(($H).re)
    have h₁ : (haarQuot F (QuotientGroup.mk '' ↑(levelStruct ℂ f).U)).toNNReal ≠ 0 := by
      simp only [ne_eq, ENNReal.toNNReal_eq_zero_iff, not_or]
      exact ⟨((QuotientGroup.isOpenQuotientMap_mk.isOpenMap _
        (levelStruct ℂ f).isOpen_U).measure_ne_zero _ (.image _ (by simp [-levelStruct_U]))),
        ((levelStruct ℂ f).isCompact_U.image
        (by exact continuous_quotient_mk')).measure_ne_top⟩
    dsimp [-MonoidHom.coe_range, LevelStruct.inner, LevelStruct.innerSummand] at this
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.re_sum, Complex.inv_re,
      Complex.natCast_re, Complex.normSq_natCast, div_self_mul_self', Complex.inv_im,
      Complex.natCast_im, neg_zero, zero_div, zero_mul, sub_zero, Complex.ofReal_im, Complex.im_sum,
      Complex.mul_im, add_zero, mul_eq_zero, NNReal.coe_eq_zero, h₁, false_or] at this
    ext a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦ by
      obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
      simp [← pow_two, sq_nonneg, add_nonneg, mul_nonneg]).mp this
      (Quotient.mk'' a) (Finset.mem_univ _)
    simpa [-MonoidHom.coe_range, Subgroup.relIndex_ne_zero, ← Complex.normSq_apply] using this

instance : NormedAddCommGroup (WeightTwoAutomorphicForm F D ℂ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : NormedSpace ℂ (WeightTwoAutomorphicForm F D ℂ) :=
  InnerProductSpace.Core.toNormedSpace

instance : InnerProductSpace ℂ (WeightTwoAutomorphicForm F D ℂ) := .ofCore _

instance (ℒ : LevelStruct F R) : NormedSpace ℂ (ℒ.form D ℂ) :=
  inferInstanceAs <| NormedSpace ℂ (ℒ.formSubmodule D ℂ ℂ)

instance (ℒ : LevelStruct F R) : InnerProductSpace ℂ (ℒ.form D ℂ) :=
  inferInstanceAs <| InnerProductSpace ℂ (ℒ.formSubmodule D ℂ ℂ)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

lemma LevelStruct.inner_def_of_mem (ℒ : LevelStruct F R)
    (f g) (hf : f ∈ ℒ.form D ℂ) (hg : g ∈ ℒ.form D ℂ) : ⟪f, g⟫ = ℒ.inner ⟨f, hf⟩ ⟨g, hg⟩ :=
  inner_eq ..

lemma LevelStruct.inner_coe (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) : ⟪f.1, g.1⟫ = ⟪f, g⟫ := rfl

lemma LevelStruct.inner_def (ℒ : LevelStruct F R)
    (f g : ℒ.form D ℂ) : ⟪f, g⟫ = ℒ.inner f g :=
  inner_eq ..

open MeasureTheory Pointwise in
lemma Measure.conjAct_smul_of_isUnimodularGroup
    {G : Type*} [TopologicalSpace G] [Group G] [IsUnimodularGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.Regular] (g : ConjAct G) (s : Set G) :
    μ (g • s) = μ s := by
  rw [Measure.conjAct_smul, IsUnimodularGroup.modularCharacter_eq_one]
  simp

open Pointwise in
lemma Subgroup.map_toConjAct_smul_mk' {G : Type*} [Group G] {N H : Subgroup G} [N.Normal] (g : G) :
    (ConjAct.toConjAct g • H).map (QuotientGroup.mk' N) =
      ConjAct.toConjAct (g : G ⧸ N) • H.map (QuotientGroup.mk' N) := by
  simp only [Subgroup.pointwise_smul_def, Subgroup.map_map]
  rfl

lemma _root_.le_inv_smul_iff {G α : Type*} [Group G] [MulAction G α] [Preorder α]
    [CovariantClass G α (· • ·) (· ≤ ·)] {g : G} {a b : α} : a ≤ g⁻¹ • b ↔ g • a ≤ b := by
  rw [← smul_le_smul_iff (g := g)]
  simp

lemma _root_.le_smul_sup {G α : Type*} [Monoid G] [MulAction G α] [SemilatticeSup α]
    [CovariantClass G α (· • ·) (· ≤ ·)] (g : G) (a b : α) : g • a ⊔ g • b ≤ g • (a ⊔ b) :=
  sup_le (smul_mono_right _ le_sup_left) (smul_mono_right _ le_sup_right)

lemma _root_.smul_sup {G α : Type*} [Group G] [MulAction G α] [SemilatticeSup α]
    [CovariantClass G α (· • ·) (· ≤ ·)] (g : G) (a b : α) : g • (a ⊔ b) = g • a ⊔ g • b := by
  refine (le_smul_sup ..).antisymm' ?_
  grw [← le_inv_smul_iff, ← le_smul_sup]
  simp

open scoped Pointwise in
omit [Algebra R ℂ] [NumberField.IsTotallyReal F] in
lemma LevelStruct.smul_UA (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    (g • ℒ).UA = ConjAct.toConjAct g • ℒ.UA := by
  dsimp only [UA, smul_U]
  rw [smul_sup]
  congr 1
  rw [Subgroup.conjAct_pointwise_smul_eq_self]
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  trivial

open scoped Pointwise in
omit [Algebra R ℂ] [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
  [IsQuaternionAlgebra.IsTotallyDefinite F D] in
lemma LevelStruct.smul_Δ (ℒ : LevelStruct F R) (g a : GL₂(𝔸ᶠ[F])) :
    (g • ℒ).Δ D a = ConjAct.toConjAct g • ℒ.Δ D (a * g) := by
  simp only [Δ, LevelStruct.smul_UA, smul_inf]
  simp [mul_smul]

open scoped Pointwise in
omit [Algebra R ℂ] [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
  [IsQuaternionAlgebra.IsTotallyDefinite F D] in
lemma LevelStruct.Δ_mul (ℒ : LevelStruct F R) (g a : GL₂(𝔸ᶠ[F])) :
    ℒ.Δ D (a * g) = ConjAct.toConjAct g⁻¹ • (g • ℒ).Δ D a  := by
  simp only [Δ, LevelStruct.smul_UA, smul_inf]
  simp [mul_smul]

open WeightTwoAutomorphicForm in
lemma inner_smul_eq_inner_inv_smul (f g : WeightTwoAutomorphicForm F D ℂ) (a : GL₂(𝔸ᶠ[F])) :
    ⟪a • f, g⟫ = ⟪f, a⁻¹ • g⟫ := by
  let ℒ := (a • f).levelStruct ℂ ⊓ f.levelStruct ℂ ⊓
    (g.levelStruct ℂ ⊓ ((a⁻¹) • g).levelStruct ℂ)
  rw [ℒ.inner_def_of_mem _ _
    (by dsimp only [ℒ]; grw [inf_le_left, inf_le_left]; exact mem_form _ _)
    (by dsimp only [ℒ]; grw [inf_le_right, inf_le_left]; exact mem_form _ _),
    ℒ.inner_def_of_mem _ _
    (by dsimp only [ℒ]; grw [inf_le_left, inf_le_right]; exact mem_form _ _)
    (by dsimp only [ℒ]; grw [inf_le_right, inf_le_right]; exact mem_form _ _),
    (ℒ ⊓ a • ℒ).inner_eq_of_le ℒ inf_le_left, (ℒ ⊓ a⁻¹ • ℒ).inner_eq_of_le ℒ inf_le_left]
  simp only [LevelStruct.inner]
  congrm ?_ * ?_
  · rw [← Measure.conjAct_smul_of_isUnimodularGroup _ (ConjAct.toConjAct (QuotientGroup.mk a⁻¹)),
      ← Subgroup.coe_pointwise_smul, ← Subgroup.map_toConjAct_smul_mk', ← LevelStruct.smul_U,
      smul_inf, inv_smul_smul, inf_comm]
  · refine Finset.sum_equiv (DoubleCoset.mulRightEquiv _ _ _ a ?_)
      (by simp only [Finset.mem_univ, implies_true]) fun b _ ↦ ?_
    · rw [← Subgroup.coe_pointwise_smul, ← LevelStruct.smul_UA]
      simp [smul_inf, inf_comm]
    · obtain ⟨b, rfl⟩ := DoubleCoset.mk_surjective _ _ b
      change _ * (_ * _) = _ * (_ * _)
      dsimp only [LevelStruct.ΔIndex_mk, groupSMul_apply, Equiv.coe_mulRight,
        DoubleCoset.mulRightEquiv_mk]
      congrm ?_⁻¹ * ?_
      · rw [LevelStruct.Δ_mul, ← Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct a⁻¹)]
        congr
        · rw [Subgroup.conjAct_pointwise_smul_eq_self]
          rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
          trivial
        · simp [smul_inf, inf_comm]
      · simp

lemma inner_adicCompletion_smul (f g : WeightTwoAutomorphicForm F D ℂ)
    {v : HeightOneSpectrum (𝓞 F)} (a : GL₂(v.adicCompletion F)) :
    ⟪a • f, g⟫ = ⟪f, a⁻¹ • g⟫ :=
  (inner_smul_eq_inner_inv_smul f g (GL2.finiteAdeleIncl v a)).trans (by rw [← map_inv]; rfl)

theorem LocalLevelStruct.inner_heckeOperator
    (f₁ f₂ : ℒ.toStruct.form D ℂ) :
    ⟪ℒ.heckeOperator D ℂ v hv g f₁, f₂⟫ = ⟪f₁, ℒ.heckeOperator D ℂ v hv g⁻¹ f₂⟫ := by
  classical
  obtain ⟨s, hs₁, hs₂⟩ :=
    exists_bijOn_mk_image_mul_singleton_and_mk_image_mul_singleton_inv
    _ (ℒ.isOpen_US v) (ℒ.isCompact_US v) g
  have := (Set.bijOn_comp_iff inv_injective.injOn).mp hs₂
  rw [← Finset.coe_image] at this
  classical
  rw [← LevelStruct.inner_coe, LocalLevelStruct.heckeOperator_eq_finsetSum _ _ _ _ _ hs₁,
  ← LevelStruct.inner_coe, LocalLevelStruct.heckeOperator_eq_finsetSum _ _ _ _ _ this]
  simp [inner_adicCompletion_smul]

theorem LocalLevelStruct.adjoint_heckeOperatorL
    [ℒ.toStruct.IsFinite D] [ℒ.toStruct.IsSufficientlySmall D] :
    (ℒ.heckeOperatorL D ℂ ℂ v hv g).adjoint = ℒ.heckeOperatorL D ℂ ℂ v hv g⁻¹ := by
  classical
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun f₁ f₂ ↦ ?_).symm
  exact inner_heckeOperator ℒ _ hv _ _ _

end WeightTwoAutomorphicForm

namespace HeckeAlgebra

open NumberField

variable [IsQuaternionAlgebra F D] [IsTotallyReal F]
    [IsQuaternionAlgebra.IsTotallyDefinite F D]

variable (D) {p : ℕ} (𝒮 : U₁Data F R p)

open WeightTwoAutomorphicForm

local notation "S(U, "M")" => LevelStruct.form D M (LocalLevelStruct.toStruct (U₁ 𝒮))

theorem isSymmetric_toModuleEnd_T (v : HeightOneSpectrum (𝓞 F)) (hvS hvQ) :
    (Module.toModuleEnd ℂ S(U, ℂ) (T D 𝒮 v hvS hvQ)).IsSymmetric := by
  rw [LinearMap.IsSymmetric, ← LinearMap.eq_adjoint_iff, eq_comm]
  convert (U₁ 𝒮).adjoint_heckeOperatorL (D := D) v (by simp [U₁, hvS, hvQ]; rfl)
    (Matrix.GeneralLinearGroup.diagonal ![v.adicCompletionUniformizerUnit F, 1])
  · ext1 f
    simp [T_smul_def]
    rfl
  · ext1 f
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, T_smul_def,
      LinearMap.coe_mk, LinearMap.coe_toAddHom]
    rw [HeckeOperator.T_inv (D := D) (hvQ := hvQ)]

/-- Type parametrising eigen spaces of the anemic hecke algebra on `S(U, ℂ)`. -/
def Eigenform :=
  { φ : HeckeAlgebra.anemic D 𝒮 →ₐ[R] ℂ // ∃ v : S(U, ℂ), v ≠ 0 ∧ ∀ T, T • v = φ T • v }

variable {D 𝒮}

/-- The eigenspace parametrised by an `Eigenform`. -/
def Eigenform.eigenspace (𝒻 : Eigenform D 𝒮) : Submodule ℂ S(U, ℂ) :=
  ⨅ x, (Module.toModuleEnd ℂ S(U, ℂ) x).eigenspace (𝒻.1 x)

instance : DecidableEq (Eigenform D 𝒮) := Classical.decEq _

lemma Eigenform.mem_eigenspace_iff {𝒻 : Eigenform D 𝒮} {g : S(U, ℂ)} :
    g ∈ 𝒻.eigenspace ↔ ∀ T, T • g = 𝒻.1 T • g := by simp [Eigenform.eigenspace]

/-- The `Tₚ`-eigenvalue of an eigenform. -/
abbrev Eigenform.eigenvalue (𝒻 : Eigenform D 𝒮) (v) (hvS : v ∉ 𝒮.S) (hvQ : v ∉ 𝒮.Q) : ℂ :=
  𝒻.1 ⟨T D 𝒮 v hvS hvQ, Algebra.subset_adjoin ⟨_, _, _, rfl⟩⟩

open Algebra in
@[elab_as_elim]
theorem _root_.Algebra.coe_adjoin_induction
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {s : Set A} {S : Subalgebra R A}
    {p : (x : S) → Prop}
    (hS : S = adjoin R s)
    (mem : ∀ (x) (hx : x ∈ s), p ⟨x, hS ▸ subset_adjoin hx⟩)
    (algebraMap : ∀ r, p (algebraMap R _ r))
    (add : ∀ x y, p x → p y → p (x + y))
    (mul : ∀ x y, p x → p y → p (x * y))
    (x : S) : p x := by
  subst hS
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact mem _ hx
  | algebraMap r => exact algebraMap _
  | add x y hx hy _ _ => exact add ⟨x, hx⟩ ⟨y, hy⟩ ‹_› ‹_›
  | mul x y hx hy _ _ => exact mul ⟨x, hx⟩ ⟨y, hy⟩ ‹_› ‹_›

lemma Eigenform.mem_eigenspace_iff_T {𝒻 : Eigenform D 𝒮} {g : S(U, ℂ)} :
    g ∈ 𝒻.eigenspace ↔ ∀ v hvS hvQ, T D 𝒮 v hvS hvQ • g = 𝒻.eigenvalue v hvS hvQ • g := by
  refine mem_eigenspace_iff.trans ⟨fun H _ _ _ ↦ H ⟨_, _⟩, fun H T ↦ ?_⟩
  rw [Subalgebra.smul_def]
  induction T using Algebra.coe_adjoin_induction with
  | hS => rfl
  | mem x hx => obtain ⟨v, hvS, hvQ, rfl⟩ := hx; simp [H]
  | algebraMap r => simp
  | add x y _ _ => simp [add_smul, *]
  | mul x y IH IH' =>
    rw [Subalgebra.coe_mul, mul_smul, IH', smul_comm, IH, smul_comm, map_mul, mul_smul]

lemma Eigenform.eigenvalue_injective :
    Function.Injective (Eigenform.eigenvalue (D := D) (𝒮 := 𝒮)) :=
  fun 𝒻 𝒻' e ↦ Subtype.ext (AlgHom.adjoin_ext
    (by rintro _ ⟨v, hvS, hvQ, rfl⟩; exact congr($e _ _ _)))

lemma Eigenform.eigenSpace_ne_bot (𝒻 : Eigenform D 𝒮) :
    𝒻.eigenspace ≠ ⊥ := by
  simp only [ne_eq, Submodule.eq_bot_iff, not_forall]
  exact ⟨𝒻.2.choose, mem_eigenspace_iff.mpr 𝒻.2.choose_spec.2, 𝒻.2.choose_spec.1⟩

lemma Eigenform.exists (φ : ∀ v ∉ 𝒮.S, v ∉ 𝒮.Q → ℂ) (μ : S(U, ℂ)) (hμ : μ ≠ 0)
    (hμ' : ∀ v hvS hvQ, T D 𝒮 v hvS hvQ • μ = φ v hvS hvQ • μ) :
    ∃ 𝒻 : Eigenform D 𝒮, (∀ v hvS hvQ, 𝒻.eigenvalue v hvS hvQ = φ v hvS hvQ) ∧
      μ ∈ 𝒻.eigenspace := by
  have : ∀ x ∈ HeckeAlgebra.anemic D 𝒮, ∃ a : ℂ, x • μ = a • μ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨v, hvS, hvQ, rfl⟩ := hx; exact ⟨φ _ _ _, hμ' _ _ _⟩
    | algebraMap r => exact ⟨algebraMap _ _ r, by simp⟩
    | add x y hx hy H₁ H₂ =>
      obtain ⟨a₁, ha₁⟩ := H₁
      obtain ⟨a₂, ha₂⟩ := H₂
      exact ⟨a₁ + a₂, by simp [add_smul, ha₁, ha₂]⟩
    | mul x y hx hy H₁ H₂ =>
      obtain ⟨a₁, ha₁⟩ := H₁
      obtain ⟨a₂, ha₂⟩ := H₂
      exact ⟨a₂ * a₁, by rw [mul_smul, ha₂, smul_comm, ha₁, mul_smul]⟩
  choose! a ha using this
  have H : ∀ x ∈ HeckeAlgebra.anemic D 𝒮, ∀ a' : ℂ, x • μ = a' • μ → a x = a' := by
    simp +contextual [ha, ← sub_eq_zero (a := _ • _) (b := _ • _), ← sub_smul, hμ,
      sub_eq_zero (a := a _)]
  let aφ : anemic D 𝒮 →ₐ[R] ℂ :=
  { toFun := (a ·)
    map_one' := H _ (by simp) _ (by simp)
    map_mul' T₁ T₂ := H _ (mul_mem T₁.2 T₂.2) _ (by
      simp only [mul_smul, SetLike.coe_mem, ha]; rw [smul_comm, ha _ T₁.2, smul_comm])
    map_zero' := H _ (by simp) _ (by simp)
    map_add' T₁ T₂ := H _ (add_mem T₁.2 T₂.2) _ (by simp [add_smul, ha])
    commutes' r := H _ (by simp) _ (by simp) }
  exact ⟨⟨aφ, μ, hμ, by simpa⟩, fun v hvS hvQ ↦ H _
    (Algebra.subset_adjoin ⟨v, hvS, hvQ, rfl⟩) _ (hμ' ..), by simpa [mem_eigenspace_iff]⟩

open scoped DirectSum in
theorem _root_.DirectSum.IsInternal.reindex {ι κ M S : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M] {A : ι → S}
    (hA : DirectSum.IsInternal A) {B : κ → S} (f : κ → ι) (hf : Function.Injective f)
    (hf₁ : ∀ i, B i = A (f i)) (hf₂ : ∀ x ∉ Set.range f, ∀ a, a ∈ A x → a = 0) :
    DirectSum.IsInternal B := by
  classical
  let φ : (⨁ i, A i) →+ ⨁ i, B i :=
  { toFun := DFinsupp.mapRange (fun _ ↦ (Equiv.refl _).subtypeEquiv
      (by simp [← hf₁])) (fun _ ↦ rfl) ∘ DFinsupp.comapDomain f hf
    map_zero' := by ext; simp
    map_add' a b := by ext; simp }
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b e ↦ ?_, fun a ↦ ?_⟩
    · ext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hi; exact congr($e i)
      · simp [hf₂ _ hi]
    · refine ⟨.mk _ (a.support.map ⟨f, hf⟩) fun i ↦ (Equiv.refl _).subtypeEquiv
        (fun _ ↦ by rw! [hf₁]; congr!; exact (Finset.mem_map.mp i.2).choose_spec.2)
        (a (Finset.mem_map.mp i.2).choose), ?_⟩
      ext i
      dsimp [φ]
      simp only [Equiv.subtypeEquiv_apply, Equiv.refl_apply]
      by_cases H : a i = 0
      · rw [DirectSum.mk_apply_of_notMem, H, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
        simpa
      · rw [DirectSum.mk_apply_of_mem (by simpa)]
        dsimp
        generalize_proofs H
        rw [hf (H.choose_spec.2)]
  unfold DirectSum.IsInternal at hA ⊢
  refine (Function.Bijective.of_comp_iff _ hφ).mp ?_
  rw [← AddMonoidHom.coe_comp]
  convert hA
  ext i a
  by_cases hi : i ∈ Set.range f; swap
  · obtain rfl : a = 0 := by ext1; exact hf₂ _ hi _ a.2
    simp
  obtain ⟨i, rfl⟩ := hi
  dsimp [φ]
  rw [DirectSum.coeAddMonoidHom_of]
  erw [DFinsupp.comapDomain_single (β := (A ·)) f hf i a]
  rw [DFinsupp.mapRange_single]
  exact DirectSum.coeAddMonoidHom_of ..

variable (D 𝒮) in
theorem Eigenform.isInternal :
    DirectSum.IsInternal fun 𝒻 : Eigenform D 𝒮 ↦ 𝒻.eigenspace := by
  classical
  refine (LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute
    (n := { v | v ∉ 𝒮.S ∧ v ∉ 𝒮.Q })
    (T := fun v ↦ Module.toModuleEnd ℂ ((U₁ 𝒮).toStruct.form D ℂ) (T D 𝒮 v.1 v.2.1 v.2.2))
    (fun v ↦ isSymmetric_toModuleEnd_T _ _ _ v.2.1 v.2.2)
    (fun v w _ ↦ by ext1; simp [← mul_smul, mul_comm])).reindex (κ := Eigenform D 𝒮)
      (B := Eigenform.eigenspace) (fun 𝒻 v ↦ 𝒻.eigenvalue v.1 v.2.1 v.2.2) ?_ ?_ ?_
  · intro 𝒻 𝒻' e
    exact Eigenform.eigenvalue_injective (by ext v hvS hvQ; exact congr($e ⟨v, hvS, hvQ⟩))
  · intro 𝒻
    ext v
    simp [Eigenform.mem_eigenspace_iff_T]
  · intro f hf μ hμ
    by_contra hμ'
    obtain ⟨𝒻, h₁, h₂⟩ := Eigenform.exists (fun v hvS hvQ ↦ f ⟨v, hvS, hvQ⟩) μ hμ'
      (by simpa using hμ)
    exact hf ⟨𝒻, funext (by simp [h₁])⟩

variable (D 𝒮) in
lemma Eigenform.cardinalMk_le : Cardinal.mk (Eigenform D 𝒮) ≤ Module.finrank ℂ S(U, ℂ) := by
  have := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
    (Eigenform.isInternal D 𝒮)).lift_rank_eq.symm
  rw [← Module.finrank_eq_rank] at this
  simp only [Cardinal.lift_natCast, rank_directSum, Cardinal.lift_sum, Cardinal.lift_id] at this
  rw [this]
  refine le_of_eq_of_le ?_ (Cardinal.sum_le_sum _ _ fun 𝒻 ↦ show 1 ≤ _ from ?_)
  · simpa using (Cardinal.lift_id' _).symm
  · rw [Cardinal.one_le_iff_pos, Module.rank_pos_iff_of_free, Submodule.nontrivial_iff_ne_bot]
    exact 𝒻.eigenSpace_ne_bot

instance : Fintype (Eigenform D 𝒮) := (Cardinal.lt_aleph0_iff_fintype.mp
  ((Eigenform.cardinalMk_le D 𝒮).trans_lt (by simp))).some

/-- The subring of `ℂ` generated by the eigenvalues of an eigenform. -/
abbrev Eigenform.integers (𝒻 : Eigenform D 𝒮) : Subalgebra R ℂ := 𝒻.1.range

/-- The induced map of an `Eigenform` from an hecke algebra to its integers. -/
abbrev Eigenform.toIntegers (𝒻 : Eigenform D 𝒮) : anemic D 𝒮 →ₐ[R] 𝒻.integers := 𝒻.1.rangeRestrict

/-- The (minimal) prime corresponding to an eigenform. -/
def Eigenform.prime (𝒻 : Eigenform D 𝒮) : PrimeSpectrum (anemic D 𝒮) :=
  ⟨RingHom.ker 𝒻.1.toRingHom, RingHom.ker_isPrime _⟩

/-- `𝕋/𝔭(f) = 𝒪(f)` -/
def Eigenform.primeQuotient (𝒻 : Eigenform D 𝒮) :
    (anemic D 𝒮 ⧸ 𝒻.prime.asIdeal) ≃ₐ[R] 𝒻.integers := Ideal.quotientKerEquivRange _

@[simp]
lemma Eigenform.primeQuotient_mk (𝒻 : Eigenform D 𝒮) (x : anemic D 𝒮) :
    𝒻.primeQuotient (Ideal.Quotient.mk _ x) = 𝒻.toIntegers x := rfl

lemma Eigenform.toIntegers_surjective (𝒻 : Eigenform D 𝒮) :
    Function.Surjective 𝒻.toIntegers := 𝒻.1.rangeRestrict_surjective

instance : Algebra.IsIntegral R (HeckeAlgebra D 𝒮) :=
  .of_injective (Subalgebra.val _) Subtype.val_injective

instance : Algebra.IsIntegral R (anemic D 𝒮) :=
  .of_injective (Subalgebra.val _) Subtype.val_injective

instance [IsNoetherianRing R] : IsNoetherian R (anemic D 𝒮) :=
  isNoetherian_of_injective (anemic D 𝒮).val.toLinearMap Subtype.val_injective

instance (𝒻 : Eigenform D 𝒮) : Algebra.IsIntegral R 𝒻.integers :=
  .of_surjective _ 𝒻.toIntegers_surjective

instance [IsNoetherianRing R] (𝒻 : Eigenform D 𝒮) : Module.Finite R 𝒻.integers :=
  .of_surjective 𝒻.toIntegers.toLinearMap 𝒻.toIntegers_surjective

variable (D 𝒮) in
/-- The embedding of the anemic Hecke algebra into a product of domains, indexed by eigenforms. -/
def toProdEigenform : anemic D 𝒮 →ₐ[R] Π (𝒻 : Eigenform D 𝒮), 𝒻.integers :=
  AlgHom.pi fun 𝒻 ↦ 𝒻.toIntegers

@[simp]
lemma toProdEigenform_apply (x : anemic D 𝒮) (𝒻 : Eigenform D 𝒮) :
    toProdEigenform D 𝒮 x 𝒻 = 𝒻.toIntegers x := rfl

lemma smul_formTensorScalar_tmul (T : HeckeAlgebra D 𝒮) (a b) :
    T • (U₁ 𝒮).toStruct.formTensorScalar D ℂ ℂ (a ⊗ₜ[R] b) =
      (U₁ 𝒮).toStruct.formTensorScalar D ℂ ℂ (a ⊗ₜ[R] (T • b)) := by
  simp [LevelStruct.formTensorScalar_tmul, ← formMap_smul]

variable [FaithfulSMul R ℂ]

variable (D 𝒮) in
lemma toProdEigenform_injective : Function.Injective (toProdEigenform D 𝒮) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  ext1
  refine FaithfulSMul.eq_of_smul_eq_smul (α := S(U, ℂ)) fun f ↦ ?_
  have := (Eigenform.isInternal D 𝒮).submodule_iSup_eq_top.ge (Set.mem_univ f)
  induction this using Submodule.iSup_induction' with
  | zero => simp
  | add x y hx hy _ _ => simp only [smul_add, *]
  | mem 𝒻 f hf =>
    refine (Eigenform.mem_eigenspace_iff.mp hf x).trans ?_
    simp [show 𝒻.1 x = 0 from congr(($hx 𝒻).1)]

instance : IsReduced (anemic D 𝒮) :=
  isReduced_of_injective _ (toProdEigenform_injective D 𝒮)

open scoped TensorProduct

instance {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K] :
    Module.Flat R K :=
  have : IsDomain R := .of_faithfulSMul R K
  let : Algebra (FractionRing R) K := FractionRing.liftAlgebra _ _
  .trans R (FractionRing R) K

theorem Algebra.lsmul_injective_of_faithfulSMul
    (R : Type*) {A : Type*} (B : Type*) (M : Type*) [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [AddCommMonoid M] [Module R M] [Module A M]
    [Module B M] [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
    [FaithfulSMul A M] :
    Function.Injective (Algebra.lsmul R (A := A) B M) :=
  fun _ _ e ↦ FaithfulSMul.eq_of_smul_eq_smul (α := M) fun x ↦ congr($e x)

theorem Algebra.TensorProduct.lTensor_injective {R S : Type*} (A : Type*) {B D : Type*}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring D] [Algebra R D]
    [Module.Flat R A] (g : B →ₐ[R] D) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.lTensor (S := S) A g) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ hg

@[simp]
lemma _root_.AlgHom.map_zero {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) : f 0 = 0 := _root_.map_zero _

lemma Eigenform.pi_lift_injective :
    Function.Injective ((AlgHom.pi fun 𝒻 ↦
    Algebra.TensorProduct.lift (.id _ _) 𝒻.1 fun _ _ ↦ .all _ _) :
      ℂ ⊗[R] anemic D 𝒮 →ₐ[ℂ] (Eigenform D 𝒮 → ℂ)) := by
  refine (injective_iff_map_eq_zero _).mpr fun a e ↦ ?_
  refine Algebra.TensorProduct.lTensor_injective (S := ℂ) ℂ _
    (Algebra.lsmul_injective_of_faithfulSMul R (A := anemic D 𝒮) R S(U, R)) ?_
  refine (lTensorHomEquivHomLTensor _ _ _ _).injective ?_
  refine (LinearMap.liftBaseChangeEquiv ℂ).injective ?_
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := ((U₁ 𝒮).toStruct.formTensorScalar D ℂ ℂ).symm.surjective x
  simp only [lTensorHomEquivHomLTensor_apply, AlgHom.map_zero,
    LinearEquiv.map_zero, LinearMap.zero_apply]
  have := (Eigenform.isInternal D 𝒮).submodule_iSup_eq_top.ge (Set.mem_univ x)
  induction this using Submodule.iSup_induction' with
  | zero => simp
  | add x y hx hy _ _ => simp only [*, map_add, zero_add]
  | mem 𝒻 f hf =>
  trans ((U₁ 𝒮).toStruct.formTensorScalar D ℂ ℂ).symm
    ((Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) 𝒻.1 fun _ _ ↦ .all _ _) a • f); swap
  · have := congr($e 𝒻)
    simp_all
  clear e
  induction a with
  | zero => simp
  | add x y _ _ => simp only [map_add, LinearMap.add_apply, add_smul, *]
  | tmul x y =>
  have := Eigenform.mem_eigenspace_iff.mp hf
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, ne_eq,
    Algebra.TensorProduct.lift_tmul, mul_smul, ← this]
  clear hf this
  obtain ⟨f, rfl⟩ := ((U₁ 𝒮).toStruct.formTensorScalar D ℂ ℂ).surjective f
  simp only [LinearEquiv.symm_apply_apply, map_smul]
  induction f with
  | zero => simp
  | add x y H₁ H₂ => simp only [map_add, smul_add, *]
  | tmul a b =>
  simp [Subalgebra.smul_def, smul_formTensorScalar_tmul, TensorProduct.smul_tmul', mul_comm]

/-- There is a correspondence between `K`-subalgebras of `Kⁿ` and partitions of `n`, where
for each set in the partition we take the diagonal subalgebra. -/
def Pi.subalgebraEquiv (n K : Type*) [Finite n] [Field K] : Subalgebra K (n → K) ≃ Setoid n where
  toFun s := { r i j := ∀ a ∈ s, a i = a j, iseqv := by constructor <;> grind }
  invFun s :=
  { carrier := { a | ∀ i j, i ≈ j → a i = a j }
    mul_mem' {a b} ha hb i j e := by simp [ha i j e, hb i j e]
    add_mem' {a b} ha hb i j e := by simp [ha i j e, hb i j e]
    algebraMap_mem' := by simp }
  left_inv s := by
    classical
    let st : Setoid n := { r i j := ∀ a ∈ s, a i = a j, iseqv := by constructor <;> grind }
    cases nonempty_fintype n
    ext v
    change (∀ (i j : n), (∀ a ∈ s, a i = a j) → v i = v j) ↔ v ∈ s
    refine ⟨fun H ↦ ?_, by grind⟩
    have : v = ∑ i : Quotient st, i.lift v H • (Quotient.mk _ ⁻¹' {i}).indicator 1 := by
      ext; simp [Set.indicator]
    rw [this]
    refine sum_mem fun i _ ↦ s.smul_mem ?_ _
    obtain ⟨i, rfl⟩ := Quotient.mk_surjective i
    have (j : n) (hj : ¬ i ≈ j) : ∃ a ∈ s, a i = 1 ∧ a j = 0 := by
      obtain ⟨a, ha, h⟩ := not_forall₂.mp hj
      exact ⟨(a i - a j)⁻¹ • (a - algebraMap K (n → K) (a j)),
        s.smul_mem (sub_mem ha (by simp)) _, by simp [sub_eq_zero, h], by simp⟩
    choose! a has ha₁ ha₀ using this
    have : (∏ j ∈ { j | ¬ i ≈ j }, a j) ∈ s := prod_mem fun j hj ↦ has _ (by simpa using hj)
    convert this
    ext j
    rw [Finset.prod_apply]
    by_cases h : j ≈ i
    · trans 1
      · simp [Quotient.eq, h]
      · refine (Finset.prod_eq_one fun k hk ↦ ?_).symm
        rw [h _ (has _ (by simpa using hk)), ha₁ _ (by simpa using hk)]
    · trans 0
      · simp [Quotient.eq, h]
      · refine (Finset.prod_eq_zero (i := j) (by simpa using mt Setoid.symm h) ?_).symm
        exact ha₀ _ (mt Setoid.symm h)
  right_inv s := by
    classical
    ext i j
    change (∀ (a : n → K) (ha : ∀ i j, i ≈ j → a i = a j), _) ↔ i ≈ j
    refine ⟨fun H ↦ ?_, by grind⟩
    simpa using H (fun k ↦ if i ≈ k then 1 else 0)
      (fun i' j' e ↦ by simp [rel_congr_right e])

@[simp]
lemma Pi.subalgebraEquiv_top (n K : Type*) [Finite n] [Field K] :
    Pi.subalgebraEquiv n K ⊤ = ⊥ := by
  classical
  ext i j
  exact ⟨fun H ↦ by simpa [Pi.single_apply] using H (Pi.single j 1) (by simp), by aesop⟩

variable (D 𝒮) in
/-- The complex anemic Hecke algebra is isomorphic to a product of copies of `ℂ`'s,
one for each eigenform. -/
def tensorEquivPi : ℂ ⊗[R] anemic D 𝒮 ≃ₐ[ℂ] (Eigenform D 𝒮 → ℂ) := by
  refine .ofBijective (AlgHom.pi fun 𝒻 ↦
    Algebra.TensorProduct.lift (.id _ _) 𝒻.1 fun _ _ ↦ .all _ _) ⟨Eigenform.pi_lift_injective, ?_⟩
  rw [← AlgHom.range_eq_top, ← (Pi.subalgebraEquiv _ _).injective.eq_iff, Pi.subalgebraEquiv_top,
    ← le_bot_iff]
  exact fun 𝒻 𝒻' H ↦ Subtype.ext (AlgHom.ext fun x ↦ by simpa using H _ ⟨1 ⊗ₜ x, rfl⟩)

@[simp]
lemma tensorEquivPi_tmul_apply (z T 𝒻) :
    tensorEquivPi D 𝒮 (z ⊗ₜ T) 𝒻 = z • 𝒻.1 T := rfl

/-- The eigenforms corresponds exactly to maps from `𝕋` to `ℂ`. -/
def Eigenform.equivAlgHom : Eigenform D 𝒮 ≃ (anemic D 𝒮 →ₐ[R] ℂ) :=
  .ofBijective Subtype.val ⟨Subtype.val_injective, fun φ ↦ by
  let φ' := (Algebra.TensorProduct.lift (.id ℂ ℂ) φ (fun _ _ ↦ .all _ _)).comp
    (tensorEquivPi D 𝒮).symm.toAlgHom
  obtain ⟨𝒻, h𝒻⟩ : ∃ i, φ' (Pi.single i 1) ≠ 0 := by
    by_contra! H
    have : φ' (∑ i, Pi.single i 1) = 1 := by rw [Finset.univ_sum_single]; exact map_one _
    simp [H] at this
  refine ⟨𝒻, ?_⟩
  have: φ' = Pi.evalAlgHom _ _ 𝒻 := by
    ext f
    refine mul_left_injective₀ h𝒻 ?_
    dsimp only
    rw [← map_mul, ← Pi.single_mul_right]
    trans φ' (f 𝒻 • Pi.single 𝒻 1)
    · congr 1; ext; simp [Pi.single_apply]
    · simp
  ext T
  simpa [φ'] using congr($this (tensorEquivPi D 𝒮 (1 ⊗ₜ T))).symm⟩

lemma Eigenform.under_prime (𝒻 : Eigenform D 𝒮) : 𝒻.prime.asIdeal.under R = ⊥ := by
  refine le_bot_iff.mp fun x hx ↦ ?_
  simpa [prime] using hx

lemma Eigenform.prime_mem_minimalPrimes [IsNoetherianRing R] (𝒻 : Eigenform D 𝒮) :
    𝒻.prime.asIdeal ∈ minimalPrimes (anemic D 𝒮) := by
  refine ⟨⟨inferInstance, bot_le⟩, fun P ⟨hP, _⟩ hP' ↦ ?_⟩
  refine (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) hP' ?_).ge
  refine le_antisymm (by exact Ideal.comap_mono hP') (by rw [𝒻.under_prime]; exact bot_le)

-- linter complained that [P.IsPrime] wasn't needed, so this lemma is now
-- poorly-named
lemma Eigenform.exists_le_of_isPrime (P : Ideal (anemic D 𝒮)) (hP : P.under R = ⊥) :
    ∃ 𝒻 : Eigenform D 𝒮, P ≤ 𝒻.prime.asIdeal := by
  have : Nontrivial (ℂ ⊗[R] (anemic D 𝒮 ⧸ P)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _ <| by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.alg_map_eq, ← RingHom.comap_ker,
        Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, ← hP]
  have : P.map (Algebra.TensorProduct.includeRight : _ →ₐ[R] ℂ ⊗[R] anemic D 𝒮) ≠ ⊤ := by
    rwa [← Ideal.Quotient.nontrivial_iff,
      ← (Algebra.TensorProduct.tensorQuotientEquiv R _ _ _).nontrivial_congr]
  have : P.map (AlgHom.pi fun 𝒻 ↦ 𝒻.1 : anemic D 𝒮 →ₐ[R] (Eigenform D 𝒮 → ℂ)) ≠ ⊤ := by
    rw [ne_eq, ← (Ideal.comap_injective_of_surjective (tensorEquivPi D 𝒮).toRingEquiv
      (tensorEquivPi D 𝒮).surjective).eq_iff]
    convert! this using 2
    rw [← Ideal.map_coe, ← Ideal.map_symm, ← Ideal.map_coe, Ideal.map_map]
    congr
    ext T
    apply (tensorEquivPi D 𝒮).injective
    ext 𝒻
    simp
  obtain ⟨M, hM, H⟩ := Ideal.exists_le_maximal _ this
  obtain ⟨⟨𝒻, p⟩, e⟩ := (PrimeSpectrum.sigmaToPi_bijective _).surjective ⟨M, inferInstance⟩
  obtain rfl : p = ⊥ := Subsingleton.elim _ _
  obtain rfl := congr(($e).asIdeal)
  exact ⟨𝒻, (Ideal.map_le_iff_le_comap.mp H:)⟩

lemma Eigenform.exists_of_isPrime [IsNoetherianRing R]
    (P : Ideal (anemic D 𝒮)) [P.IsPrime] (hP : P.under R = ⊥) :
    ∃ 𝒻 : Eigenform D 𝒮, P = 𝒻.prime.asIdeal := by
  obtain ⟨𝒻, h𝒻⟩ := exists_le_of_isPrime P hP
  exact ⟨𝒻, h𝒻.antisymm (𝒻.prime_mem_minimalPrimes.2 ⟨‹_›, bot_le⟩ h𝒻)⟩

end TotallyDefiniteQuaternionAlgebra.HeckeAlgebra
