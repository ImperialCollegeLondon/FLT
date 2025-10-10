/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.Group.Subgroup.Pointwise
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Algebra.Central.Defs
import Mathlib.Tactic.LinearCombination'
import Mathlib.Topology.Algebra.Group.Basic
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.Ring
import FLT.HaarMeasure.HaarChar.AdeleRing
import FLT.Mathlib.Topology.HomToDiscrete
import FLT.Mathlib.GroupTheory.DoubleCoset
import FLT.Mathlib.Topology.Algebra.Group.Quotient
import FLT.HaarMeasure.HaarChar.RealComplex

import FLT.DivisionAlgebra.scratch
import FLT.DivisionAlgebra.scratch3
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
  -- MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient
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

/-- The K-algebra equivalence of D and K^n. -/
abbrev D_iso : (D ≃ₗ[K] ((Fin (Module.finrank K D) → K))) := Module.Finite.equivPi K D

/-- The 𝔸-algebra equivalence of D_𝔸 and 𝔸^d. -/
abbrev D𝔸_iso : (D_𝔸 ≃ₗ[(AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K))) :=
  ((TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm).trans
    (TensorProduct.AlgebraTensorModule.finiteEquivPi K D (AdeleRing (𝓞 K) K))

local instance : IsModuleTopology (AdeleRing (𝓞 K) K)
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) := by

  sorry -- can be solved by typeclass inference if Mathlib#29315 is merged.

/-- The topological equivalence via D𝔸_iso. -/
abbrev D𝔸_iso_top : D_𝔸 ≃L[(AdeleRing (𝓞 K) K)]
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) :=
  IsModuleTopology.continuousLinearEquiv (D𝔸_iso K D)

/-- The inclusion of K^n into 𝔸^n. -/
abbrev incl_Kn_𝔸Kn : (Fin (Module.finrank K D) → K) →
    (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) :=
  fun x i ↦ algebraMap K (AdeleRing (𝓞 K) K) (x i)

omit [FiniteDimensional K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
theorem Kn_discrete : ∀ x : (Fin (Module.finrank K D) → K),
    ∃ U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K),
    IsOpen U ∧ (incl_Kn_𝔸Kn K D)⁻¹' U = {x} := by
  exact (DiscretePi (algebraMap K (AdeleRing (𝓞 K) K)) (Module.finrank K D))
    (NumberField.AdeleRing.discrete K)

omit [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
theorem D_discrete_extracted (U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) :
    incl_Kn_𝔸Kn K D ⁻¹' U  = (D_iso K D) ''
    (⇑(D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U) := by
  ext x
  constructor
  · intro hx
    use (D_iso K D).symm x
    simpa [← Algebra.algebraMap_eq_smul_one] using hx
  · intro ⟨y, hy1, hy2⟩
    have : (D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) =
        (incl_Kn_𝔸Kn K D) ∘ (D_iso K D) := by
      ext d n
      simp [← Algebra.algebraMap_eq_smul_one]
    rw [this] at hy1
    simpa [← hy2] using hy1

omit [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
theorem D_discrete : ∀ x : D, ∃ U : Set D_𝔸,
    IsOpen U ∧ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U = {x} := by
  apply Discrete_of_HomeoDiscrete (Y' := ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)))
    (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) (D𝔸_iso_top K D)
  apply Discrete_of_HomDiscrete (X' := Fin (Module.finrank K D) → K)
    ((D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) (D_iso K D)
  simpa [D_discrete_extracted] using Kn_discrete K D

/-- The additive subgroup with carrier defined by Algebra.TensorProduct.includeLeft. -/
local instance includeLeft_subgroup : AddSubgroup D_𝔸 :=
  AddMonoidHom.range (G := D) (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)

local instance : DiscreteTopology (includeLeft_subgroup K D).carrier := by
  rw [includeLeft_subgroup]
  apply (singletons_open_iff_discrete).mp
  rintro ⟨a, a', ha⟩
  obtain ⟨U, hUopen, hUeq⟩ := (D_discrete K D) a'
  refine isOpen_mk.mpr ⟨U, hUopen, Set.image_val_inj.mp ?_⟩
  simp only [Subtype.image_preimage_coe, Set.image_singleton]
  ext d
  constructor
  · rintro ⟨⟨c, hc⟩, hd2⟩
    refine Set.mem_singleton_of_eq ?_
    rw [← hc] at hd2
    apply Set.mem_preimage.mpr at hd2
    simp only [AddMonoidHom.coe_coe, hUeq, Set.mem_singleton_iff] at hd2
    simp_rw [← hc, hd2, ha]
  · intro hd
    constructor
    · refine Set.mem_range.mpr ⟨a', ?_⟩
      rwa [hd]
    · rw [hd, ← ha]
      exact Set.mem_preimage.mp (by simp [hUeq])

instance : T2Space (D ⊗[K] AdeleRing (𝓞 K) K) := IsModuleTopology.t2Space (AdeleRing (𝓞 K) K)

lemma T_finite_extracted1 : IsCompact (Y K D ∩
    Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
  refine IsCompact.inter_right (Y_compact K D) ?_
  have : DiscreteTopology (includeLeft_subgroup K D).carrier := by
    infer_instance
  simpa [includeLeft_subgroup] using AddSubgroup.isClosed_of_discrete
    (H := includeLeft_subgroup K D)

lemma T_finite : Set.Finite (T K D) := by
  have h := IsCompact.finite (T_finite_extracted1 K D)
    (inter_Discrete (includeLeft_subgroup K D).carrier (Y K D))
  have h1 : Units.val '' T K D ⊆ (Y K D) ∩
      (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
    rintro _ ⟨t, ⟨ht1, d, rfl⟩, rfl⟩
    exact ⟨ht1, d, rfl⟩
  exact Set.Finite.of_finite_image (Set.Finite.subset h h1)
    (Function.Injective.injOn Units.val_injective)

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
    by simpa using Units.val_inj.mp (id (Eq.symm (by simpa [mul_assoc] using
    (Mathlib.Tactic.LinearCombination'.mul_pf eq2 eq1))))⟩
  refine ⟨incl K D b1, by simp only [Set.mem_range, exists_apply_eq_apply],  x1⁻¹, ?_,
    eq_mul_inv_of_mul_eq (Units.val_inj.mp eq1), ?_, hx1⟩
  · rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq (Units.val_inj.mp eq1))))]
    exact (Subgroup.mul_mem_cancel_right (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K)) hβ).mpr
      ((Subgroup.inv_mem_iff (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))).mpr
      (NumberField.AdeleRing.units_mem_ringHaarCharacter_ker K D b1))
  · obtain ⟨t, ht, ht1⟩ := exists_eq_right'.mpr h
    simp_rw [(Eq.symm (inv_mul_eq_of_eq_mul (eq_mul_inv_of_mul_eq ht1)))]
    exact Set.mem_mul.mpr ⟨↑t⁻¹, Set.mem_image_of_mem Units.val ht, x2, hx2, rfl⟩

end Aux

/-- The inclusion of `ringHaarChar_ker D_𝔸` into the product space `D_𝔸 × D_𝔸ᵐᵒᵖ`. -/
def incl₂ : ringHaarChar_ker D_𝔸 → Prod D_𝔸 D_𝔸ᵐᵒᵖ :=
  fun u => Units.embedProduct D_𝔸 (Subgroup.subtype (ringHaarChar_ker D_𝔸) u)

/-- An auxillary set used in the proof of compact_quotient'. -/
def M : Set (ringHaarChar_ker D_𝔸) := Set.preimage (incl₂ K D)
  (Set.image (fun p => (p.1, MulOpposite.op p.2)) (Aux.C K D))

/-- The map from `ringHaarChar_ker D_𝔸` to the quotient `Dˣ \ ringHaarChar_ker D_𝔸`. -/
abbrev toQuot (a : ringHaarChar_ker D_𝔸) : (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  (Quotient.mk (QuotientGroup.rightRel ((MonoidHom.range (incl K D)).comap
  (ringHaarChar_ker D_𝔸).subtype)) a)

lemma toQuot_cont : Continuous (toQuot K D) := by exact { isOpen_preimage := fun s a ↦ a }

lemma toQuot_surjective : (toQuot K D) '' (M K D) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  rintro ⟨a, ha⟩
  obtain ⟨c, hc, ν, hν, rfl, h31⟩ := Aux.antidiag_mem_C K D ha
  simp only [toQuot, Subgroup.comap_subtype, Set.mem_image, Subtype.exists]
  refine ⟨ν, hν, ?_, ?_ ⟩
  · simp only [M, Set.mem_preimage, Set.mem_image, Prod.exists]
    exact ⟨ν, Units.val (ν⁻¹), h31, rfl⟩
  · have : Quot.mk ⇑(QuotientGroup.rightRel ((incl K D).range.subgroupOf
        (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K)))) ⟨c * ν, ha⟩ =
        Quot.mk ⇑(QuotientGroup.rightRel ((incl K D).range.subgroupOf
        (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))))
        ⟨ν, hν⟩ := by
      refine Quot.sound ?_
      rw [@QuotientGroup.rightRel_apply]
      refine Subgroup.mem_subgroupOf.mpr ?_
      simp only [@Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, mul_inv_cancel_left,
        inv_mem_iff, MonoidHom.mem_range]
      exact hc
    rw [this]
    rfl

lemma incl₂_isClosedEmbedding : Topology.IsClosedEmbedding (incl₂ K D) := by
  apply Units.isClosedEmbedding_embedProduct.comp
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_iff_le_induced.mpr fun U a ↦ a)
    (Subgroup.subtype_injective (ringHaarChar_ker (D ⊗[K] AdeleRing (𝓞 K) K))) ?_
  simp only [Subgroup.coe_subtype]
  refine Topology.IsInducing.isClosedMap ({ eq_induced := rfl }) ?_
  simp only [Subtype.range_coe_subtype, SetLike.setOf_mem_eq]
  exact IsClosed.preimage (continuous_id')
    (IsClosed.preimage (map_continuous ringHaarChar) (by simp))

lemma ImAux_isCompact : IsCompact ((fun p ↦ (p.1, MulOpposite.op p.2)) '' Aux.C K D) :=
  IsCompact.image (Aux.C_compact K D) <| by fun_prop

lemma M_compact : IsCompact (M K D) := Topology.IsClosedEmbedding.isCompact_preimage
  (incl₂_isClosedEmbedding K D) (ImAux_isCompact K D)

lemma compact_quotient : CompactSpace (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  isCompact_univ_iff.mp (by simpa only [toQuot_surjective, Set.image_univ] using
    (((IsCompact.image (M_compact K D) (toQuot_cont K D)))))

end NumberField.AdeleRing.DivisionAlgebra

section FiniteAdeleRing

open scoped TensorProduct.RightActions

-- Instance to help speed up instance synthesis
instance inst1 : NonUnitalNonAssocRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  Algebra.TensorProduct.instRing.toNonUnitalRing.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance isnt2 : NonAssocSemiring (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

-- Instance to help speed up instance synthesis
local instance inst3 : NonUnitalNonAssocRing (D ⊗[K] NumberField.InfiniteAdeleRing K) :=
  Algebra.TensorProduct.instRing.toNonUnitalRing.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
local instance inst4 : NonAssocSemiring (D ⊗[K] NumberField.InfiniteAdeleRing K) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

variable [MeasurableSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

/-- The equivalence of the units of D_𝔸 and the Prod of units of (D ⊗ 𝔸_K^f) (D ⊗ 𝔸_K^∞). -/
def iso₁ : D_𝔸ˣ ≃* Prod (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ (Dfx K D) :=
  (Units.mapEquiv (AlgEquiv.toMulEquiv (Algebra.TensorProduct.prodRight K K D _ _))).trans
  (MulEquiv.prodUnits)

local instance : Module (NumberField.AdeleRing (𝓞 K) K)
    (D ⊗[K] (NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)) := by
  exact TensorProduct.RightActions.instModule_fLT K
    (NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) D

def mapp : (D ⊗[K] (NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
    →ₐ[K] (D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  (Algebra.TensorProduct.prodRight K K D (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K))

local instance hmm : Module (NumberField.AdeleRing (𝓞 K) K)
    (D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K) := by
  simp_rw [NumberField.AdeleRing]
  exact
    nameme (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
      (D ⊗[K] NumberField.InfiniteAdeleRing K) (D ⊗[K] FiniteAdeleRing (𝓞 K) K)

set_option maxHeartbeats 0 in
-- rfl is not being inferred; and something about the have statement breaks
def bar : (D ⊗[K] (NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
    →ₗ[NumberField.AdeleRing (𝓞 K) K]
    (D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K) where
  toFun x := mapp K D x
  map_add' a b := by
    exact RingHom.map_add (mapp K D).toRingHom a b
  map_smul' m x := by
    simp only [RingHom.id_apply]
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    simp_rw [hx]
    simp_rw [Finset.smul_sum]
    simp only [map_sum]
    simp only [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul]
    simp_rw [TensorProduct.smul_tmul']
    simp only [TensorProduct.comm_symm_tmul]
    obtain ⟨m1, m2⟩ := m
    have : (m1, m2) • ∑ x ∈ s, (mapp K D) (x.1 ⊗ₜ[K] x.2) =
        ∑ x ∈ s, (m1, m2) • ((mapp K D) (x.1 ⊗ₜ[K] x.2)) := by
      have I := hmm K D
      apply Module.toDistribMulAction at I
      apply DistribMulAction.toDistribSMul at I
      have := @Finset.smul_sum (NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)
        (D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K)
        (D × NumberField.InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _ I (m1, m2)
        (fun x => (mapp K D) (x.1 ⊗ₜ[K] x.2)) s
      convert this


      -- really need to work out how to solve this instancing problem...
      all_goals sorry
    simp_rw [this]
    rfl

lemma iso₁_cont_extracted : Continuous (Algebra.TensorProduct.prodRight K K D
    (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) := by
  have I : NonUnitalNonAssocSemiring (D ⊗[K] NumberField.InfiniteAdeleRing K) := by
    let I := inst3 K D
    exact I.toNonUnitalNonAssocSemiring
  have J : NonUnitalNonAssocSemiring (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := by
    let J := inst1 K D
    exact J.toNonUnitalNonAssocSemiring
  convert IsModuleTopology.continuous_of_linearMap (bar K D)
  simp_rw [NumberField.AdeleRing]
  exact smul_cont _ _ _ _

set_option maxHeartbeats 250000 in
-- final is not infering without increasing?
lemma iso₁_symm_continuous : Continuous (Algebra.TensorProduct.prodRight K K D
    (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).invFun := by
  simp only [AlgEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, AlgEquiv.symm_toEquiv_eq_symm,
    EquivLike.coe_coe]
  apply (Equiv.isOpenMap_symm_iff _).mp
  simp only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, AlgEquiv.symm_symm,
    EquivLike.coe_coe]
  have : NonUnitalNonAssocSemiring (D ⊗[K] (NumberField.AdeleRing (𝓞 K) K)) :=
    Algebra.TensorProduct.instNonUnitalNonAssocSemiring
  simp_rw [NumberField.AdeleRing] at this
  convert IsModuleTopology.isOpenMap_of_surjective (φ := bar K D)
  · simp_rw [bar, mapp]
    simp only [AlgHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk, Classical.imp_iff_left_iff]
    left
    exact AlgEquiv.surjective _
  · simp_rw [NumberField.AdeleRing]
    exact Final (NumberField.InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
      (D ⊗[K] NumberField.InfiniteAdeleRing K) (D ⊗[K] FiniteAdeleRing (𝓞 K) K)

lemma iso₁_continuous : Continuous (iso₁ K D) := by
  rw [iso₁, MulEquiv.coe_trans]
  apply Continuous.comp ?_ ?_
  · apply Continuous.prodMk
    · apply Continuous.units_map
      exact continuous_fst
    · apply Continuous.units_map
      exact continuous_snd
  · apply Continuous.units_map
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.coe_mk,
      AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    exact iso₁_cont_extracted K D

/-- The restriction of ringHaarChar_ker D_𝔸 to Dfx K D. -/
abbrev rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => (iso₁ K D) a.val |>.2

lemma rest₁_continuous : Continuous (rest₁ K D) := by
  exact Continuous.comp continuous_snd (Continuous.comp
    (iso₁_continuous K D) continuous_subtype_val)

local instance : MeasurableSpace (D ⊗[K] NumberField.InfiniteAdeleRing K ×
    D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  borel (D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K)

local instance : BorelSpace (D ⊗[K] NumberField.InfiniteAdeleRing K ×
    D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  {measurable_eq := rfl }

abbrev foo : D ⊗[K] NumberField.AdeleRing (𝓞 K) K ≃ₜ+
    D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K where
  toFun := (Algebra.TensorProduct.prodRight _ _ _ _ _).toFun
  invFun := (Algebra.TensorProduct.prodRight _ _ _ _ _).invFun
  map_add' _ _ := (Algebra.TensorProduct.prodRight _ _ _ _ _).map_add' _ _
  left_inv := (Algebra.TensorProduct.prodRight _ _ _ _ _).left_inv
  right_inv := (Algebra.TensorProduct.prodRight K K D (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K)).right_inv
  continuous_toFun := by
    exact iso₁_cont_extracted K D
  continuous_invFun := by
    exact iso₁_symm_continuous K D

set_option maxHeartbeats 0 in
-- no idea... the istancing in this file is terrible
lemma ringHaarChar_eq1 (a : (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ) (b : Dfx K D) :
    ringHaarChar ((iso₁ K D).symm (a, b)) =
    ringHaarChar (MulEquiv.prodUnits.symm (a, b)) := by
  unfold iso₁
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (foo K D)
  intro x
  dsimp only [MulEquiv.symm_trans_apply, Units.mapEquiv_symm, MulEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, ContinuousAddEquiv.mulLeft_apply,
    Units.coe_mapEquiv, MulEquiv.coe_mk, EquivLike.coe_coe, ContinuousAddEquiv.coe_mk,
    Equiv.toFun_as_coe, Equiv.invFun_as_coe, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [MulEquivClass.map_mul]
  have : NonUnitalNonAssocRing (D ⊗[K] (NumberField.AdeleRing (𝓞 K) K)) := by
    exact Algebra.TensorProduct.instNonUnitalNonAssocRing -- not sure why I need this instance
  simp_rw [NumberField.AdeleRing] -- not really sure what this is doing
  rw [AlgEquiv.apply_symm_apply]

lemma Step1 (r : ℝ) (hr : 0 < r) (d : ℕ) (hd : d ≠ 0) : ∃ m : ℝˣ,
    ringHaarChar m = r^(1/(d : ℝ)) := by
  simp_rw [MeasureTheory.ringHaarChar_real]
  have : IsUnit (r^(1/(d : ℝ))) := by
    simp only [one_div, isUnit_iff_ne_zero]
    exact (Real.rpow_ne_zero (le_of_lt hr) (by simpa)).mpr (Ne.symm (ne_of_lt hr))
  use (Units.mk0 (r^(1/(d : ℝ))) (by simpa))
  simp only [one_div, Units.val_mk0, coe_nnnorm, Real.norm_eq_abs, abs_eq_self]
  exact Real.rpow_nonneg (le_of_lt hr) (↑d)⁻¹

lemma Step2 (r : ℝ) (hr : r > 0) (d : ℕ) (hd : d ≠ 0) : ∃ m : (Fin d → ℝ)ˣ, ringHaarChar m = r ∧
    (∃ a : ℝˣ, m.val = algebraMap ℝ (Fin d → ℝ) a) := by
  obtain ⟨m', hm'⟩ := Step1 r hr d hd
  use (MulEquiv.piUnits (ι := Fin d) (M := fun _ => ℝ)).symm (fun (i : Fin d) => m')
  constructor
  · have : ringHaarChar (MulEquiv.piUnits.symm (fun (i : Fin d) ↦ m')) = ∏ (i : Fin d),
        ringHaarChar ((fun i ↦ m') i) := by
      have := MeasureTheory.ringHaarChar_pi (ι := Fin d) (A := fun _ : Fin d => ℝ)
        (fun (i : Fin d) ↦ m')
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this ⊢
      convert this
      exact BorelSpace.measurable_eq
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, NNReal.coe_pow, hm']
    simp only [one_div]
    exact Real.rpow_inv_natCast_pow (le_of_lt hr) hd
  · use m'
    rfl

-- new things I need:

local instance : Algebra ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K) := by

  sorry

local instance : Module.Finite ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K) := by

  sorry

local instance : Module.Free ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K) := by
  -- trivial as reals are a field
  sorry

local instance : IsModuleTopology ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K) := by

  sorry

local instance : MeasurableSpace (D ⊗[K] NumberField.InfiniteAdeleRing K) :=
  borel (D ⊗[K] NumberField.InfiniteAdeleRing K)

local instance : BorelSpace (D ⊗[K] NumberField.InfiniteAdeleRing K) := { measurable_eq := rfl }

local instance : MeasurableSpace (D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  borel (D ⊗[K] FiniteAdeleRing (𝓞 K) K)

local instance : BorelSpace (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := { measurable_eq := rfl }

lemma Step3 (r : ℝ) (hr : r > 0) : ∃ y, ringHaarChar ((iso₁ K D).symm (y,1)) = r := by
  obtain ⟨m, hm, ha⟩ := Step2 r hr (Module.finrank ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K))
    (Nat.ne_zero_iff_zero_lt.mpr Module.finrank_pos)
  have h : IsUnit ((iso' (D ⊗[K] NumberField.InfiniteAdeleRing K)).symm m) := by
    refine isUnit_iff_exists.mpr ?_
    obtain ⟨a, ha⟩ := ha
    use (iso' (D ⊗[K] NumberField.InfiniteAdeleRing K)).symm
      ((algebraMap ℝ (Fin (Module.finrank ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K)) → ℝ)) (1/a))
    have h1 : (iso' (D ⊗[K] NumberField.InfiniteAdeleRing K)).symm
        ((algebraMap ℝ (Fin (Module.finrank ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K)) → ℝ)) a) =
        ∑ j, ((algebraMap ℝ (Fin (Module.finrank ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K)) → ℝ))
        a) j • (Classical.choose (basis_existance (D ⊗[K] NumberField.InfiniteAdeleRing K))) j :=
      Module.Basis.equivFun_symm_apply _ _
    have h2 : (iso' (D ⊗[K] NumberField.InfiniteAdeleRing K)).symm
          ((algebraMap ℝ (Fin (Module.finrank ℝ (D ⊗[K] NumberField.InfiniteAdeleRing K)) → ℝ))
          (1/a)) = ∑ j, ((algebraMap ℝ (Fin (Module.finrank ℝ
          (D ⊗[K] NumberField.InfiniteAdeleRing K)) → ℝ)) (1/a)) j • (Classical.choose
          (basis_existance (D ⊗[K] NumberField.InfiniteAdeleRing K))) j :=
        Module.Basis.equivFun_symm_apply _ _
    simp_rw [ha, h1, h2]
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, one_div, map_inv₀]
    simp_rw [← Finset.smul_sum, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul,
      Classical.choose_spec (basis_existance _), mul_one]
    simp only [ne_eq, Units.ne_zero, not_false_eq_true, inv_mul_cancel₀, one_smul, mul_inv_cancel₀,
      and_self]
  have := ringHaarChar_eq1' (D ⊗[K] NumberField.InfiniteAdeleRing K) m
    (Exists.elim ha (fun a ha_eq => ⟨(a : ℝ), by rw [←ha_eq]⟩)) h
  use h.unit
  simp_rw [ringHaarChar_eq1, ringHaarChar_prod]
  simp only [map_one, mul_one]
  rw [← this]
  exact hm

lemma rest₁_surjective : (rest₁ K D) '' Set.univ = Set.univ := by
  simp only [Set.image_univ]
  refine Eq.symm (Set.ext ?_)
  intro x
  simp only [Set.mem_univ, Set.mem_range, Subtype.exists, true_iff]
  obtain ⟨r, hx⟩ : ∃ r, ringHaarChar ((iso₁ K D).symm (1,x)) = r := exists_eq'
  have hr : r > 0 := by
    rw [←hx]
    have (a : (D_𝔸)ˣ): 0 < ringHaarChar a := by
      exact addEquivAddHaarChar_pos _
    exact this ((iso₁ K D).symm (1, x))
  obtain ⟨y, hy⟩ : ∃ y, ringHaarChar ((iso₁ K D).symm (y,1)) = r := by
    obtain ⟨y, hy⟩ := Step3 K D r hr
    use y
    aesop
  use (iso₁ K D).symm (y⁻¹, x)
  constructor
  · rw [rest₁]
    refine Units.val_inj.mp ?_
    simp only [MulEquiv.apply_symm_apply]
  · ext
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe, NNReal.coe_one,
      NNReal.coe_eq_one]
    have : (y⁻¹, x) = (y⁻¹, 1) * (1, x) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    simp_rw [this, map_mul]
    have : ringHaarChar ((iso₁ K D).symm (y⁻¹, 1)) = r⁻¹ := by
      rw [← hy]
      have : ringHaarChar ((iso₁ K D).symm (y⁻¹, 1)) * (ringHaarChar ((iso₁ K D).symm (y, 1))) = 1
          := by
        simp_rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        have : (iso₁ K D).symm (1, 1) = 1 := by
          exact (MulEquiv.map_eq_one_iff (iso₁ K D).symm).mpr rfl
        simp only [this, map_one]
      exact Eq.symm (inv_eq_of_mul_eq_one_left this)
    simpa [this, hx] using (inv_mul_cancel₀ hr.ne')

lemma α_equivariant : ∀ (a b : ↥(ringHaarChar_ker D_𝔸)),
    (QuotientGroup.rightRel (Subgroup.comap (ringHaarChar_ker D_𝔸).subtype
    (NumberField.AdeleRing.DivisionAlgebra.incl K D).range)) a b →
    (Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a) =
     Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D b)) := by
  intros a b hab
  refine Quotient.eq''.mpr ?_
  unfold rest₁
  obtain ⟨h, rfl⟩ := hab
  simp_rw [QuotientGroup.rightRel, MulAction.orbitRel, MulAction.orbit, Set.mem_range,
    Subtype.exists, Subgroup.mk_smul, smul_eq_mul, MonoidHom.mem_range, exists_prop,
    exists_exists_eq_and]
  obtain ⟨t, t', ht⟩ := h
  use t'
  have : incl₁ K D t' = ((iso₁ K D) (NumberField.AdeleRing.DivisionAlgebra.incl K D t')).2 := by
    rfl
  simp_rw [this, ht, ← Prod.snd_mul, Subgroup.subtype_apply, Subgroup.comap_subtype, ← map_mul]
  rfl

/-- The obvious map Dˣ \ D_𝔸^(1) to Dˣ \ (Dfx K D). -/
def α : Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (NumberField.AdeleRing.DivisionAlgebra.incl K D)).comap
    (ringHaarChar_ker D_𝔸).subtype)) →
    Quotient (QuotientGroup.rightRel (incl₁ K D).range) :=
  Quot.lift
    (fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a))
    (α_equivariant K D)

lemma α_continuous : Continuous (α K D) := by
  rw [α]
  refine Continuous.quotient_lift ?_ (α_equivariant K D)
  refine Continuous.comp' ?_ ?_
  · exact { isOpen_preimage := fun s a ↦ a }
  · exact rest₁_continuous K D

lemma α_surjective : Function.Surjective (α K D) := by
  refine (Quot.surjective_lift (f := fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range)
    (rest₁ K D a)) (α_equivariant K D)).mpr ?_
  refine Set.range_eq_univ.mp ?_
  ext x
  simp only [Set.mem_range, Subtype.exists, Set.mem_univ, iff_true]
  have h := rest₁_surjective K D
  have : ∃ a : (ringHaarChar_ker (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)),
      (rest₁ K D) a = x.out := by
    refine Set.mem_range.mp ?_
    simp only [Set.image_univ] at h
    aesop
  obtain ⟨a, ha⟩ := this
  use a
  simp only [Subtype.coe_eta, SetLike.coe_mem, exists_const, ha]
  exact Quotient.out_eq x

theorem NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) := by
  have := isCompact_univ_iff.mpr (NumberField.AdeleRing.DivisionAlgebra.compact_quotient K D)
  apply isCompact_univ_iff.mp
  have := IsCompact.image (this) (α_continuous K D)
  rw [Set.image_univ_of_surjective (α_surjective K D)] at this
  exact this

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If `D` is a finite-dimensional division algebra over a number field `K`
then the double coset space `Dˣ \ (D ⊗ 𝔸_K^infty)ˣ / U` is finite for any compact open subgroup `U`
of `(D ⊗ 𝔸_F^infty)ˣ`.
-/
open scoped TensorProduct.RightActions in
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (DoubleCoset.Quotient (Set.range (incl₁ K D)) U) := by
  have ToFinCover := IsCompact.elim_finite_subcover
    (ι := (DoubleCoset.Quotient (Set.range (incl₁ K D)) U))
    (U := fun q ↦ Quot.mk ⇑(QuotientGroup.rightRel (incl₁ K D).range) ''
    DoubleCoset.doubleCoset (Quotient.out q) (Set.range ⇑(incl₁ K D)) U) (isCompact_univ_iff.mpr
    (NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D))
  have ⟨t, FinCover_descended⟩ := ToFinCover (DoubleCoset.isOpen_doubleCoset_rightrel_mk
    ((incl₁ K D).range) U hU) (DoubleCoset.union_image_mk_rightRel (incl₁ K D).range U
    ▸ Set.Subset.rfl)
  apply (DoubleCoset.iUnion_finset_quotTodoubleCoset ((incl₁ K D).range) U).mp
  exact ⟨t, DoubleCoset.union_finset_rightrel_cover ((incl₁ K D).range) U t FinCover_descended⟩

end FiniteAdeleRing
