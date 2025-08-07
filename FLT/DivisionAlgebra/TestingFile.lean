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
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.Ring
import FLT.HaarMeasure.HaarChar.AdeleRing
import FLT.Hacks.RightActionInstances
import FLT.NumberField.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.Group.Basic


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

local instance : T2Space (D ⊗[K] AdeleRing (𝓞 K) K) := IsModuleTopology.t2Space (AdeleRing (𝓞 K) K)

lemma incl₂_isClosedEmbedding : Topology.IsClosedEmbedding (incl₂ K D) := by
  apply Topology.IsClosedEmbedding.comp
  · exact { toIsEmbedding := Units.isEmbedding_embedProduct, isClosed_range :=
      embedProduct_closed D_𝔸}
  · refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
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

variable [FiniteDimensional K D]

-- Instance to help speed up instance synthesis
instance : NonUnitalNonAssocRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance : NonAssocSemiring (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

-- Instance to help speed up instance synthesis
local instance : NonUnitalNonAssocRing (D ⊗[K] NumberField.InfiniteAdeleRing K) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
local instance : NonAssocSemiring (D ⊗[K] NumberField.InfiniteAdeleRing K) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

variable [Algebra.IsCentral K D] [MeasurableSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

def iso₁ : D_𝔸ˣ ≃* Prod (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ (Dfx K D) :=
  (Units.mapEquiv (AlgEquiv.toMulEquiv (Algebra.TensorProduct.prodRight K K D _ _))).trans
  (MulEquiv.prodUnits)

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

    -- Kevin has an outline of the proof of the continuity of this.
    sorry

/-- The restriction of ringHaarChar_ker D_𝔸 to Dfx K D. -/
abbrev rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => (iso₁ K D) a.val |>.2

lemma rest₁_continuous : Continuous (rest₁ K D) := by
  refine Continuous.comp continuous_snd (Continuous.comp
    (iso₁_continuous K D) continuous_subtype_val)

local instance : MeasurableSpace (D ⊗[K] NumberField.InfiniteAdeleRing K) := by
  exact borel (D ⊗[K] NumberField.InfiniteAdeleRing K)

local instance : BorelSpace (D ⊗[K] NumberField.InfiniteAdeleRing K) := by
  exact { measurable_eq := rfl }

local instance : MeasurableSpace (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := by
  exact borel (D ⊗[K] FiniteAdeleRing (𝓞 K) K)

local instance : BorelSpace (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := by
  exact { measurable_eq := rfl }

abbrev D𝔸_iso : (D_𝔸 ≃ₗ[(NumberField.AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) →
    NumberField.AdeleRing (𝓞 K) K))) :=
  ((TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm).trans
    (TensorProduct.AlgebraTensorModule.finiteEquivPi (R := K) (M := D)
    (N := NumberField.AdeleRing (𝓞 K) K))

 local instance : IsModuleTopology (NumberField.AdeleRing (𝓞 K) K)
     ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)) := by
   -- its back!
   sorry

abbrev D𝔸_iso_top : D_𝔸 ≃L[(NumberField.AdeleRing (𝓞 K) K)]
    ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)) :=
  IsModuleTopology.continuousLinearEquiv (D𝔸_iso K D)

-- so can go D_𝔸 → 𝔸_K^d (d = dim_K D)
lemma help (x : D_𝔸ˣ) : IsUnit (D𝔸_iso_top K D x) := by
  refine isUnit_iff_exists_inv.mpr ?_
  obtain ⟨x, x', h1, h2⟩ := x
  use D𝔸_iso_top K D x'
  simp only [IsModuleTopology.continuousLinearEquiv_apply]



  sorry

abbrev D𝔸_iso_top' : D_𝔸ˣ → ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K))ˣ :=
  fun x => Units.mk (D𝔸_iso_top K D x)
  -- need to work out a nice way to write this


abbrev test2 : NumberField.AdeleRing (𝓞 K) K ≃L[ℚ]
    (Fin (Module.finrank ℚ K) → NumberField.AdeleRing (𝓞 ℚ) ℚ) := by
  exact (NumberField.AdeleRing.piEquiv ℚ K).symm

-- gives 𝔸_K → 𝔸_ℚ^m (m = dim_ℚ K)

abbrev test3 : ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)) ≃L[ℚ]
   Fin (Module.finrank K D) →  (Fin (Module.finrank ℚ K) → NumberField.AdeleRing (𝓞 ℚ) ℚ) := by
  -- should be immediate from test2
  sorry

-- need to work out the best way to write this
def hmm : Fin (Module.finrank K D) → (Fin (Module.finrank ℚ K) → NumberField.AdeleRing (𝓞 ℚ) ℚ)
    ≃ₗ[ℚ] Fin ((Module.finrank K D) * (Module.finrank ℚ K)) → NumberField.AdeleRing (𝓞 ℚ) ℚ := by
  -- this is true mathematically, just not sure if Lean knows this?
  sorry

abbrev test4 : ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)) ≃L[ℚ]
    Fin ((Module.finrank K D) * (Module.finrank ℚ K)) → NumberField.AdeleRing (𝓞 ℚ) ℚ := by
  --combination of test and hmm
  have := test3 K D

  sorry

-- so can go 𝔸_K^d → A_ℚ^{md}

abbrev test4' : ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K))ˣ →
    (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) → NumberField.AdeleRing (𝓞 ℚ) ℚ)ˣ := by
  -- will need to also think of a nice way to write this using test4 (which isnt done)
  sorry

local instance : MeasurableSpace (Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K) := by
  exact borel (Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)

local instance : BorelSpace (Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K) := by
  exact { measurable_eq := rfl }

lemma ringHaarChar_eq1 (a : (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)ˣ) : ringHaarChar a =
    ringHaarChar (R := ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)))
    (D𝔸_iso_top' K D a) := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv (X := D_𝔸)
    (Y := ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)))
    (D𝔸_iso_top K D).toContinuousAddEquiv
  -- need to prove this

  sorry

local instance : MeasurableSpace (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) →
    NumberField.AdeleRing (𝓞 ℚ) ℚ) := by
  exact borel (Fin (Module.finrank K D * Module.finrank ℚ K) → NumberField.AdeleRing (𝓞 ℚ) ℚ)

local instance : BorelSpace (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) →
    NumberField.AdeleRing (𝓞 ℚ) ℚ) := by
  exact { measurable_eq := rfl }

lemma ringHaarChar_eq2 (a : ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K))ˣ) :
    ringHaarChar (R := ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K))) a =
    ringHaarChar (R := (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) →
    NumberField.AdeleRing (𝓞 ℚ) ℚ)) (test4' K D a) := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (X := ((Fin (Module.finrank K D) → NumberField.AdeleRing (𝓞 K) K)))
    (Y := (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) → NumberField.AdeleRing (𝓞 ℚ) ℚ))
    (test4 K D).toContinuousAddEquiv
  -- will need to prove this
  sorry

lemma rest₁_surjective (t : ℕ) : (rest₁ K D) '' Set.univ = Set.univ := by
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
    simp_rw [ringHaarChar_eq1]
    suffices (∃ a, (ringHaarChar (R := (Fin (Module.finrank K D) →
        NumberField.AdeleRing (𝓞 K) K)) a = r ∧ ∃ y,
        a = (D𝔸_iso_top' K D ((iso₁ K D).symm (y, 1))))) by
      obtain ⟨a, ⟨ha, ⟨y, hay⟩⟩⟩ := this
      use y
      simp_rw [← hay]
      exact ha
    simp_rw [ringHaarChar_eq2]
    suffices (∃ b, ringHaarChar (R := (Fin ((Module.finrank K D) * (Module.finrank ℚ K)) →
        NumberField.AdeleRing (𝓞 ℚ) ℚ)) b = r ∧ ∃ a, test4' K D a = b ∧
        ∃ y,  a = (D𝔸_iso_top' K D ((iso₁ K D).symm (y, 1)))) by
      obtain ⟨b, hb, a, ha, y, hy⟩ := this
      use a
      simp_rw [ha]
      refine ⟨hb, by use y⟩
    /- there almost certainly is a nice way to be proving this...
       but it is now enough to choose b with :
        ⬝ 1 in the finite adele places
        ⬝ r^{1/(Fin (Module.finrank K D * Module.finrank ℚ K))} in the infinite places
       the first part of the proof will be to do with products
       the second parts will be simply chooising nice elements such that they match
       ... no idea how hard this second part will be, but it at least sounds reasonable
    -/

    sorry
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

lemma α_surjective  : Function.Surjective (α K D) := by
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
    rw [h]
    · exact trivial
    · exact USize.size -- not sure why this goal has appeared.
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
    Finite (Doset.Quotient (Set.range (incl₁ K D)) U) := by
  sorry

end FiniteAdeleRing
