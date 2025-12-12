/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
import FLT.HaarMeasure.HaarChar.AdeleRing
import FLT.Mathlib.GroupTheory.DoubleCoset
import FLT.Mathlib.Topology.HomToDiscrete
import FLT.HaarMeasure.HaarChar.RealComplex
/-

# Fujisaki's lemma

We prove a lemma which Voight (in his quaternion algebra book) attributes to Fujisaki:
if `D` is a finite-dimensional division algebra over a number field `K`
and if `U ⊆ (D ⊗[K] 𝔸_K^infty)ˣ` is a compact open subgroup then the double coset
space `Dˣ \ (D ⊗[K] 𝔸_K^infty)ˣ / U` is finite.

-/

suppress_compilation

open IsDedekindDomain MeasureTheory

open scoped TensorProduct

variable (K : Type*) [Field K] [NumberField K]
variable (D : Type*) [DivisionRing D] [Algebra K D]

namespace NumberField.AdeleRing.DivisionAlgebra

set_option quotPrecheck false in
/-- `D_𝔸` is notation for `D ⊗[K] 𝔸_K`. -/
notation "D_𝔸" => (D ⊗[K] AdeleRing (𝓞 K) K)

open scoped TensorProduct.RightActions

/-- The inclusion Dˣ → D_𝔸ˣ as a group homomorphism. -/
noncomputable abbrev incl : Dˣ →* D_𝔸ˣ :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

namespace Aux

/-- The inclusion of K^n into 𝔸^n. -/
abbrev incl_Kn_𝔸Kn : (Fin (Module.finrank K D) → K) →
    (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) :=
  fun x i ↦ algebraMap K (AdeleRing (𝓞 K) K) (x i)

theorem Kn_discrete : ∀ x : (Fin (Module.finrank K D) → K),
    ∃ U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K),
    IsOpen U ∧ (incl_Kn_𝔸Kn K D)⁻¹' U = {x} := by
  exact (DiscretePi (algebraMap K (AdeleRing (𝓞 K) K)) (Module.finrank K D))
    (NumberField.AdeleRing.discrete K)

variable [FiniteDimensional K D]

/-- The K-algebra equivalence of D and K^n. -/
abbrev D_iso : (D ≃ₗ[K] ((Fin (Module.finrank K D) → K))) := Module.Finite.equivPi K D

-- Mathlib#29315....
attribute [local instance 1100] IsTopologicalSemiring.toIsModuleTopology

-- ...makes this work
example : IsModuleTopology (AdeleRing (𝓞 K) K)
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) := inferInstance

/-- The 𝔸-algebra equivalence of D_𝔸 and 𝔸^d. -/
abbrev D𝔸_iso : (D_𝔸 ≃ₗ[(AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K))) :=
  ((TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm).trans
    (TensorProduct.AlgebraTensorModule.finiteEquivPi K D (AdeleRing (𝓞 K) K))

/-- The topological equivalence via D𝔸_iso. -/
abbrev D𝔸_iso_top : D_𝔸 ≃L[(AdeleRing (𝓞 K) K)]
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) :=
  IsModuleTopology.continuousLinearEquiv (D𝔸_iso K D)

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

theorem D_discrete : ∀ x : D, ∃ U : Set D_𝔸,
    IsOpen U ∧ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U = {x} := by
  apply Discrete_of_HomeoDiscrete (Y' := ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)))
    (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) (D𝔸_iso_top K D)
  apply Discrete_of_HomDiscrete (X' := Fin (Module.finrank K D) → K)
    ((D𝔸_iso_top K D) ∘ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) (D_iso K D)
  simpa [D_discrete_extracted] using Kn_discrete K D

variable [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)]

lemma existsE : ∃ E : Set (D_𝔸), IsCompact E ∧
    ∀ φ : D_𝔸 ≃ₜ+ D_𝔸, addEquivAddHaarChar φ = 1 → ∃ e₁ ∈ E, ∃ e₂ ∈ E,
    e₁ ≠ e₂ ∧ φ e₁ - φ e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  --have := MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient
  sorry -- **TODO** prove that if A is a locally compact ab group and Gamma is a cocompact
  -- subgroup then there's some positive real M such that if U ⊆ A and μ(U)>M then
  -- U -> A/Gamma isn't injective.

/-- An auxiliary set E used in the proof of Fukisaki's lemma. -/
def E : Set D_𝔸 := (existsE K D).choose

lemma E_compact : IsCompact (E K D) := (existsE K D).choose_spec.1

lemma E_noninjective_left {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    x * e₁ - x * e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  (existsE K D).choose_spec.2 (ContinuousAddEquiv.mulLeft x) h

lemma E_noninjective_right [Algebra.IsCentral K D] {x : D_𝔸ˣ} (h : x ∈ ringHaarChar_ker D_𝔸) :
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    e₁ * x⁻¹ - e₂ * x⁻¹  ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  let φ : D_𝔸 ≃ₜ+ D_𝔸 := ContinuousAddEquiv.mulRight x⁻¹
  have hφ : addEquivAddHaarChar φ = 1 := by
    rwa [ ← inv_mem_iff, mem_ringHaarChar_ker, ringHaarChar_apply,
      isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul K D x⁻¹] at h
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

lemma X_meets_kernel' [Algebra.IsCentral K D] {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
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

/-- The additive subgroup with carrier defined by Algebra.TensorProduct.includeLeft. -/
local instance includeLeft_subgroup : AddSubgroup D_𝔸 :=
  AddMonoidHom.range (G := D) (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)

local instance : DiscreteTopology (includeLeft_subgroup K D).carrier := by
  rw [includeLeft_subgroup]
  apply discreteTopology_iff_isOpen_singleton.mpr
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
    ⟨(inter_Discrete (includeLeft_subgroup K D).carrier (Y K D))⟩
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

lemma antidiag_mem_C [Algebra.IsCentral K D] {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ b ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ),
    ∃ ν ∈ ringHaarChar_ker D_𝔸,
    β = b * ν ∧ ((ν : D_𝔸), ((ν⁻¹ : D_𝔸ˣ) : D_𝔸)) ∈ C K D := by
  obtain ⟨x1, hx1, b1, ⟨b1, rfl⟩, eq1⟩ := X_meets_kernel K D hβ
  obtain ⟨x2, hx2, b2, ⟨b2, rfl⟩, eq2⟩ := X_meets_kernel' K D hβ
  obtain ⟨x1, rfl⟩ : IsUnit x1 := ⟨↑β⁻¹ * incl K D b1,
    ((Units.eq_inv_mul_iff_mul_eq β).mpr eq1).symm⟩
  obtain ⟨x2, rfl⟩ : IsUnit x2 := ⟨incl K D b2 * β, ((Units.mul_inv_eq_iff_eq_mul β).mp eq2).symm⟩
  have h : x2 * x1 ∈ T K D := ⟨by simpa only [Y] using Set.mul_mem_mul hx2 hx1,
    b2 * b1, by norm_cast at eq1 eq2; rw [map_mul, ← eq2, ← eq1]; group⟩
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

variable [FiniteDimensional K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
    [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)]

/-- The inclusion of `ringHaarChar_ker D_𝔸` into the product space `D_𝔸 × D_𝔸ᵐᵒᵖ`. -/
def incl₂ : ringHaarChar_ker D_𝔸 → Prod D_𝔸 D_𝔸ᵐᵒᵖ :=
  fun u => Units.embedProduct D_𝔸 (Subgroup.subtype (ringHaarChar_ker D_𝔸) u)

/-- An auxiliary set used in the proof of compact_quotient'. -/
def M : Set (ringHaarChar_ker D_𝔸) := Set.preimage (incl₂ K D)
  (Set.image (fun p => (p.1, MulOpposite.op p.2)) (Aux.C K D))

/-- The map from `ringHaarChar_ker D_𝔸` to the quotient `Dˣ \ ringHaarChar_ker D_𝔸`. -/
abbrev toQuot (a : ringHaarChar_ker D_𝔸) : (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  (Quotient.mk (QuotientGroup.rightRel ((MonoidHom.range (incl K D)).comap
  (ringHaarChar_ker D_𝔸).subtype)) a)

lemma toQuot_cont : Continuous (toQuot K D) where
  isOpen_preimage := fun _ a ↦ a

lemma toQuot_surjective [Algebra.IsCentral K D] : (toQuot K D) '' (M K D) = Set.univ := by
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

lemma compact_quotient [Algebra.IsCentral K D] :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype))) :=
  isCompact_univ_iff.mp (by simpa only [toQuot_surjective, Set.image_univ] using
    (((IsCompact.image (M_compact K D) (toQuot_cont K D)))))

end NumberField.AdeleRing.DivisionAlgebra

section FiniteAdeleRing

open scoped NumberField

variable [Algebra.IsCentral K D]

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

/-- Df is notation for D ⊗ 𝔸_K^∞ -/
abbrev Df := D ⊗[K] (FiniteAdeleRing (𝓞 K) K)

/-- Dinfx is notation for (D ⊗ 𝔸_K^∞)ˣ -/
abbrev Dinfx := (D ⊗[K] (NumberField.InfiniteAdeleRing K))ˣ

/-- Dinf is notation for D ⊗ 𝔸_K^∞ -/
abbrev Dinf := D ⊗[K] (NumberField.InfiniteAdeleRing K)

-- Instance to help speed up instance synthesis
instance : NonUnitalNonAssocRing (Df K D) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance : NonAssocSemiring (Dinf K D) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

-- Instance to help speed up instance synthesis
instance : NonUnitalNonAssocRing (Dinf K D) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance : NonAssocSemiring (Df K D) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

open NumberField

open scoped TensorProduct.RightActions

variable [FiniteDimensional K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
    [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)]

/-- Notation for (Algebra.TensorProduct.prodRight K K D (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K)). -/
abbrev D𝔸_prodRight : D_𝔸 ≃ₐ[K] Dinf K D × Df K D :=
  (Algebra.TensorProduct.prodRight K K D (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

/-- The (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)-module structure on (Dinf K D × Df K D). -/
local instance : Module (AdeleRing (𝓞 K) K) (Dinf K D × Df K D) where
  smul rs mn := (rs.1 • mn.1, rs.2 • mn.2)
  one_smul mn := by cases mn; ext; exacts [one_smul _ _, one_smul _ _]
  mul_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact mul_smul _ _ _
  smul_zero rs := by cases rs; ext <;> exact smul_zero _
  smul_add rs mn mn' := by
    cases rs; cases mn; cases mn'
    ext <;>
    exact smul_add _ _ _
  add_smul rs rs' mn := by
    cases rs; cases rs'; cases mn
    ext <;>
    exact add_smul _ _ _
  zero_smul mn := by cases mn; ext <;> exact zero_smul _ _

local instance : IsModuleTopology (AdeleRing (𝓞 K) K) (Dinf K D × Df K D) := by
  exact IsModuleTopology.instProd'

/-- The 𝔸_K linear map coming from D𝔸_prodRight. -/
abbrev D𝔸_prodRight' : D_𝔸 →ₗ[AdeleRing (𝓞 K) K] (Dinf K D × Df K D) where
  toFun x := D𝔸_prodRight K D x
  map_add' a b := by
    exact RingHom.map_add (D𝔸_prodRight K D).toRingHom a b
  map_smul' m x := by
    simp only [RingHom.id_apply]
    obtain ⟨s, hx⟩ := TensorProduct.exists_finset x
    letI := AddEquivClass.instAddMonoidHomClass (D_𝔸 ≃ₐ[K] Dinf K D × Df K D)
    simp_rw [hx, Finset.smul_sum, map_sum, TensorProduct.RightActions.smul_def,
      TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul,
      Finset.smul_sum]
    rfl

omit [Algebra.IsCentral K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
lemma D𝔸_prodRight_cont : Continuous (D𝔸_prodRight K D) := by
  have I : NonUnitalNonAssocSemiring (Dinf K D) := by
    exact (instNonUnitalNonAssocRingDinf K D).toNonUnitalNonAssocSemiring
  have J : NonUnitalNonAssocSemiring (Df K D) := by
    exact (instNonUnitalNonAssocRingDf K D).toNonUnitalNonAssocSemiring
  exact IsModuleTopology.continuous_of_linearMap (D𝔸_prodRight' K D)

omit [Algebra.IsCentral K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
 lemma D𝔸_prodRight.symm_cont : Continuous (D𝔸_prodRight K D).symm := by
  apply (Equiv.isOpenMap_symm_iff _).mp
  have : NonUnitalNonAssocSemiring D_𝔸 := Algebra.TensorProduct.instNonUnitalNonAssocSemiring
  simp_rw [AdeleRing] at this
  convert IsModuleTopology.isOpenMap_of_surjective (φ := D𝔸_prodRight' K D)
  exact Iff.symm (imp_iff_right (AlgEquiv.surjective _))

/-- The continuous isomorphism coming from D𝔸_prod viewed on additive groups. -/
abbrev D𝔸_prodRight'' : D_𝔸 ≃ₜ+ Dinf K D × Df K D where
  __ := D𝔸_prodRight K D
  continuous_toFun := D𝔸_prodRight_cont K D
  continuous_invFun := D𝔸_prodRight.symm_cont K D

/-- The equivalence of the units of D_𝔸 and the Prod of units of (D ⊗ 𝔸_K^f) and (D ⊗ 𝔸_K^∞). -/
abbrev D𝔸_prodRight_units : D_𝔸ˣ ≃* Prod (Dinfx K D) (Dfx K D) :=
  (Units.mapEquiv (D𝔸_prodRight K D)).trans (MulEquiv.prodUnits)

omit [Algebra.IsCentral K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
lemma D𝔸_prodRight_units_cont : Continuous (D𝔸_prodRight_units K D) := by
  rw [ MulEquiv.coe_trans]
  apply Continuous.comp ?_ ?_
  · apply Continuous.prodMk
    · apply Continuous.units_map
      exact continuous_fst
    · apply Continuous.units_map
      exact continuous_snd
  · apply Continuous.units_map
    exact D𝔸_prodRight_cont K D

/-- The restriction of ringHaarChar_ker D_𝔸 to (D ⊗ 𝔸_K^∞)ˣ via D𝔸_iso_prod_units. -/
abbrev rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => (D𝔸_prodRight_units K D) a.val |>.2

omit [Algebra.IsCentral K D] in
lemma rest₁_continuous : Continuous (rest₁ K D) := Continuous.comp continuous_snd (Continuous.comp
  (D𝔸_prodRight_units_cont K D) continuous_subtype_val)

local instance : Algebra ℝ (InfiniteAdeleRing K) := by
  exact RingHom.toAlgebra (RingHom.comp
    (RingEquiv.toRingHom (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm)
    (RingHom.smulOneHom (R := ℝ) (S := (mixedEmbedding.mixedSpace K))))

noncomputable instance : Algebra ℝ (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K|>.symm.toRingHom.comp (algebraMap ℝ _)).toAlgebra

-- can/should I do this?
local instance bar : InfiniteAdeleRing K ≃ₗ[ℝ] (mixedEmbedding.mixedSpace K) where
  __ := NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
  map_smul' m x := by
    simp
    constructor
    ·
      sorry
    ·
      sorry

local instance : Module.Finite ℝ (InfiniteAdeleRing K) := by
  have : Module.Finite ℝ (mixedEmbedding.mixedSpace K) := by
    exact Module.Finite.prod
  exact Module.Finite.equiv (bar K).symm

open scoped TensorProduct.RightActions
local instance : Algebra ℝ (Dinf K D) := by
  have h2 : Algebra ℝ (InfiniteAdeleRing K ⊗[K] D) := by
    exact Algebra.TensorProduct.leftAlgebra (R := K) (S := ℝ) (A := InfiniteAdeleRing K) (B := D)
  -- need something saying I can switch the tensor
  -- there is nothing in TensorProduct.RightActions
  sorry

local instance : Module.Finite ℝ (InfiniteAdeleRing K ⊗[K] D) := by

  sorry

local instance : Module.Finite ℝ (Dinf K D) := by

  -- depends on Algebra ℝ (Dinf K D)
  -- (InfiniteAdeleRing K) is a fininted ℝ module...
  sorry

local instance : Module.Free ℝ (Dinf K D) := by
  exact Module.free_of_finite_type_torsion_free'

local instance : IsModuleTopology ℝ (Dinf K D) := by
  /- By Algebra ℝ (InfiniteAdeleRing K); (InfiniteAdeleRing K) has the ℝ-module topology.
    Now since (Dinf K D) has the (InfiniteAdeleRing K)-module topolology it also has the
    ℝ-module topology.
  -/
  have : IsModuleTopology ℝ (InfiniteAdeleRing K) := by

    sorry
  have : IsModuleTopology (InfiniteAdeleRing K) (Dfx K D) := by
    -- really...
    sorry
  sorry

local instance : MeasurableSpace (Dinf K D) :=
  borel (Dinf K D)

local instance : BorelSpace (Dinf K D) := {measurable_eq := rfl }

local instance : MeasurableSpace (Df K D) := borel (Df K D)

local instance : BorelSpace (Df K D) := { measurable_eq := rfl }

local instance : MeasurableSpace (Dinf K D × Df K D) := Prod.instMeasurableSpace

local instance : SecondCountableTopology (InfiniteAdeleRing K) := by
  infer_instance

local instance : SecondCountableTopologyEither (D ⊗[K] InfiniteAdeleRing K)
    (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := by
  refine {out := ?_}
  left
  apply?
  sorry

local instance : Nontrivial (Dinf K D) := by
  -- obvious? Not sure why its not being inferred
  sorry

omit [Algebra.IsCentral K D] in
lemma ringHaarChar_D𝔸 (a : Dinfx K D) (b : Dfx K D) :
    ringHaarChar ((D𝔸_prodRight_units K D).symm (a, b)) =
    ringHaarChar (MulEquiv.prodUnits.symm (a, b)) := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (D𝔸_prodRight'' K D)
  intro x
  dsimp only [MulEquiv.symm_trans_apply, Units.mapEquiv_symm, MulEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, ContinuousAddEquiv.mulLeft_apply,
    Units.coe_mapEquiv, MulEquiv.coe_mk, EquivLike.coe_coe, ContinuousAddEquiv.coe_mk,
    Equiv.toFun_as_coe, Equiv.invFun_as_coe, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [MulEquivClass.map_mul]
  simp only [MulEquivClass.apply_coe_symm_apply]

omit [Algebra.IsCentral K D] in
lemma rest₁_surj_extracted (r : ℝ) (h : r > 0) :
    ∃ y, ringHaarChar ((D𝔸_prodRight_units K D).symm (y,1)) = r := by
  have a : IsUnit (r ^ (1 / Module.finrank ℝ (Dinf K D) : ℝ)) := by
    simp only [one_div, isUnit_iff_ne_zero, ne_eq]
    refine (Real.rpow_ne_zero (by positivity) ?_).mpr (by positivity)
    simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
    exact (Nat.ne_zero_iff_zero_lt.mpr Module.finrank_pos)
  have := ringHaarChar_ModuleFinite_unit (K := ℝ) (R := Dinf K D) (a.unit)
  use ((Units.map (algebraMap ℝ (Dinf K D))) a.unit)
  rw [ringHaarChar_D𝔸, ringHaarChar_prod, map_one, mul_one]
  simp_all only [gt_iff_lt, RingHom.toMonoidHom_eq_coe, NNReal.coe_pow]
  have t : (ringHaarChar a.unit) = r ^ ((1 / Module.finrank ℝ (Dinf K D) : ℝ)) := by
    simp_rw [MeasureTheory.ringHaarChar_real, IsUnit.unit_spec, coe_nnnorm, Real.norm_eq_abs,
      one_div, abs_eq_self]
    positivity
  simp_rw [t, one_div]
  exact Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_zero_iff_zero_lt.mpr Module.finrank_pos)

omit [Algebra.IsCentral K D] in
lemma rest₁_surjective : (rest₁ K D) '' Set.univ = Set.univ := by
  simp only [Set.image_univ]
  refine Eq.symm (Set.ext ?_)
  intro x
  simp only [Set.mem_univ, Set.mem_range, Subtype.exists, true_iff]
  obtain ⟨r, hx⟩ : ∃ r, ringHaarChar ((D𝔸_prodRight_units K D).symm (1,x)) = r := exists_eq'
  have hr : r > 0 := by
    rw [←hx]
    have (a : (D_𝔸)ˣ): 0 < ringHaarChar a := by
      exact addEquivAddHaarChar_pos _
    exact this ((D𝔸_prodRight_units K D).symm (1, x))
  obtain ⟨y, hy⟩ : ∃ y, ringHaarChar ((D𝔸_prodRight_units K D).symm (y,1)) = r := by
    obtain ⟨y, hy⟩ := rest₁_surj_extracted K D r hr
    use y
    aesop
  use (D𝔸_prodRight_units K D).symm (y⁻¹, x)
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
    have : ringHaarChar ((D𝔸_prodRight_units K D).symm (y⁻¹, 1)) = r⁻¹ := by
      rw [← hy]
      have : ringHaarChar ((D𝔸_prodRight_units K D).symm (y⁻¹, 1)) *
          (ringHaarChar ((D𝔸_prodRight_units K D).symm (y, 1))) = 1 := by
        simp_rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
        have : (D𝔸_prodRight_units K D).symm (1, 1) = 1 :=
          (MulEquiv.map_eq_one_iff (D𝔸_prodRight_units K D).symm).mpr rfl
        simp only [this, map_one]
      exact Eq.symm (inv_eq_of_mul_eq_one_left this)
    simp_rw [this, hx]
    simpa using (inv_mul_cancel₀ hr.ne')

omit [Algebra.IsCentral K D] in
lemma incl_D𝔸quot_equivariant : ∀ (a b : ↥(ringHaarChar_ker D_𝔸)),
    (QuotientGroup.rightRel (Subgroup.comap (ringHaarChar_ker D_𝔸).subtype
    (AdeleRing.DivisionAlgebra.incl K D).range)) a b →
    (Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a) =
     Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D b)) := by
  refine fun a b hab ↦ Quotient.eq''.mpr ?_
  obtain ⟨⟨t, t', ht⟩, rfl⟩ := hab
  simp_rw [QuotientGroup.rightRel, MulAction.orbitRel, MulAction.orbit, Set.mem_range,
    Subtype.exists, Subgroup.mk_smul, smul_eq_mul, MonoidHom.mem_range, exists_prop,
    exists_exists_eq_and]
  use t'
  have : incl₁ K D t' = ((D𝔸_prodRight_units K D) (AdeleRing.DivisionAlgebra.incl K D t')).2 := by
    rfl
  simp_rw [this, ht, ← Prod.snd_mul, Subgroup.subtype_apply, Subgroup.comap_subtype, ← map_mul]
  rfl

/-- The obvious map Dˣ \ D_𝔸^(1) to Dˣ \ (Dfx K D). -/
abbrev incl_D𝔸quot : Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (NumberField.AdeleRing.DivisionAlgebra.incl K D)).comap
    (ringHaarChar_ker D_𝔸).subtype)) →
    Quotient (QuotientGroup.rightRel (incl₁ K D).range) :=
  Quot.lift
    (fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a))
    (incl_D𝔸quot_equivariant K D)

omit [Algebra.IsCentral K D] in
lemma incl_D𝔸quot_continuous : Continuous (incl_D𝔸quot K D) := by
  refine Continuous.quotient_lift ?_ (incl_D𝔸quot_equivariant K D)
  exact Continuous.comp' ({isOpen_preimage := fun s a ↦ a}) (rest₁_continuous K D)

omit [Algebra.IsCentral K D] in
lemma incl_D𝔸quot_surjective : Function.Surjective (incl_D𝔸quot K D) := by
  refine (Quot.surjective_lift (f := fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range)
    (rest₁ K D a)) (incl_D𝔸quot_equivariant K D)).mpr ?_
  refine Set.range_eq_univ.mp ?_
  ext x
  simp only [Set.mem_range, Subtype.exists, Set.mem_univ, iff_true]
  have h := rest₁_surjective K D
  obtain ⟨a, ha⟩ : ∃ a : (ringHaarChar_ker D_𝔸),
      (rest₁ K D) a = x.out := by
    refine Set.mem_range.mp ?_
    aesop
  use a
  simp [ha]

open scoped TensorProduct.RightActions in
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) := by
  have := isCompact_univ_iff.mpr (NumberField.AdeleRing.DivisionAlgebra.compact_quotient K D)
  apply isCompact_univ_iff.mp
  have := IsCompact.image (this) (incl_D𝔸quot_continuous K D)
  rw [Set.image_univ_of_surjective (incl_D𝔸quot_surjective K D)] at this
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
