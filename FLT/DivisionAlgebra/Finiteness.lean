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

abbrev D_iso : (D ≃ₗ[K] ((Fin (Module.finrank K D) → K))) := by
  exact Module.Finite.equivPi K D

def D𝔸_iso : (D_𝔸 ≃ₗ[(AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K))) := by
  suffices h : ((Fin (Module.finrank K D) → K) ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[(AdeleRing (𝓞 K) K)]
      (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K) by
    have H1 := TensorProduct.AlgebraTensorModule.finiteEquivPi (R := K) (M := D)
      (N := AdeleRing (𝓞 K) K)
    have H2 : D ⊗[K] AdeleRing (𝓞 K) K ≃ₗ[AdeleRing (𝓞 K) K] (AdeleRing (𝓞 K) K) ⊗[K] D :=
      (TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm
    exact H2.trans H1
  have h1 := (TensorProduct.piScalarRight K (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K)
    (Fin (Module.finrank K D)))
  have h2 : (Fin (Module.finrank K D) → K) ⊗[K] AdeleRing (𝓞 K) K ≃ₗ[(AdeleRing (𝓞 K) K)]
      AdeleRing (𝓞 K) K ⊗[K] (Fin (Module.finrank K D) → K) := by
    exact (TensorProduct.RightActions.Module.TensorProduct.comm _ _ _).symm
  exact h2.trans h1

local instance : IsModuleTopology (AdeleRing (𝓞 K) K)
    ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) := by
  --have := IsModuleTopology.instPi (R := AdeleRing (𝓞 K) K) (ι := Fin (Module.finrank K D))
  --  (A := Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)

    -- no idea how to get this to work
  sorry

def D𝔸_iso_top : D_𝔸 ≃L[(AdeleRing (𝓞 K) K)] ((Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)) := by
  exact (IsModuleTopology.continuousLinearEquiv (D𝔸_iso K D).symm).symm

abbrev incl_Kn_𝔸Kn : (Fin (Module.finrank K D) → K) → (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K)
    := fun x i ↦ algebraMap K (AdeleRing (𝓞 K) K) (x i)

omit [FiniteDimensional K D] [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
theorem Kn_discrete : ∀ x : (Fin (Module.finrank K D) → K),
    ∃ U : Set (Fin (Module.finrank K D) → AdeleRing (𝓞 K) K),
    IsOpen U ∧ (incl_Kn_𝔸Kn K D)⁻¹' U = {x} := by
  intro x
  have h (i : Fin (Module.finrank K D)) := (NumberField.AdeleRing.discrete K) (x i)
  use Set.pi (Set.univ) (fun (i : Fin (Module.finrank K D)) => Classical.choose (h i))
  constructor
  · have (i : Fin (Module.finrank K D)) := (Classical.choose_spec (h i)).1
    refine isOpen_set_pi ?_ fun a a_1 ↦ this a
    exact Set.finite_univ
  · unfold incl_Kn_𝔸Kn
    have H (i : Fin (Module.finrank K D)) := (Classical.choose_spec (h i)).2
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_singleton_iff]
    constructor
    · intro hy
      ext t
      have hy := hy t
      have H := H t
      rw [← Set.mem_preimage] at hy
      aesop
    · intro eq i
      refine Set.mem_preimage.mp ?_
      aesop

-- this can definitely be golfed (and extracted for smaller lemmas)
omit [MeasurableSpace (D ⊗[K] AdeleRing (𝓞 K) K)] [BorelSpace (D ⊗[K] AdeleRing (𝓞 K) K)] in
theorem D_discrete : ∀ x : D, ∃ U : Set D_𝔸,
    IsOpen U ∧ (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' U = {x} := by
  intro t
  obtain ⟨U, Uopen, Ueq⟩ := Kn_discrete K D (D_iso K D t)
  use Set.image ((D𝔸_iso_top K D).symm) U
  constructor
  · exact (ContinuousLinearEquiv.isOpenMap (D𝔸_iso_top K D).symm) U Uopen
  · unfold incl_Kn_𝔸Kn at Ueq
    ext y
    simp only [Set.mem_singleton_iff]
    have h1 : (D_iso K D).symm '' ((fun (x : Fin (Module.finrank K D) → K)
        (i : Fin (Module.finrank K D)) ↦ (algebraMap K (AdeleRing (𝓞 K) K)) (x i)) ⁻¹' U)
        = {t} := by
      simp_all only [Set.image_singleton, LinearEquiv.symm_apply_apply]
    have h2 : (D_iso K D).symm '' ((fun (x : Fin (Module.finrank K D) → K)
        (i : Fin (Module.finrank K D)) ↦ (algebraMap K (AdeleRing (𝓞 K) K)) (x i)) ⁻¹' U) =
        (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) ⁻¹' (⇑(D𝔸_iso_top K D).symm '' U) := by
      ext x
      constructor
      · intro hx
        obtain ⟨a, ⟨ha1, ha2⟩⟩ := hx
        use (fun x i ↦ (algebraMap K (AdeleRing (𝓞 K) K)) (x i)) a
        simp only [Algebra.TensorProduct.includeLeft_apply]
        constructor
        · exact ha1
        · refine (ContinuousLinearEquiv.symm_apply_eq (D𝔸_iso_top K D)).mpr ?_
          subst ha2
          simp_all only [Set.image_singleton, LinearEquiv.symm_apply_apply, Set.mem_singleton_iff]
          subst ha1
          unfold D𝔸_iso_top D𝔸_iso D_iso
          simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm,
            IsModuleTopology.continuousLinearEquiv_symm_apply, LinearEquiv.trans_apply,
            TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul,
            TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
            TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
          ext i
          exact Algebra.algebraMap_eq_smul_one ((Module.Finite.equivPi K D) t i)
      · intro hx
        obtain ⟨a, ⟨ha1, ha2⟩⟩ := hx
        simp only [Set.mem_image, Set.mem_preimage]
        use (D_iso K D) x
        simp only [LinearEquiv.symm_apply_apply, and_true]
        have : a = (D𝔸_iso_top K D) ((Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) x) := by
          exact (ContinuousLinearEquiv.symm_apply_eq (D𝔸_iso_top K D)).mp ha2
        rw [this] at ha1
        unfold D_iso
        unfold D𝔸_iso_top D𝔸_iso at ha1
        simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm,
          Algebra.TensorProduct.includeLeft_apply,
          IsModuleTopology.continuousLinearEquiv_symm_apply, LinearEquiv.trans_apply,
          TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul,
          TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
          TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul] at ha1
        simp_rw [Algebra.algebraMap_eq_smul_one]
        exact ha1
    constructor
    · intro hy
      rw [← h2, h1] at hy
      exact hy
    · intro eq
      simp_rw [eq, ← h2, h1]
      rfl

abbrev includeLeft_addsub : AddSubgroup D_𝔸 :=
  { carrier := Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸),
    add_mem' a b := by
      obtain ⟨a, rfl⟩ := a
      obtain ⟨b, rfl⟩ := b
      use a + b
      exact map_add Algebra.TensorProduct.includeLeft a b,
    zero_mem' := by
      use 0
      exact map_zero Algebra.TensorProduct.includeLeft,
    neg_mem' a := by
      obtain ⟨a, rfl⟩ := a
      exact ⟨-a, rfl⟩
  }

local instance : DiscreteTopology (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸))
    := by
  apply (singletons_open_iff_discrete).mp
  intro a
  obtain ⟨a, a', ha⟩ := a
  obtain ⟨U, hUopen, hUeq⟩ := (D_discrete K D) a'
  refine isOpen_mk.mpr ⟨U, hUopen, Set.image_val_inj.mp ?_⟩
  simp only [Subtype.image_preimage_coe, Set.image_singleton]
  ext d
  constructor
  · intro hd
    obtain ⟨hd1, hd2⟩ := hd
    apply Set.mem_range.mp at hd1
    obtain ⟨c, hc⟩ := hd1
    refine Set.mem_singleton_of_eq ?_
    rw [← hc] at hd2
    apply Set.mem_preimage.mpr at hd2
    simp only [hUeq, Set.mem_singleton_iff] at hd2
    simp_rw [← hc, hd2, ha]
  · intro hd
    constructor
    · refine Set.mem_range.mpr ⟨a', ?_⟩
      rw [hd]
      exact ha
    · rw [hd, ← ha]
      exact Set.mem_preimage.mp (by simp [hUeq])

local instance : T2Space (D ⊗[K] AdeleRing (𝓞 K) K) := by

  sorry

local instance : AddSubgroup D_𝔸 where
  carrier := Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)
  add_mem' := by
    intro a b ha hb
    obtain ⟨a1, rfl⟩ := ha
    obtain ⟨b1, rfl⟩ := hb
    use a1 + b1
    exact map_add Algebra.TensorProduct.includeLeft a1 b1
  zero_mem' := by
    use 0
    exact map_zero Algebra.TensorProduct.includeLeft
  neg_mem' := by
    intro a ha
    obtain ⟨a1, ha1⟩ := ha
    use -a1
    rw [← ha1]
    rfl

lemma T_finite : Set.Finite (T K D) := by
  have h : Set.Finite ((Y K D) ∩ (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)))
      := by
    apply IsCompact.finite
    · refine IsCompact.inter_right (Y_compact K D) ?_
      have : DiscreteTopology (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
        infer_instance
      have := AddSubgroup.isClosed_of_discrete (G := D_𝔸) (H := includeLeft_addsub K D)
      infer_instance
    · refine singletons_open_iff_discrete.mp ?_
      intro ⟨a, ha1, ⟨a', ha'⟩⟩
      refine isOpen_mk.mpr ?_
      obtain ⟨U, Uopen, Ueq⟩ := D_discrete K D a'
      use U
      refine ⟨Uopen, ?_⟩
      refine Set.image_val_inj.mp ?_
      simp only [Subtype.image_preimage_coe, Set.image_singleton]
      have : (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) ∩ U = {a} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ?_
        constructor
        · rw [← ha']
          simp only [Algebra.TensorProduct.includeLeft_apply, Set.mem_inter_iff, Set.mem_range,
            exists_apply_eq_apply, true_and]
          have : (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) a' ∈ U := by
            refine Set.mem_preimage.mp ?_
            rw [Ueq]
            rfl
          exact this
        · simp only [Set.mem_inter_iff, Set.mem_range, Algebra.TensorProduct.includeLeft_apply,
            and_imp, forall_exists_index, forall_apply_eq_imp_iff]
          intro c hc
          have (b : D) : (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) b ∈ U → b = a' := by
            intro hb
            contrapose Ueq
            exact ne_of_mem_of_not_mem' hb Ueq
          have := this c hc
          simp_all only [Algebra.TensorProduct.includeLeft_apply]
      rw [Set.inter_assoc, this]
      simpa using ha1
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
    CompactSpace (Dfx K D ⧸ (incl₁ K D).range) := by
  sorry

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
