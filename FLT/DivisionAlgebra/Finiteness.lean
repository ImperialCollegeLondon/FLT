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

instance : Algebra (AdeleRing (𝓞 K) K) D_𝔸 :=
  Algebra.TensorProduct.rightAlgebra

-- Ruben did this somewhere TODO
instance : Module.Finite (AdeleRing (𝓞 K) K) D_𝔸 := sorry

/-- The module topology on `D_𝔸`. -/
local instance : TopologicalSpace D_𝔸 :=
  moduleTopology (AdeleRing (𝓞 K) K) _

local instance : IsModuleTopology (AdeleRing (𝓞 K) K) D_𝔸 := ⟨rfl⟩

local instance : IsTopologicalRing D_𝔸 :=
  IsModuleTopology.Module.topologicalRing (AdeleRing (𝓞 K) K) _

local instance : LocallyCompactSpace D_𝔸 := sorry -- we have this (unfinished) elsewhere TODO

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

instance : Algebra (FiniteAdeleRing (𝓞 K) K) (D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  Algebra.TensorProduct.rightAlgebra

-- this is in FLT somewhere
instance : Module.Finite (FiniteAdeleRing (𝓞 K) K) (D ⊗[K] FiniteAdeleRing (𝓞 K) K) := sorry

/-- The 𝔸_K^∞-module topology on D ⊗ 𝔸_K^∞-/
local instance : TopologicalSpace (D ⊗[K] FiniteAdeleRing (𝓞 K) K) :=
  moduleTopology (FiniteAdeleRing (𝓞 K) K) _

local instance : IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  ⟨rfl⟩

variable [FiniteDimensional K D]

-- Instance to help speed up instance synthesis
instance : NonUnitalNonAssocRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  let r := Algebra.TensorProduct.instRing.toNonUnitalRing
  r.toNonUnitalNonAssocRing

-- Instance to help speed up instance synthesis
instance : NonAssocSemiring (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  Algebra.TensorProduct.instRing.toNonAssocSemiring

instance : IsTopologicalRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  IsModuleTopology.Module.topologicalRing (FiniteAdeleRing (𝓞 K) K) _

variable [Algebra.IsCentral K D]

/-- Dfx is notation for (D ⊗ 𝔸_K^∞)ˣ. -/
abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

/-- The inclusion Dˣ → (D ⊗ 𝔸_K^∞)ˣ as a group homomorphism. -/
noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

-- The following are local instance from earlier -- need to work out where to move them
-- copying them here for now

local instance : TopologicalSpace D_𝔸 :=
  moduleTopology (NumberField.AdeleRing (𝓞 K) K) _

local instance : IsModuleTopology (NumberField.AdeleRing (𝓞 K) K) D_𝔸 := ⟨rfl⟩

local instance : IsTopologicalRing D_𝔸 :=
  IsModuleTopology.Module.topologicalRing (NumberField.AdeleRing (𝓞 K) K) _

local instance : LocallyCompactSpace D_𝔸 := sorry -- we have this (unfinished) elsewhere TODO

variable [MeasurableSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]

-- end of copying of instances

def iso₁ : (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)ˣ ≃* -- I need this map to be multiplicative later
    Prod (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ (Dfx K D) := by
  simp_rw [NumberField.AdeleRing, Dfx]
  have start := TensorProduct.prodRight K D D (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K)
  have interim := Units.mapEquiv (M := D ⊗[K] (NumberField.InfiniteAdeleRing K × FiniteAdeleRing
    (𝓞 K) K)) (N := D ⊗[K] NumberField.InfiniteAdeleRing K × D ⊗[K] FiniteAdeleRing (𝓞 K) K)
    start.toMulEquiv
    -- need to get a mul equiv
  have final := MulEquiv.prodUnits (M := D ⊗[K] NumberField.InfiniteAdeleRing K)
    (N := D ⊗[K] FiniteAdeleRing (𝓞 K) K)
  exact interim.trans final

abbrev rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => (iso₁ K D) a.val |>.2

local instance : TopologicalSpace (D ⊗[K] NumberField.InfiniteAdeleRing K) := by
  -- not sure how to put the wanted topology on this
  sorry

local instance : TopologicalSpace (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ := by
  exact Units.instTopologicalSpaceUnits

local instance : TopologicalSpace (Prod (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ (Dfx K D)) := by
  exact instTopologicalSpaceProd

lemma α_equivariant : ∀ (a b : ↥(ringHaarChar_ker (D ⊗[K] NumberField.AdeleRing (𝓞 K) K))),
    (QuotientGroup.rightRel (Subgroup.comap (ringHaarChar_ker
    (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)).subtype
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

    -- this is certainly true by definition
    sorry
  simp_rw [this, ht, ← Prod.snd_mul, Subgroup.subtype_apply, Subgroup.comap_subtype, ← map_mul]
  rfl

def α : Quotient (QuotientGroup.rightRel
    ((MonoidHom.range (NumberField.AdeleRing.DivisionAlgebra.incl K D)).comap
    (ringHaarChar_ker D_𝔸).subtype)) →
    Quotient (QuotientGroup.rightRel (incl₁ K D).range) :=
  Quot.lift
    (fun a => Quotient.mk (QuotientGroup.rightRel (incl₁ K D).range) (rest₁ K D a))
    (α_equivariant K D)

local instance : TopologicalSpace (_root_.Quotient (QuotientGroup.rightRel (incl₁ K D).range)) :=
  instTopologicalSpaceQuotient

lemma rest₁_continuous : Continuous (rest₁ K D) := by
  unfold rest₁
  refine Continuous.comp' continuous_snd ?_
  refine Continuous.comp' ?_ continuous_subtype_val
  -- this should probably be immediate from definition :/
  sorry

-- we should be able to infer instances of Borel etc of LHS from iso.. at least that is what I hope

lemma iso₁_ringHaarChar_equiv (a : (D ⊗[K] NumberField.InfiniteAdeleRing K)ˣ) (b : Dfx K D) :
    ringHaarChar (a, b) = ringHaarChar ((iso₁ K D).symm (a, b)) := by
  -- again hopefully should follow from however I set up iso₁ up
  sorry

def InfAdele_equiv : NumberField.InfiniteAdeleRing K ≃ K ⊗[ℚ] ℝ := by

  sorry

variable [Module ℚ D]

def Name : D ⊗[K] (NumberField.InfiniteAdeleRing K) ≃ D ⊗[K] (K ⊗[ℚ] ℝ) := by

  sorry

lemma rest₁_surjective : (rest₁ K D) '' Set.univ = Set.univ := by
  simp only [Set.image_univ]
  refine Eq.symm (Set.ext ?_)
  intro x
  simp only [Set.mem_univ, Set.mem_range, Subtype.exists, true_iff]
  obtain ⟨r, hx⟩ : ∃ r, ringHaarChar ((iso₁ K D).symm (1,x)) = r := exists_eq'
  have hr : r ≠ 0 := by
    rw [←hx]
    -- not sure why this is true right now
    sorry
  obtain ⟨y, hy⟩ : ∃ y, ringHaarChar ((iso₁ K D).symm (y,1)) = r := by
    -- will want to rewrite this as ringHaarChar y
    -- Dfx K D = (D ⨂ℚ ℝ)ˣ .. specifically ℝ ⊆ Dfx K D
    -- for z ∈ ℝ, ringHaarChar z = |z|^d where d = dim of D over ℚ
    -- so set y = z^{1/d}
    sorry
  use (iso₁ K D).symm (y⁻¹, x)
  constructor
  · rw [rest₁]
    refine Units.eq_iff.mp ?_
    simp only [MulEquiv.apply_symm_apply]
  · ext
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe, NNReal.coe_one,
      NNReal.coe_eq_one]
    have : (y⁻¹, x) = (y⁻¹, 1) * (1, x) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    simp_rw [this, map_mul]
    have : ringHaarChar ((iso₁ K D).symm (y⁻¹, 1)) = r⁻¹ := by
      rw [← hy]
      -- this requires our lemma above and using product properties
      sorry
    rw [this, hx]
    exact inv_mul_cancel₀ hr

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
    exact trivial
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
theorem NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (Doset.Quotient (Set.range (incl₁ K D)) U) := by
  sorry

end FiniteAdeleRing
