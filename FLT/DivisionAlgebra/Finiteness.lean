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
import FLT.NumberField.AdeleRing
import FLT.HaarMeasure.HaarChar.Ring

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

lemma existsE : ∃ E : Set (D_𝔸), IsCompact E ∧ ∀ x ∈ ringHaarChar_ker D_𝔸, ∃ e₁ ∈ E, ∃ e₂ ∈ E,
    e₁ ≠ e₂ ∧ x * e₁ - x * e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  sorry

/-- An auxiliary set E used in the proof of Fukisaki's lemma. -/
def E : Set D_𝔸 := (existsE K D).choose

lemma E_compact : IsCompact (E K D) := (existsE K D).choose_spec.1

lemma E_noninjective : ∀ x ∈ ringHaarChar_ker D_𝔸,
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    x * e₁ - x * e₂ ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) :=
  (existsE K D).choose_spec.2

lemma E_noninjective_right : ∀ x ∈ distribHaarChar.ker D_𝔸,
    ∃ e₁ ∈ E K D, ∃ e₂ ∈ E K D, e₁ ≠ e₂ ∧
    e₁ * x⁻¹ - e₂ * x⁻¹  ∈ Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸) := by
  sorry

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
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_left K D β hβ
  use (e1 - e2)
  constructor
  · simpa only using (Set.sub_mem_sub he1 he2)
  · have : IsUnit b := by
      simp_rw [← mul_sub_left_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
      have h1 : ↑β * (e1 - e2) ≠ 0 := by
        simpa only [ne_eq, not_not, Units.mul_right_eq_zero] using (sub_ne_zero_of_ne noteq)
      simp only [isUnit_iff_ne_zero, ne_eq]
      have h2 : b ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) ≠ 0 → b ≠ 0 := by
        intro h
        contrapose h
        simp only [ne_eq, not_not] at h ⊢
        simp only [h, TensorProduct.zero_tmul]
      simpa only [ne_eq] using h2 (Ne.symm (Lean.Grind.ne_of_ne_of_eq_right hb (id (Ne.symm h1))))
    obtain ⟨b1 , hb1⟩ := this
    simp only [Set.mem_range, exists_exists_eq_and, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    use b1
    simp only [mul_sub_left_distrib, (Eq.symm hb), Algebra.TensorProduct.includeLeft_apply, hb1,
      Algebra.TensorProduct.includeLeftRingHom_apply]

lemma X_meets_kernel' {β : D_𝔸ˣ} (hβ : β ∈ ringHaarChar_ker D_𝔸) :
    ∃ x ∈ X K D, ∃ d ∈ Set.range (incl K D : Dˣ → D_𝔸ˣ), x * β⁻¹ = d := by
  obtain ⟨e1, he1, e2, he2, noteq, b, hb⟩ := E_noninjective_right K D β hβ
  use (e1 - e2)
  constructor
  · simpa only using (Set.sub_mem_sub he1 he2)
  · have : IsUnit b := by
      simp_rw [← mul_sub_right_distrib, Algebra.TensorProduct.includeLeft_apply] at hb
      have h1 : (e1 - e2) * ↑β⁻¹ ≠ 0 := by
        simpa only [ne_eq, Units.mul_left_eq_zero] using (sub_ne_zero_of_ne noteq)
      simp only [isUnit_iff_ne_zero, ne_eq]
      have h2 : b ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K) ≠ 0 → b ≠ 0 := by
        intro h
        contrapose h
        simp only [ne_eq, not_not] at h ⊢
        simp only [h, TensorProduct.zero_tmul]
      simpa only [ne_eq] using h2 (Ne.symm (Lean.Grind.ne_of_ne_of_eq_right hb (id (Ne.symm h1))))
    obtain ⟨b1 , hb1⟩ := this
    simp only [Set.mem_range, exists_exists_eq_and, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    use b1
    simp only [mul_sub_right_distrib, (Eq.symm hb), Algebra.TensorProduct.includeLeft_apply, hb1,
      Algebra.TensorProduct.includeLeftRingHom_apply]

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
    simp only [Set.subset_inter_iff, Set.image_subset_iff]
    constructor
    · simp only [T, Set.inter_subset_left]
    · refine Set.image_subset_iff.mp ?_
      rw [T]
      have h2 : Units.val '' (Set.range (incl K D : Dˣ → D_𝔸ˣ)) ⊆
          (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)) := by
        simp only [Set.image_subset_iff]
        refine Set.range_subset_iff.mpr ?_
        intro y
        simp only [Set.mem_preimage, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          Algebra.TensorProduct.includeLeftRingHom_apply, Set.mem_range,
          Algebra.TensorProduct.includeLeft_apply, exists_apply_eq_apply]
      simp only [Set.image_inter Units.ext]
      exact (Set.Subset.trans Set.inter_subset_right h2)
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
    β = b * ν ∧ ((ν : D_𝔸), ((ν⁻¹ : D_𝔸ˣ) : D_𝔸)) ∈ C K D :=
  sorry

end Aux

lemma compact_quotient : CompactSpace (ringHaarChar_ker D_𝔸 ⧸
  (MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype) := sorry

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

theorem NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (Dfx K D ⧸ (incl₁ K D).range) := by
  sorry

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
