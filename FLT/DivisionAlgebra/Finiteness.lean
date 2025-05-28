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

set_option maxHeartbeats 1000000

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
instance : TopologicalSpace D_𝔸 :=
  moduleTopology (AdeleRing (𝓞 K) K) _

instance : IsModuleTopology (AdeleRing (𝓞 K) K) D_𝔸 := ⟨rfl⟩

instance : IsTopologicalRing D_𝔸 :=
  IsModuleTopology.Module.topologicalRing (AdeleRing (𝓞 K) K) _

instance : LocallyCompactSpace D_𝔸 := sorry -- we have this (unfinished) elsewhere TODO

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

lemma T_finite : Set.Finite (T K D) := by
  have h : Set.Finite ((Y K D) ∩ (Set.range (Algebra.TensorProduct.includeLeft : D →ₐ[K] D_𝔸)))
      := by
    apply IsCompact.finite
    · refine IsCompact.inter_right (Y_compact K D) ?_

      -- Subgroup.isClosed_of_discrete
      sorry
    ·
      -- follows form D being discrete
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
    β = b * ν ∧ ((ν : D_𝔸), ((ν⁻¹ : D_𝔸ˣ) : D_𝔸)) ∈ C K D :=
  sorry

end Aux

def incl₂ : ringHaarChar_ker D_𝔸 → Prod D_𝔸 D_𝔸 :=
  (fun i => (i.1, i⁻¹.1)).comp (Subgroup.subtype (ringHaarChar_ker D_𝔸))

def M : Set (ringHaarChar_ker D_𝔸) := Set.preimage (incl₂ K D) (Aux.C K D)

abbrev MtoQuot : (ringHaarChar_ker D_𝔸) → (ringHaarChar_ker D_𝔸 ⧸
    (MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype) := Quot.mk _

lemma compact_quotient : CompactSpace (ringHaarChar_ker D_𝔸 ⧸
    (MonoidHom.range (incl K D)).comap (ringHaarChar_ker D_𝔸).subtype) := by
  have h4 : Continuous (MtoQuot K D) := by
    exact { isOpen_preimage := fun s a ↦ a }
  have h2 : IsCompact (M K D) := by
    apply Topology.IsClosedEmbedding.isCompact_preimage
    · refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap ?_ ?_ ?_
      · rw [incl₂]
        refine continuous_induced_rng.mp ?_
        have := MeasureTheory.ringHaarChar_continuous D_𝔸
        -- think it is an application of this somewhere?
        sorry
      · intro a b eq
        simp_rw [incl₂] at eq
        aesop
      · refine Topology.IsInducing.isClosedMap ?_ ?_
        · -- true by definition?
          sorry
        · -- true as ringHaarChar_ker is closed... so their inclusions i, i⁻¹ are closed
          simp_rw [incl₂]
          simp only [Subgroup.coe_subtype]

          sorry
    · exact Aux.C_compact K D
  have h3 : (MtoQuot K D) '' (M K D) = Set.univ := by
    ext x
    refine ⟨by intro hx; simp, ?_ ⟩
    · intro hx
      obtain ⟨a, ha⟩ := x
      obtain ⟨c, hc, ν, hν, eq, h31⟩ := Aux.antidiag_mem_C K D ha
      simp only [Subgroup.comap_subtype, Set.mem_image, Subtype.exists]
      refine ⟨ν, hν, h31, ?_ ⟩
      simp_rw [MtoQuot, Subgroup.comap_subtype, eq]
        -- should be true by pulling out c... but not sure how to do this; probably overcomplicated
      sorry
  exact isCompact_univ_iff.mp (by simpa only [←h3] using IsCompact.image h2 h4)

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

variable [MeasurableSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]
  [BorelSpace (D ⊗[K] NumberField.AdeleRing (𝓞 K) K)]

def rest₁ : ringHaarChar_ker D_𝔸 → Dfx K D :=
  fun a => --((Subgroup.subtype (ringHaarChar_ker D_𝔸)) a)

           -- the RHS is tensoring over all places; just need to work out how to remove the infinite
           -- ones... this should be a .2 somewhere; not sure how to do this restriction in Lean
  sorry

def α : (ringHaarChar_ker D_𝔸 ⧸ (MonoidHom.range
    (NumberField.AdeleRing.DivisionAlgebra.incl K D)).comap (ringHaarChar_ker D_𝔸).subtype)
    → (Dfx K D ⧸ (incl₁ K D).range) :=
  fun a => Quot.mk _  (rest₁ K D a.out)

local instance : TopologicalSpace (Dfx K D ⧸ (incl₁ K D).range) :=
  QuotientGroup.instTopologicalSpace _

theorem NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact :
    CompactSpace (Dfx K D ⧸ (incl₁ K D).range) := by
  have h1 : Continuous (α K D) := by
    refine continuous_iff_isClosed.mpr ?_
    intro S hS
    -- this will be true as you only need to adjoin infinite places which will also be closed
    -- (maybe?...)

    sorry
  have h3 : (α K D) '' Set.univ = Set.univ := by
    ext a
    simp only [Subgroup.comap_subtype, Set.image_univ, Set.mem_range, Set.mem_univ, iff_true]
     -- need y to be Quot.mk _ (a.out ⊕ infinite places such that in kernel)
     -- so need a have statement saying that for a ∃ t in the infinite places with
     -- haar measure δ(1,t) = r
     -- then can show haar measure of (a.out, t) = 1
     -- this will by definition have exactly as wanted by construction
     -- may need to ask for help writing this as a statement; not used to Haar character stuff
    sorry
  have := isCompact_univ_iff.mpr (NumberField.AdeleRing.DivisionAlgebra.compact_quotient K D)
  apply isCompact_univ_iff.mp
  simpa [← h3] using IsCompact.image this h1

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If `D` is a finite-dimensional division algebra over a number field `K`
then the double coset space `Dˣ \ (D ⊗ 𝔸_K^infty)ˣ / U` is finite for any compact open subgroup `U`
of `(D ⊗ 𝔸_F^infty)ˣ`.
-/

-- not sure if I really need to show this instance or if I can infer it from somewhere else;
-- I would like to be using it as a subgroup later though? perhaps better way to phrase this all...
instance units : Subgroup (Dfx K D) where
  carrier := Set.range (incl₁ K D)
  one_mem' := by
    simp only [Set.mem_range, Units.ext_iff, Algebra.TensorProduct.includeLeft_apply,
      Units.val_one]
    use 1
    simp only [map_one, Units.val_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_range]
    obtain ⟨a1, rfl⟩ := ha
    obtain ⟨b1, rfl⟩ := hb
    use a1 * b1
    exact MonoidHom.map_mul (incl₁ K D) a1 b1
  inv_mem' := by
    intro a ha
    simp only [Set.mem_range]
    obtain ⟨a1, rfl⟩ := ha
    use a1⁻¹
    exact MonoidHom.map_inv (incl₁ K D) a1

open Doset

theorem Doset.finite {G : Type*} [Group G] (H K : Subgroup G) :
    Finite (Quotient (H : Set G) K) ↔ ∃ I : Finset (Quotient (H : Set G) K), Set.univ = ⋃ i : I,
    quotToDoset H K i.1 := by
  constructor
  · intro I
    use I -- not sure how to coerce this to what I want right now
    -- then apply union_quotToDoset
    sorry
  · intro ⟨I, hI⟩
    -- need to create a surjection based on I; should be doable?
    sorry

theorem NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (Quotient (Set.range (incl₁ K D)) (U : Set (Dfx K D))) := by
  refine Set.finite_univ_iff.mp ?_
  apply (Iff.symm Set.finite_univ_iff).mp
  apply (Doset.finite (units K D) U).mpr
  have openCover := union_quotToDoset (units K D) (U)
  simp_rw [quotToDoset] at openCover
  simp_rw [← (doset_union_rightCoset (units K D) U)] at openCover -- maybe need left instead??



  have ToFinCover := isCompact_univ_iff.mpr
      (NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D)
  apply isCompact_iff_finite_subcover.mp at ToFinCover

  -- some how want to push openCover down to an openCover of the left quotient
  -- then apply ToFinCover
  -- then push this cover up??

/-
  -- Just realised ToFinCover requires the wrong Set.univ... :/ may need something to transfer
  -- between the two. Or need to actually do this all myself?

  have ToFinCover := isCompact_univ_iff.mpr
      (NumberField.FiniteAdeleRing.DivisionAlgebra.units_cocompact K D)
  apply isCompact_iff_finite_subcover.mp at ToFinCover


  -- Need to apply FinCover with found statements to get our final claim
-/

  sorry


end FiniteAdeleRing
