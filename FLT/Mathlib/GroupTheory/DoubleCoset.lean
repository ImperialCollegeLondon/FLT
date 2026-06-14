/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, Kevin Buzzard, Andrew Yang
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.Algebra.Group.Quotient

/-!
# Double Coset

Material destined for Mathlib.
-/

@[expose] public section

theorem DoubleCoset.isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (X := G) (doubleCoset (Quotient.out i) H K) := by
  simpa only [doubleCoset] using (IsOpen.mul_left hK)

theorem DoubleCoset.isOpen_doubleCoset_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i) H K) := by
  apply (QuotientGroup.isOpenQuotientMap_rightrel_mk H).isOpenMap
  exact DoubleCoset.isOpen_doubleCoset H K hK i

def DoubleCoset.map {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ →* G₂) (eH : H₁ ≤ H₂.comap e) (eK : K₁ ≤ K₂.comap e) :
    DoubleCoset.Quotient (G := G₁) H₁ K₁ → DoubleCoset.Quotient (G := G₂) H₂ K₂ :=
  Quotient.map e fun a b H ↦ by
    simp only [DoubleCoset.rel_iff] at H ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := H
    refine ⟨e x, eH hx, e y, eK hy, by simp⟩

@[simp]
lemma DoubleCoset.map_mk {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ →* G₂) (eH : H₁ ≤ H₂.comap e) (eK : K₁ ≤ K₂.comap e) (x) :
    map H₁ K₁ H₂ K₂ e eH eK (DoubleCoset.mk _ _ x) = DoubleCoset.mk _ _ (e x) := rfl

def DoubleCoset.quotientEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Set G₁)
    (H₂ K₂ : Set G₂) (e : G₁ ≃* G₂) (eH : e ⁻¹' H₂ = H₁) (eK : e ⁻¹' K₂ = K₁) :
    DoubleCoset.Quotient H₁ K₁ ≃ DoubleCoset.Quotient H₂ K₂ :=
  Quotient.congr e fun x y ↦ by
    simp [← (Set.image_injective.mpr e.injective).eq_iff, DoubleCoset.doubleCoset_eq_image2,
      Set.image_image2, Set.image2_image_left, Set.image2_image_right,
      (Equiv.preimage_eq_iff_eq_image ..).mp eH, (Equiv.preimage_eq_iff_eq_image ..).mp eK]

@[simp]
lemma DoubleCoset.quotientEquiv_mk {G₁ G₂ : Type*} [Group G₁] [Group G₂] (H₁ K₁ : Subgroup G₁)
    (H₂ K₂ : Subgroup G₂) (e : G₁ ≃* G₂) (eH : e ⁻¹' H₂ = H₁) (eK : e ⁻¹' K₂ = K₁) (x) :
    quotientEquiv H₁ K₁ H₂ K₂ e eH eK (DoubleCoset.mk _ _ x) = DoubleCoset.mk _ _ (e x) := rfl

variable {G : Type*} [Group G] (H K : Subgroup G)

local notation H "＼" G "／" K:max => DoubleCoset.Quotient (G := G) H K
local notation H "﹨" G:max => _root_.Quotient (QuotientGroup.rightRel (α := G) H)

def DoubleCoset.ofLeft : G ⧸ K → H＼G／K :=
  Quotient.map id (by
    simp only [QuotientGroup.leftRel_apply, id_eq, Setoid.ker_def]
    intro a b hab
    exact .symm <| doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨1, by simp, _, hab, by simp⟩))

@[simp]
lemma DoubleCoset.ofLeft_mk (x : G) : ofLeft H K (QuotientGroup.mk x) = DoubleCoset.mk H K x := rfl

lemma DoubleCoset.ofLeft_surjective : Function.Surjective (ofLeft H K) :=
  Quotient.map_surjective _ Function.surjective_id

def DoubleCoset.ofRight : H﹨G → H＼G／K :=
  Quotient.map id (by
    simp only [QuotientGroup.rightRel_apply, id_eq, Setoid.ker_def]
    intro a b hab
    exact .symm <| doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨_, hab, 1, by simp, by simp⟩))

@[simp]
lemma DoubleCoset.ofRight_mk'' (x : G) : ofRight H K (.mk'' x) = DoubleCoset.mk H K x := rfl

lemma DoubleCoset.ofRight_surjective : Function.Surjective (ofRight H K) :=
  Quotient.map_surjective _ Function.surjective_id
