/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.Index

/-!
# A class-equation-style counting lemma for conjugates of subgroups

This file proves `Dickson.natClassEquation`: if `H₁, …, Hᵣ` are subgroups of a finite
group `G` which pairwise intersect trivially (along with all their conjugates), then
counting the nonidentity elements lying in conjugates of the `Hᵢ` gives the inequality
`∑ i, (|Hᵢ| - 1) * |G : N_G(Hᵢ)| ≤ |G| - 1`.

This is the integer form of the counting argument underlying the partition equation
used in the tame case of Dickson's classification of finite subgroups of `PGL₂(𝔽̄_p)`.
-/

/- The code in this file was ported from Duxing Yang's `DicksonClassification` project
and does not yet follow the mathlib style conventions enforced by the linters below. -/
set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.style.cdot false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.induction false
set_option linter.unusedFintypeInType false

@[expose] public section

open scoped Classical

namespace Dickson

noncomputable section



lemma card_conjugates_eq_normalizer_index {G' : Type*} [Group G'] [Fintype G']
    (H : Subgroup G') :
    Fintype.card {K : Subgroup G' | ∃ g : G', K = H.map (MulAut.conj g).toMonoidHom} =
    (Subgroup.normalizer (SetLike.coe H)).index := by
  rw [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card, Nat.card_congr]
  symm
  refine Equiv.ofBijective
    (fun g ↦ ⟨H.map (MulAut.conj g.out).toMonoidHom, g.out, rfl⟩)
    ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩

  · rw [Subtype.mk.injEq] at h
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b,
      QuotientGroup.eq, Subgroup.mem_normalizer_iff]
    intro x
    have h1 := SetLike.ext_iff.mp h (b.out * x * b.out⁻¹)

    have h2 := SetLike.ext_iff.mp h
      (a.out * ((a.out⁻¹ * b.out) * x * (a.out⁻¹ * b.out)⁻¹) * a.out⁻¹)
    simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at h1 h2
    constructor

    · intro hx
      obtain ⟨y, hy, hy_eq⟩ := h1.mpr ⟨x, hx, rfl⟩

      have y_eq : y = (a.out⁻¹ * b.out) * x * (a.out⁻¹ * b.out)⁻¹ := by
        calc y = a.out⁻¹ * (a.out * y * a.out⁻¹) * a.out := by group
          _ = _ := by rw [hy_eq]; group
      exact y_eq ▸ hy

    · intro hx
      obtain ⟨y, hy, hy_eq⟩ := h2.mp ⟨_, hx, rfl⟩

      have y_eq : y = x := by
        calc y = b.out⁻¹ * (b.out * y * b.out⁻¹) * b.out := by group
          _ = _ := by rw [hy_eq]; group
      exact y_eq ▸ hy

  · obtain ⟨g, hg⟩ := a.property
    have hn := QuotientGroup.out_eq' (QuotientGroup.mk g : G' ⧸ (Subgroup.normalizer (SetLike.coe H)))
    rw [QuotientGroup.eq] at hn

    have h_conj : H.map (MulAut.conj g).toMonoidHom =
        H.map (MulAut.conj (g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out).toMonoidHom := by
      ext x
      simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      constructor

      · rintro ⟨y, hy, rfl⟩
        have key : ((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g) * y *
            ((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g)⁻¹ =
            (g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * (g * y * g⁻¹) *
            (g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out := by group
        exact ⟨_, key ▸
          (Subgroup.mem_normalizer_iff.mp hn y).mp hy, by group⟩

      · rintro ⟨y, hy, rfl⟩
        have key2 : ((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g) *
            (((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g)⁻¹ * y *
            ((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g)) *
            ((g : G' ⧸ (Subgroup.normalizer (SetLike.coe H))).out⁻¹ * g)⁻¹ = y := by group
        exact ⟨_, (Subgroup.mem_normalizer_iff.mp hn _).mpr
          (key2.symm ▸ hy), by group⟩
    exact ⟨g, Subtype.ext (by rw [hg, h_conj])⟩

lemma conjClass_unique_index {G' : Type*} [Group G'] [Fintype G']
    (r : ℕ) (H : Fin r → Subgroup G')
    (hdisjoint : ∀ K L : Subgroup G',
      (∃ (i : Fin r) (g : G'), K = (H i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin r) (h : G'), L = (H j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hinj : ∀ i j : Fin r, (∃ g : G',
      (H i).map (MulAut.conj g).toMonoidHom = H j) → i = j)
    (x : G') (hx : x ≠ 1)
    (i j : Fin r) (g₁ g₂ : G')
    (hi : x ∈ (H i).map (MulAut.conj g₁).toMonoidHom)
    (hj : x ∈ (H j).map (MulAut.conj g₂).toMonoidHom) :
    i = j := by

  have h_conj_eq : (H i).map (MulAut.conj g₁).toMonoidHom =
      (H j).map (MulAut.conj g₂).toMonoidHom := by
    by_contra h
    exact hx ((Subgroup.ext_iff.mp (hdisjoint _ _ ⟨i, g₁, rfl⟩ ⟨j, g₂, rfl⟩ h) x).mp ⟨hi, hj⟩)
  refine hinj i j ⟨g₂⁻¹ * g₁, ?_⟩
  ext y; simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]; constructor

  · rintro ⟨z, hz, rfl⟩
    have h1 := SetLike.ext_iff.mp h_conj_eq (g₁ * z * g₁⁻¹)
    simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at h1
    obtain ⟨w, hw, hw_eq⟩ := h1.mp ⟨z, hz, rfl⟩

    have hw2 : w = g₂⁻¹ * g₁ * z * (g₂⁻¹ * g₁)⁻¹ := by
      calc w = g₂⁻¹ * (g₂ * w * g₂⁻¹) * g₂ := by group
        _ = g₂⁻¹ * (g₁ * z * g₁⁻¹) * g₂ := by rw [hw_eq]
        _ = _ := by group
    exact hw2 ▸ hw

  · intro hy
    have h_eq := SetLike.ext_iff.mp h_conj_eq (g₂ * y * g₂⁻¹)
    simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at h_eq
    obtain ⟨w, hw, hw_eq⟩ := h_eq.mpr ⟨y, hy, rfl⟩
    refine ⟨w, hw, ?_⟩
    calc g₂⁻¹ * g₁ * w * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * w * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * y * g₂⁻¹) * g₂ := by rw [hw_eq]
      _ = y := by group



def conjClassElements {G' : Type*} [Group G'] [Fintype G']
    (H : Subgroup G') : Finset G' :=
  Finset.univ.filter (fun x ↦ x ≠ 1 ∧ ∃ g : G', x ∈ H.map (MulAut.conj g).toMonoidHom)



def conjNonidentity {G' : Type*} [Group G'] [Fintype G']
    (H : Subgroup G') (g : G') : Finset G' :=
  Finset.univ.filter (fun x ↦ x ≠ 1 ∧ x ∈ H.map (MulAut.conj g).toMonoidHom)



lemma card_conjNonidentity {G' : Type*} [Group G'] [Fintype G']
    (H : Subgroup G') (g : G') :
    (conjNonidentity H g).card = Nat.card H - 1 := by
  let K := H.map (MulAut.conj g).toMonoidHom

  have h_eq : conjNonidentity H g = K.carrier.toFinset.erase 1 := by
    ext x
    simp only [conjNonidentity, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase, Set.mem_toFinset, ne_eq]
    rfl
  rw [h_eq, Finset.card_erase_of_mem]

  · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact congrArg (fun x ↦ x - 1) (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) H).toEquiv.symm)

  · exact Set.mem_toFinset.mpr (Subgroup.one_mem K)



lemma card_conjClassElements {G' : Type*} [Group G'] [Fintype G']
    (H : Subgroup G') (_hH : Nat.card H ≥ 2)
    (hdisjoint : ∀ K L : Subgroup G',
      (∃ g : G', K = H.map (MulAut.conj g).toMonoidHom) →
      (∃ h : G', L = H.map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥) :
    (conjClassElements H).card = (Subgroup.normalizer (SetLike.coe H)).index * (Nat.card H - 1) := by
  have h_num := card_conjugates_eq_normalizer_index H

  let S := Finset.univ.filter
    (fun K : Subgroup G' ↦ ∃ g : G', K = H.map (MulAut.conj g).toMonoidHom)
  rw [show conjClassElements H = Finset.biUnion S
      (fun K ↦ Finset.univ.filter (fun x ↦ x ≠ 1 ∧ x ∈ K)) by
      ext x
      simp only [conjClassElements, S, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor

      · rintro ⟨hx, g, hg⟩
        exact ⟨H.map (MulAut.conj g).toMonoidHom, ⟨g, rfl⟩, hx, hg⟩

      · rintro ⟨K, ⟨g, rfl⟩, hx, hxK⟩; exact ⟨hx, g, hxK⟩,
    Finset.card_biUnion (fun K hK L hL hKL ↦ by
      simp only [Finset.disjoint_left, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rintro x ⟨hx1, hxK⟩ ⟨_, hxL⟩
      exact hx1 ((Subgroup.ext_iff.mp (hdisjoint K L
        (Finset.mem_filter.mp hK).right
        (Finset.mem_filter.mp hL).right hKL) x).mp ⟨hxK, hxL⟩))]
  trans ∑ K ∈ S, (Nat.card H - 1)

  · refine Finset.sum_congr rfl fun K hK ↦ ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hK
    obtain ⟨g, rfl⟩ := hK
    exact card_conjNonidentity H g

  · rw [Finset.sum_const, smul_eq_mul, ← h_num]
    congr 1
    exact Fintype.card_of_subtype S (by
      simp only [S, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq, implies_true]) |>.symm

lemma natClassEquation {G' : Type*} [Group G'] [Fintype G']
    (r : ℕ) (H : Fin r → Subgroup G')
    (hH_card_ge : ∀ i, Nat.card (H i) ≥ 2)
    (hdisjoint : ∀ K L : Subgroup G',
      (∃ (i : Fin r) (g : G'), K = (H i).map (MulAut.conj g).toMonoidHom) →
      (∃ (j : Fin r) (h : G'), L = (H j).map (MulAut.conj h).toMonoidHom) →
      K ≠ L → K ⊓ L = ⊥)
    (hcover : ∀ x : G', x ≠ 1 →
      ∃ K : Subgroup G', (∃ (i : Fin r) (g : G'),
        K = (H i).map (MulAut.conj g).toMonoidHom) ∧ x ∈ K)
    (hinj : ∀ i j : Fin r, (∃ g : G',
      (H i).map (MulAut.conj g).toMonoidHom = H j) → i = j) :
    Nat.card G' - 1 =
      ∑ i : Fin r, (Subgroup.normalizer (SetLike.coe (H i))).index * (Nat.card (H i) - 1) := by

  have h_total_non_identity :
      (Finset.univ.filter (fun x : G' ↦ x ≠ 1)).card =
      ∑ i, (conjClassElements (H i)).card := by
    rw [← Finset.card_biUnion]

    · refine congr_arg Finset.card (Finset.ext fun x ↦ ?_)
      simp only [conjClassElements, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor

      · intro hx
        rcases hcover x hx with ⟨K, ⟨i, g, rfl⟩, hxK⟩
        exact ⟨i, hx, g, hxK⟩

      · rintro ⟨_, hx, _, _⟩
        exact hx

    · intro i _ j _ hij
      simp only [conjClassElements, Finset.disjoint_left,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rintro x ⟨hx1, g1, hxK1⟩ ⟨_, g2, hxK2⟩
      exact hij (conjClass_unique_index r H hdisjoint hinj
        x hx1 i j g1 g2 hxK1 hxK2)
  convert h_total_non_identity using 1

  · have : Finset.univ.filter (fun x : G' ↦ x ≠ 1) = Finset.univ.erase 1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, ne_eq, true_and, and_true]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ 1),
      Nat.card_eq_fintype_card, Finset.card_univ]

  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [card_conjClassElements]

    · exact hH_card_ge i

    · exact fun K L hK hL hKL ↦ hdisjoint K L
        ⟨i, hK.choose, hK.choose_spec⟩
        ⟨i, hL.choose, hL.choose_spec⟩ hKL
end

end Dickson
