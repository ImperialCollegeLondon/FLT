/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import FLT.Slop.Background.Group.Basic

@[expose] public section

/-!
# Nilpotent-group helper lemmas

This file contains group-theoretic lemmas about nilpotent groups used in the
representation-theoretic induction arguments, especially the extraction of
nontrivial central elements from nontrivial normal subgroups.
-/

universe u
variable {G : Type u} [Group G]

/--
The normal closure of a nontrivial element is not the bottom subgroup.
-/
lemma Group.normalClosure_singleton_ne_bot_of_ne_one
    (c : G) (hc : c ≠ 1) :
    Subgroup.normalClosure ({c} : Set G) ≠ ⊥ := by
  intro hN
  have hcN : c ∈ Subgroup.normalClosure ({c} : Set G) :=
    (Subgroup.subset_normalClosure (by simp : c ∈ ({c} : Set G)))
  have hcBot : c ∈ (⊥ : Subgroup G) := by simpa [hN] using hcN
  exact hc (by simpa using (Subgroup.mem_bot.mp hcBot))


open commutatorElement in
/--
A nontrivial normal subgroup of a nilpotent group has nontrivial intersection
with the center.
-/
lemma Subgroup.inf_center_ne_bot_of_normal_ne_bot_of_nilpotent [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : N ⊓ center G ≠ ⊥ := by
  open Classical in
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent (G := G)
  let P : ℕ → Prop := fun i => N ⊓ upperCentralSeries G i ≠ ⊥
  have h_ex : ∃ i, P i := ⟨n, by dsimp[P]; rw [hn, inf_top_eq]; exact hN⟩
  let k := Nat.find h_ex
  have hk_min : N ⊓ upperCentralSeries G k ≠ ⊥ := Nat.find_spec h_ex
  have k_ne_zero : k ≠ 0 := by
    intro h0; rw [h0, upperCentralSeries_zero, inf_bot_eq] at hk_min; exact hk_min rfl
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero k_ne_zero
  have h_prev_bot : N ⊓ upperCentralSeries G m = ⊥ := by
    by_contra h_ne
    have h_lt : m < k := by rw [hm]; exact Nat.lt_succ_self m
    exact Nat.find_min h_ex h_lt h_ne
  obtain ⟨z, hz_mem, hz_ne⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hk_min
  have hz_cen : z ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h_comm_Z : ⁅g, z⁆ ∈ upperCentralSeries G m := by
       have h_z_in_Zk : z ∈ upperCentralSeries G k := hz_mem.2
       rw [hm] at h_z_in_Zk
       rw [mem_upperCentralSeries_succ_iff] at h_z_in_Zk
       specialize h_z_in_Zk g
       have h_inv : ⁅g, z⁆ = ⁅z, g⁆⁻¹ := by
         rw [commutatorElement_def, commutatorElement_def]; group
       rw [h_inv]
       exact inv_mem h_z_in_Zk
    have h_comm_N : ⁅g, z⁆ ∈ N := by
      rw [commutatorElement_def]
      apply Subgroup.mul_mem
      · exact Subgroup.Normal.conj_mem ‹N.Normal› z hz_mem.1 g
      · exact Subgroup.inv_mem N hz_mem.1
    have h_in_inf : ⁅g, z⁆ ∈ N ⊓ upperCentralSeries G m := ⟨h_comm_N, h_comm_Z⟩
    rw [h_prev_bot] at h_in_inf
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h_in_inf
    exact h_in_inf
  intro h_bot
  have h_z_in_inter : z ∈ N ⊓ center G := ⟨hz_mem.1, hz_cen⟩
  rw [h_bot, mem_bot] at h_z_in_inter
  exact hz_ne h_z_in_inter

/--
In a nilpotent group, the normal closure of a nontrivial element contains a
nontrivial central element.
-/
lemma Group.exists_center_mem_normalClosure_singleton_of_ne_one
     [Group.IsNilpotent G] {c : G} (hc : c ≠ 1) :
    ∃ z : G,
      z ∈ Subgroup.center G ∧
      z ∈ Subgroup.normalClosure ({c} : Set G) ∧
      z ≠ 1 := by
  let N : Subgroup G := Subgroup.normalClosure ({c} : Set G)
  have hN_ne_bot : N ≠ ⊥ := by
    exact Group.normalClosure_singleton_ne_bot_of_ne_one c hc
  have h_inter :
      N ⊓ Subgroup.center G ≠ ⊥ := by
    exact
      Subgroup.inf_center_ne_bot_of_normal_ne_bot_of_nilpotent
        N hN_ne_bot
  obtain ⟨z, hz_inter, hz_ne⟩ :=
    Subgroup.exists_mem_ne_one_of_ne_bot h_inter
  exact ⟨z, hz_inter.2, hz_inter.1, hz_ne⟩


open commutatorElement in
/--
If a nilpotent group is nonabelian, then there is a normal abelian subgroup
strictly containing the center.

The subgroup is constructed as the closure of the center together with an
element of the second upper central subgroup which is not central.
-/
lemma Group.exists_normal_abelian_gt_center [Group.IsNilpotent G]
    (h_non_comm : ¬ IsMulCommutative G) :
    ∃ (A : Subgroup G), A.Normal ∧ IsMulCommutative A ∧ Subgroup.center G < A := by
  have h_center_proper : Subgroup.center G < ⊤ := by
    refine lt_of_le_of_ne ?_ ?_
    · intro _ _
      exact Subgroup.mem_top _
    · intro h_top
      apply h_non_comm
      constructor
      constructor
      intro a b
      have ha : a ∈ Subgroup.center G := by
        rw [h_top]
        exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  let Z1 := Subgroup.upperCentralSeries G 1
  let Z2 := Subgroup.upperCentralSeries G 2
  have h_Z1_eq_center : Z1 = Subgroup.center G :=
    Subgroup.upperCentralSeries_one G
  have h_Z1_lt_Z2 : Z1 < Z2 := by
    refine lt_of_le_of_ne ?_ ?_
    · exact Subgroup.upperCentralSeries_mono G (by decide : 1 ≤ 2)
    · intro h_eq
      have h_eq' :
          Subgroup.upperCentralSeries G 1 =
            Subgroup.upperCentralSeries G 2 := by
        simpa [Z1, Z2] using h_eq
      have h_Z1_top : Z1 = ⊤ := by
        simpa [Z1] using
          (Subgroup.upperCentralSeries.eq_top
            (G := G) (a := 1) (b := 2)
            (by decide : 1 ≠ 2)
            h_eq')
      have h_center_top : Subgroup.center G = ⊤ := by
        rw [← h_Z1_eq_center, h_Z1_top]
      have hbad : (⊤ : Subgroup G) < ⊤ :=
        lt_of_eq_of_lt (id (Eq.symm h_center_top)) h_center_proper
      exact (lt_irrefl (⊤ : Subgroup G)) hbad
  rw [h_Z1_eq_center] at h_Z1_lt_Z2
  obtain ⟨x, hx_in_Z2, hx_not_center⟩ := SetLike.exists_of_lt h_Z1_lt_Z2
  let A := Subgroup.closure (insert x (Subgroup.center G : Set G))
  have h_A_gt : Subgroup.center G < A := by
    apply SetLike.lt_iff_le_and_exists.mpr
    constructor
    · intro z hz
      apply Subgroup.subset_closure
      exact Set.mem_insert_of_mem x hz
    · exact ⟨x, Subgroup.subset_closure (Set.mem_insert x _), hx_not_center⟩
  have h_A_norm : A.Normal := by
    constructor
    intro n hn g
    dsimp [A] at hn
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · have h_conj : g * y * g⁻¹ = ⁅g, y⁆ * y := by simp [commutatorElement_def, mul_assoc]
        rw [h_conj]
        have comm_in_Z : ⁅g, y⁆ ∈ Subgroup.center G := by
           rw [← h_Z1_eq_center]
           rw [← inv_mem_iff]
           have h_inv : ⁅g, y⁆⁻¹ = y * g * y⁻¹ * g⁻¹ := by
             simp [commutatorElement_def]; group
           rw [h_inv]
           exact Subgroup.mem_upperCentralSeries_succ_iff.mp hx_in_Z2 g
        apply Subgroup.mul_mem
        · apply Subgroup.subset_closure
          exact Set.mem_insert_of_mem y comm_in_Z
        · apply Subgroup.subset_closure
          exact Set.mem_insert y _
      · rw [Subgroup.mem_center_iff.mp hy g]
        rw [mul_inv_cancel_right]
        apply Subgroup.subset_closure
        exact Set.mem_insert_of_mem x hy
    | one =>
      simp
    | mul y z _ _ h_y h_z =>
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem A h_y h_z
    | inv y _ h_y =>
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem A h_y
  have h_A_comm : IsMulCommutative A := by
    constructor; constructor
    intro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    let S := insert x (Subgroup.center G : Set G)
    have h_comm_S : ∀ s1 ∈ S, ∀ s2 ∈ S, s1 * s2 = s2 * s1 := by
      rintro s1 (rfl|h1) s2 (rfl|h2)
      · rfl -- x * x
      · exact (Subgroup.mem_center_iff.mp h2 s1)
      · exact (Subgroup.mem_center_iff.mp h1 s2).symm
      · exact (Subgroup.mem_center_iff.mp h1 s2).symm
    dsimp [A] at ha hb
    change a * b = b * a
    induction ha, hb using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact h_comm_S x hx y hy
    | one_left => simp
    | one_right => simp
    | mul_left x y z _ _ _ h1 h2 => rw [mul_assoc, h2, ←mul_assoc, h1, mul_assoc]
    | mul_right x y z _ _ _ h1 h2 => rw [←mul_assoc, h1, mul_assoc, h2, ←mul_assoc]
    | inv_left x y _ _ h => exact (Commute.inv_left h).eq
    | inv_right x y _ _ h => exact (Commute.inv_right h).eq
  exact ⟨A, h_A_norm, h_A_comm, h_A_gt⟩
