/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Transfer
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.NormNum.Prime
public import FLT.Slop.PGL2.FiniteSubgroups.PGLBasic

/-!
# Recognition theorems for groups with a partition into cyclic subgroups

This file defines `Dickson.HasCyclicPartition G configs`: the finite group `G` is
covered by a list of cyclic subgroups `Hᵢ` of order `dᵢ` (each appearing with `fᵢ`
conjugates, intersecting pairwise trivially) matching the list `configs` of
`Dickson.CyclicPartitionConfig` data.

The main results recognise a finite group from the combinatorics of such a partition:
* `Dickson.isCyclic_of_hasCyclicPartition`: one part of full order forces `G` cyclic;
* `Dickson.dihedral_of_hasCyclicPartition_odd` and
  `Dickson.dihedral_of_hasCyclicPartition_even`: partitions of type `{n, 2, …, 2}`
  force `G ≃* DihedralGroup n`;
* `Dickson.iso_A4_of_hasCyclicPartition`, `Dickson.iso_S4_of_hasCyclicPartition` and
  `Dickson.iso_A5_of_hasCyclicPartition`: the partitions corresponding to the
  exceptional groups of orders 12, 24 and 60 force `G ≃* A₄`, `S₄`, `A₅` respectively.

These are used in the tame case of Dickson's classification of finite subgroups
of `PGL₂(𝔽̄_p)`.
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

/-- Combinatorial data for one class in a cyclic partition: `f` conjugate cyclic subgroups,
each of order `d`. -/
structure CyclicPartitionConfig where
  /-- The common order `d` of the cyclic subgroups in this class. -/
  d : ℕ
  /-- The number `f` of conjugate cyclic subgroups in this class. -/
  f : ℕ

/-- `HasCyclicPartition G configs` states that the finite group `G` is covered by cyclic
subgroups (intersecting pairwise trivially) whose orders and conjugate counts match `configs`. -/
@[nolint unusedArguments]
def HasCyclicPartition (G : Type*) [Group G] [Fintype G]
    (configs : List CyclicPartitionConfig) : Prop :=
  ∃ (H : List (Subgroup G)),
    H.length = configs.length ∧
    (∀ (i : Fin configs.length),
      ∃ (Hi : Subgroup G), H[i.val]? = some Hi ∧
      let ci := configs.get i
      IsCyclic Hi ∧
      Nat.card Hi = ci.d ∧
      Nat.card ((Subgroup.normalizer (SetLike.coe Hi))) = ci.f * ci.d) ∧

    let all_conjugates := { K : Subgroup G |
      ∃ (i : Fin configs.length) (g : G) (Hi : Subgroup G),
        H[i.val]? = some Hi ∧ K = Hi.map (MulAut.conj g).toMonoidHom }
    (∀ K L : Subgroup G, K ∈ all_conjugates → L ∈ all_conjugates →
      K ≠ L → K ⊓ L = ⊥) ∧
    (∀ x : G, x ≠ 1 → ∃ K ∈ all_conjugates, x ∈ K)

theorem isCyclic_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G] (N : ℕ)
    (hN : Nat.card G = N)
    (h : HasCyclicPartition G [{d := N, f := 1}]) : IsCyclic G := by
  obtain ⟨_, hH⟩ := h
  obtain ⟨Hi, _, hCyc, hCard, _⟩ := hH.2.1 ⟨0, Nat.zero_lt_one⟩
  have hTop : Hi = ⊤ := Subgroup.eq_top_of_card_eq _ (hCard.trans hN.symm)
  obtain ⟨g, hg⟩ := hCyc.exists_generator
  exact ⟨g, fun x ↦
    let ⟨n, hn⟩ := hg ⟨x, hTop.symm ▸ Subgroup.mem_top x⟩
    ⟨n, Subtype.ext_iff.mp hn⟩⟩

theorem dihedralRecognition (G : Type*) [Group G] [Fintype G] (n : ℕ) (hn : n ≥ 2)
    (H : Subgroup G) [H.Normal]
    (hH_cyclic : IsCyclic H)
    (hH_card : Nat.card H = n)
    (hH_index : H.index = 2)
    (h_invol : ∀ g : G, g ∉ H → orderOf g = 2) :
    Nonempty (G ≃* DihedralGroup n) := by
  haveI : NeZero n := ⟨Nat.ne_of_gt ((Nat.zero_lt_succ 1).trans_le hn)⟩

  obtain ⟨a, ha⟩ : ∃ a : G, a ∉ H := by
    by_contra! h
    have h_eq : H = ⊤ := Subgroup.ext fun x ↦ iff_of_true (h x) trivial
    rw [h_eq, Subgroup.index_top] at hH_index
    contradiction
  have ha2 : a ^ 2 = 1 := by rw [← pow_orderOf_eq_one a, h_invol a ha]
  obtain ⟨b', hb'⟩ := hH_cyclic.exists_generator
  let b := (b' : G)
  have hb_mem : b ∈ H := b'.2

  have hb_order : orderOf b = n := by
    rw [← hH_card, ← orderOf_eq_card_of_forall_mem_zpowers hb']
    exact orderOf_injective H.subtype Subtype.coe_injective b'

  have hab2 : (a * b) ^ 2 = 1 := by
    rw [← pow_orderOf_eq_one (a * b),
        h_invol _ (fun h ↦ ha (mul_inv_cancel_right a b ▸ H.mul_mem h (H.inv_mem hb_mem)))]

  have h_conj : a * b * a = b⁻¹ := by
    apply mul_left_cancel (a := a * b)
    rw [← mul_assoc, ← sq, hab2, one_mul, mul_inv_cancel_right]

  have h_ba : b * a = a * b⁻¹ := by
    calc b * a = 1 * b * a := by rw [one_mul]
      _ = (a * a) * b * a := by rw [← show a * a = 1 by rw [← sq, ha2]]
      _ = a * (a * b * a) := by group
      _ = a * b⁻¹ := by rw [h_conj]

  have hb_pow_mul_a : ∀ (x : ℕ), b ^ x * a = a * (b ^ x)⁻¹ := by
    intro x
    induction' x with x ih

    · simp only [pow_zero, inv_one, one_mul, mul_one]

    · calc b ^ (x + 1) * a = b * (b ^ x * a) := by rw [pow_succ', mul_assoc]
        _ = (b * a) * (b ^ x)⁻¹ := by rw [ih, ← mul_assoc]
        _ = a * (b ^ (x + 1))⁻¹ := by rw [h_ba, mul_assoc, ← mul_inv_rev, ← pow_succ]

  have h_coset : ∀ g : G, g ∉ H → ∃ h ∈ H, g = a * h := by
    intro g hg
    have ⟨x, hx⟩ := Subgroup.index_eq_two_iff.mp hH_index

    have hgx : g * x ∈ H := by
      rcases hx g with ⟨h1, _⟩ | ⟨h1, _⟩; exact h1; exact absurd h1 hg

    have hax : a * x ∈ H := by
      rcases hx a with ⟨h1, _⟩ | ⟨h1, _⟩; exact h1; exact absurd h1 ha
    exact ⟨a⁻¹ * g,
        Subgroup.Normal.mem_comm inferInstance (show g * a⁻¹ ∈ H from
            (show g * x * (a * x)⁻¹ = g * a⁻¹ by group) ▸ H.mul_mem hgx (H.inv_mem hax)), by group⟩
  have hb_pow_n : b ^ n = 1 := by rw [← hb_order, pow_orderOf_eq_one]

  have hb_pow_mod : ∀ (x : ℕ), b ^ (x % n) = b ^ x := by
    intro x
    conv_rhs => rw [← Nat.mod_add_div x n, pow_add, pow_mul, hb_pow_n, one_pow, mul_one]

  have hb_zpow_mod : ∀ (x : ℤ), b ^ (x % (n : ℤ)) = b ^ x := by
    intro x
    conv_rhs => rw [← Int.emod_add_mul_ediv x n, zpow_add, zpow_mul,
        show b ^ (n : ℤ) = 1 by rw [zpow_natCast, hb_pow_n], one_zpow, mul_one]

  have hb_zpow_eq_toNat : ∀ (i : ℤ), b ^ i = b ^ (i % (n : ℤ)).toNat := by
    intro i
    calc b ^ i = b ^ (i % (n : ℤ)) := (hb_zpow_mod i).symm
      _ = b ^ ((i % (n : ℤ)).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))]
      _ = b ^ (i % (n : ℤ)).toNat := by rw [zpow_natCast]

  have h_b_gen : ∀ g ∈ H, ∃ k : ZMod n, g = b ^ k.val := by
    intro g hg
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hb' ⟨g, hg⟩)
    let k_nat := (i % (n : ℤ)).toNat

    have hk_nat_lt : k_nat < n := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg i (by omega))]
      exact Int.emod_lt_of_pos i (by omega)
    use (k_nat : ZMod n)
    calc g = ((⟨g, hg⟩ : H) : G) := rfl
      _ = (b' ^ i : H) := by rw [hi]
      _ = b ^ i := Subgroup.coe_zpow H b' i
      _ = b ^ k_nat := hb_zpow_eq_toNat i
      _ = b ^ (k_nat % n) := by rw [Nat.mod_eq_of_lt hk_nat_lt]
      _ = b ^ (k_nat : ZMod n).val := by rw [ZMod.val_natCast]

  have hb_pow_mul : ∀ (x y : ZMod n), b ^ (x + y).val = b ^ x.val * b ^ y.val := by
    intro x y
    calc b ^ (x + y).val = b ^ ((x.val + y.val) % n) := by rw [ZMod.val_add]
      _ = b ^ (x.val + y.val) := hb_pow_mod (x.val + y.val)
      _ = b ^ x.val * b ^ y.val := by rw [pow_add]

  have hb_pow_sub : ∀ (x y : ZMod n), b ^ (x - y).val = b ^ x.val * (b ^ y.val)⁻¹ := by
    intro x y
    apply mul_right_cancel (b := b ^ y.val)
    calc b ^ (x - y).val * b ^ y.val = b ^ ((x - y) + y).val := (hb_pow_mul (x - y) y).symm
      _ = b ^ x.val := by rw [sub_add_cancel]
      _ = b ^ x.val * (b ^ y.val)⁻¹ * b ^ y.val := by group

  have hb_comm : ∀ (x y : ℕ), (b ^ x)⁻¹ * b ^ y = b ^ y * (b ^ x)⁻¹ := by
    intro x y
    exact (Commute.pow_pow (Commute.refl b) x y).inv_left.eq

  let f_map : DihedralGroup n → G := fun g ↦ match g with
    | DihedralGroup.r k => b ^ k.val
    | DihedralGroup.sr k => a * b ^ k.val

  have f_mul : ∀ x y, f_map (x * y) = f_map x * f_map y := by
    intro x y
    rcases x with ⟨k1⟩ | ⟨k1⟩ <;> rcases y with ⟨k2⟩ | ⟨k2⟩

    · change b ^ (k1 + k2).val = b ^ k1.val * b ^ k2.val
      exact hb_pow_mul k1 k2

    · change a * b ^ (k2 - k1).val = b ^ k1.val * (a * b ^ k2.val)
      symm
      calc b ^ k1.val * (a * b ^ k2.val) = b ^ k1.val * a * b ^ k2.val := by rw [mul_assoc]
        _ = a * (b ^ k1.val)⁻¹ * b ^ k2.val := by rw [hb_pow_mul_a]
        _ = a * ((b ^ k1.val)⁻¹ * b ^ k2.val) := by rw [mul_assoc]
        _ = a * (b ^ k2.val * (b ^ k1.val)⁻¹) := by rw [hb_comm]
        _ = a * b ^ (k2 - k1).val := by rw [← hb_pow_sub]

    · change a * b ^ (k1 + k2).val = (a * b ^ k1.val) * b ^ k2.val
      rw [mul_assoc, ← hb_pow_mul]

    · change b ^ (k2 - k1).val = (a * b ^ k1.val) * (a * b ^ k2.val)
      symm
      calc (a * b ^ k1.val) * (a * b ^ k2.val)
          = a * (b ^ k1.val * (a * b ^ k2.val)) := by
            rw [mul_assoc]
        _ = a * ((b ^ k1.val * a) * b ^ k2.val) := by rw [← mul_assoc (b ^ k1.val)]
        _ = a * (b ^ k1.val * a) * b ^ k2.val := by rw [← mul_assoc a]
        _ = a * (a * (b ^ k1.val)⁻¹) * b ^ k2.val := by rw [hb_pow_mul_a]
        _ = (a * a) * (b ^ k1.val)⁻¹ * b ^ k2.val := by rw [← mul_assoc a]
        _ = 1 * (b ^ k1.val)⁻¹ * b ^ k2.val := by rw [← sq, ha2]
        _ = (b ^ k1.val)⁻¹ * b ^ k2.val := by rw [one_mul]
        _ = b ^ k2.val * (b ^ k1.val)⁻¹ := by rw [hb_comm]
        _ = b ^ (k2 - k1).val := (hb_pow_sub k2 k1).symm

  have hb_pow_inj_nat : ∀ (x y : ℕ), x < n → y < n → b ^ x = b ^ y → x = y := by
    intro x y hx hy hxy
    rcases lt_trichotomy x y with h | h | h

    · have h1 : b ^ (y - x) = 1 := by
        apply mul_right_cancel (b := b ^ x)
        calc b ^ (y - x) * b ^ x = b ^ (y - x + x) := (pow_add b (y - x) x).symm
          _ = b ^ y := by rw [Nat.sub_add_cancel h.le]
          _ = b ^ x := hxy.symm
          _ = 1 * b ^ x := (one_mul _).symm
      have h_ord : n ≤ y - x := hb_order ▸ orderOf_le_of_pow_eq_one (tsub_pos_of_lt h) h1
      omega

    · exact h

    · have h1 : b ^ (x - y) = 1 := by
        apply mul_right_cancel (b := b ^ y)
        calc b ^ (x - y) * b ^ y = b ^ (x - y + y) := (pow_add b (x - y) y).symm
          _ = b ^ x := by rw [Nat.sub_add_cancel h.le]
          _ = b ^ y := hxy
          _ = 1 * b ^ y := (one_mul _).symm
      have h_ord : n ≤ x - y := hb_order ▸ orderOf_le_of_pow_eq_one (tsub_pos_of_lt h) h1
      omega

  have hb_pow_inj : ∀ (x y : ZMod n), b ^ x.val = b ^ y.val → x = y := by
    revert hb_pow_inj_nat
    cases n

    · contradiction

    · intro h_inj x y hxy
      exact Fin.ext (h_inj x.val y.val x.isLt y.isLt hxy)

  have f_inj : Function.Injective f_map := by
    intro x y hxy
    rcases x with ⟨kx⟩ | ⟨kx⟩ <;> rcases y with ⟨ky⟩ | ⟨ky⟩

    · change b ^ kx.val = b ^ ky.val at hxy
      rw [hb_pow_inj kx ky hxy]

    · change b ^ kx.val = a * b ^ ky.val at hxy
      exfalso; exact ha (eq_mul_inv_of_mul_eq hxy.symm ▸
          H.mul_mem (H.pow_mem hb_mem _) (H.inv_mem (H.pow_mem hb_mem _)))

    · change a * b ^ kx.val = b ^ ky.val at hxy
      exfalso; exact ha (eq_mul_inv_of_mul_eq hxy ▸
          H.mul_mem (H.pow_mem hb_mem _) (H.inv_mem (H.pow_mem hb_mem _)))

    · change a * b ^ kx.val = a * b ^ ky.val at hxy
      rw [hb_pow_inj kx ky (mul_left_cancel hxy)]

  have f_surj : Function.Surjective f_map := by
    intro g
    by_cases hg : g ∈ H

    · obtain ⟨k, hk⟩ := h_b_gen g hg
      exact ⟨DihedralGroup.r k, hk.symm⟩

    · obtain ⟨h, hh, rfl⟩ := h_coset g hg
      obtain ⟨k, hk⟩ := h_b_gen h hh
      exact ⟨DihedralGroup.sr k, by change a * b ^ k.val = a * h; rw [← hk]⟩

  let f_hom : DihedralGroup n →* G :=
    { toFun := f_map
      map_one' := by change b ^ (0 : ZMod n).val = 1; rw [ZMod.val_zero, pow_zero]
      map_mul' := f_mul }
  exact ⟨MulEquiv.symm (MulEquiv.ofBijective f_hom ⟨f_inj, f_surj⟩)⟩

lemma extractDihedralStructure (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (hN : Nat.card G = 2 * n) (hn : n ≥ 2)
    (H₁ : Subgroup G)
    (hH₁_card : Nat.card H₁ = n)
    (hH₁_norm : Nat.card (Subgroup.normalizer (SetLike.coe H₁)) = 2 * n)
    (h_outside_order2 : ∀ g : G, g ∉ H₁ → g ≠ 1 → orderOf g = 2) :
    H₁.Normal ∧ H₁.index = 2 ∧ (∀ g : G, g ∉ H₁ → orderOf g = 2) := by
  refine ⟨Subgroup.normalizer_eq_top_iff.mp (Subgroup.eq_top_of_card_eq _ (hH₁_norm.trans
      hN.symm)), ?_, fun g hg ↦ h_outside_order2 g hg (fun h ↦ hg (h.symm ▸ H₁.one_mem))⟩
  apply Nat.eq_of_mul_eq_mul_right (zero_lt_two.trans_le hn)
  rw [← hN, ← hH₁_card]
  exact Subgroup.index_mul_card H₁

theorem dihedral_of_hasCyclicPartition_odd (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (hn_ge : n ≥ 3)
    (hN : Nat.card G = 2 * n)
    (h : HasCyclicPartition G [{d := n, f := 2}, {d := 2, f := 1}]) :
    Nonempty (G ≃* DihedralGroup n) := by
  obtain ⟨H_list, hLen, hProps, _, hCover⟩ := h
  obtain ⟨H0, hH0_opt, hH0_cyc, hH0_card, hH0_norm⟩ := hProps ⟨0, Nat.zero_lt_succ 1⟩
  obtain ⟨H1, hH1_opt, _, hH1_card, _⟩ := hProps ⟨1, Nat.lt_succ_self 1⟩
  haveI hH0_Normal : H0.Normal := Subgroup.normalizer_eq_top_iff.mp
    (Subgroup.eq_top_of_card_eq _ (hH0_norm.trans hN.symm))

  have h_order2 : ∀ g : G, g ∉ H0 → orderOf g = 2 := by
    intro g hg
    have hg1 : g ≠ 1 := fun h ↦ hg (h ▸ H0.one_mem)
    obtain ⟨K, ⟨i, k, HK, hHK_opt, rfl⟩, hgK⟩ := hCover g hg1
    obtain ⟨x, hx_mem, h_map_eq⟩ := Subgroup.mem_map.mp hgK
    match hi : i.val with
    | 0 =>
      rw [hi] at hHK_opt
      cases Option.some.inj (hHK_opt.symm.trans hH0_opt)
      exfalso
      exact hg (h_map_eq ▸ hH0_Normal.conj_mem x hx_mem k)
    | 1 =>
      rw [hi] at hHK_opt
      cases Option.some.inj (hHK_opt.symm.trans hH1_opt)

      have hx_ord : orderOf x = 2 := by
        have h_dvd : orderOf x ∣ 2 := by
          rw [← show Nat.card H1 = 2 from hH1_card, ← Nat.card_zpowers]
          exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx_mem)
        cases (Nat.dvd_prime Nat.prime_two).mp h_dvd with
        | inl h_one =>
          exfalso
          exact hg1 (by rw [← h_map_eq, orderOf_eq_one_iff.mp h_one, map_one])
        | inr h_two => exact h_two

      have h_ord_eq : orderOf g = orderOf x := by
        rw [← h_map_eq]
        exact orderOf_injective (MulAut.conj k).toMonoidHom (MulEquiv.injective (MulAut.conj k)) x
      rw [h_ord_eq, hx_ord]
    | d + 2 =>
      exfalso
      exact Nat.not_lt_zero d (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (hi ▸ i.isLt)))
  have hn2 : n ≥ 2 := Nat.le_trans (Nat.le_succ 2) hn_ge

  have h_dihedral :=
    extractDihedralStructure G n hN hn2 H0 hH0_card hH0_norm (fun g hg _ ↦ h_order2 g hg)
  exact dihedralRecognition G n hn2 H0 hH0_cyc hH0_card h_dihedral.2.1 h_dihedral.2.2

theorem dihedral_of_hasCyclicPartition_even (G : Type*) [Group G] [Fintype G] (n : ℕ)
    (hn_ge : n ≥ 4)
    (hN : Nat.card G = 2 * n)
    (h : HasCyclicPartition G [{d := n, f := 2}, {d := 2, f := 2}, {d := 2, f := 2}]) :
    Nonempty (G ≃* DihedralGroup n) := by
  obtain ⟨H_list, hLen, hProps, _, hCover⟩ := h
  obtain ⟨H0, hH0_opt, hH0_cyc, hH0_card, hH0_norm⟩ := hProps ⟨0, Nat.zero_lt_succ 2⟩
  obtain ⟨H1, hH1_opt, _, hH1_card, _⟩ := hProps ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
  obtain ⟨H2, hH2_opt, _, hH2_card, _⟩ := hProps ⟨2, Nat.lt_succ_self 2⟩
  haveI hH0_Normal : H0.Normal := Subgroup.normalizer_eq_top_iff.mp
    (Subgroup.eq_top_of_card_eq _ (hH0_norm.trans hN.symm))

  have h_order2 : ∀ g : G, g ∉ H0 → orderOf g = 2 := by
    intro g hg
    have hg1 : g ≠ 1 := fun h ↦ hg (h ▸ H0.one_mem)
    obtain ⟨K, ⟨i, k, HK, hHK_opt, rfl⟩, hgK⟩ := hCover g hg1
    obtain ⟨x, hx_mem, h_map_eq⟩ := Subgroup.mem_map.mp hgK

    have h_ord_x : ∀ (C : Subgroup G), Nat.card C = 2 → x ∈ C → orderOf g = 2 := by
      intro C hC hxC
      cases (Nat.dvd_prime Nat.prime_two).mp (hC ▸ (Nat.card_zpowers x).symm ▸
          Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxC)) with
      | inl h_one =>
        exfalso
        exact hg1 (by rw [← h_map_eq, orderOf_eq_one_iff.mp h_one, map_one])
      | inr h_two =>
        rw [← h_map_eq]
        exact (orderOf_injective (MulAut.conj k).toMonoidHom (MulEquiv.injective (MulAut.conj k))
            x).trans h_two
    match hi : i.val with
    | 0 =>
      rw [hi] at hHK_opt
      cases Option.some.inj (hHK_opt.symm.trans hH0_opt)
      exfalso
      exact hg (h_map_eq ▸ hH0_Normal.conj_mem x hx_mem k)
    | 1 =>
      rw [hi] at hHK_opt
      cases Option.some.inj (hHK_opt.symm.trans hH1_opt)
      exact h_ord_x H1 hH1_card hx_mem
    | 2 =>
      rw [hi] at hHK_opt
      cases Option.some.inj (hHK_opt.symm.trans hH2_opt)
      exact h_ord_x H2 hH2_card hx_mem
    | d + 3 =>
      exfalso
      exact Nat.not_lt_zero d (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ
          (Nat.lt_of_succ_lt_succ (hi ▸ i.isLt))))
  have hn2 : n ≥ 2 := Nat.le_trans (Nat.le_trans (Nat.le_succ 2) (Nat.le_succ 3)) hn_ge

  have h_dihedral :=
    extractDihedralStructure G n hN hn2 H0 hH0_card hH0_norm (fun g hg _ ↦ h_order2 g hg)
  exact dihedralRecognition G n hn2 H0 hH0_cyc hH0_card h_dihedral.2.1 h_dihedral.2.2

lemma subgroup_S4_order12_eq_A4 (H : Subgroup (Equiv.Perm (Fin 4)))
    (h_card : Nat.card H = 12) : H = alternatingGroup (Fin 4) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h_mul := Subgroup.index_mul_card H
  rw [h_card, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h_mul
  change H.index * 12 = 24 at h_mul
  omega

theorem sylow_inf_eq_bot_of_prime_card (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (P Q : Sylow p G)
    (hPQ : P ≠ Q)
    (hP_card : Nat.card (P : Subgroup G) = p) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  cases (Nat.dvd_prime hp.out).mp (hP_card ▸ Subgroup.card_dvd_of_le inf_le_left) with
  | inl h_one =>
    exact Subgroup.card_eq_one.mp h_one
  | inr hp_eq =>
    exfalso
    exact hPQ <| SetLike.coe_set_eq.mp <| Set.eq_of_subset_of_ncard_le
      (fun x hx ↦
        have h_eq : ((P : Subgroup G) ⊓ (Q : Subgroup G) : Set G) = P :=
          Set.eq_of_subset_of_ncard_le (fun y hy ↦ hy.1) (by
            change Nat.card (P : Subgroup G) ≤ Nat.card ((P : Subgroup G) ⊓ (Q : Subgroup G) :
                Subgroup G)
            rw [hP_card, hp_eq])
        (h_eq.symm ▸ hx : x ∈ ((P : Subgroup G) ⊓ (Q : Subgroup G) : Set G)).2)
      (by
        change Nat.card (Q : Subgroup G) ≤ Nat.card (P : Subgroup G)
        rw [P.card_eq_multiplicity, Q.card_eq_multiplicity])

theorem sylow3_toPermHom_ker_eq_bot_of_card_12 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 12) (h_sylow : Nat.card (Sylow 3 G) = 4) :
    (MulAction.toPermHom G (Sylow 3 G)).ker = ⊥ := by

  have h_norm_card : ∀ P : Sylow 3 G, Nat.card ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G) = 3 := fun P ↦ by
    have h_mul := Subgroup.index_mul_card ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G)
    rw [← Sylow.card_eq_index_normalizer, h_sylow, hN] at h_mul
    omega

  have h_P_card : ∀ P : Sylow 3 G, Nat.card (P : Subgroup G) = 3 := fun P ↦ by
    have h_dvd :=
      Subgroup.card_dvd_of_le (show (P : Subgroup G) ≤ (Subgroup.normalizer (SetLike.coe P)) from Subgroup.le_normalizer)
    rw [h_norm_card P] at h_dvd
    cases (Nat.dvd_prime Nat.prime_three).mp h_dvd with
    | inl h_one =>
      have h_norm_top : ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G) = ⊤ := by
        ext x
        refine ⟨fun _ ↦ Subgroup.mem_top x, fun _ ↦ by
          rw [← Sylow.coe_coe, Subgroup.mem_normalizer_iff, Subgroup.card_eq_one.mp h_one]
          exact fun y ↦ ⟨
            fun hy ↦ by rw [Subgroup.mem_bot.mp hy, mul_one, mul_inv_cancel, Subgroup.mem_bot],
            fun hy ↦
                Subgroup.mem_bot.mpr (mul_left_cancel (mul_right_cancel
                    (by rw [Subgroup.mem_bot.mp hy, mul_one, mul_inv_cancel])))
          ⟩⟩
      have h_mul := Subgroup.index_mul_card ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G)
      rw [h_norm_card P, h_norm_top, Subgroup.index_top, one_mul, hN] at h_mul
      omega
    | inr h_three =>
      exact h_three

  have h_norm_eq : ∀ P : Sylow 3 G, ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G) = P := by
    intro P

    have h_set_eq : ((P : Subgroup G) : Set G) = ((Subgroup.normalizer (SetLike.coe P)) : Set G) := by
      refine Set.eq_of_subset_of_ncard_le Subgroup.le_normalizer ?_ (Set.toFinite _)
      change Nat.card ((Subgroup.normalizer (SetLike.coe P)) : Subgroup G) ≤ Nat.card (P : Subgroup G)
      rw [h_P_card P, h_norm_card P]
    exact (SetLike.coe_set_eq.mp h_set_eq).symm

  have h_one_lt : 1 < Fintype.card (Sylow 3 G) := by
    rw [Nat.card_eq_fintype_card] at h_sylow
    omega
  obtain ⟨P, Q, hPQ⟩ := Fintype.one_lt_card_iff.mp h_one_lt
  apply eq_bot_iff.mpr
  intro g hg

  have hg_norm : ∀ S : Sylow 3 G, g ∈ (S : Subgroup G) := fun S ↦
    (h_norm_eq S) ▸
        Sylow.smul_eq_iff_mem_normalizer.mp (Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hg) S)
  exact Subgroup.mem_bot.mp (sylow_inf_eq_bot_of_prime_card G 3 P Q hPQ (h_P_card P) ▸ (⟨hg_norm P,
      hg_norm Q⟩ : g ∈ (P : Subgroup G) ⊓ (Q : Subgroup G)))

lemma iso_A4_of_card_12_sylow3_4 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 12) (h_sylow : Nat.card (Sylow 3 G) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by

  have h_inj : Function.Injective (MulAction.toPermHom G (Sylow 3 G)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (sylow3_toPermHom_ker_eq_bot_of_card_12 G hN h_sylow)

  have h_card_eq : Fintype.card (Sylow 3 G) = Fintype.card (Fin 4) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, h_sylow]

  let iso_perm : Equiv.Perm (Sylow 3 G) ≃* Equiv.Perm (Fin 4) := {
    Equiv.permCongr (Fintype.equivOfCardEq h_card_eq) with
    map_mul' := fun _ _ ↦ Equiv.ext fun _ ↦ by simp only [Equiv.toFun_as_coe, Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
  }
  let ψ_e := iso_perm.toMonoidHom.comp (MulAction.toPermHom G (Sylow 3 G))
  have hψ_e_inj : Function.Injective ψ_e := iso_perm.injective.comp h_inj

  let iso_range := MulEquiv.ofBijective ψ_e.rangeRestrict
    ⟨fun _ _ h ↦ hψ_e_inj (Subtype.ext_iff.mp h), fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩⟩

  have h_image_card : Nat.card (ψ_e.range : Subgroup (Equiv.Perm (Fin 4))) = 12 := by
    rw [← Nat.card_congr iso_range.toEquiv, hN]
  exact ⟨iso_range.trans (MulEquiv.subgroupCongr (subgroup_S4_order12_eq_A4 ψ_e.range
      h_image_card))⟩

lemma card_sylow3_of_non_normal_order3 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 12)
    (H : Subgroup G) (hH_card : Nat.card H = 3) (hH_not_normal : ¬H.Normal) :
    Nat.card (Sylow 3 G) = 4 := by
  have hn₃ : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G

  have h_div : Nat.card (Sylow 3 G) ∣ 12 := hN ▸
    (Sylow.card_eq_index_normalizer (Classical.arbitrary (Sylow 3 G))).symm ▸
      Subgroup.index_dvd_card _
  simp only [Nat.ModEq] at hn₃

  rcases show Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 from by
    have h_bound : Nat.card (Sylow 3 G) ≤ 12 := Nat.le_of_dvd (by norm_num) h_div
    interval_cases (Nat.card (Sylow 3 G)) <;> omega
  with h_one | h_four

  · exfalso
    haveI h_subsingleton : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h_one).1

    obtain ⟨P, hP⟩ := (IsPGroup.of_card
      (show Nat.card H = 3 ^ 1 by rw [hH_card]; ring)).exists_le_sylow
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'

    have hk1 : k = 1 := by
      have h1 : 3 ^ k ∣ 12 := by rw [← hk, ← hN]; exact P.1.card_subgroup_dvd_card

      have h_le_two : k ≤ 2 := by
        by_contra! hc

        have h_pow_bound : 27 ≤ 3 ^ k := calc
          27 = 3 ^ 3 := rfl
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (Nat.zero_lt_succ 2) hc
        linarith only [Nat.le_of_dvd (by norm_num) h1, h_pow_bound]
      interval_cases k

      · have h_card_le : Nat.card H ≤ Nat.card (P : Subgroup G) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hP) (Subgroup.inclusion_injective hP)
        rw [hk, pow_zero, hH_card] at h_card_le
        omega

      · rfl

      · norm_num at h1

    have hHP : H = (P : Subgroup G) := by
          apply SetLike.ext'
          apply Set.eq_of_subset_of_ncard_le hP
          show Nat.card (P : Subgroup G) ≤ Nat.card H
          rw [hk, hk1, pow_one]; omega
    exact hH_not_normal (hHP ▸ Sylow.normal_of_subsingleton P)

  · exact h_four

theorem iso_A4_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 12)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 1}]) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨H, _, hH, _⟩ := h
  obtain ⟨H₁, _, _, hH_card, hH_norm⟩ := hH ⟨1, Nat.lt_succ_self 1⟩
  refine iso_A4_of_card_12_sylow3_4 G hN (card_sylow3_of_non_normal_order3 G hN H₁ hH_card fun
      h_norm ↦ ?_)
  rw [Subgroup.normalizer_eq_top,
      Nat.card_congr (Equiv.subtypeUnivEquiv fun x ↦ Subgroup.mem_top x), hN] at hH_norm
  exact Nat.noConfusion (show 9 = 0 from congrArg (· - 3) hH_norm)

lemma card_sylow3_of_hasCyclicPartition_S4 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 24)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 4, f := 2}]) :
    Nat.card (Sylow 3 G) = 4 := by
  obtain ⟨H_list, _, hH_ex, _⟩ := h
  obtain ⟨H₁, _, _, hH₁_card, hH₁_norm⟩ := hH_ex ⟨1, by norm_num⟩
  change Nat.card H₁ = 3 at hH₁_card
  change Nat.card (Subgroup.normalizer (SetLike.coe H₁)) = 6 at hH₁_norm

  have hH₁_isPGroup : IsPGroup 3 H₁ := fun x ↦
    ⟨1, by rw [pow_one, ← orderOf_dvd_iff_pow_eq_one, ← hH₁_card]; exact orderOf_dvd_natCard x⟩
  obtain ⟨Q, hQ_le⟩ := IsPGroup.exists_le_sylow hH₁_isPGroup

  have hQ_card : Nat.card Q.toSubgroup = 3 := by
    obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq

    have hdvd_24 : 3 ^ k ∣ 24 := by
      rw [← hk, ← hN]
      exact Subgroup.card_subgroup_dvd_card Q.toSubgroup

    have hdvd_3 : 3 ∣ 3 ^ k := by
      have h := Subgroup.card_dvd_of_le hQ_le
      rw [hH₁_card, hk] at h
      exact h

    have hk1 : k = 1 := by
      have h_le : k ≤ 1 := by
        by_contra! hc
        exact (by norm_num : ¬ 9 ∣ 24) (Nat.dvd_trans (pow_dvd_pow 3 hc) hdvd_24)

      have h_pos : 1 ≤ k := by
        by_contra! hc
        have h_zero : k = 0 := by omega
        rw [h_zero, pow_zero] at hdvd_3
        revert hdvd_3
        norm_num
      omega
    rw [hk1, pow_one] at hk
    exact hk

  have hH₁_eq_Q : H₁ = Q.toSubgroup := SetLike.ext' <|
    Set.eq_of_subset_of_ncard_le hQ_le (by change Nat.card Q.toSubgroup ≤ Nat.card H₁; rw [hQ_card,
        hH₁_card])
  have h_idx := Subgroup.index_mul_card (Subgroup.normalizer (Q : Set G))
  rw [← Sylow.card_eq_index_normalizer Q] at h_idx
  have hsets : (Q : Set G) = SetLike.coe H₁ := by rw [hH₁_eq_Q, Sylow.coe_coe]
  rw [hsets, hH₁_norm, hN] at h_idx
  omega

lemma center_eq_bot_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G] (N : ℕ)
    (hN : Nat.card G = N)
    (configs : List CyclicPartitionConfig)
    (h_small : ∀ c ∈ configs, c.f * c.d < N)
    (h : HasCyclicPartition G configs) :
    Subgroup.center G = ⊥ := by
  obtain ⟨H_list, _, hH_ex, hH_disj, hH_cov⟩ := h

  let IsConj (K : Subgroup G) : Prop :=
    ∃ (i : Fin configs.length) (g : G) (Hi : Subgroup G),
      H_list[i.val]? = some Hi ∧ K = Hi.map (MulAut.conj g).toMonoidHom
  by_contra h_contra

  obtain ⟨g, hg_mem, hg_ne_one⟩ : ∃ g ∈ Subgroup.center G, g ≠ 1 := by
    by_contra! h_none
    exact h_contra <| by ext x; exact ⟨fun hx ↦ Subgroup.mem_bot.mpr (h_none x hx),
        fun hx ↦ Subgroup.mem_bot.mp hx ▸ Subgroup.one_mem _⟩
  obtain ⟨K, hK_in, hg_K⟩ := hH_cov g hg_ne_one
  obtain ⟨i, y, Hi, hHi_eq, rfl⟩ := hK_in

  have hg_Hi : g ∈ Hi := by
    obtain ⟨h_el, hh_in, hk_eq⟩ := Subgroup.mem_map.mp hg_K
    exact (calc h_el = y⁻¹ * (y * h_el * y⁻¹) * y := by group
      _ = y⁻¹ * g * y := by rw [show y * h_el * y⁻¹ = g from hk_eq]
      _ = y⁻¹ * (y * g) := by rw [mul_assoc, ← Subgroup.mem_center_iff.mp hg_mem y]
      _ = g := by group) ▸ hh_in

  have hHi_in : IsConj Hi := ⟨i, 1, Hi, hHi_eq, by
    ext z
    exact ⟨fun hz ↦ Subgroup.mem_map.mpr ⟨z, hz, by
        change 1 * z * 1⁻¹ = z
        rw [inv_one, mul_one, one_mul]⟩,
      fun hz ↦ by
        obtain ⟨y, hy, hk_eq⟩ := Subgroup.mem_map.mp hz
        change 1 * y * 1⁻¹ = z at hk_eq
        rw [inv_one, mul_one, one_mul] at hk_eq
        exact hk_eq ▸ hy⟩⟩

  have hL_eq_Hi : ∀ x : G, Hi.map (MulAut.conj x).toMonoidHom = Hi := fun x ↦ by
    have hg_L : g ∈ Hi.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨g, hg_Hi, by calc
        (MulAut.conj x) g = x * g * x⁻¹ := rfl
        _ = g * x * x⁻¹ := by rw [Subgroup.mem_center_iff.mp hg_mem x]
        _ = g := by group⟩
    by_contra h_ne
    have h_inter : g ∈ Hi.map (MulAut.conj x).toMonoidHom ⊓ Hi := ⟨hg_L, hg_Hi⟩
    rw [hH_disj _ Hi ⟨i, x, Hi, hHi_eq, rfl⟩ hHi_in h_ne] at h_inter
    exact hg_ne_one (Subgroup.mem_bot.mp h_inter)

  have h_norm_top : (Subgroup.normalizer (SetLike.coe Hi)) = ⊤ := by
    ext x; simp only [Subgroup.mem_top, iff_true, Subgroup.mem_normalizer_iff]
    exact fun n ↦ ⟨
      fun hn ↦ by rw [← hL_eq_Hi x]; exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩,
      fun hxn ↦ by rw [show n = x⁻¹ * (x * n * x⁻¹) * (x⁻¹)⁻¹ by group,
          ← hL_eq_Hi x⁻¹]; exact Subgroup.mem_map.mpr ⟨x * n * x⁻¹, hxn, rfl⟩⟩

  have h_card_norm : Nat.card (Subgroup.normalizer (SetLike.coe Hi)) = N := by
    rw [h_norm_top, ← hN]
    exact Nat.card_congr ⟨fun x ↦ x.1, fun x ↦ ⟨x, trivial⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨Hi', hHi'_eq, _, _, hHi'_norm_card⟩ := hH_ex i
  have h_lt : (configs.get i).f * (configs.get i).d < N := h_small _ (List.get_mem configs i)
  rw [← hHi'_norm_card, ← Option.some_inj.mp (hHi_eq.symm.trans hHi'_eq), h_card_norm] at h_lt
  omega

@[nolint unusedArguments]
lemma normal_order2_le_center (G : Type*) [Group G] [Fintype G]
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 2) :
    K ≤ Subgroup.center G := by
  intro x hx
  obtain ⟨k_sub, hk_gen⟩ := (isCyclic_of_prime_card hK).exists_generator
  let k := (k_sub : G)

  have hK_eq : K = Subgroup.zpowers k := by
    ext y
    constructor

    · intro hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hk_gen ⟨y, hy⟩)
      have h_eq : y = ((k_sub ^ m : K) : G) := congrArg Subtype.val hm.symm
      rw [Subgroup.coe_zpow] at h_eq
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, h_eq.symm⟩

    · intro hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact hm ▸ Subgroup.zpow_mem K k_sub.property m

  have hk_order : orderOf k = 2 :=
    (Nat.card_zpowers k).symm.trans (by rw [← hK_eq, hK])

  have hk_ne_one : k ≠ 1 := fun h ↦ Nat.noConfusion <| Nat.succ.inj <|
    show 1 = 2 by rw [← hk_order, h, orderOf_one]

  have hk2_int : k ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← hk_order, pow_orderOf_eq_one]

  have h_cases : ∀ y ∈ K, y = 1 ∨ y = k := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hK_eq ▸ hy)
    obtain ⟨c, hc⟩ := Int.even_or_odd' m
    rcases hc with rfl | rfl

    · left; rw [← hm, zpow_mul, hk2_int, one_zpow]

    · right; rw [← hm, zpow_add, zpow_mul, hk2_int, one_zpow, one_mul, zpow_one]

  have hk_center : k ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g

    rcases h_cases (g * k * g⁻¹)
        (Subgroup.Normal.conj_mem inferInstance k k_sub.property g) with h1 | hk_eq

    · exact absurd (show k = 1 by
        rw [← one_mul k, ← inv_mul_cancel g, mul_assoc, ← mul_one (g * k), ← inv_mul_cancel g]
        rw [← mul_assoc (g * k) g⁻¹ g, h1, one_mul, inv_mul_cancel]) hk_ne_one

    · exact (show g * k = (g * k * g⁻¹) * g by group).trans (by rw [hk_eq])
  rcases h_cases x hx with rfl | rfl

  · exact Subgroup.one_mem (Subgroup.center G)

  · exact hk_center

lemma card_sylow_eq_one_of_normal (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (K : Subgroup G) [K.Normal] (hK_pgroup : IsPGroup p K)
    (hK_sylow_card : Nat.card K = p ^ Nat.factorization (Nat.card G) p) :
    Nat.card (Sylow p G) = 1 := by
  obtain ⟨P, hKP⟩ := hK_pgroup.exists_le_sylow

  have hP : K = ↑P := SetLike.ext' <| Set.eq_of_subset_of_ncard_le hKP
    (hK_sylow_card.trans P.card_eq_multiplicity.symm).ge
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  exact ⟨P, fun Q ↦ by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
    rw [Sylow.smul_eq_iff_mem_normalizer, ← Sylow.coe_coe, ← hP, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g⟩

lemma not_normal_order6_of_card_sylow3_4 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 24) (h_sylow : Nat.card (Sylow 3 G) = 4)
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 6) : False := by

  obtain ⟨Q, hQ⟩ := Fintype.card_eq_one_iff.mp <| show Fintype.card (Sylow 3 K) = 1 by
    have h_dvd : Nat.card (Sylow 3 K) ∣ 6 := by
      rw [Nat.card_congr (Sylow.equivQuotientNormalizer _), ← hK]
      exact Subgroup.card_quotient_dvd_card (Subgroup.normalizer (SetLike.coe (Classical.arbitrary (Sylow 3 K) : Subgroup
          K)))
    have h_mod : Nat.card (Sylow 3 K) % 3 = 1 := card_sylow_modEq_one 3 K
    rw [← Nat.card_eq_fintype_card (α := Sylow 3 K)]
    have : Nat.card (Sylow 3 K) ≠ 4 := fun h ↦ by obtain ⟨k, hk⟩ := h_dvd; rw [h] at hk; omega
    have : Nat.card (Sylow 3 K) ≤ 6 := Nat.le_of_dvd (by norm_num) h_dvd
    omega
  haveI : (Q : Subgroup K).Normal := ⟨fun n hn g ↦
    (Sylow.smul_eq_iff_mem_normalizer.mp (show g • Q = Q from hQ (g • Q))) n |>.mp hn⟩
  haveI : (Q : Subgroup K).Characteristic := Sylow.characteristic_of_normal Q inferInstance
  haveI : (Subgroup.map K.subtype (Q : Subgroup K)).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  set QG := Subgroup.map K.subtype (Q : Subgroup K)

  have hQG_card : Nat.card QG = 3 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm.toEquiv,
        Q.card_eq_multiplicity, hK,
        Nat.factorization_eq_one (m := 2) rfl Nat.prime_three (by norm_num),
        pow_one]

  obtain ⟨P, hP⟩ := (show IsPGroup 3 QG by rw [IsPGroup.iff_card]; exact ⟨1, by rw [hQG_card,
      pow_one]⟩).exists_le_sylow

  have h_card_eq : Nat.card QG = Nat.card (P : Subgroup G) := by
    rw [hQG_card, P.card_eq_multiplicity, hN,
        Nat.factorization_eq_one (m := 8) rfl Nat.prime_three (by norm_num),
        pow_one]
  haveI : (P : Subgroup G).Normal :=
    (SetLike.ext' <| Set.eq_of_subset_of_ncard_le hP h_card_eq.ge : QG = ↑P) ▸ inferInstance

  have h_sylow_one : Nat.card (Sylow 3 G) = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
    exact ⟨P, fun R ↦ by
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P R
      rw [Sylow.smul_eq_iff_mem_normalizer, ← Sylow.coe_coe, P.normalizer_eq_top]
      exact Subgroup.mem_top g⟩
  omega

lemma toPermHom_injective_of_card_24 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 24)
    (h_sylow : Nat.card (Sylow 3 G) = 4)
    (h_center : Subgroup.center G = ⊥) :
    Function.Injective (MulAction.toPermHom G (Sylow 3 G)) := by
  set K := (MulAction.toPermHom G (Sylow 3 G)).ker
  have P : Sylow 3 G := Classical.arbitrary _

  have hK_dvd : Nat.card K ∣ 6 :=
    (show Nat.card (Subgroup.normalizer (SetLike.coe P)) = 6 from
      (show 4 * Nat.card (Subgroup.normalizer (SetLike.coe P)) = 24 → Nat.card (Subgroup.normalizer (SetLike.coe P)) = 6 by intros; omega)
        (show 4 * Nat.card (Subgroup.normalizer (SetLike.coe P)) = 24 by
          rw [← h_sylow, Sylow.card_eq_index_normalizer P, ← hN]
          exact (Subgroup.normalizer (SetLike.coe P)).index_mul_card)
    ) ▸ Subgroup.card_dvd_of_le (fun _ hg ↦
        Sylow.smul_eq_iff_mem_normalizer.mp (Equiv.Perm.ext_iff.mp (MonoidHom.mem_ker.mp hg) P))

  have hK_one : Nat.card K = 1 :=
    (show Nat.card K ≤ 6 → Nat.card K ≠ 0 → Nat.card K ≠ 2 → Nat.card K ≠ 3 → Nat.card K ≠ 4 →
        Nat.card K ≠ 5 → Nat.card K ≠ 6 → Nat.card K = 1 by intros; omega)
      (Nat.le_of_dvd (by norm_num) hK_dvd)
      (fun h ↦ by rw [h] at hK_dvd; revert hK_dvd; norm_num)
      (fun h2 ↦
        absurd (Nat.card_eq_one_iff_exists.mpr ⟨(1 : K), fun x ↦
          Subtype.ext (Subgroup.mem_bot.mp (
            show x.val ∈ (⊥ : Subgroup G) by
              rw [← eq_bot_iff.mpr (le_trans (normal_order2_le_center G K h2) (le_of_eq h_center))]
              exact x.property
          ))⟩)
          (by rw [h2]; norm_num))
      (fun h3 ↦
        absurd (card_sylow_eq_one_of_normal G 3 K (IsPGroup.iff_card.mpr ⟨(1 : Nat), by rw [h3,
            pow_one]⟩)
          (by rw [hN, Nat.factorization_eq_one (m := 8) rfl Nat.prime_three (by norm_num), pow_one,
              h3]))
          (show Nat.card (Sylow 3 G) ≠ 1 by rw [h_sylow]; norm_num))
      (fun h ↦ by rw [h] at hK_dvd; revert hK_dvd; norm_num)
      (fun h ↦ by rw [h] at hK_dvd; revert hK_dvd; norm_num)
      (fun h6 ↦ not_normal_order6_of_card_sylow3_4 G hN h_sylow K h6)
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  exact fun x hx ↦
    show x = 1 from congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (
      show orderOf (⟨x, hx⟩ : K) ∣ 1 by rw [← hK_one]; exact orderOf_dvd_natCard (⟨x, hx⟩ : K)
    )))

theorem iso_S4_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 24)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 4, f := 2}]) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  have h_sylow : Nat.card (Sylow 3 G) = 4 := card_sylow3_of_hasCyclicPartition_S4 G hN h

  have h_center : Subgroup.center G = ⊥ := center_eq_bot_of_hasCyclicPartition G 24 hN _
    (fun c hc ↦ by
      simp only [List.mem_cons, List.mem_nil_iff] at hc
      rcases hc with rfl | rfl | rfl | h_false
      · norm_num
      · norm_num
      · norm_num
      · exact nomatch h_false) h

  let e :=
    Fintype.equivOfCardEq
        (show Fintype.card (Sylow 3 G) = Fintype.card (Fin 4) by rw [← Nat.card_eq_fintype_card,
            h_sylow, Fintype.card_fin])
  let phi := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 3 G))
  exact ⟨MulEquiv.ofBijective phi ((Fintype.bijective_iff_injective_and_card phi).mpr
    ⟨e.permCongrHom.injective.comp (toPermHom_injective_of_card_24 G hN h_sylow h_center),

    show Fintype.card G = Fintype.card (Equiv.Perm (Fin 4)) by
      rw [← Nat.card_eq_fintype_card, hN,
        Fintype.card_perm, Fintype.card_fin]
      norm_num⟩)⟩

lemma orderOf_mem_of_hasCyclicPartition_A5 (G : Type*) [Group G] [Fintype G]
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}])
    (x : G) (hx : x ≠ 1) : orderOf x ∈ ({2, 3, 5} : Finset ℕ) := by
  obtain ⟨_, -, hconfigs, -, hall⟩ := h
  obtain ⟨_, ⟨i, _, Hi, hHi, rfl⟩, hxK⟩ := hall x hx
  obtain ⟨y, hy_mem, hxy⟩ := Subgroup.mem_map.mp hxK
  obtain ⟨_, hHi', _, hCard, _⟩ := hconfigs i
  cases Option.some.inj (hHi.symm.trans hHi')

  have h_div : orderOf x ∣ Nat.card Hi := by
    rw [← hxy, orderOf_dvd_iff_pow_eq_one, ← map_pow]
    rw [show y ^ Nat.card Hi = 1 from congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp
        (orderOf_dvd_natCard (⟨y, hy_mem⟩ : Hi)))]
    exact map_one _
  have hx_ord : orderOf x ≠ 1 := mt orderOf_eq_one_iff.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases i with ⟨_ | _ | _ | i_val, hi⟩

  · rw [show Nat.card Hi = 2 from hCard] at h_div
    exact Or.inl (((Nat.dvd_prime (by norm_num)).mp h_div).resolve_left hx_ord)

  · rw [show Nat.card Hi = 3 from hCard] at h_div
    exact Or.inr (Or.inl (((Nat.dvd_prime (by norm_num)).mp h_div).resolve_left hx_ord))

  · rw [show Nat.card Hi = 5 from hCard] at h_div
    exact Or.inr (Or.inr (((Nat.dvd_prime (by norm_num)).mp h_div).resolve_left hx_ord))

  · revert hi; simp only [List.length_cons, List.length_nil]; omega

lemma card_sylow5_of_hasCyclicPartition_A5 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}]) :
    Nat.card (Sylow 5 G) = 6 := by
  obtain ⟨_, -, hconfigs, -, _⟩ := h
  obtain ⟨H₂, -, -, hH₂_card, hH₂_norm_card⟩ := hconfigs ⟨2, by norm_num⟩

  obtain ⟨P, hP_le⟩ := (IsPGroup.iff_card.mpr ⟨1,
      by rw [hH₂_card]; rfl⟩ : IsPGroup 5 H₂).exists_le_sylow

  have hP_eq : (P : Subgroup G) = H₂ := by
    apply (Subgroup.eq_of_le_of_card_ge hP_le ?_).symm
    rw [hH₂_card, P.card_eq_multiplicity, hN,
        Nat.factorization_eq_one (m := 12) rfl Nat.prime_five (by norm_num)]
    norm_num
  rw [P.card_eq_index_normalizer, ← Sylow.coe_coe, hP_eq]
  have h_mul := (Subgroup.normalizer (SetLike.coe H₂)).index_mul_card
  rw [hH₂_norm_card, hN] at h_mul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h_mul

lemma card_sylow3_of_hasCyclicPartition_A5 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}]) :
    Nat.card (Sylow 3 G) = 10 := by
  obtain ⟨_, -, hconfigs, -, _⟩ := h
  obtain ⟨H₁, -, -, hH₁_card, hH₁_norm_card⟩ := hconfigs ⟨1, by norm_num⟩

  obtain ⟨P, hP_le⟩ := (IsPGroup.iff_card.mpr ⟨1,
      by rw [hH₁_card]; rfl⟩ : IsPGroup 3 H₁).exists_le_sylow

  have hP_eq : (P : Subgroup G) = H₁ := by
    apply (Subgroup.eq_of_le_of_card_ge hP_le ?_).symm
    rw [hH₁_card, P.card_eq_multiplicity, hN,
        Nat.factorization_eq_one (m := 20) rfl Nat.prime_three (by norm_num)]
    norm_num
  rw [P.card_eq_index_normalizer, ← Sylow.coe_coe, hP_eq]
  have h_mul := (Subgroup.normalizer (SetLike.coe H₁)).index_mul_card
  rw [hH₁_norm_card, hN] at h_mul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h_mul

lemma sylow_le_normal_of_coprime_index (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [Fact (Nat.Prime p)] (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime N.index p) (P : Sylow p G) : (P : Subgroup G) ≤ N := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (IsPGroup.map P.2 (QuotientGroup.mk' N))
  rcases n with _ | n

  · intro x hx
    obtain ⟨_⟩ := Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])
    have h_sub : Subsingleton ↥(P.map (QuotientGroup.mk' N)) := inferInstance
    exact QuotientGroup.ker_mk' N ▸ MonoidHom.mem_ker.mpr (congr_arg Subtype.val <| match h_sub with
      | ⟨h_allEq⟩ => h_allEq (⟨QuotientGroup.mk' N x,
          Subgroup.mem_map_of_mem _ hx⟩ : ↥(P.map (QuotientGroup.mk' N))) 1)

  · exact nomatch ((Fact.out : Nat.Prime p).not_dvd_one ((hcop : Nat.gcd N.index p = 1) ▸
      Nat.dvd_gcd (dvd_trans (dvd_pow_self p (Nat.succ_ne_zero n))
        (hn ▸ Subgroup.card_subgroup_dvd_card (P.map (QuotientGroup.mk' N)))) (dvd_refl p)))

lemma card_elements_orderOf_prime (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hp_pow : Nat.factorization (Nat.card G) p = 1) :
    Fintype.card {x : G | orderOf x = p} = Nat.card (Sylow p G) * (p - 1) := by

  have h_card : ∀ P : Sylow p G, Nat.card (P : Subgroup G) = p := fun P ↦ by
    rw [P.card_eq_multiplicity, hp_pow, pow_one]

  let f : (Σ P : Sylow p G, {x : G // x ∈ (P : Subgroup G) ∧ x ≠ 1}) → {x : G | orderOf x = p} :=
    fun ⟨P, x, hxP, hx1⟩ ↦ ⟨x, by
      have h_le := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxP)
      rw [h_card P, Nat.card_eq_fintype_card, Fintype.card_zpowers] at h_le
      cases Nat.dvd_prime hp.out |>.mp h_le with
      | inl h => exact absurd (orderOf_eq_one_iff.mp h) hx1
      | inr h => exact h⟩

  have h_bij : Function.Bijective f := ⟨
    fun ⟨P, x, hxP, hx1⟩ ⟨Q, y, hyQ, hy1⟩ hxy ↦ by
      cases Subtype.ext_iff.mp hxy
      by_cases hPQ : P = Q

      · cases hPQ; rfl

      · exact absurd (Subgroup.mem_bot.mp <|
          (sylow_inf_eq_bot_of_prime_card G p P Q hPQ (h_card P) ▸ ⟨hxP,
              hyQ⟩ : x ∈ (⊥ : Subgroup G))) hx1,
    fun ⟨x, hx⟩ ↦ by
      have ⟨P, hP⟩ := (IsPGroup.iff_card.mpr ⟨1, by
        rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hx, pow_one]⟩ :
          IsPGroup p (Subgroup.zpowers x)).exists_le_sylow
      exact ⟨⟨P, x, hP (Subgroup.mem_zpowers x),
          fun h ↦ hp.out.ne_one (by
            change orderOf x = p at hx
            rw [h, orderOf_one] at hx
            exact hx.symm)⟩, rfl⟩
  ⟩
  haveI (P : Sylow p G) : Fintype {x : G // x ∈ (P : Subgroup G) ∧ x ≠ 1} := Fintype.ofFinite _
  change Fintype.card {x : G | orderOf x = p} = _
  rw [← Fintype.card_congr (Equiv.ofBijective f h_bij), Fintype.card_sigma]

  have h_card_P : ∀ P : Sylow p G,
      Fintype.card {x : G // x ∈ (P : Subgroup G) ∧ x ≠ 1} = p - 1 := fun P ↦ by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ↥(((P : Subgroup G) : Set G) \ {1}) = p - 1
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem P.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (fun x ↦ x - 1) (h_card P)
  simp only [h_card_P, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  rw [← Nat.card_eq_fintype_card]

lemma mem_of_orderOf_prime_sylow_le (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [Fact (Nat.Prime p)]
    (N : Subgroup G)
    (h : ∀ P : Sylow p G, (P : Subgroup G) ≤ N)
    (x : G) (hx : orderOf x = p) : x ∈ N := by

  have hH : IsPGroup p (Subgroup.zpowers x) := IsPGroup.iff_card.mpr ⟨1, by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hx, pow_one]⟩
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  exact h P (hP (Subgroup.mem_zpowers x))

lemma exists_orderOf_15_of_card_15 (H : Type*) [Group H] [Fintype H]
    (hH : Nat.card H = 15) : ∃ x : H, orderOf x = 15 := by
  let P := Classical.arbitrary (Sylow 3 H)

  have hP_card_eq_one : Nat.card (Sylow 3 H) = 1 := by
    have h1 : Nat.card (Sylow 3 H) ∣ 15 :=
      hH ▸ (Nat.card_congr (Sylow.equivQuotientNormalizer P)).symm ▸
          Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card (Sylow 3 H) % 3 = 1 := card_sylow_modEq_one 3 H
    revert h1 h2
    exact match Nat.card (Sylow 3 H) with
    | 1 => fun _ _ ↦ rfl
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => fun h1 h2 ↦
        by revert h1 h2; norm_num
    | c + 16 => fun h1 _ ↦ by have := Nat.le_of_dvd (by norm_num) h1; omega

  have hP_sub : Subsingleton (Sylow 3 H) := (Nat.card_eq_one_iff_unique.mp hP_card_eq_one).1
  have hP_norm : (P : Subgroup H).Normal :=
    ⟨fun n hn g ↦
        (match hP_sub with | ⟨h_allEq⟩ => h_allEq (g • P) P) ▸
            Subgroup.mem_map_of_mem _ hn⟩
  let Q := Classical.arbitrary (Sylow 5 H)

  have hQ_card_eq_one : Nat.card (Sylow 5 H) = 1 := by
    have h1 : Nat.card (Sylow 5 H) ∣ 15 :=
      hH ▸ (Nat.card_congr (Sylow.equivQuotientNormalizer Q)).symm ▸
          Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card (Sylow 5 H) % 5 = 1 := card_sylow_modEq_one 5 H
    revert h1 h2
    exact match Nat.card (Sylow 5 H) with
    | 1 => fun _ _ ↦ rfl
    | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => fun h1 h2 ↦
        by revert h1 h2; norm_num
    | c + 16 => fun h1 _ ↦ by have := Nat.le_of_dvd (by norm_num) h1; omega

  have hQ_sub : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hQ_card_eq_one).1
  have hQ_norm : (Q : Subgroup H).Normal :=
    ⟨fun n hn g ↦
        (match hQ_sub with | ⟨h_allEq⟩ => h_allEq (g • Q) Q) ▸
            Subgroup.mem_map_of_mem _ hn⟩

  have hP_card : Nat.card (P : Subgroup H) = 3 := by
    convert P.card_eq_multiplicity
    rw [hH, Nat.factorization_eq_one (m := 5) rfl Nat.prime_three (by norm_num), pow_one]

  have hQ_card : Nat.card (Q : Subgroup H) = 5 := by
    convert Q.card_eq_multiplicity
    rw [hH, Nat.factorization_eq_one (m := 3) rfl Nat.prime_five (by norm_num), pow_one]
  obtain ⟨p', hp_gen⟩ := (isCyclic_of_prime_card hP_card).exists_generator
  obtain ⟨q', hq_gen⟩ := (isCyclic_of_prime_card hQ_card).exists_generator

  have hp_order_H : orderOf (p' : H) = 3 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hp_gen, hP_card]

  have hq_order_H : orderOf (q' : H) = 5 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hq_gen, hQ_card]

  have hpq_comm : Commute (p' : H) (q' : H) := by
    have h_bot : (P : Subgroup H) ⊓ Q = ⊥ := by
      rw [← Subgroup.card_eq_one]

      have h :=
        Nat.dvd_gcd (Subgroup.card_dvd_of_le (K:=(P:Subgroup H)) inf_le_left)
            (Subgroup.card_dvd_of_le (K:=(Q:Subgroup H)) inf_le_right)
      revert h; rw [hP_card, hQ_card]; exact Nat.eq_one_of_dvd_one

    have hpq_eq_one : (p' : H) * q' * (p' : H)⁻¹ * (q' : H)⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← h_bot, Subgroup.mem_inf]
      exact ⟨(show (p':H) * ((q':H) * (p':H)⁻¹ * (q':H)⁻¹) = (p':H) * q' * (p':H)⁻¹ * (q':H)⁻¹ by
        group) ▸
              P.mul_mem p'.2 (hP_norm.conj_mem (p':H)⁻¹ (P.inv_mem p'.2) (q':H)),
            (show ((p':H) * q' * (p':H)⁻¹) * (q':H)⁻¹ = (p':H) * q' * (p':H)⁻¹ * (q':H)⁻¹ by group)
                ▸
              Q.mul_mem (hQ_norm.conj_mem (q':H) q'.2 (p':H)) (Q.inv_mem q'.2)⟩
    rw [commute_iff_eq]
    calc (p' : H) * q'
      _ = ((p' : H) * q' * (p' : H)⁻¹ * (q' : H)⁻¹) * ((q' : H) * (p' : H)) := by group
      _ = (q' : H) * (p' : H) := by rw [hpq_eq_one, one_mul]
  use (p' : H) * (q' : H)
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hpq_comm]

  · rw [hp_order_H, hq_order_H]

  · rw [hp_order_H, hq_order_H]; norm_num

lemma card_ge_45_of_orders_3_and_5 (G : Type*) [Group G] [Fintype G]
    (hG : Nat.card G = 60)
    (h_n3 : Nat.card (Sylow 3 G) = 10) (h_n5 : Nat.card (Sylow 5 G) = 6)
    (N : Subgroup G)
    (h3 : ∀ x : G, orderOf x = 3 → x ∈ N)
    (h5 : ∀ x : G, orderOf x = 5 → x ∈ N) :
    45 ≤ Nat.card N := by

  have hc3 : Set.ncard {x : G | orderOf x = 3} = 20 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      card_elements_orderOf_prime G 3 (by rw [hG,
          Nat.factorization_eq_one (m := 20) rfl Nat.prime_three (by norm_num)]), h_n3]

  have hc5 : Set.ncard {x : G | orderOf x = 5} = 24 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      card_elements_orderOf_prime G 5 (by rw [hG,
          Nat.factorization_eq_one (m := 12) rfl Nat.prime_five (by norm_num)]), h_n5]

  have hN : {x : G | orderOf x = 3} ∪ {x : G | orderOf x = 5} ∪ {1} ⊆ (N : Set G) :=
    Set.union_subset (Set.union_subset h3 h5) (Set.singleton_subset_iff.mpr N.one_mem)
  have h_le := Set.ncard_le_ncard hN (Set.toFinite _)
  rw [Set.ncard_union_eq
      (by simp only [Set.disjoint_singleton_right]; norm_num)
      (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq
      (by simp only [Set.disjoint_left, Set.mem_setOf_eq]
          intro x hx; rw [hx]; norm_num)
      (Set.toFinite _) (Set.toFinite _),
    hc3, hc5, Set.ncard_singleton] at h_le
  exact h_le

lemma not_normal_of_card_lt (G : Type*) [Group G] [Fintype G]
    (p : ℕ) [Fact (Nat.Prime p)]
    (hp : Nat.factorization (Nat.card G) p = 1)
    (N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime N.index p)
    (h_count : Nat.card (Sylow p G) * (p - 1) + 1 > Nat.card N) : False := by

  have h_sub : {x : G | orderOf x = p} ∪ {1} ⊆ (N : Set G) :=Set.union_subset
      (mem_of_orderOf_prime_sylow_le G p N (sylow_le_normal_of_coprime_index G p N hcop))
          (Set.singleton_subset_iff.mpr N.one_mem)
  have h_le := Set.ncard_le_ncard h_sub (Set.toFinite _)
  rw [Set.ncard_union_eq
      (by simp only [Set.disjoint_singleton_right, Set.mem_setOf_eq, orderOf_one]
          exact (Nat.Prime.ne_one Fact.out).symm)
      (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    card_elements_orderOf_prime G p hp,
    Set.ncard_singleton] at h_le
  change Nat.card (Sylow p G) * (p - 1) + 1 ≤ Nat.card N at h_le
  linarith only [h_count, h_le]

lemma isSimple_of_hasCyclicPartition_A5 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}]) :
    IsSimpleGroup G := by
  have h_n5 : Nat.card (Sylow 5 G) = 6 := card_sylow5_of_hasCyclicPartition_A5 G hN h
  have h_n3 : Nat.card (Sylow 3 G) = 10 := card_sylow3_of_hasCyclicPartition_A5 G hN h
  haveI : Nontrivial G := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hN]; norm_num
  exact IsSimpleGroup.mk (fun N hN_normal ↦ by
    by_contra h_contra
    have hN_ne_bot : N ≠ ⊥ := fun h_eq ↦ h_contra (Or.inl h_eq)
    have hN_card_div : Nat.card N ∣ 60 := hN ▸ Subgroup.card_subgroup_dvd_card N

    have hN_card_gt1 : 1 < Nat.card N :=
      lt_of_le_of_ne (Nat.pos_of_dvd_of_pos hN_card_div (by norm_num))
        (fun h_le ↦ h_contra (Or.inl (Subgroup.eq_bot_of_card_eq N h_le.symm)))

    have hN_card_lt60 : Nat.card N < 60 :=
      lt_of_le_of_ne (Nat.le_of_dvd (by norm_num) hN_card_div)
        (fun h_ge ↦ h_contra (Or.inr (Subgroup.eq_top_of_card_eq N (hN.symm ▸ h_ge))))

    have hcases : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4 ∨ Nat.card N = 5 ∨
        Nat.card N = 6 ∨ Nat.card N = 10 ∨ Nat.card N = 12 ∨ Nat.card N = 15 ∨
        Nat.card N = 20 ∨ Nat.card N = 30 ∨
        (7 ≤ Nat.card N ∧ Nat.card N ≤ 9) ∨
        Nat.card N = 11 ∨
        (13 ≤ Nat.card N ∧ Nat.card N ≤ 14) ∨
        (16 ≤ Nat.card N ∧ Nat.card N ≤ 19) ∨
        (21 ≤ Nat.card N ∧ Nat.card N ≤ 29) ∨
        (31 ≤ Nat.card N ∧ Nat.card N ≤ 59) := by omega

    have h_fac3 : (Nat.factorization 60) 3 = 1 := Nat.factorization_eq_one (m :=
      20) rfl Nat.prime_three (by norm_num)

    have h_fac5 : (Nat.factorization 60) 5 = 1 := Nat.factorization_eq_one (m :=
      12) rfl Nat.prime_five (by norm_num)

    rcases hcases with h2 | h3 | h4 | h5 | h6 | h10 | h12 | h15 | h20 | h30 |
        h7_9 | h11 | h13_14 | h16_19 | h21_29 | h31_59

    · exact hN_ne_bot (le_bot_iff.mp (center_eq_bot_of_hasCyclicPartition G 60 hN _
        (by intro c hc; simp only [List.mem_cons, List.mem_nil_iff,
            or_false] at hc; rcases hc with rfl | rfl | rfl <;> norm_num) h ▸
                normal_order2_le_center G N h2))

    · exact absurd (card_sylow_eq_one_of_normal G 3 N
        (fun x ↦ ⟨1, by rw [← h3, pow_one,
            ← orderOf_dvd_iff_pow_eq_one]; exact orderOf_dvd_natCard _⟩)
        (by rw [h3, hN, h_fac3, pow_one]))
        (by rw [h_n3]; norm_num)

    · haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
      obtain ⟨g, hg⟩ := exists_orderOf_15_of_card_15 (G ⧸ N) (by rw [← Subgroup.index_eq_card,
          Nat.eq_of_mul_eq_mul_right (by rw [h4]; norm_num)
              (show N.index * Nat.card N = 15 * Nat.card N by rw [Subgroup.index_mul_card N, hN,
                  h4])])
      obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective N g

      have h15 : 15 ∣ orderOf g' := by
        rw [← hg, ← hg']; exact orderOf_map_dvd (QuotientGroup.mk' N) g'

      have hmem :=
        orderOf_mem_of_hasCyclicPartition_A5 G h g'
            (by rintro rfl; change (1 : G ⧸ N) = g at hg'; rw [← hg',
                orderOf_one] at hg; exact absurd hg (by norm_num))
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h2 | h3 | h5

      · rw [h2] at h15; exact absurd h15 (by norm_num)

      · rw [h3] at h15; exact absurd h15 (by norm_num)

      · rw [h5] at h15; exact absurd h15 (by norm_num)

    · exact absurd (card_sylow_eq_one_of_normal G 5 N
        (fun x ↦ ⟨1, by rw [← h5, pow_one,
            ← orderOf_dvd_iff_pow_eq_one]; exact orderOf_dvd_natCard _⟩)
        (by rw [h5, hN, h_fac5, pow_one]))
        (by rw [h_n5]; norm_num)

    · exact not_normal_of_card_lt G 3 (by rw [hN, h_fac3]) N
        (by rw [Nat.eq_of_mul_eq_mul_right (by rw [h6]; norm_num)
            (show N.index * Nat.card N = 10 * Nat.card N by rw [Subgroup.index_mul_card N, hN,
                h6])]; norm_num)
        (by rw [h_n3, h6]; norm_num)

    · exact not_normal_of_card_lt G 5 (by rw [hN, h_fac5]) N
        (by rw [Nat.eq_of_mul_eq_mul_right (by rw [h10]; norm_num)
            (show N.index * Nat.card N = 6 * Nat.card N by rw [Subgroup.index_mul_card N, hN,
                h10])]; norm_num)
        (by rw [h_n5, h10]; norm_num)

    · exact not_normal_of_card_lt G 3 (by rw [hN, h_fac3]) N
        (by rw [Nat.eq_of_mul_eq_mul_right (by rw [h12]; norm_num)
            (show N.index * Nat.card N = 5 * Nat.card N by rw [Subgroup.index_mul_card N, hN,
                h12])]; norm_num)
        (by rw [h_n3, h12]; norm_num)

    · have hidx : N.index = 4 :=
      Nat.eq_of_mul_eq_mul_right (by rw [h15]; norm_num)
          (show N.index * Nat.card N = 4 * Nat.card N by rw [Subgroup.index_mul_card N, hN, h15])
      exact absurd (card_ge_45_of_orders_3_and_5 G hN h_n3 h_n5 N
        (fun x hx ↦ mem_of_orderOf_prime_sylow_le G 3 N
          (fun P ↦ sylow_le_normal_of_coprime_index G 3 N (by rw [hidx]; norm_num) P) x hx)
        (fun x hx ↦ mem_of_orderOf_prime_sylow_le G 5 N
          (fun P ↦ sylow_le_normal_of_coprime_index G 5 N (by rw [hidx]; norm_num) P) x hx))
        (by rw [h15]; norm_num)

    · exact not_normal_of_card_lt G 5 (by rw [hN, h_fac5]) N
        (by rw [Nat.eq_of_mul_eq_mul_right (by rw [h20]; norm_num)
            (show N.index * Nat.card N = 3 * Nat.card N by rw [Subgroup.index_mul_card N, hN,
                h20])]; norm_num)
        (by rw [h_n5, h20]; norm_num)

    · have hidx : N.index = 2 :=
      Nat.eq_of_mul_eq_mul_right (by rw [h30]; norm_num)
          (show N.index * Nat.card N = 2 * Nat.card N by rw [Subgroup.index_mul_card N, hN, h30])
      exact absurd (card_ge_45_of_orders_3_and_5 G hN h_n3 h_n5 N
        (fun x hx ↦ mem_of_orderOf_prime_sylow_le G 3 N
          (fun P ↦ sylow_le_normal_of_coprime_index G 3 N (by rw [hidx]; norm_num) P) x hx)
        (fun x hx ↦ mem_of_orderOf_prime_sylow_le G 5 N
          (fun P ↦ sylow_le_normal_of_coprime_index G 5 N (by rw [hidx]; norm_num) P) x hx))
        (by rw [h30]; norm_num)

    · rcases (by omega : Nat.card N = 7 ∨ Nat.card N = 8 ∨ Nat.card N = 9) with
        h | h | h <;>
        (rw [h] at hN_card_div; exact absurd hN_card_div (by norm_num))

    · obtain h := (by omega : Nat.card N = 11)
      rw [h] at hN_card_div
      exact absurd hN_card_div (by norm_num)

    · rcases (by omega : Nat.card N = 13 ∨ Nat.card N = 14) with
        h | h <;>
        (rw [h] at hN_card_div; exact absurd hN_card_div (by norm_num))

    · rcases (by omega : Nat.card N = 16 ∨ Nat.card N = 17 ∨
        Nat.card N = 18 ∨ Nat.card N = 19) with
        h | h | h | h <;>
        (rw [h] at hN_card_div; exact absurd hN_card_div (by norm_num))

    · rcases (by omega : Nat.card N = 21 ∨ Nat.card N = 22 ∨
        Nat.card N = 23 ∨ Nat.card N = 24 ∨ Nat.card N = 25 ∨
        Nat.card N = 26 ∨ Nat.card N = 27 ∨ Nat.card N = 28 ∨
        Nat.card N = 29) with
        h | h | h | h | h | h | h | h | h <;>
        (rw [h] at hN_card_div
         exact absurd hN_card_div (by norm_num))

    · rcases h31_59 with ⟨h31, _⟩
      obtain ⟨k, hk⟩ := hN_card_div

      have h_lt : k < 2 := by
        by_contra! h
        have := Nat.mul_le_mul h31 h
        rw [← hk] at this
        exact absurd this (by norm_num)
      have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with rfl | rfl

      · rw [mul_zero] at hk; exact absurd hk (by norm_num)

      · rw [mul_one] at hk; exact absurd hk.symm hN_card_lt60.ne)

lemma exists_normal_complement_of_sylow2_15 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (h_n2 : Nat.card (Sylow 2 G) = 15) :
    ∃ K : Subgroup G, K.Normal ∧ Nat.card K = 15 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := Sylow.nonempty

  have h_centralizer : (Subgroup.normalizer (SetLike.coe P)) ≤ Subgroup.centralizer (P : Subgroup G) := fun x hx y hy ↦
    haveI := Fintype.ofFinite (Subgroup.normalizer (SetLike.coe P))
    (Subtype.ext_iff.mp ((IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (show Nat.card (Subgroup.normalizer (SetLike.coe P)) = 2 ^ 2 by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.normalizer (SetLike.coe P))
        rw [← Nat.card_congr (Sylow.equivQuotientNormalizer P), h_n2, hN] at this; omega
      )).is_comm.comm ⟨x, hx⟩ ⟨y, Subgroup.le_normalizer hy⟩)).symm
  let K := MonoidHom.ker (MonoidHom.transferSylow P h_centralizer)

  have hK_comp : K.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P h_centralizer
  exact ⟨K, MonoidHom.normal_ker _, by
    have h_mul := hK_comp.card_mul_card
    change Nat.card K * Nat.card (P : Subgroup G) = Nat.card G at h_mul
    rw [Sylow.card_eq_multiplicity P, hN,
        Nat.factorization_eq_two (m := 15) rfl Nat.prime_two (by norm_num)] at h_mul
    omega⟩

lemma card_sylow2_ne_one_of_simple_60 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (hSimple : IsSimpleGroup G) :
    Nat.card (Sylow 2 G) ≠ 1 := by
  intro h_card
  obtain ⟨P, hP⟩ := Nat.card_eq_one_iff_exists.mp h_card

  have hP_normal : (P : Subgroup G).Normal :=
    ⟨fun n hn g ↦ hP (g • P) ▸ Set.mem_smul_set.mpr ⟨n, hn, rfl⟩⟩

  have hP_card : Nat.card (P : Subgroup G) = 4 := by
    rw [Sylow.card_eq_multiplicity P, hN,
        Nat.factorization_eq_two (m := 15) rfl Nat.prime_two (by norm_num)]
    norm_num
  rcases Subgroup.Normal.eq_bot_or_eq_top hP_normal with h_bot | h_top

  · rw [h_bot,
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y ↦ Subtype.ext (by rw [Subgroup.mem_bot.mp x.2,
          Subgroup.mem_bot.mp y.2])⟩, ⟨1, Subgroup.one_mem ⊥⟩⟩] at hP_card
    omega

  · rw [h_top, Nat.card_congr ⟨Subtype.val, fun g ↦ ⟨g, Subgroup.mem_top g⟩, fun _ ↦ rfl,
      fun _ ↦ rfl⟩, hN] at hP_card
    omega

lemma card_sylow2_ne_three_of_simple_60 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (hSimple : IsSimpleGroup G) :
    Nat.card (Sylow 2 G) ≠ 3 := by
  intro h
  let ϕ := MulAction.toPermHom G (Sylow 2 G)
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.normal_ker ϕ) with h_bot | h_top

  · exact absurd (Nat.card_le_card_of_injective ϕ (by rwa [MonoidHom.ker_eq_bot_iff] at h_bot))
      (by rw [hN, Nat.card_perm, h]; norm_num)

  · rw [Nat.card_eq_one_iff_unique.mpr ⟨⟨fun P Q ↦ by
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
      exact Eq.symm (show (ϕ g) P = P by
        rw [show ϕ g = 1 by change g ∈ ϕ.ker; rw [h_top]; exact Subgroup.mem_top g]
        rfl)
    ⟩, Sylow.nonempty⟩] at h
    omega

lemma card_sylow2_eq_five_of_simple_60 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (hSimple : IsSimpleGroup G) :
    Nat.card (Sylow 2 G) = 5 := by
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Sylow 2 G) = n := ⟨_, rfl⟩

  have hdvd : n ∣ 60 := by
    rw [← hn, ← hN, Sylow.card_eq_index_normalizer (Classical.arbitrary (Sylow 2 G))]
    exact Subgroup.card_quotient_dvd_card _
  have h_modeq : n % 2 = 1 := hn ▸ card_sylow_modEq_one 2 G
  have h_le : n ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd

  have h_cases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
    interval_cases n <;> revert h_modeq hdvd <;> norm_num
  rcases h_cases with rfl | rfl | rfl | rfl

  · exact absurd hn (card_sylow2_ne_one_of_simple_60 G hN hSimple)

  · exact absurd hn (card_sylow2_ne_three_of_simple_60 G hN hSimple)

  · exact hn

  · exfalso
    obtain ⟨K, hK_normal, hK_card⟩ := exists_normal_complement_of_sylow2_15 G hN hn
    rcases Subgroup.Normal.eq_bot_or_eq_top hK_normal with rfl | rfl

    · rw [Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y ↦ Subtype.ext (by rw [Subgroup.mem_bot.mp x.2,
        Subgroup.mem_bot.mp y.2])⟩, ⟨1, Subgroup.one_mem ⊥⟩⟩] at hK_card
      omega

    · rw [Nat.card_congr ⟨Subtype.val, fun g ↦ ⟨g, Subgroup.mem_top g⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩,
        hN] at hK_card
      omega

lemma toPermHom_injective_of_simple_60 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (hSimple : IsSimpleGroup G) :
    Function.Injective (MulAction.toPermHom G (Sylow 2 G)) := by
  let ϕ := MulAction.toPermHom G (Sylow 2 G)
  rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.normal_ker ϕ) with h_bot | h_top

  · rwa [MonoidHom.ker_eq_bot_iff] at h_bot

  · exfalso
    have h_five := card_sylow2_eq_five_of_simple_60 G hN hSimple
    rw [Nat.card_eq_one_iff_unique.mpr ⟨⟨fun P Q ↦ by
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
      exact Eq.symm (show (ϕ g) P = P by
        rw [show ϕ g = 1 by change g ∈ ϕ.ker; rw [h_top]; exact Subgroup.mem_top g]
        rfl)
    ⟩, Sylow.nonempty⟩] at h_five
    omega

lemma subgroup_S5_order60_eq_A5
    (H : Subgroup (Equiv.Perm (Fin 5))) (hH : Nat.card H = 60) :
    H = alternatingGroup (Fin 5) := by
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two (by
    have h_mul := Subgroup.index_mul_card H
    rw [hH, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h_mul
    norm_num at h_mul
    omega)

lemma iso_A5_of_simple_60 (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60) (hSimple : IsSimpleGroup G) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by

  let e := Fintype.equivOfCardEq (show Fintype.card (Sylow 2 G) = Fintype.card (Fin 5) by
    rw [← Nat.card_eq_fintype_card, card_sylow2_eq_five_of_simple_60 G hN hSimple]; rfl)

  let ψ : G →* Equiv.Perm (Fin 5) :=
    (MonoidHom.mk' (Equiv.permCongr e)
        (by intro _ _; ext; simp)).comp (MulAction.toPermHom G (Sylow 2 G))

  have hψ_inj : Function.Injective ψ := fun g₁ g₂ hg ↦
    toPermHom_injective_of_simple_60 G hN hSimple ((Equiv.permCongr e).injective hg)

  let iso : G ≃* ψ.range :=
    { toFun := fun g ↦ ⟨ψ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      invFun := fun y ↦ Classical.choose (MonoidHom.mem_range.mp y.property)
      left_inv :=
        fun g ↦ hψ_inj (Classical.choose_spec (MonoidHom.mem_range.mp (MonoidHom.mem_range.mpr ⟨g,
            rfl⟩)))
      right_inv := fun y ↦ Subtype.ext (Classical.choose_spec (MonoidHom.mem_range.mp y.property))
      map_mul' := fun a b ↦ Subtype.ext (map_mul ψ a b) }
  exact ⟨iso.trans (MulEquiv.subgroupCongr (subgroup_S5_order60_eq_A5 ψ.range
    (by rw [← Nat.card_congr iso.toEquiv, hN])))⟩

theorem iso_A5_of_hasCyclicPartition (G : Type*) [Group G] [Fintype G]
    (hN : Nat.card G = 60)
    (h : HasCyclicPartition G [{d := 2, f := 2}, {d := 3, f := 2}, {d := 5, f := 2}]) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) :=
  iso_A5_of_simple_60 G hN (isSimple_of_hasCyclicPartition_A5 G hN h)
end

end Dickson
