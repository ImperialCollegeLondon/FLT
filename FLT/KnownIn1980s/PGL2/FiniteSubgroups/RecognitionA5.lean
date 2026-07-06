/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.Tactic.NormNum.NatFactorial
public import FLT.KnownIn1980s.PGL2.FiniteSubgroups.PGLBasic

/-!
# Recognition of `A₅` inside `PGL₂(𝔽̄_p)`

This file proves `Dickson.recognition_A5`-style results: a finite subgroup of
`PGL p = PGL₂(𝔽̄_p)` of order 60 satisfying the constraints arising in the wild case
of Dickson's classification is isomorphic to the alternating group `A₅`.

The proof is the classical Sylow-theoretic argument that a group of order 60 with no
normal Sylow subgroups is simple, hence isomorphic to `A₅` (via the action on the five
Sylow 2-subgroups / cosets argument), combined with the dichotomy
`Dickson.element_dichotomy` for elements of a finite subgroup of `PGL p`: every
element either has order `p` or has order coprime to `p`.
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

/-- A finite group is a `Fintype`. The `[Group G]` hypothesis restricts this instance to
firing on groups, rather than acting as a general `Finite → Fintype` instance. -/
@[nolint unusedArguments]
noncomputable instance instFintypeOfGroupOfFinite {G : Type*} [Group G] [Finite G] :
    Fintype G := Fintype.ofFinite _

private lemma factorization_60_2 : (60 : ℕ).factorization 2 = 2 := by
  exact Nat.factorization_eq_two (m := 15) rfl Nat.prime_two (by norm_num)

private lemma factorization_60_3 : (60 : ℕ).factorization 3 = 1 := by
  exact Nat.factorization_eq_one (m := 20) rfl Nat.prime_three (by norm_num)

private lemma factorization_60_5 : (60 : ℕ).factorization 5 = 1 := by
  exact Nat.factorization_eq_one (m := 12) rfl Nat.prime_five (by norm_num)

private lemma factorization_30_3 : (30 : ℕ).factorization 3 = 1 := by
  exact Nat.factorization_eq_one (m := 10) rfl Nat.prime_three (by norm_num)

private lemma factorization_30_5 : (30 : ℕ).factorization 5 = 1 := by
  exact Nat.factorization_eq_one (m := 6) rfl Nat.prime_five (by norm_num)

private lemma factorization_15_5 : (15 : ℕ).factorization 5 = 1 := by
  exact Nat.factorization_eq_one (m := 3) rfl Nat.prime_five (by norm_num)

private lemma factorization_15_3 : (15 : ℕ).factorization 3 = 1 := by
  exact Nat.factorization_eq_one (m := 5) rfl Nat.prime_three (by norm_num)

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]


omit h_odd in
lemma commute_preserves_fixedPoint (g h : PGL p) (x : ProjectiveLine p)
    (hcomm : g * h = h * g) (hfx : h • x = x) :
    h • (g • x) = g • x := by
  rw [← mul_smul, ← hcomm, mul_smul, hfx]

lemma order_p_one_fixed_point (g : PGL p) (hg : orderOf g = p) :
    Set.ncard (fixedPoints p g) = 1 :=
  (fixedPoints_dichotomy p g
    (fun h ↦ Nat.Prime.ne_one Fact.out (hg.symm.trans ((congrArg orderOf h).trans orderOf_one)))
    (orderOf_pos_iff.mp (hg.symm ▸ Nat.Prime.pos Fact.out))).1.mpr hg

lemma coprime_order_two_fixed_points (h : PGL p) (hh_ne : h ≠ 1)
    (hh_fin : IsOfFinOrder h) (hh_cop : Nat.Coprime (orderOf h) p) :
    Set.ncard (fixedPoints p h) = 2 :=
  (fixedPoints_dichotomy p h hh_ne hh_fin).2.mpr hh_cop.symm

lemma two_fixed_points_contradicts_order_p (g : PGL p) (x y : ProjectiveLine p)
    (hg_order : orderOf g = p)
    (hxy : x ≠ y) (hfx : g • x = x) (hfy : g • y = y) : False :=
  let ⟨_, ha⟩ := Set.ncard_eq_one.mp (order_p_one_fixed_point p g hg_order)
  hxy <|
    ((Set.eq_singleton_iff_unique_mem.mp ha).2 x hfx).trans
    ((Set.eq_singleton_iff_unique_mem.mp ha).2 y hfy).symm

lemma swap_contradicts_odd_order (g : PGL p) (x y : ProjectiveLine p)
    (hg_order : orderOf g = p)
    (hxy : x ≠ y) (hswap_x : g • x = y) (hswap_y : g • y = x) : False :=
  two_fixed_points_contradicts_order_p p (g^2) x y
    (by
      rw [orderOf_pow', hg_order, Nat.gcd_comm, Nat.gcd_rec,
          (Nat.Prime.eq_two_or_odd (Fact.out : Nat.Prime p) |> Or.resolve_left <| ne_of_gt h_odd.out),
          Nat.gcd_one_left, Nat.div_one]
      positivity)
    hxy
    (by rw [sq, mul_smul, hswap_x, hswap_y])
    (by rw [sq, mul_smul, hswap_y, hswap_x])

theorem no_commute_p_coprime (g h : PGL p) (_ : g ≠ 1) (hh_ne : h ≠ 1)
    (hg_order : orderOf g = p) (hh_fin : IsOfFinOrder h)
    (hh_coprime : Nat.Coprime (orderOf h) p)
    (hcomm : g * h = h * g) :
    False := by
  obtain ⟨x, y, hxy, h_fixed⟩ := Set.ncard_eq_two.mp (coprime_order_two_fixed_points p h hh_ne hh_fin hh_coprime)
  have H_fix (z : ProjectiveLine p) : h • z = z ↔ z = x ∨ z = y :=
    (Set.ext_iff.mp h_fixed z).trans (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff])
  match (H_fix (g • x)).mp (commute_preserves_fixedPoint p g h x hcomm ((H_fix x).mpr (Or.inl rfl))),
        (H_fix (g • y)).mp (commute_preserves_fixedPoint p g h y hcomm ((H_fix y).mpr (Or.inr rfl))) with
  | Or.inl hgx, Or.inl hgy => exact absurd (MulAction.injective g (hgx.trans hgy.symm)) hxy
  | Or.inl hgx, Or.inr hgy => exact two_fixed_points_contradicts_order_p p g x y hg_order hxy hgx hgy
  | Or.inr hgx, Or.inl hgy => exact swap_contradicts_odd_order p g x y hg_order hxy hgx hgy
  | Or.inr hgx, Or.inr hgy => exact absurd (MulAction.injective g (hgx.trans hgy.symm)) hxy

theorem element_dichotomy (G : Subgroup (PGL p)) [Finite G]
    (g : G) :
    orderOf (g : PGL p) = p ∨ Nat.Coprime (orderOf (g : PGL p)) p := by
  have hn : orderOf (g : PGL p) ≠ 0 := (isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf g,
    orderOf_pos _, by rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]⟩).orderOf_pos.ne'
  obtain ⟨a, ha⟩ : ∃ a : ℕ, p ^ a ∣ orderOf (g : PGL p) ∧ ¬p ^ (a + 1) ∣ orderOf (g : PGL p) :=
    ⟨_, Nat.ordProj_dvd _ _, Nat.pow_succ_factorization_not_dvd hn Fact.out⟩
  set b := orderOf (g : PGL p) / p ^ a
  have hab : orderOf (g : PGL p) = p ^ a * b := (Nat.mul_div_cancel' ha.1).symm
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h ↦ hn (by rw [hab, h, mul_zero]))
  have hb : b.Coprime p := Nat.Coprime.symm ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr
    (fun h ↦ ha.2 (by rw [hab, pow_succ]; exact mul_dvd_mul_left (p ^ a) h)))
  rcases a with _ | _ | a
  · right
    rw [hab, pow_zero, one_mul]
    exact hb
  · by_cases hb_one : b = 1
    · left
      rw [hab, hb_one, pow_one, mul_one]
    · have hgb_ord : orderOf ((g : PGL p) ^ b) = p := by
        rw [orderOf_pow' _ hb_pos.ne', hab, pow_one, Nat.gcd_eq_right ⟨p, mul_comm p b⟩, Nat.mul_div_cancel _ hb_pos]
      have hgp_ord : orderOf ((g : PGL p) ^ p) = b := by
        rw [orderOf_pow' _ (Fact.out : Nat.Prime p).ne_zero, hab, pow_one, Nat.gcd_eq_right ⟨b, rfl⟩, mul_comm p b, Nat.mul_div_cancel _ (Nat.Prime.pos Fact.out)]
      exfalso
      exact no_commute_p_coprime p ((g : PGL p) ^ b) ((g : PGL p) ^ p)
        (fun h ↦ by rw [h, orderOf_one] at hgb_ord; exact (Fact.out : Nat.Prime p).ne_one hgb_ord.symm)
        (fun h ↦ by rw [h, orderOf_one] at hgp_ord; exact hb_one hgp_ord.symm)
        hgb_ord
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨b, hb_pos, by rw [← hgp_ord, pow_orderOf_eq_one]⟩)
        (by rw [hgp_ord]; exact hb)
        (by rw [← pow_add, add_comm, pow_add])
  · have hgb_ord : orderOf ((g : PGL p) ^ b) = p ^ (a + 2) := by
      rw [orderOf_pow' _ hb_pos.ne', hab, Nat.gcd_eq_right ⟨p ^ (a + 2), mul_comm (p ^ (a + 2)) b⟩, Nat.mul_div_cancel _ hb_pos]
    haveI : Finite (Subgroup.zpowers ((g : PGL p) ^ b)) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hgb_ord]; exact (pow_pos (Nat.Prime.pos Fact.out) _).ne')
    haveI : IsCyclic (Subgroup.zpowers ((g : PGL p) ^ b)) :=
      ⟨⟨⟨(g : PGL p) ^ b, Subgroup.mem_zpowers _⟩, fun ⟨x, hx⟩ ↦ by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx; exact ⟨k, Subtype.ext hk⟩⟩⟩
    have hpgrp : IsPGroup p (Subgroup.zpowers ((g : PGL p) ^ b)) := fun ⟨x, hx⟩ ↦
      ⟨a + 2, Subtype.ext (orderOf_dvd_iff_pow_eq_one.mp (hgb_ord ▸ orderOf_dvd_of_mem_zpowers hx))⟩
    have hdvd : p ^ (a + 2) ∣ p := by
      rw [← hgb_ord, ← Nat.card_zpowers, ← IsCyclic.exponent_eq_card]
      exact isPGroup_exponent_dvd_prime p (Subgroup.zpowers ((g : PGL p) ^ b)) hpgrp
    have h_p_lt_pa : p < p ^ (a + 2) := by
      calc p = p ^ 1 := (pow_one p).symm
           _ < p ^ (a + 2) := Nat.pow_lt_pow_right (Fact.out : Nat.Prime p).one_lt (Nat.succ_lt_succ (Nat.zero_lt_succ a))
    exact absurd (Nat.le_of_dvd (Nat.Prime.pos Fact.out) hdvd) (not_le_of_gt h_p_lt_pa)

theorem element_partition_count (G : Subgroup (PGL p)) [Finite G] :
    Nat.card G - 1 =
      Nat.card {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p} +
      Nat.card {g : G | g ≠ 1 ∧ Nat.Coprime (orderOf (g : PGL p)) p} := by
  have h_disj : Disjoint {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p}
                         {g : G | g ≠ 1 ∧ Nat.Coprime (orderOf (g : PGL p)) p} := by
    simp only [Set.disjoint_left, Set.mem_setOf_eq]
    rintro g ⟨_, h1⟩ ⟨_, h2⟩
    rw [h1] at h2
    exact Nat.Prime.ne_one Fact.out ((Nat.gcd_self p).symm.trans h2)
  have h_sum : Nat.card G = 1 + Nat.card {g : G | g ≠ 1} := by
    let e : {g : G | g = 1} ⊕ {g : G | g ≠ 1} ≃ G := Equiv.sumCompl (fun g ↦ g = 1)
    haveI : Unique {g : G | g = 1} := ⟨⟨⟨1, rfl⟩⟩, fun ⟨g, hg⟩ ↦ Subtype.ext hg⟩
    rw [← Nat.card_congr e, Nat.card_sum, Nat.card_unique]
  have h_set : {g : G | g ≠ 1} = {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p} ∪
                                 {g : G | g ≠ 1 ∧ Nat.Coprime (orderOf (g : PGL p)) p} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_union, ← and_or_left]
    exact (and_iff_left (element_dichotomy p G g)).symm
  rw [h_sum, h_set, Nat.card_congr (Equiv.Set.union h_disj), Nat.card_sum,Nat.add_sub_cancel_left]


@[nolint unusedArguments]
lemma order_3_centralizes_order_5 {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (g : G)
    (hQ_card : Nat.card Q = 5) (hg_order : orderOf g = 3)
    (hQ_normal : Q.Normal) :
    ∀ q : G, q ∈ Q → g * q = q * g := by
  intro q hq
  by_cases hq1 : q = 1
  · rw [hq1, mul_one, one_mul]
  · have hq_ord : orderOf q = 5 := by
      have h1 : orderOf q ∣ 5 := hQ_card ▸ (Nat.card_zpowers q).symm ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hq)
      rcases Nat.dvd_prime (Nat.prime_five) |>.mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hq1
      · exact h

    obtain ⟨a, ha⟩ : ∃ a : ℤ, g * q * g⁻¹ = q^a := by
      obtain ⟨x, hx⟩ := (isCyclic_of_prime_card hQ_card).exists_generator
      obtain ⟨a, ha⟩ := hx ⟨q, hq⟩
      obtain ⟨b, hb⟩ := hx ⟨g * x * g⁻¹, hQ_normal.conj_mem _ x.2 g⟩
      use b
      have ha' : q = (x : G) ^ a := (congrArg Subtype.val ha).symm.trans (Subgroup.coe_zpow Q x a)
      have hb' : g * (x : G) * g⁻¹ = (x : G) ^ b := (congrArg Subtype.val hb).symm.trans (Subgroup.coe_zpow Q x b)
      calc
        g * q * g⁻¹ = g * (x : G) ^ a * g⁻¹ := by rw [ha']
        _ = (g * (x : G) * g⁻¹) ^ a := map_zpow (MulEquiv.toMonoidHom (MulAut.conj g)) (x : G) a
        _ = ((x : G) ^ b) ^ a := by rw [hb']
        _ = q ^ b := by rw [← zpow_mul, mul_comm, zpow_mul, ← ha']

    have h_pow_conj : ∀ n : ℕ, g^n * q * (g^n)⁻¹ = q^(a^n) := by
      intro n
      induction n with
      | zero => rw [pow_zero, inv_one, mul_one, one_mul, pow_zero, zpow_one]
      | succ n ih =>
          calc
            g^(n + 1) * q * (g^(n + 1))⁻¹ = g * (g^n * q * (g^n)⁻¹) * g⁻¹ := by simp only [pow_succ', mul_inv_rev, mul_assoc]
            _ = g * q^(a^n) * g⁻¹ := by rw [ih]
            _ = (g * q * g⁻¹) ^ (a^n) := map_zpow (MulEquiv.toMonoidHom (MulAut.conj g)) q (a^n)
            _ = q ^ (a ^ (n + 1)) := by
              have h_exp : a ^ n * a = a ^ (n + 1) := by ring
              rw [ha, ← zpow_mul, mul_comm, h_exp]

    have h_order_3 : q = q^(a^3) := by
      have hg3 : g^3 = 1 := hg_order ▸ pow_orderOf_eq_one g
      calc q = g^3 * q * (g^3)⁻¹ := by rw [hg3, inv_one, one_mul, mul_one]
           _ = q^(a^3) := h_pow_conj 3

    have h_div : (5 : ℤ) ∣ a^3 - 1 := by
      have h1 : (orderOf q : ℤ) ∣ a^3 - 1 := orderOf_dvd_iff_zpow_eq_one.mpr <| by
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one, ← h_order_3, mul_inv_cancel]
      rw [hq_ord] at h1
      exact h1

    obtain ⟨k, hk⟩ : ∃ k : ℤ, a = 5 * k + 1 := by
      have hk : a = 5 * (a / 5) + (a % 5) := by omega
      have hM : a^3 - 1 = 5 * (25 * (a / 5)^3 + 15 * (a / 5)^2 * (a % 5) + 3 * (a / 5) * (a % 5)^2) + ((a % 5)^3 - 1) := by
        calc a^3 - 1 = (5 * (a / 5) + a % 5)^3 - 1 := congrArg (fun x ↦ x^3 - 1) hk
        _ = _ := by ring
      obtain ⟨N, hN⟩ := h_div
      have h_cases : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
      rcases h_cases with hr | hr | hr | hr | hr <;> rw [hr, hN] at hM
      · omega
      · exact ⟨a / 5, by omega⟩
      · omega
      · omega
      · omega

    calc
      g * q = g * q * (g⁻¹ * g) := by rw [inv_mul_cancel, mul_one]
      _ = g * q * g⁻¹ * g := by rw [← mul_assoc]
      _ = q ^ (5 * k + 1) * g := by rw [ha, hk]
      _ = (q ^ (5 : ℤ)) ^ k * q * g := by rw [zpow_add, zpow_mul, zpow_one]
      _ = q * g := by rw [show q ^ (5 : ℤ) = 1 by exact_mod_cast (hq_ord ▸ pow_orderOf_eq_one q), one_zpow, one_mul]

lemma sylow_card_dvd_index {G : Type*} [Group G] [Finite G]
    (p m n k : ℕ) [hp : Fact (Nat.Prime p)]
    (hn : Nat.card G = n)
    (h_mul : n = m * p ^ k)
    (h_fac : n.factorization p = k) :
    Fintype.card (Sylow p G) ∣ m := by
  let P : Sylow p G := Classical.arbitrary (Sylow p G)
  have h_idx : (P : Subgroup G).index = m := by
    have h := Subgroup.index_mul_card (P : Subgroup G)
    rw [P.card_eq_multiplicity.trans (by rw [hn, h_fac]), hn, h_mul] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos k) h
  rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P, ← h_idx]
  exact Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup G)))

lemma sylow_5_options (G : Type*) [Group G] [Finite G]
    (hn : Nat.card G = 60) :
    Fintype.card (Sylow 5 G) = 1 ∨ Fintype.card (Sylow 5 G) = 6 := by
  have h_div12 : Fintype.card (Sylow 5 G) ∣ 12 := by
    let P : Sylow 5 G := Classical.arbitrary (Sylow 5 G)
    have h_idx : (P : Subgroup G).index = 12 := by
      have h := Subgroup.index_mul_card (P : Subgroup G)
      rw [P.card_eq_multiplicity.trans (by rw [hn, factorization_60_5, pow_one]), hn] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P, ← h_idx]
    exact Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup G)))
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 5 G) = 5 * k + 1 := ⟨Fintype.card (Sylow 5 G) / 5, by
    have : Fintype.card (Sylow 5 G) % 5 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 5 G
    omega⟩
  have : k ≤ 2 := by have := Nat.le_of_dvd (by norm_num) h_div12; omega
  interval_cases k <;> (revert h_div12; rw [hk]; norm_num)


lemma sylow_5_not_one (G : Subgroup (PGL p))
    [Finite G] (hp3 : p = 3)
    (hn : Nat.card G = 60) (hn3 : Fintype.card (Sylow p G) = 10)
    : Fintype.card (Sylow 5 G) ≠ 1 := by
  contrapose! hn3
  obtain ⟨Q, hQ_card, hQ_normal⟩ : ∃ Q : Subgroup G, Nat.card Q = 5 ∧ Q.Normal := by
    obtain ⟨Q, hQ⟩ := Fintype.card_eq_one_iff.mp hn3
    refine ⟨Q.toSubgroup, ?_, ⟨fun n hn g ↦ hQ (g • Q) ▸ Subgroup.mem_map_of_mem _ hn⟩⟩
    convert Q.card_eq_multiplicity
    rw [hn, factorization_60_5, pow_one]


  obtain ⟨g, hg⟩ : ∃ g : G, orderOf g = 3 :=
    exists_prime_orderOf_dvd_card 3 (by rw [Fintype.card_eq_nat_card, hn]; norm_num)

  obtain ⟨q, hq_mem, hq_ord⟩ : ∃ q : G, q ∈ Q ∧ orderOf q = 5 := by
    obtain ⟨q', hq_gen⟩ := (isCyclic_of_prime_card hQ_card).exists_generator
    exact ⟨q', q'.2, by rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hq_gen, hQ_card]⟩

  have hg_ord : orderOf (g : PGL p) = 3 := by rw [Subgroup.orderOf_coe, hg]
  have hq_ord_PGL : orderOf (q : PGL p) = 5 := by rw [Subgroup.orderOf_coe, hq_ord]

  exfalso
  exact no_commute_p_coprime p (g : PGL p) (q : PGL p)
    (fun h ↦ by rw [h, orderOf_one] at hg_ord; norm_num at hg_ord)
    (fun h ↦ by rw [h, orderOf_one] at hq_ord_PGL; norm_num at hq_ord_PGL)
    (by rw [hg_ord, hp3])
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, by rw [← hq_ord_PGL, pow_orderOf_eq_one]⟩)
    (by rw [hq_ord_PGL, hp3]; norm_num)
    (congrArg Subtype.val (order_3_centralizes_order_5 Q g hQ_card hg hQ_normal q hq_mem))





lemma normal_contains_all_sylow {G : Type*} [Group G] [Finite G]
    {q : ℕ} [hq : Fact (Nat.Prime q)]
    (N : Subgroup G) [N.Normal]
    (P : Sylow q G) (hP : (P : Subgroup G) ≤ N) :
    ∀ Q : Sylow q G, (Q : Subgroup G) ≤ N := by
  intro Q x hx
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  obtain ⟨y, hy, rfl⟩ := hx
  exact Subgroup.Normal.conj_mem ‹_› _ (hP hy) _


lemma order_15_unique_sylow_5 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 15) :
    Fintype.card (Sylow 5 G) = 1 := by
  have h_div3 : Fintype.card (Sylow 5 G) ∣ 3 := by
    let P : Sylow 5 G := Classical.arbitrary (Sylow 5 G)
    have h_idx : (P : Subgroup G).index = 3 := by
      have h := Subgroup.index_mul_card (P : Subgroup G)
      rw [P.card_eq_multiplicity.trans (by rw [hn, factorization_15_5, pow_one]), hn] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P, ← h_idx]
    exact Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup G)))
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 5 G) = 5 * k + 1 := ⟨Fintype.card (Sylow 5 G) / 5, by
    have : Fintype.card (Sylow 5 G) % 5 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 5 G
    omega⟩
  have : k ≤ 0 := by have := Nat.le_of_dvd (by norm_num) h_div3; omega
  interval_cases k; revert h_div3; rw [hk]; norm_num



lemma sylow_normal_of_unique_in_normal {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (N : Subgroup G) [hN : N.Normal]
    (h_unique : Fintype.card (Sylow p N) = 1) :
    ∃ P : Sylow p N, (P.toSubgroup.map N.subtype).Normal := by
  obtain ⟨P, hP⟩ := Fintype.card_eq_one_iff.mp h_unique
  have hP_norm : (P : Subgroup N).Normal := ⟨fun n hn g ↦ hP (g • P) ▸ Subgroup.mem_map_of_mem _ hn⟩
  have : (P : Subgroup N).Characteristic := Sylow.characteristic_of_normal P hP_norm
  exact ⟨P, ConjAct.normal_of_characteristic_of_normal⟩


lemma too_many_elements_of_prime_order {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (_ : Nat.card G = p * q)
    (hn_p : Fintype.card (Sylow p G) = q)
    (hn_q : Fintype.card (Sylow q G) = p)
    (hpq : p ≠ q) (hp_ge : p ≥ 3) (hq_ge : q ≥ 3) : False := by
  rcases lt_trichotomy p q with h_lt | rfl | h_gt
  · have h1 : Nat.card (Sylow q G) % q = 1 % q := card_sylow_modEq_one q G
    rw [Nat.card_eq_fintype_card, hn_q, Nat.mod_eq_of_lt hq.out.one_lt, Nat.mod_eq_of_lt h_lt] at h1
    omega
  · exact hpq rfl
  · have h1 : Nat.card (Sylow p G) % p = 1 % p := card_sylow_modEq_one p G
    rw [Nat.card_eq_fintype_card, hn_p, Nat.mod_eq_of_lt hp.out.one_lt, Nat.mod_eq_of_lt h_gt] at h1
    omega


lemma order_30_n3_ne_10_of_n5_eq_6 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 30)
    (hn5 : Fintype.card (Sylow 5 G) = 6) :
    Fintype.card (Sylow 3 G) ≠ 10 := by
  intro hn3

  have h_card : Fintype.card G = 30 := Nat.card_eq_fintype_card.symm.trans hn

  have hP_card : ∀ P : Sylow 5 G, Nat.card (P : Subgroup G) = 5 := fun P ↦ by
    rw [Sylow.card_eq_multiplicity P, hn, factorization_30_5, pow_one]
  have hQ_card : ∀ Q : Sylow 3 G, Nat.card (Q : Subgroup G) = 3 := fun Q ↦ by
    rw [Sylow.card_eq_multiplicity Q, hn, factorization_30_3, pow_one]

  let S5 (P : Sylow 5 G) : Finset G := Finset.filter (fun x ↦ x ∈ (P : Subgroup G) ∧ orderOf x = 5) Finset.univ
  let S3 (Q : Sylow 3 G) : Finset G := Finset.filter (fun x ↦ x ∈ (Q : Subgroup G) ∧ orderOf x = 3) Finset.univ
  let F5 := Finset.filter (fun x : G ↦ orderOf x = 5) Finset.univ
  let F3 := Finset.filter (fun x : G ↦ orderOf x = 3) Finset.univ
  let F1 := Finset.filter (fun x : G ↦ orderOf x = 1) Finset.univ

  have hS5_card : ∀ P, (S5 P).card = 4 := fun P ↦ by
    have h_eq : S5 P = (Finset.filter (fun x ↦ x ∈ (P : Subgroup G)) Finset.univ).erase 1 := by
      ext x; simp only [S5, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hxP, hx5⟩; exact ⟨fun h ↦ absurd (hx5.symm.trans (orderOf_eq_one_iff.mpr h)) (by norm_num), hxP⟩
      · rintro ⟨hx1, hxP⟩
        have h_div : orderOf x ∣ 5 := hP_card P ▸ (Nat.card_zpowers x).symm ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxP)
        exact ⟨hxP, (Nat.dvd_prime (Nat.prime_five)).mp h_div |>.resolve_left (mt orderOf_eq_one_iff.mp hx1)⟩
    rw [h_eq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, Subgroup.one_mem _⟩)]
    rw [← Fintype.card_subtype (fun x ↦ x ∈ (P : Subgroup G)), show Fintype.card { x // x ∈ (P : Subgroup G) } = Fintype.card P from rfl]
    rw [← Nat.card_eq_fintype_card, hP_card P]

  have hS3_card : ∀ Q, (S3 Q).card = 2 := fun Q ↦ by
    have h_eq : S3 Q = (Finset.filter (fun x ↦ x ∈ (Q : Subgroup G)) Finset.univ).erase 1 := by
      ext x; simp only [S3, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hxQ, hx3⟩; exact ⟨fun h ↦ absurd (hx3.symm.trans (orderOf_eq_one_iff.mpr h)) (by norm_num), hxQ⟩
      · rintro ⟨hx1, hxQ⟩
        have h_div : orderOf x ∣ 3 := hQ_card Q ▸ (Nat.card_zpowers x).symm ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxQ)
        exact ⟨hxQ, (Nat.dvd_prime (Nat.prime_three)).mp h_div |>.resolve_left (mt orderOf_eq_one_iff.mp hx1)⟩
    rw [h_eq, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, Subgroup.one_mem _⟩)]
    rw [← Fintype.card_subtype (fun x ↦ x ∈ (Q : Subgroup G)), show Fintype.card { x // x ∈ (Q : Subgroup G) } = Fintype.card Q from rfl]
    rw [← Nat.card_eq_fintype_card, hQ_card Q]

  have hF5_bound : 24 ≤ F5.card := by
    let U5 := Finset.univ.biUnion S5
    have hU5_card : U5.card = 24 := by
      have h_disj : ∀ P Q : Sylow 5 G, P ≠ Q → Disjoint (S5 P) (S5 Q) := fun P Q hPQ ↦ by
        rw [Finset.disjoint_left]; rintro x hxP hxQ
        simp only [S5, Finset.mem_filter, Finset.mem_univ, true_and] at hxP hxQ
        have hzP : Subgroup.zpowers x = P.toSubgroup :=
          SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Subgroup.zpowers_le.mpr hxP.1) ((Nat.card_zpowers x).trans (hxP.2.trans (hP_card P).symm)).ge
        have hzQ : Subgroup.zpowers x = Q.toSubgroup :=
          SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Subgroup.zpowers_le.mpr hxQ.1) ((Nat.card_zpowers x).trans (hxQ.2.trans (hP_card Q).symm)).ge
        exact hPQ (by ext y; exact Subgroup.ext_iff.mp (hzP.symm.trans hzQ) y)
      rw [Finset.card_biUnion (fun P _ Q _ hPQ ↦ h_disj P Q hPQ), Finset.sum_congr rfl (fun P _ ↦ hS5_card P), Finset.sum_const, Finset.card_univ, hn5]
      rfl
    exact hU5_card ▸ Finset.card_le_card (fun x hx ↦ by
      obtain ⟨P, hxP⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hxP.2).2.2⟩)

  have hF3_bound : 20 ≤ F3.card := by
    let U3 := Finset.univ.biUnion S3
    have hU3_card : U3.card = 20 := by
      have h_disj : ∀ Q1 Q2 : Sylow 3 G, Q1 ≠ Q2 → Disjoint (S3 Q1) (S3 Q2) := fun Q1 Q2 hQQ ↦ by
        rw [Finset.disjoint_left]; rintro x hxQ1 hxQ2
        simp only [S3, Finset.mem_filter, Finset.mem_univ, true_and] at hxQ1 hxQ2
        have hzQ1 : Subgroup.zpowers x = Q1.toSubgroup :=
          SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Subgroup.zpowers_le.mpr hxQ1.1) ((Nat.card_zpowers x).trans (hxQ1.2.trans (hQ_card Q1).symm)).ge
        have hzQ2 : Subgroup.zpowers x = Q2.toSubgroup :=
          SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Subgroup.zpowers_le.mpr hxQ2.1) ((Nat.card_zpowers x).trans (hxQ2.2.trans (hQ_card Q2).symm)).ge
        exact hQQ (by ext y; exact Subgroup.ext_iff.mp (hzQ1.symm.trans hzQ2) y)
      rw [Finset.card_biUnion (fun Q1 _ Q2 _ hQQ ↦ h_disj Q1 Q2 hQQ), Finset.sum_congr rfl (fun Q _ ↦ hS3_card Q), Finset.sum_const, Finset.card_univ, hn3]
      rfl
    exact hU3_card ▸ Finset.card_le_card (fun x hx ↦ by
      obtain ⟨Q, hxQ⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hxQ.2).2.2⟩)

  have hF1_card : F1.card = 1 := by
    rw [show F1 = {1} from Finset.ext (fun x ↦ by
      simp only [F1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, orderOf_eq_one_iff])]
    exact Finset.card_singleton 1

  have h_disj_53 : Disjoint F5 F3 := by
    rw [Finset.disjoint_left]; intro x hx5 hx3
    exact absurd ((Finset.mem_filter.mp hx5).2.symm.trans (Finset.mem_filter.mp hx3).2) (by norm_num)

  have h_disj_53_1 : Disjoint (F5 ∪ F3) F1 := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]; intro x hx5 hx1
      exact absurd ((Finset.mem_filter.mp hx5).2.symm.trans (Finset.mem_filter.mp hx1).2) (by norm_num)
    · rw [Finset.disjoint_left]; intro x hx3 hx1
      exact absurd ((Finset.mem_filter.mp hx3).2.symm.trans (Finset.mem_filter.mp hx1).2) (by norm_num)

  have h_le : F5.card + F3.card + F1.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint h_disj_53, ← Finset.card_union_of_disjoint h_disj_53_1]
    exact Finset.card_le_univ _

  rw [h_card, hF1_card] at h_le
  omega

@[nolint unusedArguments]
lemma card_sup_of_coprime_normal {G : Type*} [Group G]
    (H K : Subgroup G) [Finite H] [Finite K]
    (hH : H.Normal) (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod, ← Nat.card_congr]
  refine Equiv.ofBijective (fun x ↦ ⟨x.1 * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨hx, hhx⟩, ⟨kx, hkx⟩⟩ ⟨⟨hy, hhy⟩, ⟨ky, hky⟩⟩ hxy
    have hxy' : hx * kx = hy * ky := Subtype.ext_iff.mp hxy
    have h_eq : hx⁻¹ * hy = kx * ky⁻¹ := inv_mul_eq_iff_eq_mul.mpr (by
      rw [← mul_assoc, hxy', mul_assoc, mul_inv_cancel, mul_one] : hx * (kx * ky⁻¹) = hy).symm
    have h_one : hx⁻¹ * hy = 1 := Subgroup.mem_bot.mp <| (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot ▸
      (⟨H.mul_mem (H.inv_mem hhx) hhy, h_eq.symm ▸ K.mul_mem hkx (K.inv_mem hky)⟩ : hx⁻¹ * hy ∈ H ⊓ K)
    exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp h_one)) (Subtype.ext (mul_inv_eq_one.mp (h_eq.symm.trans h_one)))
  · rintro ⟨x, hx⟩
    obtain ⟨h, hh, k, hk, rfl⟩ : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
      rw [Subgroup.sup_eq_closure] at hx
      induction hx using Subgroup.closure_induction
      · rename_i x_val hx_mem
        rcases hx_mem with hxH | hxK
        · exact ⟨x_val, hxH, 1, K.one_mem, (mul_one x_val).symm⟩
        · exact ⟨1, H.one_mem, x_val, hxK, (one_mul x_val).symm⟩
      · exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
      · rename_i x_val y_val hx_mem hy_mem hx_ih hy_ih
        obtain ⟨h1, hh1, k1, hk1, rfl⟩ := hx_ih
        obtain ⟨h2, hh2, k2, hk2, rfl⟩ := hy_ih
        refine ⟨h1 * (k1 * h2 * k1⁻¹), H.mul_mem hh1 (hH.conj_mem _ hh2 k1), k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        group
      · rename_i x_val hx_mem hx_ih
        obtain ⟨h, hh, k, hk, rfl⟩ := hx_ih
        refine ⟨k⁻¹ * h⁻¹ * k, (by rw [inv_inv] : k⁻¹ * h⁻¹ * k⁻¹⁻¹ = k⁻¹ * h⁻¹ * k) ▸ hH.conj_mem _ (H.inv_mem hh) k⁻¹, k⁻¹, K.inv_mem hk, ?_⟩
        group
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, Subtype.ext rfl⟩



lemma order_30_unique_sylow_5 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 30) :
    Fintype.card (Sylow 5 G) = 1 := by
  by_contra h_contra
  have hn5 : Fintype.card (Sylow 5 G) = 6 := by
    have h_cases : Fintype.card (Sylow 5 G) = 1 ∨ Fintype.card (Sylow 5 G) = 6 := by
      have h_div6 : Fintype.card (Sylow 5 G) ∣ 6 := by
        let P : Sylow 5 G := Classical.arbitrary (Sylow 5 G)
        have h_idx : (P : Subgroup G).index = 6 := by
          have h := Subgroup.index_mul_card (P : Subgroup G)
          rw [P.card_eq_multiplicity.trans (by rw [hn, factorization_30_5, pow_one]), hn] at h
          exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
        rw [← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P, ← h_idx]
        exact Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup G)))
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 5 G) = 5 * k + 1 := ⟨Fintype.card (Sylow 5 G) / 5, by
        have : Fintype.card (Sylow 5 G) % 5 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 5 G
        omega⟩
      have : k ≤ 1 := by have := Nat.le_of_dvd (by norm_num) h_div6; omega
      interval_cases k <;> (revert h_div6; rw [hk]; norm_num)
    exact h_cases.resolve_left h_contra

  have hn3 : Fintype.card (Sylow 3 G) = 1 := by
    have h_cases : Fintype.card (Sylow 3 G) = 1 ∨ Fintype.card (Sylow 3 G) = 10 := by
      have h_div10 : Fintype.card (Sylow 3 G) ∣ 10 :=
        sylow_card_dvd_index 3 10 30 1 hn rfl factorization_30_3
      obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 3 G) = 3 * k + 1 := ⟨Fintype.card (Sylow 3 G) / 3, by
        have : Fintype.card (Sylow 3 G) % 3 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 3 G
        omega⟩
      have : k ≤ 3 := by have := Nat.le_of_dvd (by norm_num) h_div10; omega
      interval_cases k <;> (revert h_div10; rw [hk]; norm_num)
    exact h_cases.resolve_right (order_30_n3_ne_10_of_n5_eq_6 hn hn5)

  obtain ⟨N₃, hN₃⟩ : ∃ N₃ : Subgroup G, N₃.Normal ∧ Nat.card N₃ = 3 :=
    let ⟨N₃, hN₃⟩ := Fintype.card_eq_one_iff.mp hn3
    ⟨N₃.toSubgroup, Subgroup.Normal.mk (fun n h_mem g ↦ hN₃ (g • N₃) ▸ Subgroup.mem_map_of_mem _ h_mem), N₃.card_eq_multiplicity.trans (by rw [hn, factorization_30_3, pow_one])⟩

  obtain ⟨P₅, hP₅⟩ : ∃ P₅ : Subgroup G, Nat.card P₅ = 5 := by
    exact Sylow.exists_subgroup_card_pow_prime 5 (show 5 ^ 1 ∣ Nat.card G from hn.symm ▸ by norm_num)

  have h_card_sup : Nat.card (N₃ ⊔ P₅ : Subgroup G) = 15 :=
    (card_sup_of_coprime_normal N₃ P₅ hN₃.1 (by rw [hN₃.2, hP₅]; norm_num)).trans (by rw [hN₃.2, hP₅])

  haveI h_normal_sup : (N₃ ⊔ P₅ : Subgroup G).Normal :=
    Subgroup.normal_of_index_eq_two (Nat.eq_of_mul_eq_mul_right (show 0 < 15 by norm_num) (by rw [← h_card_sup, Subgroup.index_mul_card, hn, h_card_sup]))

  obtain ⟨P₅', hP₅'⟩ : ∃ P₅' : Sylow 5 (↥(N₃ ⊔ P₅)), (P₅'.toSubgroup.map (Subgroup.subtype (N₃ ⊔ P₅))).Normal :=
    sylow_normal_of_unique_in_normal (N₃ ⊔ P₅) (order_15_unique_sylow_5 h_card_sup)

  have h_is_maximal : ∀ {Q : Subgroup G}, IsPGroup 5 Q → (P₅'.toSubgroup.map (N₃ ⊔ P₅).subtype : Subgroup G) ≤ Q → Q = P₅'.toSubgroup.map (N₃ ⊔ P₅).subtype :=
    fun {Q} hQ hQ' ↦ SetLike.ext' (Eq.symm <| Set.eq_of_subset_of_ncard_le hQ' (by
      have hP5'_card : Nat.card (P₅'.toSubgroup.map (N₃ ⊔ P₅).subtype) = 5 :=
        (Subgroup.card_subtype _ _).trans (P₅'.card_eq_multiplicity.trans (by rw [h_card_sup, factorization_15_5]; rfl))
      have ⟨k, hk⟩ := IsPGroup.exists_card_eq hQ
      exact ((le_antisymm (by
        have : k ≤ 1 := by by_contra h; exact absurd (dvd_trans (pow_dvd_pow 5 (not_le.mp h)) (hk ▸ hn ▸ Subgroup.card_subgroup_dvd_card Q)) (by norm_num)
        interval_cases k <;> rw [hk] <;> norm_num) (by
        rw [← hP5'_card]; exact Nat.card_mono (Set.toFinite (Q : Set G)) (show _ ⊆ _ from hQ')) : Nat.card Q = 5).trans hP5'_card.symm).le
    ))

  obtain ⟨P₅'', hP₅''⟩ : ∃ P₅'' : Sylow 5 G, (P₅''.toSubgroup).Normal :=
    ⟨{ P₅'.toSubgroup.map (N₃ ⊔ P₅).subtype with
       isPGroup' := IsPGroup.map P₅'.isPGroup' (N₃ ⊔ P₅).subtype
       is_maximal' := h_is_maximal }, hP₅'⟩

  exact h_contra (Fintype.card_eq_one_iff.mpr ⟨P₅'', fun P ↦ let ⟨g, hg⟩ := MulAction.exists_smul_eq G P₅'' P; hg.symm.trans Sylow.smul_eq_of_normal⟩)


lemma order_15_unique_sylow_3 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 15) :
    Fintype.card (Sylow 3 G) = 1 := by
  have h_div5 : Fintype.card (Sylow 3 G) ∣ 5 :=
    sylow_card_dvd_index 3 5 15 1 hn rfl factorization_15_3
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 3 G) = 3 * k + 1 := ⟨Fintype.card (Sylow 3 G) / 3, by
    have : Fintype.card (Sylow 3 G) % 3 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 3 G
    omega⟩
  have : k ≤ 1 := by have := Nat.le_of_dvd (by norm_num) h_div5; omega
  interval_cases k <;> (revert h_div5; rw [hk]; norm_num)


lemma order_30_unique_sylow_3 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 30) :
    Fintype.card (Sylow 3 G) = 1 := by
  have hn5 : Fintype.card (Sylow 5 G) = 1 := order_30_unique_sylow_5 hn

  obtain ⟨N₅, hN₅⟩ : ∃ N₅ : Subgroup G, N₅.Normal ∧ Nat.card N₅ = 5 :=
    let ⟨N₅, hN₅⟩ := Fintype.card_eq_one_iff.mp hn5
    ⟨N₅.toSubgroup, Subgroup.Normal.mk (fun n h_mem g ↦ hN₅ (g • N₅) ▸ Subgroup.mem_map_of_mem _ h_mem), N₅.card_eq_multiplicity.trans (by rw [hn, factorization_30_5, pow_one])⟩

  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, Nat.card P₃ = 3 := by
    exact Sylow.exists_subgroup_card_pow_prime 3 (show 3 ^ 1 ∣ Nat.card G from hn.symm ▸ by norm_num)

  have h_card_sup : Nat.card (N₅ ⊔ P₃ : Subgroup G) = 15 :=
    (card_sup_of_coprime_normal N₅ P₃ hN₅.1 (by rw [hN₅.2, hP₃]; norm_num)).trans (by rw [hN₅.2, hP₃])

  haveI h_normal_sup : (N₅ ⊔ P₃ : Subgroup G).Normal :=
    Subgroup.normal_of_index_eq_two (Nat.eq_of_mul_eq_mul_right (show 0 < 15 by norm_num) (by rw [← h_card_sup, Subgroup.index_mul_card, hn, h_card_sup]))

  obtain ⟨P₃', hP₃'⟩ : ∃ P₃' : Sylow 3 (↥(N₅ ⊔ P₃)), (P₃'.toSubgroup.map (Subgroup.subtype (N₅ ⊔ P₃))).Normal :=
    sylow_normal_of_unique_in_normal (N₅ ⊔ P₃) (order_15_unique_sylow_3 h_card_sup)

  have h_is_maximal : ∀ {Q : Subgroup G}, IsPGroup 3 Q → (P₃'.toSubgroup.map (N₅ ⊔ P₃).subtype : Subgroup G) ≤ Q → Q = P₃'.toSubgroup.map (N₅ ⊔ P₃).subtype :=
    fun {Q} hQ hQ' ↦ SetLike.ext' (Eq.symm <| Set.eq_of_subset_of_ncard_le hQ' (by
      have hP3'_card : Nat.card (P₃'.toSubgroup.map (N₅ ⊔ P₃).subtype) = 3 :=
        (Subgroup.card_subtype _ _).trans (P₃'.card_eq_multiplicity.trans (by rw [h_card_sup, factorization_15_3]; rfl))
      have ⟨k, hk⟩ := IsPGroup.exists_card_eq hQ
      exact ((le_antisymm (by
        have : k ≤ 1 := by by_contra h; exact absurd (dvd_trans (pow_dvd_pow 3 (not_le.mp h)) (hk ▸ hn ▸ Subgroup.card_subgroup_dvd_card Q)) (by norm_num)
        interval_cases k <;> rw [hk] <;> norm_num) (by
        rw [← hP3'_card]; exact Nat.card_mono (Set.toFinite (Q : Set G)) (show _ ⊆ _ from hQ')) : Nat.card Q = 3).trans hP3'_card.symm).le
    ))

  obtain ⟨P₃'', hP₃''⟩ : ∃ P₃'' : Sylow 3 G, (P₃''.toSubgroup).Normal :=
    ⟨{ P₃'.toSubgroup.map (N₅ ⊔ P₃).subtype with
       isPGroup' := IsPGroup.map P₃'.isPGroup' (N₅ ⊔ P₃).subtype
       is_maximal' := h_is_maximal }, hP₃'⟩

  exact Fintype.card_eq_one_iff.mpr ⟨P₃'', fun P ↦ let ⟨g, hg⟩ := MulAction.exists_smul_eq G P₃'' P; hg.symm.trans Sylow.smul_eq_of_normal⟩

@[nolint unusedArguments]
lemma no_normal_30_with_all_sylow3 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 60)
    (N : Subgroup G) [N.Normal]
    (hN30 : Nat.card N = 30)
    (hn3 : Fintype.card (Sylow 3 G) = 10)
    (hP : ∀ P : Sylow 3 G, (P : Subgroup G) ≤ N) : False := by
  obtain ⟨P₃, hP₃⟩ := Fintype.card_eq_one_iff.mp (order_30_unique_sylow_3 hN30)

  have h_unique : ∀ P : Sylow 3 G, P.toSubgroup = P₃.toSubgroup.map N.subtype := fun P ↦ by
    have hP_card : Nat.card (P.toSubgroup.subgroupOf N) = 3 :=
      (Nat.card_congr ⟨fun (x : P.toSubgroup.subgroupOf N) ↦ (⟨x.1.1, x.2⟩ : P.toSubgroup), fun x ↦ (⟨⟨x.1, hP P x.2⟩, x.2⟩ : P.toSubgroup.subgroupOf N), fun _ ↦ rfl, fun _ ↦ rfl⟩ : Nat.card _ = Nat.card P.toSubgroup).trans
        (P.card_eq_multiplicity.trans (by rw [hn, factorization_60_3, pow_one]))

    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := 3) (fun x ↦ ⟨1, by
      rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mp (hP_card ▸ (show orderOf x ∣ Nat.card (Subgroup.zpowers x) by rw [Nat.card_zpowers]).trans (Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x)))⟩)

    exact (Subgroup.map_subgroupOf_eq_of_le (hP P)).symm.trans <| congrArg (Subgroup.map N.subtype) <|
      (SetLike.ext' <| Set.eq_of_subset_of_ncard_le hQ ((Q.card_eq_multiplicity.trans (by rw [hN30, factorization_30_3, pow_one]) : Nat.card Q.toSubgroup = 3).trans hP_card.symm).le).trans (congrArg Sylow.toSubgroup (hP₃ Q))

  have h_one : Fintype.card (Sylow 3 G) ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun P Q ↦ SetLike.ext' (congrArg ((↑) : Subgroup G → Set G) ((h_unique P).trans (h_unique Q).symm))
  omega

@[nolint unusedArguments]
lemma no_normal_30_with_all_sylow5 {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 60)
    (N : Subgroup G) [N.Normal]
    (hN30 : Nat.card N = 30)
    (hn5 : Fintype.card (Sylow 5 G) = 6)
    (hP : ∀ P : Sylow 5 G, (P : Subgroup G) ≤ N) : False := by
  obtain ⟨P₅, hP₅⟩ := Fintype.card_eq_one_iff.mp (order_30_unique_sylow_5 hN30)

  have h_unique : ∀ P : Sylow 5 G, P.toSubgroup = P₅.toSubgroup.map N.subtype := fun P ↦ by
    have hP_card : Nat.card (P.toSubgroup.subgroupOf N) = 5 :=
      (Nat.card_congr ⟨fun (x : P.toSubgroup.subgroupOf N) ↦ (⟨x.1.1, x.2⟩ : P.toSubgroup), fun x ↦ (⟨⟨x.1, hP P x.2⟩, x.2⟩ : P.toSubgroup.subgroupOf N), fun _ ↦ rfl, fun _ ↦ rfl⟩ : Nat.card _ = Nat.card P.toSubgroup).trans
        (P.card_eq_multiplicity.trans (by rw [hn, factorization_60_5, pow_one]))

    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := 5) (fun x ↦ ⟨1, by
      rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mp (hP_card ▸ (show orderOf x ∣ Nat.card (Subgroup.zpowers x) by rw [Nat.card_zpowers]).trans (Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x)))⟩)

    exact (Subgroup.map_subgroupOf_eq_of_le (hP P)).symm.trans <| congrArg (Subgroup.map N.subtype) <|
      (SetLike.ext' <| Set.eq_of_subset_of_ncard_le hQ ((Q.card_eq_multiplicity.trans (by rw [hN30, factorization_30_5, pow_one]) : Nat.card Q.toSubgroup = 5).trans hP_card.symm).le).trans (congrArg Sylow.toSubgroup (hP₅ Q))

  have h_one : Fintype.card (Sylow 5 G) ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun P Q ↦ SetLike.ext' (congrArg ((↑) : Subgroup G → Set G) ((h_unique P).trans (h_unique Q).symm))
  omega



lemma normal_with_element_contains_all_sylow {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact (Nat.Prime q)]
    (N : Subgroup G) [N.Normal]
    (hSylow_prime : ∀ P : Sylow q G, Nat.card (P : Subgroup G) = q)
    (g : G) (hgN : g ∈ N) (hg : orderOf g = q) :
    ∀ P : Sylow q G, (P : Subgroup G) ≤ N := by
  obtain ⟨P₀, h_le⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card ((Nat.card_zpowers g).trans (hg.trans (pow_one q).symm)))
  have hP₀ : g ∈ (P₀ : Subgroup G) := h_le (Subgroup.mem_zpowers g)
  have h_card : (P₀ : Set G).ncard ≤ (Subgroup.zpowers g : Set G).ncard :=
    ((Nat.card_coe_set_eq (P₀ : Set G)).symm.trans <|
      (hSylow_prime P₀).trans <|
        hg.symm.trans <|
          (Nat.card_zpowers g).symm.trans <|
            Nat.card_coe_set_eq (Subgroup.zpowers g : Set G)).le

  exact normal_contains_all_sylow N P₀ <|
    SetLike.ext' (Set.eq_of_subset_of_ncard_le (Subgroup.zpowers_le.mpr hP₀) h_card) ▸
      Subgroup.zpowers_le.mpr hgN


lemma cauchy_element_in_subgroup {G : Type*} [Group G] [Finite G]
    {q : ℕ} [Fact (Nat.Prime q)]
    (N : Subgroup G) (hN : q ∣ Nat.card N) :
    ∃ g : G, g ∈ N ∧ orderOf g = q :=
  let ⟨⟨g, hg⟩, hq_ord⟩ := exists_prime_orderOf_dvd_card' q hN
  ⟨g, hg, (Subgroup.orderOf_coe ⟨g, hg⟩).trans hq_ord⟩

lemma sylow_prime_pairwise_disjoint {G : Type*} [Group G] [Finite G]
    {q : ℕ} [hq : Fact (Nat.Prime q)]
    (hS : ∀ P : Sylow q G, Nat.card (P : Subgroup G) = q)
    (P Q : Sylow q G) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  have h_dvd := hS P ▸ Subgroup.card_dvd_of_le (inf_le_left : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ P)
  rcases (Nat.dvd_prime hq.out).mp h_dvd with h_one | h_q
  · exact Subgroup.card_eq_one.mp h_one
  · have h_eq : (P : Subgroup G) ⊓ Q = P :=
      SetLike.ext' <| Set.eq_of_subset_of_ncard_le inf_le_left <|
        (((Nat.card_coe_set_eq _).symm : (P : Set G).ncard = Nat.card (P : Subgroup G)).trans <|
          (hS P).trans <| h_q.symm.trans (Nat.card_coe_set_eq _)).le
    have h_PQ : (P : Subgroup G) = Q :=
      SetLike.ext' <| Set.eq_of_subset_of_ncard_le (h_eq ▸ inf_le_right) <|
        (((Nat.card_coe_set_eq _).symm : (Q : Set G).ncard = Nat.card (Q : Subgroup G)).trans <|
          (hS Q).trans <| (hS P).symm.trans (Nat.card_coe_set_eq _)).le
    exact absurd (Sylow.ext h_PQ) hPQ


lemma card_ge_of_contains_all_sylow {G : Type*} [Group G] [Finite G]
    {q : ℕ} [hq : Fact (Nat.Prime q)]
    (N : Subgroup G)
    (hS : ∀ P : Sylow q G, Nat.card (P : Subgroup G) = q)
    (hN : ∀ P : Sylow q G, (P : Subgroup G) ≤ N)
    (n_sylow : ℕ) (hn_sylow : Fintype.card (Sylow q G) = n_sylow) :
    Nat.card N ≥ n_sylow * (q - 1) + 1 := by

  let U : Sylow q G → Finset G := fun P ↦ (P : Set G).toFinset \ {1}

  have h_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Sylow q G))) U := fun P _ Q _ hPQ ↦
    Finset.disjoint_left.mpr fun x hxP hxQ ↦
      (Finset.mem_sdiff.mp hxP).2 <| Finset.mem_singleton.mpr <| Subgroup.mem_bot.mp <|
        sylow_prime_pairwise_disjoint hS P Q hPQ ▸
          (⟨Set.mem_toFinset.mp (Finset.mem_sdiff.mp hxP).1, Set.mem_toFinset.mp (Finset.mem_sdiff.mp hxQ).1⟩ : x ∈ (P : Subgroup G) ⊓ (Q : Subgroup G))

  have h_card : ∀ P : Sylow q G, (U P).card = q - 1 := fun P ↦ by
    have h_sub : ({1} : Finset G) ⊆ (P : Set G).toFinset :=
      Finset.singleton_subset_iff.mpr <| Set.mem_toFinset.mpr <| Subgroup.one_mem (P : Subgroup G)
    have hP_card : ((P : Set G).toFinset).card = q :=
      (Set.ncard_eq_toFinset_card' _).symm.trans ((Nat.card_coe_set_eq _).symm.trans (hS P))
    exact (Finset.card_sdiff_of_subset h_sub).trans (by rw [Finset.card_singleton, hP_card])

  have h_subset : insert 1 (Finset.univ.biUnion U) ⊆ (N : Set G).toFinset := by
    rw [Finset.insert_subset_iff, Finset.biUnion_subset]
    exact ⟨Set.mem_toFinset.mpr (Subgroup.one_mem N), fun P _ x hx ↦
      Set.mem_toFinset.mpr <| hN P <| Set.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1⟩

  have h_eq : (insert 1 (Finset.univ.biUnion U)).card = n_sylow * (q - 1) + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_biUnion h_disj, Finset.sum_congr rfl (fun P _ ↦ h_card P),
      Finset.sum_const, Finset.card_univ, hn_sylow, nsmul_eq_mul, Nat.cast_id]
    exact fun h ↦ let ⟨_, _, hP⟩ := Finset.mem_biUnion.mp h; (Finset.mem_sdiff.mp hP).2 (Finset.mem_singleton.mpr rfl)

  have h_N_card : Nat.card N = (N : Set G).toFinset.card :=
    (Nat.card_coe_set_eq _).trans (Set.ncard_eq_toFinset_card' _)
  exact h_N_card.symm ▸ h_eq ▸ Finset.card_le_card h_subset

lemma normal_divides_4_eq_bot {G : Type*} [Group G] [Finite G]
    (hn : Nat.card G = 60)
    (hn3 : Fintype.card (Sylow 3 G) = 10)
    (N : Subgroup G) [N.Normal]
    (hN_div : Nat.card N ∣ 4)
    (hN_ne_bot : N ≠ ⊥) : False := by

  have hGN_card : Nat.card (G ⧸ N) = 15 ∨ Nat.card (G ⧸ N) = 30 := by
    have hc : Nat.card (G ⧸ N) * Nat.card N = 60 := by rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    have h2 : Nat.card N ≤ 4 := Nat.le_of_dvd (Nat.zero_lt_succ 3) hN_div
    have h_pos : 1 ≤ Nat.card N := Nat.pos_of_ne_zero fun h0 ↦ Nat.succ_ne_zero 3 (eq_zero_of_zero_dvd (h0 ▸ hN_div))
    interval_cases h : Nat.card N
    · exact absurd (eq_bot_iff.mpr fun x hx ↦ orderOf_eq_one_iff.mp <| Nat.dvd_one.mp <| h ▸
        ((Nat.card_zpowers x).symm ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx) : orderOf x ∣ Nat.card N)) hN_ne_bot
    · right; exact Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ 1) ((h ▸ hc : Nat.card (G ⧸ N) * 2 = 60).trans (by rfl))
    · exact absurd (h ▸ hN_div : 3 ∣ 4) (by norm_num)
    · left; exact Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ 3) ((h ▸ hc : Nat.card (G ⧸ N) * 4 = 60).trans (by rfl))
  obtain ⟨Q, hQ⟩ := Fintype.card_eq_one_iff.mp (hGN_card.elim order_15_unique_sylow_3 order_30_unique_sylow_3)
  have hQ_card : Nat.card Q.toSubgroup = 3 :=
    Sylow.card_eq_multiplicity Q |>.trans (by rcases hGN_card with h | h <;> rw [h] <;> simp only [factorization_15_3, factorization_30_3, pow_one])
  let M := Subgroup.comap (QuotientGroup.mk' N) Q.toSubgroup
  have hM_card : Nat.card M ≤ 12 := by
    have h_idx := Subgroup.card_mul_index Q.toSubgroup
    have eq_idx : Q.toSubgroup.index > 0 := Nat.pos_of_ne_zero fun h0 ↦ by
      rcases hGN_card with h | h <;> exact absurd (show Nat.card (G ⧸ N) = 0 by rw [← h_idx, h0, mul_zero] |>.symm ▸ h) (by norm_num)
    have h4 : Nat.card M = 3 * Nat.card N := Nat.eq_of_mul_eq_mul_right eq_idx <| by
      rw [← Q.toSubgroup.index_comap_of_surjective (QuotientGroup.mk'_surjective N), Subgroup.card_mul_index M,
          Subgroup.card_eq_card_quotient_mul_card_subgroup N, ← h_idx, hQ_card,
          Q.toSubgroup.index_comap_of_surjective (QuotientGroup.mk'_surjective N)]; ring
    exact h4.symm ▸ Nat.mul_le_mul_left 3 (Nat.le_of_dvd (Nat.zero_lt_succ 3) hN_div)
  have hP_card : ∀ P : Sylow 3 G, Nat.card (P : Subgroup G) = 3 := fun P ↦
    (Sylow.card_eq_multiplicity P).trans (by rw [hn, factorization_60_3, pow_one])
  have hP_le : ∀ P : Sylow 3 G, (P : Subgroup G) ≤ M := fun P ↦ by
    obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow (IsPGroup.map P.isPGroup' (QuotientGroup.mk' N))
    exact Subgroup.map_le_iff_le_comap.mp (hQ Q' ▸ hQ')
  exact absurd ((card_ge_of_contains_all_sylow M hP_card hP_le 10 hn3).trans hM_card : 21 ≤ 12) (by norm_num)

lemma sylow3_in_normal_forces_large {G : Type*} [Group G] [Finite G]
    (hn3 : Fintype.card (Sylow 3 G) = 10)
    (hS3 : ∀ P : Sylow 3 G, Nat.card (P : Subgroup G) = 3)
    (N : Subgroup G)
    (hN : ∀ P : Sylow 3 G, (P : Subgroup G) ≤ N)
    (hN_card : Nat.card N ∣ 60)
    (hN_ne_top : Nat.card N ≠ 60) :
    Nat.card N = 30 := by
  obtain ⟨k, hk⟩ := hN_card
  have : k ≤ 2 := by
    have := (Nat.mul_le_mul_right k (card_ge_of_contains_all_sylow N hS3 hN 10 hn3)).trans (le_of_eq hk.symm)
    omega
  interval_cases k <;> omega

lemma sylow5_in_normal_forces_large {G : Type*} [Group G] [Finite G]
    (hn5 : Fintype.card (Sylow 5 G) = 6)
    (hS5 : ∀ P : Sylow 5 G, Nat.card (P : Subgroup G) = 5)
    (N : Subgroup G)
    (hN : ∀ P : Sylow 5 G, (P : Subgroup G) ≤ N)
    (hN_card : Nat.card N ∣ 60)
    (hN_ne_top : Nat.card N ≠ 60) :
    Nat.card N = 30 := by
  obtain ⟨k, hk⟩ := hN_card
  have : k ≤ 2 := by
    have := (Nat.mul_le_mul_right k (card_ge_of_contains_all_sylow N hS5 hN 6 hn5)).trans (le_of_eq hk.symm)
    omega
  interval_cases k <;> omega

@[nolint unusedArguments]
lemma is_simple_60_aux {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hn : Nat.card G = 60)
    (hn3 : Fintype.card (Sylow 3 G) = 10)
    (hn5 : Fintype.card (Sylow 5 G) = 6)
    (N : Subgroup G) [hN_normal : N.Normal] :
    N = ⊥ ∨ N = ⊤ := by
  have hS3 : ∀ P : Sylow 3 G, Nat.card (P : Subgroup G) = 3 := fun P ↦
    P.card_eq_multiplicity.trans (by rw [hn, factorization_60_3, pow_one])
  have hS5 : ∀ P : Sylow 5 G, Nat.card (P : Subgroup G) = 5 := fun P ↦
    P.card_eq_multiplicity.trans (by rw [hn, factorization_60_5, pow_one])
  by_cases hN_top : Nat.card N = 60
  · right
    rw [← Subgroup.index_eq_one]
    have h_mul := Subgroup.card_mul_index N
    rw [hN_top, hn] at h_mul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h_mul.trans (mul_one 60).symm)
  · left
    by_contra hN_ne_bot
    have h_dvd : Nat.card N ∣ 60 := hn ▸ Subgroup.card_subgroup_dvd_card N
    by_cases hN_div_3 : 3 ∣ Nat.card N
    · obtain ⟨g, hgN, hg⟩ := cauchy_element_in_subgroup N hN_div_3
      have hN_all3 := normal_with_element_contains_all_sylow N hS3 g hgN hg
      exact no_normal_30_with_all_sylow3 hn N (sylow3_in_normal_forces_large hn3 hS3 N hN_all3 h_dvd hN_top) hn3 hN_all3
    · by_cases hN_div_5 : 5 ∣ Nat.card N
      · obtain ⟨g, hgN, hg⟩ := cauchy_element_in_subgroup N hN_div_5
        have hN_all5 := normal_with_element_contains_all_sylow N hS5 g hgN hg
        exact no_normal_30_with_all_sylow5 hn N (sylow5_in_normal_forces_large hn5 hS5 N hN_all5 h_dvd hN_top) hn5 hN_all5
      · have h_cop : Nat.Coprime (Nat.card N) 15 := by
          rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.coprime_mul_iff_right]
          exact ⟨(Nat.prime_three.coprime_iff_not_dvd.mpr hN_div_3).symm,
                 (Nat.prime_five.coprime_iff_not_dvd.mpr hN_div_5).symm⟩
        exact normal_divides_4_eq_bot hn hn3 N (h_cop.dvd_of_dvd_mul_right (show Nat.card N ∣ 4 * 15 from h_dvd)) hN_ne_bot

theorem is_simple_60 (G : Subgroup (PGL p))
    [Finite G] (hp3 : p = 3)
    (hn : Nat.card G = 60) (hn3 : Fintype.card (Sylow p G) = 10) :
    IsSimpleGroup G :=
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (hn.symm ▸ by norm_num)
  { eq_bot_or_eq_top_of_normal := fun N hN ↦
      is_simple_60_aux hn (hp3 ▸ hn3) ((sylow_5_options G hn).resolve_left (sylow_5_not_one p G hp3 hn hn3)) N }

lemma simple_group_faithful_action_on_sylow {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) {q : ℕ} [Fact (Nat.Prime q)]
    (hn_ne_1 : Fintype.card (Sylow q G) ≠ 1) :
    Function.Injective (MulAction.toPermHom G (Sylow q G)) := by
  let hf := MulAction.toPermHom G (Sylow q G)
  rcases hs.2 hf.ker (MonoidHom.normal_ker hf) with h | h
  · exact (MonoidHom.ker_eq_bot_iff hf).mp h
  · exact absurd (Fintype.card_eq_one_iff.mpr ⟨Classical.arbitrary _, fun P ↦ by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (Classical.arbitrary _)
      exact hg ▸ (DFunLike.congr_fun (hf.mem_ker.mp (h ▸ Subgroup.mem_top g)) P).symm⟩) hn_ne_1


lemma simple_60_n2_ne_15 (G : Type*) [Group G] [Finite G]
    (hn : Nat.card G = 60) (hs : IsSimpleGroup G) :
    Fintype.card (Sylow 2 G) ≠ 15 := by
  intro hn2
  let P : Sylow 2 G := Classical.arbitrary (Sylow 2 G)
  have hP_card : Nat.card (P : Subgroup G) = 4 :=
    P.card_eq_multiplicity.trans (by rw [hn, factorization_60_2]; rfl)
  have h_cent : (Subgroup.normalizer ((P : Subgroup G) : Set G)) ≤ Subgroup.centralizer (P : Set G) := by
    have h_norm_idx : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 15 := by
      show (Subgroup.normalizer (P : Set G)).index = 15
      rw [← Sylow.card_eq_index_normalizer P, Nat.card_eq_fintype_card, hn2]
    have h_norm_card : Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 4 :=
      Nat.eq_of_mul_eq_mul_right (show 0 < 15 by norm_num) (
        (congrArg (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) * ·) h_norm_idx.symm).trans
          ((Subgroup.card_mul_index _).trans (hn.trans (rfl : 60 = 4 * 15))))
    have h_norm_eq : (P : Subgroup G) = (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
      SetLike.ext' (Set.eq_of_subset_of_ncard_le Subgroup.le_normalizer
        ((Nat.card_coe_set_eq ((Subgroup.normalizer ((P : Subgroup G) : Set G)) : Set G)).symm.trans
          (h_norm_card.trans (hP_card.symm.trans (Nat.card_coe_set_eq (P : Set G))))).le)
    rw [← h_norm_eq]
    exact fun x hx y hy ↦ Subtype.ext_iff.mp
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := P) (p := 2)
        (hP_card.trans (rfl : 4 = 2 ^ 2))).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  rcases hs.2 _ (MonoidHom.normal_ker (MonoidHom.transferSylow P h_cent)) with h | h
  · exact absurd (MonoidHom.ker_transferSylow_isComplement' P h_cent).card_mul
      (by rw [h, Subgroup.card_bot, hP_card, hn]; norm_num)
  · exact absurd (MonoidHom.ker_transferSylow_isComplement' P h_cent).card_mul
      (by rw [h, Subgroup.card_top, hn, hP_card]; norm_num)

lemma simple_60_n2_eq_5 (G : Type*) [Group G] [Finite G]
    (hn : Nat.card G = 60) (hs : IsSimpleGroup G) :
    Fintype.card (Sylow 2 G) = 5 := by
  have h_div15 : Fintype.card (Sylow 2 G) ∣ 15 :=
    sylow_card_dvd_index 2 15 60 2 hn rfl factorization_60_2
  have h_cases : Fintype.card (Sylow 2 G) = 1 ∨ Fintype.card (Sylow 2 G) = 3 ∨
      Fintype.card (Sylow 2 G) = 5 ∨ Fintype.card (Sylow 2 G) = 15 := by
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow 2 G) = 2 * k + 1 := ⟨Fintype.card (Sylow 2 G) / 2, by
      have : Fintype.card (Sylow 2 G) % 2 = 1 := by rw [← Nat.card_eq_fintype_card]; exact card_sylow_modEq_one 2 G
      omega⟩
    have : k ≤ 7 := by have := Nat.le_of_dvd (by norm_num) h_div15; omega
    interval_cases k <;> (revert h_div15; rw [hk]; norm_num)
  rcases h_cases with h1 | h3 | h5 | h15
  · obtain ⟨P, hP⟩ := Fintype.card_eq_one_iff.mp h1
    have hP_card : Nat.card (P : Subgroup G) = 4 :=
      P.card_eq_multiplicity.trans (by rw [hn, factorization_60_2]; rfl)
    rcases hs.2 (P : Subgroup G)
      ⟨fun _ hmem g ↦ hP (g • P) ▸ Subgroup.mem_map_of_mem _ hmem⟩ with h | h
    · exact absurd hP_card (by rw [h, Subgroup.card_bot]; norm_num)
    · exact absurd hP_card (by rw [h, Subgroup.card_top, hn]; norm_num)
  · exact absurd (hn ▸ Nat.card_le_card_of_injective _
        (simple_group_faithful_action_on_sylow hs (by rw [h3]; norm_num)) : 60 ≤ _)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]; norm_num)
  · exact h5
  · exact absurd h15 (simple_60_n2_ne_15 G hn hs)

theorem simple_60_is_A5 (G : Type*) [Group G] [Finite G]
    (hn : Nat.card G = 60) (hs : IsSimpleGroup G) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  let f := MulAction.toPermHom G (Sylow 2 G)
  have h_iso_range : G ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict ⟨fun x y h ↦ (simple_group_faithful_action_on_sylow hs (by rw [simple_60_n2_eq_5 G hn hs]; norm_num)) (congrArg Subtype.val h),
      fun ⟨z, hz⟩ ↦ hz.elim fun y hy ↦ ⟨y, Subtype.ext hy⟩⟩
  have h_index : f.range.index = 2 := by
    have h_perm_card : Nat.card (Equiv.Perm (Sylow 2 G)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, simple_60_n2_eq_5 G hn hs]; rfl
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 60 by norm_num) (
      (congrArg (f.range.index * ·) (hn.symm.trans (Nat.card_congr h_iso_range.toEquiv))).trans
        ((Subgroup.index_mul_card _).trans
          (h_perm_card.trans (rfl : 120 = 2 * 60))))
  exact ⟨(h_iso_range.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h_index))).trans
    (Fintype.equivOfCardEq ((simple_60_n2_eq_5 G hn hs).trans (Fintype.card_fin 5).symm)).altCongrHom⟩

theorem recognition_A5_proof (G : Subgroup (PGL p))
    [Finite G] (hp3 : p = 3)
    (hn : Nat.card G = 60) (hn3 : Fintype.card (Sylow p G) = 10) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) :=
  simple_60_is_A5 G hn (is_simple_60 p G hp3 hn hn3)

end

end Dickson
