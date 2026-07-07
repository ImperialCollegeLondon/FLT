/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.GroupTheory.PGroup
public import FLT.Slop.BrauerInduction.Background.Group.Conjugacy

/-!

# `p`-regular and `p`-singular elements

This file introduces `p`-regular and `p`-singular elements in a group `G`,
and formalizes the `p`-decomposition for elements of finite order.

An element is `p`-regular if its order is coprime to `p`, and `p`-singular if
its order is a power of `p`.

Every element `x` of finite order can be uniquely decomposed as

`x = s * r = r * s`,

where `s` is `p`-singular and `r` is `p`-regular.

## Main definitions

* `IsPRegular p a`: A predicate stating that the order of `a` is coprime to `p`.
* `IsPSingular p a`: A predicate stating that the order of `a` is a power of `p`.
* `Group.pRegular p a`: The canonical `p`-regular factor of `a`.
* `Group.pSingular p a`: The canonical `p`-singular factor of `a`.

## Main results

* `Group.pDecomp`: the decomposition theorem `pSingular p a * pRegular p a = a`.
* `Group.pDecomp'`: the reversed version `pRegular p a * pSingular p a = a`.
* `Group.pDecomp_commute`: the `p`-singular and `p`-regular factors commute.
* `Group.pSingular_pRegular_unique`: uniqueness of the `p`-decomposition.
* `Group.pDecomp_mul_of_commute`: the `p`-decomposition of a commuting product.

-/

@[expose] public section

namespace Slop
open Slop

universe u v

variable {G : Type u} [Group G]
variable (p : ℕ)

lemma Nat.ordProj_ordCompl_coprime {n : ℕ} [Fact p.Prime] (h : n ≠ 0) :
    let a := ordProj[p] n
    let b := ordCompl[p] n
    Nat.Coprime a b := by
  have hcop : Nat.Coprime p (ordCompl[p] n) :=
     Nat.coprime_ordCompl (Fact.out : Nat.Prime p) h
  exact Nat.gcd_pow_left_of_gcd_eq_one hcop

/-- An element of a group is `p`-regular if its order is coprime to `p`. -/
def IsPRegular (a : G) : Prop := Nat.Coprime (orderOf a) p

namespace IsPRegular

@[simp]
lemma one : IsPRegular p (1 : G) := by simp [IsPRegular]

lemma order_coprime {a : G} (h : IsPRegular p a) :
    Nat.Coprime (orderOf a) p := h

/-- An element is `p`-regular iff its inverse is `p`-regular. -/
lemma inv_iff (a : G) : IsPRegular p a⁻¹ ↔ IsPRegular p a := by
    simp only [IsPRegular, orderOf_inv]

/--
The product of commuting `p`-regular elements is `p`-regular.
-/
lemma mul {a b : G} (ha : IsPRegular p a) (hb : IsPRegular p b)
    (hcomm : Commute a b) : IsPRegular p (a * b) := by
  have h_dvd : orderOf (a * b) ∣ orderOf a * orderOf b :=
    Commute.orderOf_mul_dvd_mul_orderOf hcomm
  exact Nat.Coprime.coprime_dvd_left h_dvd (Nat.Coprime.mul_left ha hb)

/--
The image of a `p`-regular element under a group homomorphism is `p`-regular.
-/
lemma map {H : Type v} [Group H] (f : G →* H) {a : G}
    (h : IsPRegular p a) : IsPRegular p (f a) := by
  have h_dvd : orderOf (f a) ∣ orderOf a := orderOf_map_dvd f a
  exact Nat.Coprime.coprime_dvd_left h_dvd h

lemma isConj {a b : G} (ha : IsPRegular p a) (h : IsConj a b) :
    IsPRegular p b := by
  simpa only [IsPRegular, IsConj.orderOf_eq h] using ha

lemma conj {a : G} (h : IsPRegular p a) (b : G) :
    IsPRegular p (b * a * b⁻¹) :=
      IsPRegular.isConj p h (isConj_iff.mpr ⟨b, rfl⟩)

lemma conj' {a : G} (h : IsPRegular p a) (b : G) :
    IsPRegular p (b⁻¹ * a * b) :=
      IsPRegular.isConj p h (isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩)

/-- p-regularity is invariant under conjugacy. -/
lemma iff_isConj {a b : G} (h : IsConj a b) :
    IsPRegular p a ↔ IsPRegular p b :=
  ⟨fun ha ↦ isConj p ha h, fun hb ↦ isConj p hb h.symm⟩

lemma not_dvd_orderOf [Fact p.Prime] {a : G} (h : IsPRegular p a) :
    ¬ p ∣ orderOf a := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h.symm

/--
A `p`-regular element has finite order, provided `p` is prime.
-/
lemma isOfFinOrder [Fact p.Prime] {a : G}
    (h : IsPRegular p a) :
    IsOfFinOrder a := by
  rw [← orderOf_ne_zero_iff]
  intro hzero
  have hp_dvd : p ∣ orderOf a := by
    rw [hzero]
    exact dvd_zero p
  exact h.not_dvd_orderOf p hp_dvd

/-- A `p`-regular element has nonzero order. -/
lemma neZero_orderOf
    [Fact p.Prime] {a : G} (ha : IsPRegular p a) :
    NeZero (orderOf a) :=
  ⟨(orderOf_ne_zero_iff).2 (IsPRegular.isOfFinOrder p ha)⟩

lemma orderOf_dvd_ordCompl [Fact p.Prime] {a : G} (h : IsPRegular p a) {n : ℕ}
    (hd : orderOf a ∣ n) : orderOf a ∣ ordCompl[p] n :=
  Nat.dvd_ordCompl_of_dvd_not_dvd hd h.not_dvd_orderOf

lemma of_mem_zpowers {a b : G} (ha : a ∈ Subgroup.zpowers b) (hb : IsPRegular p b) :
    IsPRegular p a := by
  have h_dvd : orderOf a ∣ orderOf b := orderOf_dvd_of_mem_zpowers ha
  exact Nat.Coprime.coprime_dvd_left h_dvd hb

/--
A power of a `p`-regular element is `p`-regular.
-/
lemma pow (a : G) (h : IsPRegular p a) (n : ℕ) :
    IsPRegular p (a ^ n) :=
  h.coprime_dvd_left (orderOf_pow_dvd n)

lemma pow_ordProj [Fact p.Prime] {a : G} (ha : IsOfFinOrder a) :
    IsPRegular p (a ^ ordProj[p] (orderOf a)) := by
  let n : ℕ := orderOf a
  have hn0 : n ≠ 0 := orderOf_ne_zero_iff.mpr ha
  -- ordCompl[p] n is coprime to p
  have hcop : Nat.Coprime (ordCompl[p] n) p := by
    simpa [Nat.coprime_comm, n] using Nat.coprime_ordCompl Fact.out hn0
  have hpow1 :
      (a ^ ordProj[p] n) ^ ordCompl[p] n = 1 := by
    calc
      (a ^ ordProj[p] n) ^ ordCompl[p] n
          = a ^ (ordProj[p] n * ordCompl[p] n) := by
              rw [pow_mul]
      _ = a ^ n := by
              rw [Nat.ordProj_mul_ordCompl_eq_self]
      _ = 1 := by
              simp only [pow_orderOf_eq_one a, n]
  have hdvd : orderOf (a ^ ordProj[p] n) ∣ ordCompl[p] n :=
    orderOf_dvd_of_pow_eq_one hpow1
  exact hcop.of_dvd_left hdvd

@[simp]
lemma subtype_iff
    {H : Subgroup G} (x : H) :
    IsPRegular p ((x : H) : G) ↔ IsPRegular p x := by
  simp only [IsPRegular, orderOf_submonoid]

end IsPRegular

/-- An element of a group is `p`-singular if its order is a power of `p`. -/
def IsPSingular (a : G) : Prop := ∃ n, orderOf a = p ^ n

namespace IsPSingular

@[simp]
lemma one : IsPSingular p (1 : G) := ⟨0, by simp⟩

/-- An element is `p`-singular iff its inverse is `p`-singular. -/
lemma inv_iff (a : G) : IsPSingular p a⁻¹ ↔ IsPSingular p a := by
    simp only [IsPSingular, orderOf_inv]

/--
The product of commuting `p`-singular elements is `p`-singular.
-/
lemma mul [Fact p.Prime] {a b : G} (ha : IsPSingular p a)
    (hb : IsPSingular p b) (hcomm : Commute a b) : IsPSingular p (a * b) := by
  rcases ha with ⟨n, ha⟩
  rcases hb with ⟨m, hb⟩
  have h_dvd : orderOf (a * b) ∣ orderOf a * orderOf b :=
    Commute.orderOf_mul_dvd_mul_orderOf hcomm
  rw [ha, hb, ← pow_add] at h_dvd
  obtain ⟨k, -, heq⟩ := (Nat.dvd_prime_pow Fact.out).mp h_dvd
  exact ⟨k, heq⟩

lemma map [Fact p.Prime] {H : Type v} [Group H] (f : G →* H) {a : G}
    (ha : IsPSingular p a) : IsPSingular p (f a) := by
  rcases ha with ⟨n, hn⟩
  have h_dvd : orderOf (f a) ∣ orderOf a := orderOf_map_dvd f a
  rw [hn] at h_dvd
  obtain ⟨k, -, heq⟩ := (Nat.dvd_prime_pow Fact.out).mp h_dvd
  exact ⟨k, heq⟩

lemma isConj {a b : G} (ha : IsPSingular p a) (h : IsConj a b) :
    IsPSingular p b := by
  obtain ⟨n,hn⟩ := ha
  use n
  rw [← hn]
  exact IsConj.orderOf_eq (IsConj.symm h)

lemma conj {a : G} (h : IsPSingular p a) (b : G) :
    IsPSingular p (b * a * b⁻¹) :=
      IsPSingular.isConj p h (isConj_iff.mpr ⟨b, rfl⟩)

lemma conj' {a : G} (h : IsPSingular p a) (b : G) :
    IsPSingular p (b⁻¹ * a * b) :=
      IsPSingular.isConj p h (isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩)

/--
A `p`-singular element has finite order, provided `p` is prime.
-/
lemma isOfFinOrder [Fact p.Prime] {a : G}
    (h : IsPSingular p a) :
    IsOfFinOrder a := by
  rcases h with ⟨n, hn⟩
  rw [← orderOf_ne_zero_iff]
  rw [hn]
  exact pow_ne_zero n (Nat.Prime.ne_zero Fact.out)

/-- A `p`-regular element has nonzero order. -/
lemma neZero_orderOf
    [Fact p.Prime] {a : G} (h : IsPSingular p a) :
    NeZero (orderOf a) :=
  ⟨(orderOf_ne_zero_iff).2 (IsPSingular.isOfFinOrder p h)⟩

lemma orderOf_dvd_ordProj [Fact p.Prime] {a : G} (h : IsPSingular p a) {n : ℕ}
    (hd : orderOf a ∣ n) (hn : n ≠ 0) :
    orderOf a ∣ ordProj[p] n := by
  rcases h with ⟨a, ha⟩
  rw [ha] at hd ⊢
  exact (Nat.Prime.pow_dvd_iff_dvd_ordProj (Fact.out : Nat.Prime p) hn).mp hd

/--
An element is `p`-singular iff the cyclic subgroup it generates is a
`p`-group.
-/
lemma iff_zpowers_isPGroup [Fact p.Prime] (a : G) :
    IsPSingular p a ↔ IsPGroup p (Subgroup.zpowers a) := by
  unfold IsPSingular
  rw [IsPGroup.iff_orderOf]
  constructor
  · rintro ⟨n, hn⟩ ⟨b, hb⟩
    rcases hb with ⟨m, rfl⟩
    have h_dvd : orderOf (a ^ m) ∣ p ^ n := by
      rw [← hn]
      apply orderOf_dvd_of_mem_zpowers
      simp only [Subgroup.zpow_mem_zpowers]
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 h_dvd with ⟨m, _, heq⟩
    use m
    simp [← heq, ← Subgroup.orderOf_coe]
  · intro hg
    rcases hg ⟨a, Subgroup.mem_zpowers a⟩ with ⟨n, hn⟩
    use n
    simp [← hn, ← Subgroup.orderOf_coe]

lemma isPRegular_eq_one [Fact p.Prime]
    (a : G) (hs : IsPSingular p a) (hr : IsPRegular p a) :
    a = 1 := by
  simp only [IsPSingular, IsPRegular] at *
  obtain ⟨n, hn⟩ := hs
  rw [hn] at hr
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  cases n with
  | zero => exact orderOf_eq_one_iff.mp hn
  | succ k =>
    rw [Nat.coprime_pow_left_iff] at hr
    · rw [Nat.coprime_self] at hr
      simp only [hr, lt_self_iff_false] at hp
    · simp

@[simp]
lemma subtype_iff
    {H : Subgroup G} (x : H) :
    IsPSingular p ((x : H) : G) ↔ IsPSingular p x := by
  simp only [IsPSingular, orderOf_submonoid]

end IsPSingular

namespace Group

section pRegular

/--
The canonical `p`-regular factor of an element of finite order.

It is defined as a Bezout power of the element, using the decomposition of
`orderOf a` into its `p`-part and prime-to-`p` part.
-/
noncomputable def pRegular (a : G) : G :=
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  a ^ (Nat.gcdA n m * n)

@[simp]
lemma pRegular_one : pRegular p (1 : G) = 1 := by simp [pRegular]

/-- The inverse of a `p`-regular element is `p`-regular. -/
lemma pRegular_inv [Fact p.Prime] {a : G} :
    pRegular p (a⁻¹) = (pRegular p a)⁻¹ := by
  have h_ord : orderOf (a⁻¹) = orderOf a := orderOf_inv a
  simp only [pRegular, h_ord, Nat.cast_pow, inv_zpow', zpow_neg]

lemma pRegular_map {H : Type v} [Group H] (f : G →* H) (hf : Function.Injective f)
    (a : G) : pRegular p (f a) = f (pRegular p a) := by
  have h_ord : orderOf (f a) = orderOf a := orderOf_injective f hf a
  simp only [pRegular, h_ord, Nat.cast_pow, map_zpow]

/-- `orderOf (pRegular p x)` divides the `p'`-part `ordCompl[p] (orderOf x)`. -/
theorem orderOf_pRegular_dvd (a : G) :
    orderOf (pRegular p a) ∣ ordCompl[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  let k : ℤ := Nat.gcdA n m
  have: n * m = orderOf a := Nat.ordProj_mul_ordCompl_eq_self (orderOf a) p
  have hpow : (pRegular p a) ^ m = 1 := by
    calc
      (pRegular p a) ^ m
          = (a ^ (k * n)) ^ m := by
                simp only [pRegular, Nat.cast_pow, m, k, n]
      _   = a ^ ((k * n) * m) := by
                simp only [zpow_mul, zpow_natCast]
      _   = a ^ (k * (n * m)) := by
                rw [mul_assoc]
      _   = a ^ (k * (orderOf a : ℤ)) := by
                simp only [← this, Nat.cast_mul]
      _   = 1 := by
                simp only [zpow_mul, zpow_natCast, zpow_pow_orderOf]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- `pRegular p x` is p-regular: its order is coprime to `p`. -/
@[simp]
lemma isPRegular_pRegular [Fact p.Prime] {a : G} (h : IsOfFinOrder a) :
    IsPRegular p (pRegular p a) := by
  have hdiv : orderOf (pRegular p a) ∣ ordCompl[p] (orderOf a) :=
    orderOf_pRegular_dvd p a
  have hcop : Nat.Coprime p (ordCompl[p] (orderOf a)) :=
    Nat.coprime_ordCompl (Fact.out : Nat.Prime p) (orderOf_ne_zero_iff.mpr h)
  exact (hcop.symm).coprime_dvd_left hdiv

end pRegular

section pSingular

/--
The canonical `p`-singular factor of an element of finite order.

It is defined as a Bezout power of the element, using the decomposition of
`orderOf a` into its `p`-part and prime-to-`p` part.
-/
noncomputable def pSingular (a : G) : G :=
  let m := ordProj[p] (orderOf a)
  let n := ordCompl[p] (orderOf a)
  a ^ (Nat.gcdB m n * n)

@[simp]
lemma pSingular_one : pSingular p (1 : G) = 1 := by simp [pSingular]

lemma pSingular_inv [Fact p.Prime] {a : G} :
    pSingular p (a⁻¹) = (pSingular p a)⁻¹ := by
  have h_ord : orderOf (a⁻¹) = orderOf a := orderOf_inv a
  simp only [pSingular, h_ord, Int.natCast_ediv, Nat.cast_pow, inv_zpow', zpow_neg]

lemma pSingular_map {H : Type v} [Group H] (f : G →* H) (h : Function.Injective f)
    (a : G) : pSingular p (f a) = f (pSingular p a) := by
  have h_ord : orderOf (f a) = orderOf a := orderOf_injective f h a
  simp only [pSingular, h_ord, Int.natCast_ediv, Nat.cast_pow, map_zpow]

theorem orderOf_pSingular_dvd (a : G) :
    orderOf (pSingular p a) ∣ ordProj[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  let k : ℤ := Nat.gcdB n m
  have : n * m = orderOf a := Nat.ordProj_mul_ordCompl_eq_self (orderOf a) p
  have hpow : (pSingular p a) ^ n = 1 := by
    calc
      (pSingular p a) ^ n
          = (a ^ (k * m)) ^ n := by
                simp only [pSingular, Int.natCast_ediv, Nat.cast_pow, n, k, m]
      _   = a ^ ((k * m) * n) := by
                simp only [zpow_mul, zpow_natCast]
      _   = a ^ (k * (m * n)) := by
                rw [mul_assoc]
      _   = a ^ (k * (n * m)) := by
                simp only [mul_comm (n : ℤ) m]
      _   = a ^ (k * (orderOf a : ℤ)) := by
                simp only [← this, Nat.cast_mul]
      _   = 1 := by
                simp only [zpow_mul, zpow_natCast, zpow_pow_orderOf]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- `pSingular p a` is p-singular: its order is a power of `p`. -/
lemma isPSingular_pSingular (a : G) [Fact p.Prime] :
    IsPSingular p (pSingular p a) := by
  let n := ordProj[p] (orderOf a)
  obtain ⟨k, hk⟩ : ∃ k, n = p ^ k := ⟨(orderOf a).factorization p, rfl⟩
  rcases orderOf_pSingular_dvd p a with ⟨m, hm⟩
  have h₁ : orderOf (pSingular p a) ∣ n := orderOf_pSingular_dvd p a
  have h₂ : orderOf (pSingular p a) ∣ p ^ k := by rw [← hk]; exact h₁
  cases k with
  | zero =>
      have : orderOf (pSingular p a) = 1 :=
          Nat.dvd_one.mp ((Nat.ModEq.dvd_iff rfl h₁).mp h₂)
      exact ⟨0, by simp [this]⟩
  | succ k =>
      set n := orderOf (pSingular p a) with hn
      by_cases h : n = 1
      · exact ⟨0, by simp [n, h]⟩
      · have hppk : IsPrimePow (p ^ (k+1)) :=
          ⟨p, k+1, Nat.prime_iff.mp Fact.out, Nat.succ_pos _, rfl⟩
        have hppn : IsPrimePow n := by
          rw [hn]
          apply IsPrimePow.dvd hppk
          · exact (Nat.ModEq.dvd_iff rfl h₁).mp h₂
          · exact Ne.symm (Ne.intro fun a ↦ h (id (Eq.symm a)))
        rcases hppn with ⟨q, e, hqprime, hepos, hpow⟩
        have hqe : q ^ e ∣ p ^ (k+1) := by rw [hpow]; simp only [h₂]
        have hq : q ∣ p ^ (k+1) := Nat.dvd_of_pow_dvd (Nat.succ_le_of_lt hepos) hqe
        have h_eq : q = p :=
          Nat.prime_eq_prime_of_dvd_pow (Nat.prime_iff.mpr hqprime) Fact.out hq
        subst h_eq
        exact ⟨e, by simp [hn, hpow]⟩

end pSingular

section pDecomposition

lemma isPSingular_isPRegular_orders_coprime
    {a b : G} (ha : IsPSingular p a) (hb : IsPRegular p b) :
    Nat.Coprime (orderOf a) (orderOf b) := by
  rcases ha with ⟨n, hn⟩
  rw [hn]
  exact hb.symm.pow_left n

/-- Powers of `a` commute, hence the canonical factors commute. -/
lemma pDecomp_commute (a : G) :
    Commute (pSingular p a) (pRegular p a) := by simp [pSingular, pRegular]

theorem pDecomp [Fact p.Prime] {a : G} (hf : IsOfFinOrder a) :
    pSingular p a * pRegular p a = a := by
  let m := ordProj[p] (orderOf a)
  let n := ordCompl[p] (orderOf a)
  let r : ℤ := Nat.gcdA m n
  let s : ℤ := Nat.gcdB m n
  have hs : pSingular p a = a ^ (s * n) := rfl
  have hr : pRegular p a = a ^ (r * m) := rfl
  -- apply Bézout
  have hbez : m * r + n * s = 1 := by
    have hcop : Nat.Coprime m n :=
      Nat.ordProj_ordCompl_coprime p (orderOf_ne_zero_iff.mpr hf)
    rw [← Nat.gcd_eq_gcd_ab m n, hcop.gcd_eq_one]
    rfl
  rw [hs, hr, zpow_mul_comm a (s * ↑n) (r * ↑m)]
  have := congrArg (fun t : ℤ => a ^ t) hbez
  simp only [zpow_add, zpow_one, mul_comm _ r, mul_comm _ s] at this
  exact this

theorem pDecomp' [Fact p.Prime] {a : G} (h : IsOfFinOrder a) :
    pRegular p a * pSingular p a = a := by
  rw [← (pDecomp_commute p a).eq, pDecomp p h]


/--
Uniqueness of the `p`-decomposition.

If `a = b * c = c * b`, where `b` is `p`-singular and `c` is `p`-regular,
then `b` and `c` are respectively the canonical `p`-singular and `p`-regular
factors of `a`.
-/
theorem pSingular_pRegular_unique [Fact p.Prime]
    {a b c : G}
    (ha : IsOfFinOrder a)
    (h₁ : b * c = a) (h₂ : c * b = a)
    (hb : IsPSingular p b)
    (hc : IsPRegular p c) :
    b = pSingular p a ∧ c = pRegular p a := by
  have hcomm : Commute b c := by
    have : b * c = c * b := h₁.trans h₂.symm
    exact (commute_iff_eq b c).mpr this
  have horder : orderOf a = orderOf b * orderOf c := by
    rw [← h₁]
    exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm
      (isPSingular_isPRegular_orders_coprime p hb hc)
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  have hn : b ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp <|
    IsPSingular.orderOf_dvd_ordProj p hb (by rw [horder]; exact dvd_mul_right _ _)
      (orderOf_ne_zero_iff.mpr ha)
  have hm : c ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp <|
    IsPRegular.orderOf_dvd_ordCompl p hc (by rw [horder]; exact dvd_mul_left _ _)
  let r : ℤ := Nat.gcdA n m
  let s : ℤ := Nat.gcdB n m
  have hbez : n * r + m * s = 1 := by
    have hcop : Nat.Coprime n m := Nat.ordProj_ordCompl_coprime p (orderOf_ne_zero_iff.mpr ha)
    rw [← Nat.gcd_eq_gcd_ab n m, hcop.gcd_eq_one]; rfl
  have hms : c ^ (m * s) = 1 := by rw [zpow_mul, zpow_natCast, hm, one_zpow]
  have hs_eq : b = pSingular p a := by
    calc b
      _ = b * c ^ (m * s) := by rw [hms, mul_one]
      _ = b ^ (n * r + m * s) * c ^ (m * s) := by rw [hbez, zpow_one]
      _ = b ^ (n * r) * b ^ (m * s) * c ^ (m * s) := by rw [zpow_add]
      _ = b ^ (m * s) * 1 := by rw [zpow_mul, zpow_natCast, hn, one_zpow, hms, one_mul]
      _ = (b * c) ^ (s * m) := by rw [← hms, ← hcomm.mul_zpow, mul_comm (m : ℤ) s]
      _ = pSingular p a := by rw [h₁]; rfl
  have hv_eq : c = pRegular p a := by
    calc c
      _ = b ^ (n * r) * c := by rw [zpow_mul, zpow_natCast, hn, one_zpow, one_mul]
      _ = b ^ (n * r) * c ^ (n * r + m * s) := by rw [hbez, zpow_one]
      _ = b ^ (n * r) * (c ^ (n * r) * c ^ (m * s)) := by rw [zpow_add]
      _ = (b * c) ^ (r * n) := by rw [hms, mul_one, ← hcomm.mul_zpow, mul_comm (n : ℤ) r]
      _ = pRegular p a := by rw [h₁]; rfl
  exact ⟨hs_eq, hv_eq⟩

lemma pRegular_eq_self_of_isPRegular [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hr : IsPRegular p a) :
    pRegular p a = a := by
  have hs : IsPSingular p (1 : G) := IsPSingular.one p
  obtain ⟨_, hr_eq⟩ := pSingular_pRegular_unique p hf (one_mul a) (mul_one a) hs hr
  exact hr_eq.symm

lemma pSingular_eq_self_of_isPSingular [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hs : IsPSingular p a) :
    pSingular p a = a := by
  have hr : IsPRegular p (1 : G) := IsPRegular.one p
  obtain ⟨hs_eq, _⟩ := pSingular_pRegular_unique p hf (mul_one a) (one_mul a) hs hr
  exact hs_eq.symm

lemma isPSingular_pRegular_eq_one [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hs : IsPSingular p a) :
    pRegular p a = 1 := by
  have hr : IsPRegular p (1 : G) := by simp
  obtain ⟨_, hv_eq⟩ := pSingular_pRegular_unique p hf (mul_one a) (one_mul a) hs hr
  exact hv_eq.symm

lemma isPRegular_pSingular_eq_one [Fact p.Prime]
     {a : G} (hf : IsOfFinOrder a) (hr : IsPRegular p a) :
    pSingular p a = 1 := by
  have hs : IsPSingular p (1 : G) := by simp
  obtain ⟨hs_eq, _⟩ := pSingular_pRegular_unique p hf (one_mul a) (mul_one a) hs hr
  exact hs_eq.symm

/-- Conjugation carries the `p`-elementary/`p`-regular factors
    to those of the conjugate element. -/
lemma pDecomp_SemiconjBy [Fact p.Prime] {a b c : G} (h : SemiconjBy a b c) :
    SemiconjBy a (pSingular p b) (pSingular p c) ∧
    SemiconjBy a (pRegular p b) (pRegular p c) := by
  have h_ord : orderOf b = orderOf c := h.orderOf_eq
  constructor
  · simp only [pSingular, h_ord]
    exact h.zpow_right _
  · simp only [pRegular, h_ord]
    exact h.zpow_right _

@[simp]
lemma pRegular_conj [Fact p.Prime] (a b : G) :
    Group.pRegular p (a * b * a⁻¹) = a * Group.pRegular p b * a⁻¹ := by
  have h_semi : SemiconjBy a b (a * b * a⁻¹) := by
    rw [SemiconjBy, inv_mul_cancel_right]
  have h_reg := (pDecomp_SemiconjBy p h_semi).right
  exact eq_mul_inv_of_mul_eq h_reg.eq.symm


@[simp]
lemma pRegular_conj' [Fact p.Prime] (a b : G) :
    Group.pRegular p (a⁻¹ * b * a)  = a⁻¹ * Group.pRegular p b * a := by
  have h := pRegular_conj p (a⁻¹) b
  rw [inv_inv] at h
  exact h

@[simp]
lemma pSingular_conj [Fact p.Prime] (a b : G) :
    Group.pSingular p (a * b * a⁻¹) = a * Group.pSingular p b * a⁻¹ := by
  have h_semi : SemiconjBy a b (a * b * a⁻¹) := by
    rw [SemiconjBy, inv_mul_cancel_right]
  have h_sing := (pDecomp_SemiconjBy p h_semi).left
  exact eq_mul_inv_of_mul_eq h_sing.eq.symm

/--
If h is p-regular and s is p-singular and they commute, then the p-regular part
of (h * s) is just h.
-/
lemma pRegular_mul_eq_self_of_pSingular_commute [Fact p.Prime]
      {a b : G} (hf : IsOfFinOrder (a * b))
      (ha : IsPRegular p a) (hb : IsPSingular p b)
      (hcomm : Commute a b) :
    Group.pRegular p (a * b) = a := by
  have h_mul : b * a = a * b := hcomm.symm.eq
  obtain ⟨_, h_reg_eq⟩ :=
    pSingular_pRegular_unique p (a := a * b) (b := b) (c := a) hf h_mul rfl hb ha
  exact h_reg_eq.symm

lemma isPRegular_eq_one_of_mem_pGroup [Fact p.Prime]
    {a : G} {P : Subgroup G} (hP : IsPGroup p P)
    (haP : a ∈ P) (hr : IsPRegular p a) : a = 1 := by
  -- 1. Extract the fact that a is p-singular from the p-group property
  have hs : IsPSingular p a := by
    rcases (IsPGroup.iff_orderOf).mp hP ⟨a, haP⟩ with ⟨k, hk⟩
    use k
    simp only [← hk, Subgroup.orderOf_mk]
  -- 2. A sinngular and regular element is 1
  exact IsPSingular.isPRegular_eq_one p a hs hr

/-- Two p-regular parts commute if the elements commute. -/
lemma pRegular.commute {a b : G} (h : Commute a b) :
    Commute (pRegular p a) (pRegular p b) := Commute.zpow_zpow h _ _

/-- Two p-singular parts commute if the elements commute. -/
lemma pSingular.commute {a b : G} (h : Commute a b) :
    Commute (pSingular p a) (pSingular p b) := Commute.zpow_zpow h _ _

/-- If a and b commute, then the p-regular part of a commutes with the p-singular part of b. -/
lemma pRegular_pSingular_commute {a b : G} (h : Commute a b) :
    Commute (Group.pRegular p a) (Group.pSingular p b) := Commute.zpow_zpow h _ _

/-- If a and b commute, then the p-singular part of a commutes with the
  p-regular part of b. -/
lemma pSingular_pRegular_commute {a b : G} (h : Commute a b) :
    Commute (Group.pSingular p a) (Group.pRegular p b) := Commute.zpow_zpow h _ _

/--
The `p`-decomposition of a commuting product is the product of the
corresponding `p`-singular and `p`-regular factors.
-/
lemma pDecomp_mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b)
    (hcomm : Commute a b) :
    Group.pSingular p (a * b) = Group.pSingular p a * Group.pSingular p b ∧
    Group.pRegular p (a * b) = Group.pRegular p a * Group.pRegular p b := by
  let ar := Group.pRegular p a
  let as := Group.pSingular p a
  let br := Group.pRegular p b
  let bs := Group.pSingular p b
  let cr := ar * br
  let cu := as * bs
  -- 1 & 2. Use IsPRegular.mul and IsPSingular.mul lemmas
  have hcr : IsPRegular p cr :=
    (isPRegular_pRegular p ha).mul p (isPRegular_pRegular p hb) (pRegular.commute p hcomm)
  have hcu : IsPSingular p cu :=
    (isPSingular_pSingular p a).mul p (isPSingular_pSingular p b) (pSingular.commute p hcomm)
  -- 3. Show cu * cr = a * b
  have h_prod : cu * cr = a * b := by
    rw [mul_assoc, ← mul_assoc bs]
    have: Commute bs ar := Commute.zpow_zpow hcomm.symm _ _
    rw [this, mul_assoc, ← mul_assoc as]
    have hcomm_a : Commute as ar := pDecomp_commute p a
    have hcomm_b : Commute bs br := pDecomp_commute p b
    rw [hcomm_a.eq, hcomm_b.eq, pDecomp' p hb, pDecomp' p ha]
  -- 4. Show cr and cu commute
  have hcomm_c : Commute cu cr := by
    apply Commute.mul_left
    · apply Commute.mul_right
      · exact pDecomp_commute p a
      · exact Commute.zpow_zpow hcomm _ _
    · apply Commute.mul_right
      · exact Commute.zpow_zpow hcomm.symm _ _
      · exact pDecomp_commute p b
  -- 5. Apply uniqueness to get both equalities
  have h_prod_rev : cr * cu = a * b := by
    rw [← hcomm_c.eq, h_prod]
  have hfab : IsOfFinOrder (a * b) := Commute.isOfFinOrder_mul hcomm ha hb
  obtain ⟨hs_eq, hr_eq⟩ := pSingular_pRegular_unique p hfab h_prod h_prod_rev hcu hcr
  exact ⟨hs_eq.symm, hr_eq.symm⟩

/-- Two p-regular parts multiply together if the original elements commute. -/
lemma pRegular.mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) (hcomm : Commute a b) :
    Group.pRegular p (a * b) = Group.pRegular p a * Group.pRegular p b :=
  (pDecomp_mul_of_commute p ha hb hcomm).right

/-- Two p-singular parts multiply together if the original elements commute. -/
lemma pSingular.mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b)
    (hcomm : Commute a b) :
    Group.pSingular p (a * b) = Group.pSingular p a * Group.pSingular p b :=
  (pDecomp_mul_of_commute p ha hb hcomm).left

/-- If `s` is p-singular and commutes with `a`, then `pRegular (a * s) = pRegular a`. -/
lemma pRegular_mul_eq_left_of_right_pSingular_commute [Fact p.Prime]
    {a s : G} (ha_fin : IsOfFinOrder s) (hb_fin : IsOfFinOrder a)
    (hs : IsPSingular p s) (hcomm : Commute s a) :
    Group.pRegular p (a * s) = Group.pRegular p a := by
  calc
    Group.pRegular p (a * s)
        = Group.pRegular p a * Group.pRegular p s := by
          rw [Group.pRegular.mul_of_commute p hb_fin ha_fin hcomm.symm]
    _   = Group.pRegular p a := by
          simp only [Group.isPSingular_pRegular_eq_one p ha_fin hs, mul_one]

/--
Raising an element to the `p`-part of its order only depends on its
`p`-regular factor.
-/
lemma pow_ordProj_eq_pRegular_pow_ordProj [Fact p.Prime]
    {a : G} (h : IsOfFinOrder a) :
    a ^ ordProj[p] (orderOf a) = Group.pRegular p a ^ ordProj[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let ar := Group.pRegular p a
  let as := Group.pSingular p a
  have hdecomp : as * ar = a := pDecomp p h
  have hcomm : Commute as ar := pDecomp_commute p a
  have : as ^ n = 1 := by
    have hdvd : orderOf as ∣ n := Group.orderOf_pSingular_dvd p a
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  calc
    a ^ n = (as * ar) ^ n := by rw [hdecomp]
    _     = as ^ n * ar ^ n := hcomm.mul_pow n
    _     = 1 * ar ^ n := by rw [this]
    _     = ar ^ n := by rw [one_mul]

end pDecomposition

end Group

end Slop
