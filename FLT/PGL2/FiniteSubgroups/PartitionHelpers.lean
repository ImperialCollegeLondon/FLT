/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.Tactic.Cases
public import FLT.PGL2.FiniteSubgroups.PGLBasic

/-!
# Sylow `p`-subgroup lemmas for finite subgroups of `PGL₂(𝔽̄_p)`

This file proves the basic facts about Sylow `p`-subgroups of a finite subgroup `G` of
`PGL p = PGL₂(𝔽̄_p)` whose order is divisible by `p` (the *wild* case of Dickson's
classification).

The key geometric input is that an element of order `p` in `PGL p` fixes exactly one
point of the projective line. From this we deduce:
* each Sylow `p`-subgroup `P` of `G` fixes a unique point `sylowFixedPoint`
  of `ℙ¹(𝔽̄_p)`, and distinct Sylow `p`-subgroups have distinct fixed points
  (`Dickson.sylow_fixedPoint_injective`);
* distinct Sylow `p`-subgroups intersect trivially
  (`Dickson.sylow_pairwise_trivial_intersection`);
* a count of the elements of order dividing `p` in `G`
  (`Dickson.count_order_p_elements`);
* the normalizer of `P` in `G` is the stabilizer of its fixed point, and numerical
  consequences for `|G|` (`Dickson.normalizer_complement_divides_main`,
  `Dickson.group_order_gt_normalizer`).
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

noncomputable section PartitionHelpers

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

omit h_odd in
theorem sylow_card_prime_pow (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ k : ℕ, k ≥ 1 ∧ Nat.card P = p ^ k :=
  ⟨(Nat.card G).factorization p,
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp <| Nat.mem_primeFactors.mpr ⟨Fact.out, hG_p, Nat.card_pos.ne'⟩),
    P.card_eq_multiplicity⟩

theorem sylow_card_ge_3 (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card P ≥ 3 := by
  obtain ⟨k, hk, hk_eq⟩ := sylow_card_prime_pow p G hG_p P
  rw [hk_eq]
  exact (Nat.succ_le_of_lt (Fact.out : p > 2)).trans (Nat.le_self_pow (by omega) p)


theorem sylow_unique_fixedPoint (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∃! x : ProjectiveLine p,
      ∀ g : PGL p, g ∈ (P : Subgroup G).map (Subgroup.subtype G) → g • x = x := by
  let P' : Subgroup (PGL p) := Subgroup.map (Subgroup.subtype G) (P : Subgroup G)
  let e : (P : Subgroup G) ≃ P' := (Subgroup.equivMapOfInjective _ _ Subtype.coe_injective).toEquiv
  haveI : Finite P' := Finite.of_equiv _ e

  refine (isPGroup_comm_exponent_fixedPoint p P' (P.2.map (Subgroup.subtype G)) ?_).2.2
  by_contra h
  haveI : Unique P' := ⟨⟨1⟩, fun x ↦ by_contra fun hx ↦ h (Nontrivial.mk ⟨x, 1, hx⟩)⟩
  have h1: Nat.card P' = 1 := Nat.card_unique
  have h3: Nat.card P' ≥ 3 := Nat.card_congr e ▸ sylow_card_ge_3 p G hG_p P
  linarith only [h1, h3]

omit h_odd in
@[nolint unusedArguments]
theorem normalizer_stabilizes_fixedPoint (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) (x : ProjectiveLine p)
    (hx : ∀ g ∈ (P : Subgroup G), (g : PGL p) • x = x)
    (hx_unique : ∀ y, (∀ g ∈ (P : Subgroup G), (g : PGL p) • y = y) → y = x) :
    ∀ g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), (g : PGL p) • x = x := fun g hg ↦
  have h_inv : (g⁻¹ : PGL p) • x = x := hx_unique _ fun h hh ↦ by
    rw [← mul_smul, (show (h : PGL p) * (g⁻¹ : PGL p) = (g⁻¹ : PGL p) * (g * h * g⁻¹ : G) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_assoc, inv_mul_cancel, one_mul]),
      mul_smul, hx (g * h * g⁻¹) ((hg h).mp hh)]
  (congr_arg (fun y ↦ (g : PGL p) • y) h_inv.symm).trans (smul_inv_smul (g : PGL p) x)

theorem sylow_element_order_p (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G)
    (g : G) (hg : g ∈ (P : Subgroup G)) (hg_ne : g ≠ 1) :
    orderOf (g : PGL p) = p := by
  let P' : Subgroup (PGL p) := (P : Subgroup G).map (Subgroup.subtype G)
  haveI : Finite P' := Finite.of_equiv P (Subgroup.equivMapOfInjective _ _ Subtype.coe_injective).toEquiv
  exact isPGroup_orderOf_eq_prime p P' (P.2.map (Subgroup.subtype G))
    ⟨(g : PGL p), Subgroup.mem_map_of_mem (Subgroup.subtype G) hg⟩
    (fun h ↦ hg_ne <| Subtype.ext <| congr_arg (fun x : P' ↦ x.1) h)

theorem order_p_one_fixedPoint (g : PGL p) (hg : orderOf g = p) :
    Set.ncard (fixedPoints p g) = 1 :=
  (fixedPoints_dichotomy p g
    (fun h ↦ Nat.Prime.ne_one Fact.out (hg.symm.trans ((congr_arg orderOf h).trans orderOf_one)))
    (orderOf_pos_iff.mp (hg.symm ▸ Nat.Prime.pos Fact.out))).1.mpr hg

/-- The unique fixed point on the projective line `ℙ¹(𝔽̄_p)` of a Sylow `p`-subgroup `P`. -/
noncomputable def sylowFixedPoint (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) : ProjectiveLine p :=
  (sylow_unique_fixedPoint p G hG_p P).choose

theorem sylow_element_fixes (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (g : G) (hg : g ∈ (P : Subgroup G)) :
    (g : PGL p) • sylowFixedPoint p G hG_p P = sylowFixedPoint p G hG_p P :=
  (sylow_unique_fixedPoint p G hG_p P).choose_spec.1 g (Subgroup.mem_map_of_mem _ hg)

theorem eq_sylow_fixedPoint (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) (y : ProjectiveLine p)
    (hy : ∀ g : G, g ∈ (P : Subgroup G) → (g : PGL p) • y = y) :
    y = sylowFixedPoint p G hG_p P :=
  (sylow_unique_fixedPoint p G hG_p P).choose_spec.2 y fun _ hg ↦ by
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    exact hy g' hg'

theorem shared_element_shared_fixedPoint (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P Q : Sylow p G)
    (g : G) (hgP : g ∈ (P : Subgroup G)) (hgQ : g ∈ (Q : Subgroup G)) (hg_ne : g ≠ 1) :
    sylowFixedPoint p G hG_p P = sylowFixedPoint p G hG_p Q := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp <|
    order_p_one_fixedPoint p (g : PGL p) (sylow_element_order_p p G P g hgP hg_ne)
  exact ((Set.ext_iff.mp ha _).mp (sylow_element_fixes p G hG_p P g hgP)).trans
    ((Set.ext_iff.mp ha _).mp (sylow_element_fixes p G hG_p Q g hgQ)).symm



theorem sylow_pairwise_trivial_intersection (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P Q : Sylow p G) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  by_contra h_int

  obtain ⟨g, ⟨hgP, hgQ⟩, hg_ne_one⟩ : ∃ g : G, g ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) ∧ g ≠ 1 := by
    by_contra h; apply h_int; ext x
    exact ⟨fun hx ↦ by_contra fun hx_ne ↦ h ⟨x, hx, hx_ne⟩,
           fun hx ↦ (Subgroup.mem_bot.mp hx).symm ▸ ⟨P.one_mem, Q.one_mem⟩⟩

  have h_comm_G : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a := fun a ha b hb ↦ by
    by_cases ha1 : a = 1; · rw [ha1, one_mul, mul_one]
    by_cases hb1 : b = 1; · rw [hb1, mul_one, one_mul]
    exact Subtype.ext <| commute_of_orderOf_prime_common_fixedPoint p (a : PGL p) (b : PGL p)
      (sylowFixedPoint p G hG_p P)
      (sylow_element_order_p p G P a ha ha1)
      (sylow_element_order_p p G Q b hb hb1)
      (sylow_element_fixes p G hG_p P a ha)
      (shared_element_shared_fixedPoint p G hG_p P Q g hgP hgQ hg_ne_one ▸ sylow_element_fixes p G hG_p Q b hb)

  let S : Subgroup G := {
    carrier := {x | ∃ a ∈ P, ∃ b ∈ Q, x = a * b}
    mul_mem' := by
      rintro _ _ ⟨yP, hyP, yQ, hyQ, rfl⟩ ⟨zP, hzP, zQ, hzQ, rfl⟩
      refine ⟨yP * zP, P.mul_mem hyP hzP, yQ * zQ, Q.mul_mem hyQ hzQ, ?_⟩
      rw [mul_assoc, ← mul_assoc yQ, ← h_comm_G zP hzP yQ hyQ, mul_assoc zP, ← mul_assoc yP]
    one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
    inv_mem' := by
      rintro _ ⟨yP, hyP, yQ, hyQ, rfl⟩
      refine ⟨yP⁻¹, P.inv_mem hyP, yQ⁻¹, Q.inv_mem hyQ, ?_⟩
      rw [mul_inv_rev, ← h_comm_G yP⁻¹ (P.inv_mem hyP) yQ⁻¹ (Q.inv_mem hyQ)]
  }

  have h_p_group : IsPGroup p (P ⊔ Q : Subgroup G) := fun x ↦ by
    have h_sup_le : (P ⊔ Q : Subgroup G) ≤ S := sup_le
      (fun y hy ↦ ⟨y, hy, 1, Q.one_mem, (mul_one y).symm⟩)
      (fun y hy ↦ ⟨1, P.one_mem, y, hy, (one_mul y).symm⟩)
    obtain ⟨a, ha, b, hb, hx_eq⟩ := h_sup_le x.2
    obtain ⟨nA, hnA⟩ := P.2 ⟨a, ha⟩
    obtain ⟨nB, hnB⟩ := Q.2 ⟨b, hb⟩
    use nA + nB
    have hA : a ^ (p ^ nA) = 1 := congr_arg Subtype.val hnA
    have hB : b ^ (p ^ nB) = 1 := congr_arg Subtype.val hnB
    exact Subtype.ext <| by
      show (x : G) ^ (p ^ (nA + nB)) = 1
      rw [hx_eq, Commute.mul_pow (h_comm_G a ha b hb),
          pow_add, pow_mul, hA, one_pow, one_mul,
          mul_comm (p ^ nA), pow_mul, hB, one_pow]

  exact hPQ <| Sylow.ext <| Q.is_maximal' P.2 <|
    (P.is_maximal' h_p_group le_sup_left) ▸ le_sup_right


theorem count_order_p_elements (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card {g : G | orderOf g = p} =
      Fintype.card (Sylow p G) * (Nat.card P - 1) := by

  have h_elements_order_p : {g : G | orderOf g = p} = ⋃ Q ∈ (Finset.univ : Finset (Sylow p G)), ((Q : Subgroup G) \ {1} : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨fun hg ↦ ?_, fun ⟨Q, hgQ, hg_ne_one⟩ ↦ ?_⟩
    · have h_sylow : IsPGroup p (Subgroup.zpowers g) := fun ⟨x, hx⟩ ↦ by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        use 1
        exact Subtype.ext <| show (g ^ k) ^ (p ^ 1) = 1 by
          rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
              show g ^ (p : ℤ) = 1 by rw [zpow_natCast]; exact (congrArg (fun n : ℕ ↦ g ^ n) hg).symm.trans (pow_orderOf_eq_one g), one_zpow]
      obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow h_sylow
      exact ⟨Q, hQ (Subgroup.mem_zpowers g), fun h_eq ↦ (Fact.out : Nat.Prime p).ne_one <|
        hg.symm.trans ((congrArg orderOf h_eq).trans orderOf_one)⟩
    · exact (orderOf_injective (Subgroup.subtype G) Subtype.coe_injective g).symm.trans <|
        sylow_element_order_p p G Q g hgQ hg_ne_one

  have h_card_union : ∀ (s : Finset (Sylow p G)),
      (⋃ Q ∈ s, ((Q : Subgroup G) \ {1} : Set G)).ncard = ∑ Q ∈ s, ((Q : Subgroup G) \ {1} : Set G).ncard := by
    intro s
    induction' s using Finset.induction with Q s hQs ih
    · rw [Finset.sum_empty]
      have h_emp : (⋃ Q ∈ (∅ : Finset (Sylow p G)), ((Q : Subgroup G) \ {1} : Set G)) = ∅ := by
        ext x
        refine ⟨fun hx ↦ ?_, fun h ↦ h.elim⟩
        simp only [Set.mem_iUnion, exists_prop] at hx
        obtain ⟨R, hR, _⟩ := hx
        cases hR
      rw [h_emp, Set.ncard_empty]
    · have h_eq : (⋃ R ∈ insert Q s, ((R : Subgroup G) \ {1} : Set G)) = ((Q : Subgroup G) \ {1} : Set G) ∪ ⋃ R ∈ s, ((R : Subgroup G) \ {1} : Set G) := by
        ext x
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union, exists_prop]
        exact ⟨fun ⟨R, hR, hxR⟩ ↦ hR.elim (fun h ↦ Or.inl <| h ▸ hxR) (fun h ↦ Or.inr ⟨R, h, hxR⟩),
               fun h ↦ h.elim (fun hxQ ↦ ⟨Q, Or.inl rfl, hxQ⟩) (fun ⟨R, hRs, hxR⟩ ↦ ⟨R, Or.inr hRs, hxR⟩)⟩
      rw [h_eq, Set.ncard_union_eq, ih, Finset.sum_insert hQs]
      rw [Set.disjoint_left]
      rintro x ⟨hxQ, hx_ne⟩ hx_s
      simp only [Set.mem_iUnion, Set.mem_sdiff, Set.mem_singleton_iff, exists_prop] at hx_s
      obtain ⟨R, hRs, hxR, _⟩ := hx_s
      exact hx_ne <| Subgroup.mem_bot.mp <|
        sylow_pairwise_trivial_intersection p G hG_p Q R (fun h ↦ hQs (h ▸ hRs)) ▸
        (⟨hxQ, hxR⟩ : x ∈ (Q : Subgroup G) ⊓ (R : Subgroup G))

  have h_card_diff : ∀ Q : Sylow p G, ((Q : Subgroup G) \ {1} : Set G).ncard = Nat.card P - 1 := fun Q ↦ by
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr Q.one_mem) (Set.toFinite _),
        Set.ncard_singleton, ← Nat.card_coe_set_eq]
    exact show Nat.card Q - 1 = Nat.card P - 1 from
      congr_arg (· - 1) ((Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity P).symm)

  rw [Nat.card_coe_set_eq, h_elements_order_p, h_card_union Finset.univ,
      Finset.sum_congr rfl (fun Q _ ↦ h_card_diff Q), Finset.sum_const, Finset.card_univ]
  rfl

end PartitionHelpers

noncomputable section Borel

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

theorem fixes_infinity_commutes_order_p
    (g h : PGL p)
    (hg_fix : g • infinity p = infinity p)
    (hh_fix : h • infinity p = infinity p)
    (hh_order : orderOf h = p)
    (h_comm : g * h = h * g) :
    orderOf g = 1 ∨ orderOf g = p := by
  obtain ⟨a, b, d, h_ne, hg⟩ := (fixesInfinity_iff_upperTriangular p g).mp hg_fix
  obtain ⟨β, hh⟩ := isUnipotent_of_fixesInfinity_orderOf p _ hh_fix hh_order
  have hβ_nonzero : β ≠ 0 := fun h_zero ↦ (Nat.Prime.ne_one Fact.out) <|
    hh_order.symm.trans <| (congr_arg orderOf (by
      rw [hh, QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      refine ⟨1, Units.ext (by
        ext i j
        match i, j with
        | 0, 0 => rfl
        | 0, 1 => exact h_zero.symm
        | 1, 0 => rfl
        | 1, 1 => rfl)⟩ : h = 1)).trans orderOf_one
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by
    rw [Matrix.det_fin_two]; exact (by ring : a * d = a * d - b * 0) ▸ h_ne)
  let B := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, β; 0, 1] (by
    rw [Matrix.det_fin_two]; exact (by ring : 1 = 1 * 1 - β * 0) ▸ one_ne_zero)
  obtain ⟨c, hc⟩ : ∃ c : (K p)ˣ, Units.map (algebraMap (K p) (Matrix (Fin 2) (Fin 2) (K p))).toMonoidHom c = (B * A)⁻¹ * (A * B) := by
    have h1 := h_comm.symm
    rw [hg, hh] at h1
    have h_center : (B * A)⁻¹ * (A * B) ∈ Subgroup.center (GL (Fin 2) (K p)) := QuotientGroup.eq.mp h1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h_center
    exact h_center
  have h_mul : A.val * B.val = (c : K p) • (B.val * A.val) := by
    have h3 := congr_arg Units.val (eq_mul_of_inv_mul_eq hc.symm)
    simp only [Units.val_mul] at h3
    have h_map : (Units.map (algebraMap (K p) (Matrix (Fin 2) (Fin 2) (K p))).toMonoidHom c).val =
        (c : K p) • (1 : Matrix (Fin 2) (Fin 2) (K p)) := by
      change algebraMap (K p) (Matrix (Fin 2) (Fin 2) (K p)) (c : K p) = _
      rw [Algebra.algebraMap_eq_smul_one]
    rw [h_map, Matrix.mul_smul, Matrix.mul_one] at h3
    exact h3
  have h_d : d = (c : K p) * d := by
    have h4 := congr_fun (congr_fun h_mul 1) 1
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, A, B] at h4
    change 0 * β + d * 1 = (c : K p) * (0 * b + 1 * d) at h4
    calc d = 0 * β + d * 1 := by ring
      _ = (c : K p) * (0 * b + 1 * d) := h4
      _ = (c : K p) * d := by ring

  have hc1 : (c : K p) = 1 := mul_right_cancel₀ (fun h ↦ h_ne (by rw [h, mul_zero])) (h_d.symm.trans (one_mul d).symm)
  have h_matrix_comm : A.val * B.val = B.val * A.val := by
    rw [hc1, one_smul] at h_mul; exact h_mul

  have h_ad : a = d := by
    have h_01 := congr_fun (congr_fun h_matrix_comm 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, A, B] at h_01
    change a * β + b * 1 = 1 * b + β * d at h_01
    have h_eq : a * β = d * β := by
      calc a * β = a * β + b * 1 - b := by ring
        _ = 1 * b + β * d - b := by rw [h_01]
        _ = d * β := by ring
    exact mul_right_cancel₀ hβ_nonzero h_eq
  by_cases hb : b = 0
  · left
    rw [hg, orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have hd_ne : d ≠ 0 := fun h_zero ↦ h_ne (by rw [h_zero]; exact mul_zero a)
    refine ⟨Units.mk0 d hd_ne, Units.ext (by
      ext i j
      match i, j with
      | 0, 0 => exact h_ad.symm
      | 0, 1 => exact hb.symm
      | 1, 0 => rfl
      | 1, 1 => rfl)⟩
  · right
    nontriviality
    rw [hg]
    have hb_contra : ¬ (∃ c_unit : K p, A.val = c_unit • 1) := by
      rintro ⟨c_unit, hc_unit⟩
      have hc_val2 : b = 0 := by
        have h_val := congr_arg (fun m : Matrix (Fin 2) (Fin 2) (K p) ↦ m 0 1) hc_unit
        change b = c_unit * 0 at h_val
        rw [h_val, mul_zero]
      exact hb hc_val2
    refine orderOf_eq_prime_of_discrim_zero p A hb_contra (by
      have h_trace : Matrix.trace A.val = a + d := by
        rw [Matrix.trace_fin_two]
        rfl
      have h_det : Matrix.det A.val = a * d - b * 0 := by
        rw [Matrix.det_fin_two]
        rfl
      rw [h_trace, h_det, h_ad]
      ring)


theorem common_fixedPoint_commutes_order_p
    (g h : PGL p) (x : ProjectiveLine p)
    (hg_fix : g • x = x) (hh_fix : h • x = x)
    (hh_order : orderOf h = p) (h_comm : g * h = h * g) :
    orderOf g = 1 ∨ orderOf g = p := by
  obtain ⟨k, hk⟩ := exists_smul_eq_infinity p x
  have hg_fix' : (k * g * k⁻¹) • infinity p = infinity p := by
    rw [← hk, mul_smul, inv_smul_smul, mul_smul, hg_fix]
  have hh_fix' : (k * h * k⁻¹) • infinity p = infinity p := by
    rw [← hk, mul_smul, inv_smul_smul, mul_smul, hh_fix]
  have h_comm' : (k * g * k⁻¹) * (k * h * k⁻¹) = (k * h * k⁻¹) * (k * g * k⁻¹) := by
    change (MulAut.conj k) g * (MulAut.conj k) h = (MulAut.conj k) h * (MulAut.conj k) g
    rw [← map_mul, ← map_mul, h_comm]
  have ord_eq (z : PGL p) : orderOf (k * z * k⁻¹) = orderOf z :=
    orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective z
  rw [← ord_eq g]
  exact fixes_infinity_commutes_order_p p (k * g * k⁻¹) (k * h * k⁻¹)
    hg_fix' hh_fix' ((ord_eq h).trans hh_order) h_comm'


omit h_odd in
theorem order_one_or_p_in_sylow (G : Subgroup (PGL p)) [Finite G]
    (_hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (g : G) (hg_norm : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (h_order : orderOf (g : PGL p) = 1 ∨ orderOf (g : PGL p) = p) :
    g ∈ (P : Subgroup G) := by
  have h_cyclic : IsPGroup p (Subgroup.zpowers g) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, ← Subgroup.orderOf_coe g]
    exact h_order.elim (fun h ↦ ⟨0, by rw [h, pow_zero]⟩) (fun h ↦ ⟨1, by rw [h, pow_one]⟩)
  exact (P.is_maximal'
    (IsPGroup.to_sup_of_normal_right' h_cyclic P.isPGroup' (Subgroup.zpowers_le.mpr hg_norm))
    le_sup_right) ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers g)


theorem normalizer_fixes_element_in_sylow (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (g : G) (hg_norm : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (h : G) (hh_in_P : h ∈ (P : Subgroup G)) (hh_ne : h ≠ 1)
    (h_conj_eq : g * h * g⁻¹ = h) :
    g ∈ (P : Subgroup G) := by
  have h_comm_G : g * h = h * g := by
    rw [← mul_one (g * h), ← inv_mul_cancel g, ← mul_assoc, h_conj_eq]
  have h_fixed : (g : PGL p) • sylowFixedPoint p G hG_p P = sylowFixedPoint p G hG_p P :=
    normalizer_stabilizes_fixedPoint p G P (sylowFixedPoint p G hG_p P)
      (sylow_element_fixes p G hG_p P)
      (eq_sylow_fixedPoint p G hG_p P)
      g hg_norm
  have h_order := common_fixedPoint_commutes_order_p p (g : PGL p) (h : PGL p)
    (sylowFixedPoint p G hG_p P) h_fixed
    (sylow_element_fixes p G hG_p P h hh_in_P)
    (sylow_element_order_p p G P h hh_in_P hh_ne)
    (congr_arg Subtype.val h_comm_G)
  exact order_one_or_p_in_sylow p G hG_p P g hg_norm h_order


noncomputable instance conjOnP (G : Subgroup (PGL p)) (P : Sylow p G) :
    MulAction (↑(Subgroup.normalizer ((P : Subgroup G) : Set G))) (↑(P : Subgroup G)) where
  smul g h := ⟨g.val * h.val * g.val⁻¹, (g.prop h.val).1 h.prop⟩
  one_smul h := by
    apply Subtype.ext
    change (1 : G) * h.val * (1 : G)⁻¹ = h.val
    rw [inv_one, mul_one, one_mul]
  mul_smul g₁ g₂ h := by
    apply Subtype.ext
    change (g₁.val * g₂.val) * h.val * (g₁.val * g₂.val)⁻¹ = (g₁.val * (g₂.val * h.val * g₂.val⁻¹)) * g₁.val⁻¹
    rw [mul_inv_rev, mul_assoc g₁.val, mul_assoc g₁.val, ← mul_assoc (g₂.val * h.val), ← mul_assoc g₁.val]


theorem stabilizer_conj_eq_P (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (h : ↑(P : Subgroup G)) (hh_ne : h ≠ 1) :
    MulAction.stabilizer (↑(Subgroup.normalizer ((P : Subgroup G) : Set G))) h =
    (P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  haveI : Finite ↥(P.map G.subtype) := Set.Finite.to_subtype (Set.Finite.subset (Set.finite_range G.subtype) (by
    rintro x ⟨y, _, rfl⟩
    exact Set.mem_range_self y))
  have h_abelian : ∀ g : G, g ∈ (P : Subgroup G) → g * h.val * g⁻¹ = h.val := by
    intro g hg
    have h_comm_map := (isPGroup_comm_exponent_fixedPoint p (P.map G.subtype)
      (P.2.map (Subgroup.subtype G))
        ⟨⟨⟨G.subtype h.val, Subgroup.mem_map_of_mem G.subtype h.2⟩, 1, fun h_eq ↦ hh_ne (Subtype.ext (Subtype.ext (congr_arg (fun x : P.map G.subtype ↦ x.val) h_eq)))⟩⟩).1
    have h_comm : g * h.val = h.val * g := Subtype.ext (congr_arg (fun x : P.map G.subtype ↦ x.val) (h_comm_map ⟨G.subtype g, Subgroup.mem_map_of_mem G.subtype hg⟩ ⟨G.subtype h.val, Subgroup.mem_map_of_mem G.subtype h.2⟩))
    rw [h_comm, mul_inv_cancel_right]
  ext ⟨g, hg⟩
  constructor <;> intro hg'
  · exact normalizer_fixes_element_in_sylow p G hG_p P g hg h.val h.2 (fun h_eq ↦ hh_ne (Subtype.ext h_eq)) (congr_arg Subtype.val hg')
  · exact Subtype.ext <| h_abelian g hg'


theorem normalizer_complement_divides_main (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) (hG_p : p ∣ Nat.card G) :
    Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) / Nat.card P ∣
      Nat.card P - 1 := by
  haveI := Fintype.ofFinite G
  letI : MulAction (Subgroup.normalizer ((P : Subgroup G) : Set G)) (P : Subgroup G) := conjOnP p G P
  letI : SMul (Subgroup.normalizer ((P : Subgroup G) : Set G)) (P : Subgroup G) := (conjOnP p G P).toSMul

  have h_orbit_card : ∀ h : (P : Subgroup G), h ≠ 1 → Nat.card (MulAction.orbit (Subgroup.normalizer ((P : Subgroup G) : Set G)) h) = Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) / Nat.card P := by
    intro h hh_ne
    haveI : Nonempty (MulAction.stabilizer (Subgroup.normalizer ((P : Subgroup G) : Set G)) h) := ⟨1⟩
    have e : ↥((P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))) ≃ (P : Subgroup G) :=
      ⟨fun x ↦ ⟨x.1.1, x.2⟩, fun x ↦ ⟨⟨x.1, Subgroup.le_normalizer x.2⟩, x.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    have h_stab : Nat.card (MulAction.stabilizer (Subgroup.normalizer ((P : Subgroup G) : Set G)) h) = Nat.card P := by
      rw [stabilizer_conj_eq_P p G hG_p P h hh_ne]; exact Nat.card_congr e
    have h_quot := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MulAction.stabilizer (Subgroup.normalizer ((P : Subgroup G) : Set G)) h)
    rw [h_stab] at h_quot
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ h), h_quot,
        Nat.mul_div_cancel _ Nat.card_pos]

  calc Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) / Nat.card P
    _ ∣ ∑ ω ∈ Finset.image (fun h : (P : Subgroup G) ↦ MulAction.orbit (Subgroup.normalizer ((P : Subgroup G) : Set G)) h) (Finset.univ.erase 1), Nat.card ω := by
      apply Finset.dvd_sum
      rintro ω hω
      rcases Finset.mem_image.mp hω with ⟨h, hh, rfl⟩
      exact h_orbit_card h (Finset.mem_erase.mp hh).1 ▸ dvd_rfl
    _ = (Finset.univ.erase (1 : (P : Subgroup G))).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_image' (h := fun _ ↦ 1)
      intro i hi
      have e : ↥(Finset.filter (fun j ↦ MulAction.orbit (Subgroup.normalizer ((P : Subgroup G) : Set G)) j = MulAction.orbit (Subgroup.normalizer ((P : Subgroup G) : Set G)) i) (Finset.univ.erase 1)) ≃ MulAction.orbit (Subgroup.normalizer ((P : Subgroup G) : Set G)) i := by
        apply Equiv.subtypeEquivProp
        ext x
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
        refine ⟨fun h ↦ h.2 ▸ MulAction.mem_orbit_self x, fun hx ↦ ⟨?_, MulAction.orbit_eq_iff.mpr hx⟩⟩
        rintro rfl
        rcases hx with ⟨g, hg⟩
        apply (Finset.mem_erase.mp hi).1
        have hv := congr_arg Subtype.val hg
        change g.val * i.val * g.val⁻¹ = 1 at hv
        exact Subtype.ext (show i.val = 1 by
          calc i.val = g.val⁻¹ * (g.val * i.val * g.val⁻¹) * g.val := by group
            _ = g.val⁻¹ * 1 * g.val := by rw [hv]
            _ = 1 := by group)
      rw [Finset.sum_const, smul_eq_mul, mul_one,
          Nat.card_congr e.symm, Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card P - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- The index `|N_G(P)| / |P|` of a Sylow `p`-subgroup `P` in its normalizer in `G`. -/
@[nolint unusedArguments]
def normalizerQuotient (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) : ℕ :=
  Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) / Nat.card P



omit h_odd in
theorem group_order_gt_normalizer (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Nat.card G > Nat.card P * normalizerQuotient p G P := by
  have e : Nat.card (G ⧸ Subgroup.normalizer ((P : Subgroup G) : Set G)) =
      Fintype.card (Sylow p G) :=
    (Nat.card_congr (Sylow.equivQuotientNormalizer P)).symm.trans Nat.card_eq_fintype_card
  rw [normalizerQuotient, Nat.mul_div_cancel' (Subgroup.card_dvd_of_le Subgroup.le_normalizer),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.normalizer ((P : Subgroup G) : Set G)),
    e]
  have h := Nat.mul_lt_mul_of_pos_right hn_p_gt1 (Nat.card_pos (α := Subgroup.normalizer ((P : Subgroup G) : Set G)))
  rw [one_mul] at h
  exact h


end Borel

noncomputable section RecognitionHelpers

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]




omit h_odd in
theorem not_dvd_pred_pow (k : ℕ) (hk : k ≥ 1) : ¬ p ∣ (p ^ k - 1) := by
  intro h
  have h_add : p ∣ (p ^ k - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_pow k p (Fact.out : Nat.Prime p).pos)]
    exact dvd_pow_self p (ne_of_gt hk)
  exact Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p) ((Nat.dvd_add_right h).mp h_add)



omit h_odd in
theorem factorization_pgl_order (m : ℕ) (hm : m ≥ 1) :
    (p ^ m * (p ^ (2 * m) - 1)).factorization p = m := by
  have h_zero : (p ^ (2 * m) - 1).factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    exact Or.inr (Or.inl (not_dvd_pred_pow p (2 * m) (Nat.mul_pos (Nat.succ_pos 1) hm)))
  rw [Nat.factorization_mul_of_coprime (by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact not_dvd_pred_pow p (2 * m) (Nat.mul_pos (Nat.succ_pos 1) hm))]
  simp only [Finsupp.coe_add, Pi.add_apply]
  rw [(Fact.out : Nat.Prime p).factorization_pow, Finsupp.single_eq_same, h_zero, add_zero]


omit h_odd in
theorem sylow_order_of_pgl_order (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (P : Sylow p G) :
    Nat.card P = p ^ m := by
  rw [P.card_eq_multiplicity, hn, factorization_pgl_order p m hm]

theorem sylow_fixedPoint_injective (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    Function.Injective (sylowFixedPoint p G hG_p) := by
  intro P Q hPQ
  by_contra h_contra
  have h_comm_G : ∀ (g : G) (_ : g ∈ (P : Subgroup G)) (h : G) (_ : h ∈ (Q : Subgroup G)), g * h = h * g := by
    intro g hg h hh
    refine Subtype.ext ?_
    by_cases hg1 : g = 1; · rw [hg1]; exact Commute.one_left (h : PGL p)
    by_cases hh1 : h = 1; · rw [hh1]; exact Commute.one_right (g : PGL p)
    exact commute_of_orderOf_prime_common_fixedPoint p (g : PGL p) (h : PGL p) (sylowFixedPoint p G hG_p P)
      (sylow_element_order_p p G P g hg hg1) (sylow_element_order_p p G Q h hh hh1)
      (sylow_element_fixes p G hG_p P g hg) (hPQ.symm ▸ sylow_element_fixes p G hG_p Q h hh)

  have h_pq : ∀ g ∈ (P : Subgroup G) ⊔ (Q : Subgroup G), ∃ a ∈ (P : Subgroup G), ∃ b ∈ (Q : Subgroup G), g = a * b := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction
    next x hx =>
      cases hx with
      | inl hx => exact ⟨x, hx, 1, Q.one_mem, (mul_one x).symm⟩
      | inr hx => exact ⟨1, P.one_mem, x, hx, (one_mul x).symm⟩
    next => exact ⟨1, P.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
    next x y hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨c, hc, d, hd, rfl⟩ := hy
      exact ⟨a * c, P.mul_mem ha hc, b * d, Q.mul_mem hb hd, by
        rw [← mul_assoc, mul_assoc a b c, (h_comm_G c hc b hb).symm, ← mul_assoc a c b, mul_assoc]⟩
    next x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, by
        rw [mul_inv_rev, ← h_comm_G a⁻¹ (P.inv_mem ha) b⁻¹ (Q.inv_mem hb)]⟩

  have h_comm_subgroup : (P : Subgroup G) ⊔ (Q : Subgroup G) = (P : Subgroup G) := by
    apply P.is_maximal'
    · obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.2
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.2
      intro g
      obtain ⟨a, ha, b, hb, hg_eq⟩ := h_pq g g.2
      have h_ord_div {H : Subgroup G} (x : G) (hx : x ∈ H) : orderOf (x : PGL p) ∣ Nat.card H :=
        (show orderOf (x : PGL p) ∣ Nat.card (Subgroup.zpowers x) by simp only [orderOf_submonoid, Nat.card_zpowers, dvd_refl]).trans
          (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx))
      use m + n
      ext
      push_cast
      rw [hg_eq]
      refine orderOf_dvd_iff_pow_eq_one.mp <| (Commute.orderOf_mul_dvd_lcm (Subtype.ext_iff.mp (h_comm_G a ha b hb))).trans <| Nat.lcm_dvd ?_ ?_
      · exact (hm ▸ h_ord_div a ha).trans (pow_dvd_pow p (Nat.le_add_right m n))
      · exact (hn ▸ h_ord_div b hb).trans (pow_dvd_pow p (Nat.le_add_left n m))
    · exact le_sup_left

  have h_eq : (Q : Subgroup G) ≤ (P : Subgroup G) := le_trans le_sup_right h_comm_subgroup.le
  have h_card : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by rw [P.card_eq_multiplicity, Q.card_eq_multiplicity]
  exact h_contra <| Sylow.ext <| SetLike.ext' <| (Set.eq_of_subset_of_ncard_le h_eq h_card.ge).symm

theorem sylow_free_action (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P Q : Sylow p G) (hPQ : P ≠ Q)
    (g : G) (hg : g ∈ (P : Subgroup G)) (hg_ne : g ≠ 1) :
    (g : PGL p) • sylowFixedPoint p G hG_p Q ≠ sylowFixedPoint p G hG_p Q := by
  intro h_fix
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp <| order_p_one_fixedPoint p (g : PGL p) (sylow_element_order_p p G P g hg hg_ne)
  have hP_mem : sylowFixedPoint p G hG_p P ∈ fixedPoints p ↑g := sylow_element_fixes p G hG_p P g hg
  have hQ_mem : sylowFixedPoint p G hG_p Q ∈ fixedPoints p ↑g := h_fix
  rw [hx, Set.mem_singleton_iff] at hP_mem hQ_mem
  exact hPQ <| sylow_fixedPoint_injective p G hG_p <| hP_mem.trans hQ_mem.symm



theorem card_sylow_mod_card (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card P ∣ (Fintype.card (Sylow p G) - 1) := by
  set S : Finset (Sylow p G) := Finset.univ \ {P} with hS_def

  have h_free_action : ∀ g : G, g ∈ (P : Subgroup G) → g ≠ 1 → ∀ Q ∈ S, g • Q ≠ Q := by
    intro g hg hg_ne Q hQ hQ_eq
    have hgQ : g ∈ (Q : Subgroup G) := order_one_or_p_in_sylow p G hG_p Q g
      (Sylow.smul_eq_iff_mem_normalizer.mp hQ_eq) (Or.inr <| sylow_element_order_p p G P g hg hg_ne)
    have h_eq : P = Q := sylow_fixedPoint_injective p G hG_p <|
      shared_element_shared_fixedPoint p G hG_p P Q g hg hgQ hg_ne
    exact (Finset.mem_sdiff.mp (hS_def ▸ hQ)).2 (Finset.mem_singleton.mpr h_eq.symm)

  have h_orbit_size : ∀ Q ∈ S, Nat.card (MulAction.orbit (P : Subgroup G) Q) = Nat.card P := by
    intro Q hQ
    have h_stab : MulAction.stabilizer (P : Subgroup G) Q = ⊥ := Subgroup.ext fun ⟨g, hg⟩ ↦
      ⟨fun h_eq ↦ Subtype.ext <| by_contra fun h_ne ↦ h_free_action g hg h_ne Q hQ h_eq,
       fun h_one ↦ h_one.symm ▸ one_smul _ Q⟩
    have h_mul := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (P : Subgroup G) Q)
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (P : Subgroup G) Q), h_stab] at h_mul
    have h_bot : Nat.card (⊥ : Subgroup (P : Subgroup G)) = 1 := Nat.card_eq_fintype_card.trans (Fintype.card_ofSubsingleton (1 : (⊥ : Subgroup (P : Subgroup G))))
    rw [h_bot, mul_one] at h_mul
    exact h_mul.symm

  have h_partition : (Finset.card S : ℕ) = ∑ o ∈ Finset.image (fun Q ↦ MulAction.orbit (↥(P : Subgroup G)) Q) S, Nat.card o := by
    rw [Finset.card_eq_sum_ones]
    refine (Finset.sum_image' (fun _ ↦ 1) fun Q hQ ↦ ?_).symm
    have h_orbit_eq : Finset.filter (fun j ↦ MulAction.orbit (↥(P : Subgroup G)) j = MulAction.orbit (↥(P : Subgroup G)) Q) S =
      Finset.univ.filter (fun j ↦ j ∈ MulAction.orbit (↥(P : Subgroup G)) Q) := by
      ext j
      simp only [Finset.mem_filter, MulAction.orbit_eq_iff]
      refine ⟨fun ⟨_, hj_orbit⟩ ↦ ⟨Finset.mem_univ _, hj_orbit⟩, fun ⟨_, hj⟩ ↦ ⟨?_, hj⟩⟩
      simp only [hS_def, Finset.mem_sdiff, Finset.mem_singleton]
      refine ⟨Finset.mem_univ _, fun hj_eq_P ↦ ?_⟩
      obtain ⟨⟨g, hg⟩, hgQ⟩ := hj
      have hgQ_G : g • Q = j := hgQ
      have hgP : g⁻¹ • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (inv_mem hg))
      exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_singleton.mpr (by rw [← inv_smul_smul g Q, hgQ_G, hj_eq_P, hgP]))
    simp only [h_orbit_eq, Nat.card_eq_fintype_card, Fintype.card_ofFinset, Finset.sum_const, smul_eq_mul, mul_one]

  have h_card_S : Fintype.card (Sylow p G) - 1 = Finset.card S := by
    rw [hS_def, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_singleton]
  rw [h_card_S, h_partition]
  exact Finset.dvd_sum fun o ho ↦ by
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp ho
    exact h_orbit_size Q hQ ▸ dvd_rfl

theorem n_p_eq_pgl (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Fintype.card (Sylow p G) = p ^ m + 1 := by
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have h_dvd : p ^ m ∣ Fintype.card (Sylow p G) - 1 :=
    sylow_order_of_pgl_order p G m hm hn P ▸
      card_sylow_mod_card p G (hn.symm ▸ dvd_mul_of_dvd_left (dvd_pow_self p (ne_of_gt hm)) _) P

  obtain ⟨k, hk⟩ : ∃ k : ℕ, Fintype.card (Sylow p G) = k * p ^ m + 1 :=
    ⟨(Fintype.card (Sylow p G) - 1) / p ^ m, by rw [Nat.div_mul_cancel h_dvd, Nat.sub_add_cancel hn_p_gt1.le]⟩

  have h_div : Fintype.card (Sylow p G) ∣ p ^ (2 * m) - 1 := by
    have h_idx : (P : Subgroup G).index = p ^ (2 * m) - 1 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : Nat.Prime p).pos m) <| by
        rw [← sylow_order_of_pgl_order p G m hm hn P, Subgroup.index_mul_card, hn, mul_comm, sylow_order_of_pgl_order p G m hm hn P]
    exact h_idx ▸ (Nat.card_eq_fintype_card (α := Sylow p G)).symm ▸ Sylow.card_dvd_index P

  obtain ⟨a, ha⟩ : ∃ a : ℕ, (p ^ m - 1) * (p ^ m + 1) = (k * p ^ m + 1) * a := by
    have h_sq : p ^ (2 * m) - 1 = (p ^ m - 1) * (p ^ m + 1) := by
      calc p ^ (2 * m) - 1 = (p ^ m) ^ 2 - 1 ^ 2 := by rw [mul_comm 2 m, pow_mul, one_pow]
        _ = (p ^ m - 1) * (p ^ m + 1) := by rw [Nat.sq_sub_sq, mul_comm]
    exact h_sq ▸ hk ▸ h_div

  have hP : p ^ m ≥ 3 := by
    have h_pow : p ^ 1 ≤ p ^ m := Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos hm
    rw [pow_one] at h_pow
    exact Nat.le_trans (Fact.out : p > 2) h_pow
  have hk_pos : k ≥ 1 := by
    cases k; · rw [Nat.zero_mul, zero_add] at hk; exact absurd hk (ne_of_gt hn_p_gt1)
    · exact Nat.succ_pos _

  have hP_pos : 0 < p ^ m := Nat.lt_of_lt_of_le (by norm_num) hP
  have hP_sub_lt : p ^ m - 1 < p ^ m := Nat.sub_lt hP_pos (by norm_num)

  have h_expand : (p ^ m - 1) * p ^ m + (p ^ m - 1) = k * a * p ^ m + a := by
    calc (p ^ m - 1) * p ^ m + (p ^ m - 1) = (p ^ m - 1) * (p ^ m + 1) := by rw [Nat.mul_add, mul_one]
      _ = k * a * p ^ m + a := by rw [ha, Nat.add_mul, one_mul, mul_right_comm]

  have h_a_lt : a < p ^ m := by
    by_contra h_not_lt
    have h_div_eq : ((p ^ m - 1) + (p ^ m - 1) * p ^ m) / p ^ m = (a + k * a * p ^ m) / p ^ m := by rw [add_comm (p ^ m - 1), h_expand, add_comm a]
    rw [Nat.add_mul_div_right (p ^ m - 1) (p ^ m - 1) hP_pos, Nat.add_mul_div_right a (k * a) hP_pos, Nat.div_eq_of_lt hP_sub_lt, zero_add] at h_div_eq
    have h_ge : 1 + p ^ m ≤ a / p ^ m + k * a := Nat.add_le_add (by rw [Nat.le_div_iff_mul_le hP_pos, one_mul]; exact le_of_not_gt h_not_lt) (Nat.le_trans (le_of_not_gt h_not_lt) (le_trans (le_of_eq (one_mul a).symm) (Nat.mul_le_mul_right a hk_pos)))
    rw [← h_div_eq, add_comm 1] at h_ge
    exact absurd h_ge (not_le_of_gt (Nat.lt_trans hP_sub_lt (Nat.lt_succ_self _)))

  have h_a_eq : a = p ^ m - 1 := by
    have h_mod_eq : ((p ^ m - 1) + (p ^ m - 1) * p ^ m) % p ^ m = (a + k * a * p ^ m) % p ^ m := by rw [add_comm (p ^ m - 1), h_expand, add_comm a]
    rw [Nat.add_mul_mod_self_right (p ^ m - 1) (p ^ m - 1) (p ^ m), Nat.add_mul_mod_self_right a (k * a) (p ^ m), Nat.mod_eq_of_lt hP_sub_lt, Nat.mod_eq_of_lt h_a_lt] at h_mod_eq
    exact h_mod_eq.symm

  have h_k_eq_one : k = 1 := by
    rw [h_a_eq] at h_expand
    exact (Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num) hP)) (show 1 * (p ^ m - 1) = k * (p ^ m - 1) by rw [one_mul]; exact Nat.eq_of_mul_eq_mul_right hP_pos (Nat.add_right_cancel h_expand))).symm

  rw [h_k_eq_one, one_mul] at hk
  exact hk

end RecognitionHelpers

end Dickson
