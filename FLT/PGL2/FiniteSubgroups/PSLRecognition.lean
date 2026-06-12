/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import FLT.PGL2.FiniteSubgroups.FieldReconstruction

/-!
# Recognising `PSL₂(𝔽_q)` inside `PGL₂(𝔽̄_p)`

Let `G` be a finite subgroup of `PGL p = PGL₂(𝔽̄_p)` of order `(q² - 1) * q / 2`
(`q = p^m`) arising in the wild case of Dickson's classification. This file shows that
after conjugation `G` lies in the image of `PGL₂(𝔽_q) → PGL₂(𝔽̄_p)`
(`Dickson.psl_G_le_pgl_range_from_orbit`), the key step in identifying `G` with
`PSL₂(𝔽_q)`.

The argument runs through:
* `Dickson.sum_of_two_squares_Fq`: every element of `𝔽_q` is a sum of two squares;
* an analysis of the dilation parameters of the normalizer of a Sylow `p`-subgroup;
* `Dickson.orbit_infty_eq_P1Fq_psl`: the `G`-orbit of `∞` is exactly `ℙ¹(𝔽_q)`.
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

noncomputable section PSLRecognition

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p > 2)]




theorem sum_of_two_squares_Fq (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (a : K p) (ha : a ∈ F_q_in_K p m) :
    ∃ (b c : K p), b ∈ F_q_in_K p m ∧ c ∈ F_q_in_K p m ∧
      b ^ 2 + c ^ 2 = a := by
  have h_card : Fintype.card (GaloisField p m) = p ^ m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p m (by omega)]

  obtain ⟨a', ha'⟩ : ∃ a' : GaloisField p m, galoisFieldRingHom p m a' = a := by
    change a ^ p ^ m = a at ha
    obtain ⟨s, hs⟩ := Polynomial.splits_iff_exists_multiset.mp (instIsSplittingFieldZModGaloisFieldHSubPolynomialHPowNatX p m).1
    have h_eval := congr_arg (Polynomial.eval a ∘ Polynomial.map (galoisFieldRingHom p m)) hs
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ha, sub_self,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map] at h_eval

    have h_monic : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial (GaloisField p m)).Monic :=
      Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) (by
        rw [Polynomial.degree_X_pow, Polynomial.degree_X]
        exact WithBot.coe_lt_coe.mpr (lt_of_lt_of_le (by norm_num) hpm))

    rw [h_monic.leadingCoeff, map_one, one_mul, eq_comm, Multiset.prod_eq_zero_iff] at h_eval
    simp only [Multiset.mem_map] at h_eval
    obtain ⟨a', _, ha'⟩ := h_eval
    exact ⟨a', sub_eq_zero.mp ha' |> Eq.symm⟩

  obtain ⟨b', c', hbc'⟩ : ∃ b' c' : GaloisField p m, b'^2 + c'^2 = a' := by
    have hp2 : (Polynomial.X ^ 2 : Polynomial (GaloisField p m)).degree = 2 := Polynomial.degree_X_pow 2
    have hq2 : (Polynomial.X ^ 2 - Polynomial.C a' : Polynomial (GaloisField p m)).degree = 2 :=
      Polynomial.degree_X_pow_sub_C (by norm_num) a'
    obtain ⟨b', c', hbc'⟩ := FiniteField.exists_root_sum_quadratic hp2 hq2
      (by apply Nat.odd_iff.mp; rw [h_card]; exact Odd.pow ((Fact.out : Nat.Prime p).odd_of_ne_two (ne_of_gt (Fact.out : p > 2))))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hbc'
    exact ⟨b', c', by rw [← sub_eq_zero, ← hbc']; ring⟩

  refine ⟨galoisFieldRingHom p m b', galoisFieldRingHom p m c', ?_, ?_, ?_⟩
  · change (galoisFieldRingHom p m b') ^ p ^ m = galoisFieldRingHom p m b'
    rw [← map_pow, ← h_card, FiniteField.pow_card]
  · change (galoisFieldRingHom p m c') ^ p ^ m = galoisFieldRingHom p m c'
    rw [← map_pow, ← h_card, FiniteField.pow_card]
  · rw [← map_pow, ← map_pow, ← map_add, hbc', ha']


theorem sq_is_half_root_or_zero (m : ℕ) (b : K p) (hb : b ∈ F_q_in_K p m) :
    b ^ 2 = 0 ∨ (b ^ 2 ≠ 0 ∧ (b ^ 2) ^ ((p ^ m - 1) / 2) = 1) := by
  change b ^ p ^ m = b at hb
  rcases eq_or_ne b 0 with rfl | hb0
  · exact Or.inl (zero_pow two_ne_zero)
  · refine Or.inr ⟨pow_ne_zero 2 hb0, ?_⟩
    have h_even : 2 ∣ p ^ m - 1 := by
      rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)]
      have h_odd : ¬ Even p := fun h ↦ ne_of_gt (Fact.out : p > 2) ((Nat.Prime.even_iff Fact.out).mp h)
      exact iff_of_false (fun h ↦ h_odd (Nat.even_pow.mp h).1) (by norm_num)
    rw [← pow_mul, Nat.mul_div_cancel' h_even]
    apply mul_left_cancel₀ hb0
    calc b * b ^ (p ^ m - 1) = b ^ (p ^ m - 1 + 1) := by rw [← pow_succ']
      _ = b ^ p ^ m := by rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)]
      _ = b := hb
      _ = b * 1 := (mul_one b).symm


theorem additive_subgroup_eq_F_q_from_squares (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (V : Set (K p)) (hV_card : Set.ncard V = p ^ m)
    (hV_add : ∀ x y, x ∈ V → y ∈ V → x + y ∈ V)
    (hV_zero : (0 : K p) ∈ V)
    (hV_one : (1 : K p) ∈ V)
    (hV_sq_stable : ∀ c : K p, c ^ ((p ^ m - 1) / 2) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V) :
    V = F_q_in_K p m := by
  have hV_contains_sq : ∀ b ∈ F_q_in_K p m, b ^ 2 ∈ V := fun b hb ↦
    match sq_is_half_root_or_zero p m b hb with
    | Or.inl h => h ▸ hV_zero
    | Or.inr ⟨h_ne, h_root⟩ => mul_one (b ^ 2) ▸ hV_sq_stable (b ^ 2) h_root h_ne 1 hV_one
  have hFq_sub_V : F_q_in_K p m ⊆ V := fun a ha ↦ by
    obtain ⟨b, c, hb, hc, hbc⟩ := sum_of_two_squares_Fq p m hm hpm a ha
    exact hbc ▸ hV_add _ _ (hV_contains_sq b hb) (hV_contains_sq c hc)
  symm
  exact Set.eq_of_subset_of_ncard_le hFq_sub_V
    (by rw [hV_card, F_q_card p m hm])
    (Set.finite_of_ncard_pos (by rw [hV_card]; exact pow_pos (Fact.out : Nat.Prime p).pos _))





theorem sylow_order_of_psl_order (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (P : Sylow p G) :
    Nat.card P = p ^ m := by
  have h_even : 2 ∣ p ^ (2 * m) - 1 := by
    rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)]
    exact iff_of_false (fun h ↦ ne_of_gt (Fact.out : p > 2) ((Nat.Prime.even_iff Fact.out).mp (Nat.even_pow.mp h).1)) (by norm_num)
  have h_two : (2 : ℕ).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun h ↦ not_le_of_gt Fact.out (Nat.le_of_dvd (by norm_num) h)
  rw [P.card_eq_multiplicity, hn, Nat.factorization_div (dvd_mul_of_dvd_right h_even _)]
  change p ^ ((p ^ m * (p ^ (2 * m) - 1)).factorization p - Nat.factorization 2 p) = p ^ m
  rw [h_two, Nat.sub_zero]
  exact congrArg (p ^ ·) (factorization_pgl_order p m hm)

theorem n_p_gt_one_of_psl_order (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    Fintype.card (Sylow p G) > 1 := by
  by_contra h_contra
  obtain ⟨P, hP⟩ : ∃ P : Sylow p G, ∀ Q : Sylow p G, Q = P :=
    Fintype.card_eq_one_iff.mp (by have := Fintype.card_pos_iff.mpr (inferInstanceAs (Nonempty (Sylow p G))); omega)
  haveI h_normal : (P : Subgroup G).Normal := ⟨fun n hn g ↦ hP (g • P) ▸ Subgroup.mem_map_of_mem _ hn⟩

  have h_even : 2 ∣ p ^ (2 * m) - 1 := by
    rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Fact.out : Nat.Prime p).pos)]
    exact iff_of_false (fun h ↦ ne_of_gt (Fact.out : p > 2) ((Nat.Prime.even_iff Fact.out).mp (Nat.even_pow.mp h).1)) (by norm_num)

  have h_hole : p ∣ Nat.card G := dvd_trans (dvd_pow_self p (by omega : m ≠ 0)) (by rw [hn, Nat.mul_div_assoc _ h_even]; exact dvd_mul_right (p ^ m) _)
  have hP_divides : (p ^ (2 * m) - 1) / 2 ∣ p ^ m - 1 := by
    rw [← sylow_order_of_psl_order p G m hm hn P]
    rw [show (p ^ (2 * m) - 1) / 2 = (Nat.card G) / (Nat.card P) from by rw [hn, sylow_order_of_psl_order p G m hm hn P, Nat.mul_div_assoc _ h_even, Nat.mul_div_cancel_left _ (pow_pos (Fact.out : Nat.Prime p).pos _)]]
    convert normalizer_complement_divides_main p G P h_hole using 1
    rw [Subgroup.normalizer_eq_top]
    simp only [Subgroup.mem_top, Nat.card_subtype_true]
  have h_le := Nat.le_of_dvd (Nat.sub_pos_of_lt (by omega : 1 < p ^ m)) hP_divides
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2), pow_mul'] at h_le
  have h_le2 : (p ^ m) ^ 2 ≤ p ^ m * 2 := by omega
  rw [pow_two] at h_le2
  nlinarith only [hpm, h_le2]

end PSLRecognition

noncomputable section PSLOrbit

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]



theorem n_p_eq_psl (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Fintype.card (Sylow p G) = p ^ m + 1 := by
  have hp_gt_two : p > 2 := Fact.out
  have h_even : 2 ∣ p ^ (2 * m) - 1 := by
    rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Nat.le_trans (by norm_num : 1 ≤ 2) hp_gt_two.le))]
    have h_odd : ¬ Even p := fun h ↦ ne_of_gt hp_gt_two ((Nat.Prime.even_iff Fact.out).mp h)
    exact iff_of_false (fun h ↦ h_odd (Nat.even_pow.mp h).1) (by norm_num)
  have hG_p : p ∣ Nat.card G := by
    rw [hn]
    exact Nat.dvd_div_of_mul_dvd (mul_comm p 2 ▸ Nat.mul_dvd_mul (dvd_pow_self p (ne_of_gt hm)) h_even)

  obtain ⟨k, hk⟩ : ∃ k, Fintype.card (Sylow p G) = k * p ^ m + 1 := by
    let P := Classical.arbitrary (Sylow p G)
    have hP : Nat.card P = p ^ m := sylow_order_of_psl_order p G m hm hn P
    obtain ⟨k, hk⟩ := card_sylow_mod_card p G hG_p P
    exact ⟨k, by rw [mul_comm, ← hP, ← hk, Nat.sub_add_cancel hn_p_gt1.le]⟩

  have hk_one : k * p ^ m + 1 ∣ (p ^ m - 1) * (p ^ m + 1) := by
    have h_coprime : Nat.Coprime (k * p ^ m + 1) (p ^ m) := by change Nat.gcd (k * p ^ m + 1) (p ^ m) = 1; norm_num
    have h_sq : p ^ (2 * m) - 1 = (p ^ m - 1) * (p ^ m + 1) := by
      calc p ^ (2 * m) - 1
        _ = p ^ (m * 2) - 1 := by rw [mul_comm 2 m]
        _ = (p ^ m) ^ 2 - 1 ^ 2 := by rw [pow_mul, one_pow]
        _ = (p ^ m - 1) * (p ^ m + 1) := by rw [Nat.sq_sub_sq, mul_comm]
    have h_divG : Nat.card G ∣ p ^ m * (p ^ (2 * m) - 1) := hn ▸ Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right h_even _)
    refine h_sq ▸ h_coprime.dvd_of_dvd_mul_left (dvd_trans ?_ h_divG)
    rw [← hk, ← Nat.card_eq_fintype_card, Nat.card_congr (Sylow.equivQuotientNormalizer (Classical.arbitrary (Sylow p G)))]
    exact Subgroup.card_quotient_dvd_card _

  have hp_gt_one : 1 < p ^ m := one_lt_pow₀ (Nat.lt_trans (by norm_num : 1 < 2) hp_gt_two) (ne_of_gt hm)
  rcases k with _ | _ | k
  · rw [hk, Nat.zero_mul, Nat.zero_add] at hn_p_gt1; exact absurd hn_p_gt1 (Nat.lt_irrefl 1)
  · rw [hk, Nat.one_mul]
  · obtain ⟨a, ha⟩ := hk_one
    have h_sub : (p ^ m - 1) + 1 = p ^ m := Nat.sub_add_cancel hp_gt_one.le
    rcases a with _ | _ | a
    · nlinarith only [ha, h_sub, hp_gt_one]
    · have h_k_bound : p ^ m > k + 2 := by nlinarith only [ha, h_sub, hp_gt_one]
      nlinarith only [ha, h_sub, hp_gt_one, h_k_bound]
    · have h_a_bound : (a + 2) * (k + 2) > p ^ m - 1 := by nlinarith only [ha, h_sub, hp_gt_one]
      nlinarith only [ha, h_sub, hp_gt_one, h_a_bound]


theorem z1_eq_psl (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (P : Sylow p G) (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    normalizerQuotient p G P = (p ^ m - 1) / 2 := by
  have h_orbit_stabilizer : Nat.card (Subgroup.normalizer (P : Subgroup G)) * Fintype.card (Sylow p G) = Nat.card G := by
    rw [mul_comm, ← Nat.card_eq_fintype_card, Sylow.card_eq_index_normalizer P, Subgroup.index_mul_card]
  have h_card_normalizer : Nat.card (Subgroup.normalizer (P : Subgroup G)) = (p ^ m * (p ^ (2 * m) - 1)) / (2 * (p ^ m + 1)) := by
    have h1 : Nat.card (Subgroup.normalizer (P : Subgroup G)) * (p ^ m + 1) = p ^ m * (p ^ (2 * m) - 1) / 2 := by
      rw [← n_p_eq_psl p G m hm hn hn_p_gt1, h_orbit_stabilizer, hn]
    rw [← Nat.div_div_eq_div_mul, ← h1, Nat.mul_div_cancel _ (Nat.zero_lt_succ _)]
  have h_sq : p ^ (2 * m) - 1 = (p ^ m - 1) * (p ^ m + 1) := by
    rw [mul_comm 2 m, pow_mul]
    exact (Nat.sq_sub_sq (p ^ m) 1).trans (mul_comm _ _)
  change Nat.card (Subgroup.normalizer (P : Subgroup G)) / Nat.card P = (p ^ m - 1) / 2
  rw [sylow_order_of_psl_order p G m hm hn P, h_card_normalizer]
  rw [Nat.div_div_eq_div_mul, mul_comm (2 * (p ^ m + 1)) (p ^ m), h_sq]
  rw [← mul_assoc, ← mul_assoc, Nat.mul_div_mul_right _ _ (Nat.zero_lt_succ _)]
  rw [mul_comm (p ^ m) (p ^ m - 1), mul_comm (p ^ m) 2, Nat.mul_div_mul_right _ _ (by positivity)]



theorem normDilationParam_image_card_eq_normalizerQuotient
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    Set.ncard (Set.range (normDilationParam p G hG_p P hP_fix)) =
      normalizerQuotient p G P := by
  let f : ↥(Subgroup.normalizer (P : Subgroup G)) →* (K p)ˣ :=
    MonoidHom.mk' (fun g ↦ Units.mk0 (normDilationParam p G hG_p P hP_fix g) (dilationParam_ne_zero p _ (normalizer_element_fixes_infinity p G hG_p P hP_fix g g.property)))
      (fun a b ↦ Units.ext (normDilationParam_mul p G hG_p P hP_fix a b))

  have h_ker : f.ker = (P : Subgroup G).comap (Subgroup.subtype (Subgroup.normalizer (P : Subgroup G))) := by
    ext g
    refine ⟨fun hg ↦ ?_, fun hg ↦ Units.ext (normDilationParam_of_P p G hG_p P hP_fix g hg)⟩
    have h_coset := same_normDilationParam_imp_coset p G hG_p P hP_fix g 1 <|
      (congr_arg Units.val hg).trans (dilationParam_one p (normalizer_element_fixes_infinity p G hG_p P hP_fix 1 (Subgroup.one_mem _))).symm
    change (g.val : G) * (1 : G)⁻¹ ∈ (P : Subgroup G) at h_coset
    rw [inv_one, mul_one] at h_coset
    exact h_coset

  let e : Set.range f ≃ Set.range (normDilationParam p G hG_p P hP_fix) :=
    Equiv.ofBijective (fun ⟨u, hu⟩ ↦ ⟨u.val, by rcases hu with ⟨g, rfl⟩; exact ⟨g, rfl⟩⟩)
      ⟨fun ⟨u, _⟩ ⟨v, _⟩ h ↦ Subtype.ext (Units.ext (congr_arg Subtype.val h)),
       fun ⟨x, hx⟩ ↦ by rcases hx with ⟨g, rfl⟩; exact ⟨⟨f g, ⟨g, rfl⟩⟩, rfl⟩⟩

  change Nat.card (Set.range (normDilationParam p G hG_p P hP_fix)) = normalizerQuotient p G P
  rw [Nat.card_congr e.symm]
  change Nat.card (Set.range f) = Nat.card (Subgroup.normalizer (P : Subgroup G)) / Nat.card (P : Subgroup G)
  rw [← Subgroup.index_mul_card f.ker, Subgroup.index_ker f]
  have h_card_ker : Nat.card f.ker = Nat.card (P : Subgroup G) := by
    rw [h_ker]
    exact Nat.card_congr ⟨fun x ↦ ⟨x.val.val, x.property⟩, fun x ↦ ⟨⟨x.val, Subgroup.le_normalizer x.property⟩, x.property⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  rw [h_card_ker]
  exact (Nat.mul_div_cancel _ Nat.card_pos).symm



theorem normalizer_dilation_params_cover_nq_roots
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    ∀ c : K p, c ^ (normalizerQuotient p G P) = 1 → c ≠ 0 →
      ∃ g : G, g ∈ (P : Subgroup G).normalizer ∧
        ∀ x ∈ translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G)),
          c * x ∈ translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G)) := by
  intro c hc hc_ne_zero
  let S := Set.range (normDilationParam p G hG_p P hP_fix)
  have hS_card : S.ncard = normalizerQuotient p G P :=
    normDilationParam_image_card_eq_normalizerQuotient p G hG_p P hP_fix
  have hS_finite : S.Finite := Set.finite_range _
  have hc_mem : c ∈ hS_finite.toFinset := by
    refine finite_subgroup_eq_roots_of_unity p _ _ ?_ ?_ ?_ ?_ ?_ ?_ c hc hc_ne_zero
    · exact Nat.div_pos (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le Subgroup.le_normalizer)) Nat.card_pos
    · rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
      exact hS_card
    all_goals simp only [Set.Finite.mem_toFinset]
    · exact ⟨1, normDilationParam_of_P p G hG_p P hP_fix 1 P.one_mem⟩
    · rintro _ ⟨g₁, rfl⟩ _ ⟨g₂, rfl⟩
      exact ⟨g₁ * g₂, normDilationParam_mul p G hG_p P hP_fix g₁ g₂⟩
    · rintro _ ⟨g, rfl⟩
      exact ⟨g⁻¹, eq_inv_of_mul_eq_one_left <|
        (normDilationParam_mul p G hG_p P hP_fix g⁻¹ g).symm.trans <|
        (congr_arg _ (inv_mul_cancel g)).trans (normDilationParam_of_P p G hG_p P hP_fix 1 P.one_mem)⟩
    · rintro _ ⟨g, rfl⟩
      exact dilationParam_ne_zero p g (normalizer_element_fixes_infinity p G hG_p P hP_fix g g.property)
  obtain ⟨g, rfl⟩ := hS_finite.mem_toFinset.mp hc_mem
  exact ⟨g.val, g.property, dilationParam_scales_translationSet p G hG_p P hP_fix g.val g.property⟩




theorem translationSet_stable_under_half_roots
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (V : Set (K p))
    (hV_def : V = translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) :
    ∀ c : K p, c ^ ((p ^ m - 1) / 2) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V := by
  intro c hc hc_ne x hx
  rw [hV_def] at hx ⊢
  rw [← z1_eq_psl p G m hm hpm hn P (n_p_gt_one_of_psl_order p G m hm hpm hn)] at hc
  obtain ⟨_, _, H⟩ := normalizer_dilation_params_cover_nq_roots p G hG_p P hP_fix c hc hc_ne
  exact H x hx




theorem translationSet_scaled_eq_Fq_psl (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (V : Set (K p)) (hV_card : Set.ncard V = p ^ m)
    (hV_add : ∀ x y, x ∈ V → y ∈ V → x + y ∈ V)
    (hV_zero : (0 : K p) ∈ V)
    (hV_stable : ∀ c : K p, c ^ ((p ^ m - 1) / 2) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V)
    (v : K p) (hv : v ∈ V) (hv_ne : v ≠ 0) :
    (fun x ↦ v⁻¹ * x) '' V = F_q_in_K p m := by
  have h_inj : Function.Injective (fun x ↦ v⁻¹ * x) := mul_right_injective₀ (inv_ne_zero hv_ne)
  refine additive_subgroup_eq_F_q_from_squares p m hm hpm ((fun x ↦ v⁻¹ * x) '' V) ?_ ?_ ?_ ?_ ?_
  · exact (Set.ncard_image_of_injective V h_inj).trans hV_card
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, hV_add x y hx hy, mul_add v⁻¹ x y⟩
  · exact ⟨0, hV_zero, mul_zero v⁻¹⟩
  · exact ⟨v, hv, inv_mul_cancel₀ hv_ne⟩
  · rintro c hc hc' _ ⟨x, hx, rfl⟩
    exact ⟨c * x, hV_stable c hc hc' x hx, mul_left_comm v⁻¹ c x⟩


theorem orbit_eq_infty_union_translations_psl
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (α₀ : K p) (hα₀ : P1point p α₀ ∈ orbitInfty p G) :
    orbitInfty p G =
      {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p
        (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) := by
  have h_card_eq : (orbitInfty p G).ncard = ({infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p (Subgroup.map G.subtype P))).ncard := by
    rw [orbitInfty_ncard p G hG_p P hP_fix, n_p_eq_psl p G m hm hn (n_p_gt_one_of_psl_order p G m hm hpm hn), add_comm]
    have hd : Disjoint {infinity p} (P1point p '' ((fun b ↦ α₀ + b) '' translationSet p (Subgroup.map G.subtype P))) := by
      rw [Set.disjoint_singleton_left]
      rintro ⟨b, _, hb⟩
      simp only [infinity, P1point, Projectivization.mk_eq_mk_iff] at hb
      obtain ⟨u, hu⟩ := hb
      have h1 : (u : K p) * 0 = 1 := congr_fun hu 1
      rw [mul_zero] at h1
      exact zero_ne_one h1
    haveI : Finite ↥(P1point p '' ((fun b ↦ α₀ + b) '' translationSet p (Subgroup.map G.subtype P))) :=
      (Set.Finite.image _ (Set.Finite.image _ (Set.finite_of_ncard_pos (by rw [translationSet_card_eq_P p G hG_p P hP_fix]; exact Nat.card_pos)))).to_subtype
    rw [Set.ncard_union_eq hd]
    · rw [Set.ncard_image_of_injective]
      · rw [Set.ncard_image_of_injective]
        · rw [Set.ncard_singleton, translationSet_card_eq_P p G hG_p P hP_fix, sylow_order_of_psl_order p G m hm hn P]
        · intro x y hxy
          exact add_left_cancel hxy
      · intro x y hxy
        simp only [P1point, Projectivization.mk_eq_mk_iff] at hxy
        obtain ⟨u, hu⟩ := hxy
        have h0 : (u : K p) * y = x := congr_fun hu 0
        have h1 : (u : K p) * 1 = 1 := congr_fun hu 1
        rw [mul_one] at h1
        rw [← h0, h1, one_mul]
  have h_orbit_finite : (orbitInfty p G).Finite :=
    Set.finite_of_ncard_pos (by rw [orbitInfty_ncard p G hG_p P hP_fix, n_p_eq_psl p G m hm hn (n_p_gt_one_of_psl_order p G m hm hpm hn)]; positivity)
  exact (Set.eq_of_subset_of_ncard_le (orbit_superset_of_translations p G (translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) (fun _ ⟨g, _, hg'⟩ ↦ hg'.symm ▸ Subtype.mem g) α₀ hα₀) h_card_eq.le h_orbit_finite).symm


theorem orbit_infty_eq_P1Fq_psl_core
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    ∃ g : PGL p,
      g • infinity p = infinity p ∧
      orbitInfty p (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = P1_Fq p m := by
  have h_card : Set.ncard (orbitInfty p G) = Fintype.card (Sylow p G) := orbitInfty_ncard p G hG_p P hP_fix
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : K p, P1point p α₀ ∈ orbitInfty p G := by
    obtain ⟨x, hx, hx_ne⟩ := Set.exists_ne_of_one_lt_ncard (h_card.symm ▸ n_p_gt_one_of_psl_order p G m hm hpm hn) (infinity p)
    rcases projLine_cases p x with rfl | ⟨α₀, rfl⟩ <;> [contradiction; exact ⟨α₀, hx⟩]

  let H := Subgroup.map (Subgroup.subtype G) (P : Subgroup G)
  set V := translationSet p H with hV_def
  have hV_card : Set.ncard V = p ^ m := by
    rw [hV_def, translationSet_card_eq_P p G hG_p P hP_fix, sylow_order_of_psl_order p G m hm hn P]

  obtain ⟨v₀, hv₀_mem, hv₀_ne⟩ : ∃ v₀ ∈ V, v₀ ≠ 0 := by
    by_contra! h
    have hV_eq : V = {0} := Set.eq_singleton_iff_unique_mem.mpr ⟨hV_def.symm ▸ translationSet_zero p H, h⟩
    have : Set.ncard V = 1 := hV_eq.symm ▸ Set.ncard_singleton 0
    omega

  let g_trans := translationPGL p (-α₀)
  let g_dil := dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne)
  let g₀ := g_dil * g_trans

  refine ⟨g₀, by rw [mul_smul, translation_smul_infinity, dilation_smul_infinity], ?_⟩

  have hV_stable := translationSet_stable_under_half_roots p G m hm hpm hn hG_p P hP_fix V hV_def
  have h_Fq : (fun x ↦ v₀⁻¹ * x) '' V = F_q_in_K p m :=
    translationSet_scaled_eq_Fq_psl p m hm hpm V hV_card
      (translationSet_add p H) (translationSet_zero p H)
      hV_stable v₀ hv₀_mem hv₀_ne

  have h_orbit_V : orbitInfty p G = {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' V) := by
    rw [hV_def]
    exact orbit_eq_infty_union_translations_psl p G m hm hpm hn hG_p P hP_fix α₀ hα₀

  have h_trans_orbit : orbitInfty p (G.map (MulEquiv.toMonoidHom (MulAut.conj g_trans))) = {infinity p} ∪ P1point p '' V :=
    orbit_translate_conj p G α₀ V h_orbit_V

  have h_map_eq : G.map (MulEquiv.toMonoidHom (MulAut.conj g₀)) =
      (G.map (MulEquiv.toMonoidHom (MulAut.conj g_trans))).map (MulEquiv.toMonoidHom (MulAut.conj g_dil)) := by
    rw [Subgroup.map_map]; congr 1; ext x; simp only [g₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group

  rw [P1_Fq, h_map_eq, ← h_Fq]
  exact orbit_dilation_conj p _ v₀⁻¹ (inv_ne_zero hv₀_ne) V h_trans_orbit



theorem orbit_infty_eq_P1Fq_psl
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    ∃ g : PGL p,
      orbitInfty p (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = P1_Fq p m := by
  have h_even : 2 ∣ p ^ (2 * m) - 1 := by
    rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Nat.le_trans (by norm_num : 1 ≤ 2) (Fact.out : p > 2).le))]
    have h_odd : ¬ Even p := fun h ↦ ne_of_gt (Fact.out : p > 2) ((Nat.Prime.even_iff Fact.out).mp h)
    exact iff_of_false (fun h ↦ h_odd (Nat.even_pow.mp h).1) (by norm_num)
  have hG_p : p ∣ Nat.card G := by
    rw [hn]
    exact Nat.dvd_div_of_mul_dvd (mul_comm p 2 ▸ Nat.mul_dvd_mul (dvd_pow_self p (ne_of_gt hm)) h_even)
  obtain ⟨k₀, P₁, hP₁⟩ := exists_conj_sylow_fixing_infty p G hG_p

  let G' := G.map (MulEquiv.toMonoidHom (MulAut.conj k₀))
  let e : G ≃ G' := Equiv.ofBijective (fun x ↦ ⟨MulAut.conj k₀ x, Subgroup.mem_map_of_mem _ x.2⟩)
    ⟨fun x y hxy ↦ Subtype.ext (MulEquiv.injective _ (Subtype.mk.inj hxy)),
     fun ⟨_, y, hy, rfl⟩ ↦ ⟨⟨y, hy⟩, rfl⟩⟩

  haveI : Finite G' := Finite.of_equiv _ e

  obtain ⟨g, _, hg_orbit⟩ := orbit_infty_eq_P1Fq_psl_core p G' m hm hpm
    (by rw [← Nat.card_congr e, hn]) (by rw [← Nat.card_congr e]; exact hG_p) P₁ hP₁

  refine ⟨g * k₀, ?_⟩
  have h_map_eq : G.map (MulEquiv.toMonoidHom (MulAut.conj (g * k₀))) =
      G'.map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [h_map_eq]
  exact hg_orbit


theorem G_preserves_P1Fq_psl
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    ∃ g : PGL p,
      ∀ h ∈ G.map (MulEquiv.toMonoidHom (MulAut.conj g)),
        ∀ x ∈ P1_Fq p m, h • x ∈ P1_Fq p m := by
  obtain ⟨g, hg⟩ := orbit_infty_eq_P1Fq_psl p G m hm hpm hn
  exact ⟨g, fun h hh x hx ↦ hg ▸ preserves_orbitInfty p _ h hh x (hg ▸ hx)⟩


theorem psl_G_le_pgl_range_from_orbit
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    ∃ g : PGL p, G.map (MulEquiv.toMonoidHom (MulAut.conj g)) ≤
      (pglMap (galoisFieldRingHom (p := p) m)).range := by
  obtain ⟨g, hg⟩ := G_preserves_P1Fq_psl p G m hm hpm hn
  exact ⟨g, fun h hh ↦ preserves_P1Fq_in_range p m hm h (hg h hh)⟩

end PSLOrbit

end Dickson
