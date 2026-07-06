/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import FLT.KnownIn1980s.PGL2.FiniteSubgroups.PGLBasic
public import FLT.KnownIn1980s.PGL2.FiniteSubgroups.PartitionHelpers

/-!
# Reconstructing a finite field from a wild subgroup of `PGL₂(𝔽̄_p)`

Let `G` be a finite subgroup of `PGL p = PGL₂(𝔽̄_p)` whose Sylow `p`-subgroup is not
cyclic of order dividing `p`. This file reconstructs a finite subfield `𝔽_q ⊆ 𝔽̄_p`
(`q = p^m`) from the translations contained in `G`.

We define:
* `Dickson.FqInK p m`: the subfield `{x | x ^ p ^ m = x}` of `K p = 𝔽̄_p`,
  i.e. the image of the Galois field `𝔽_{p^m}`;
* `Dickson.translationPGL` and `Dickson.dilationPGL`: the upper-triangular translation
  `x ↦ x + b` and dilation `x ↦ cx` as elements of `PGL p`;
* `Dickson.translationSet H`: the set of `b` with `x ↦ x + b` in `H`;
* `Dickson.galoisFieldRingHom`: an embedding `GaloisField p m →+* K p` with image
  `FqInK p m`.

The main results identify the translation set of (a conjugate of) the subgroup fixing
`∞` with the additive group of `𝔽_{p^m}`, the first step in recognising `G` as
`PSL₂(𝔽_q)` or `PGL₂(𝔽_q)`.
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

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]


/-- The subfield `𝔽_{p^m}` sitting inside `K p = 𝔽̄_p`, i.e. the set of `x` with `x ^ (p ^ m) = x`. -/
noncomputable def FqInK (m : ℕ) : Set (K p) :=
  {x : K p | x ^ (p ^ m) = x}

omit h_odd in
theorem F_q_add_closed (m : ℕ) (x y : K p) (hx : x ∈ FqInK p m) (hy : y ∈ FqInK p m) :
    x + y ∈ FqInK p m := by
  show (x + y) ^ (p ^ m) = x + y
  rw [add_pow_char_pow, (hx : x ^ (p ^ m) = x), (hy : y ^ (p ^ m) = y)]

omit h_odd in
theorem F_q_mul_closed (m : ℕ) (x y : K p) (hx : x ∈ FqInK p m) (hy : y ∈ FqInK p m) :
    x * y ∈ FqInK p m := by
  show (x * y) ^ (p ^ m) = x * y
  rw [mul_pow, (hx : x ^ (p ^ m) = x), (hy : y ^ (p ^ m) = y)]

omit h_odd in
theorem F_q_zero (m : ℕ) : (0 : K p) ∈ FqInK p m :=
  (zero_pow (pow_ne_zero m (Nat.Prime.ne_zero Fact.out)))

omit h_odd in
theorem F_q_one (m : ℕ) : (1 : K p) ∈ FqInK p m :=
  one_pow (p ^ m)

omit h_odd in
theorem F_q_card (m : ℕ) (hm : m ≥ 1) : Set.ncard (FqInK p m) = p ^ m := by
  let P : Polynomial (K p) := Polynomial.X ^ (p ^ m) - Polynomial.X
  have hP_deg : P.natDegree = p ^ m := by
    refine (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_).trans (Polynomial.natDegree_X_pow (p ^ m))
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    exact one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (by omega)
  have hP_ne_zero : P ≠ 0 :=
    ne_of_apply_ne Polynomial.natDegree <| by
      rw [hP_deg, Polynomial.natDegree_zero]
      exact ne_of_gt (lt_trans zero_lt_one (one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (by omega)))
  have hP_nodup : P.roots.Nodup := by
    apply Polynomial.nodup_roots
    rw [Polynomial.separable_def, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
    rw [Nat.cast_pow, CharP.cast_eq_zero (K p) p, zero_pow (by omega), Polynomial.C_0, zero_mul, zero_sub]
    exact ⟨0, -1, by ring⟩
  rw [show FqInK p m = (P.roots.toFinset : Set (K p)) by
    ext x
    change x ^ (p ^ m) = x ↔ x ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne_zero]
    change x ^ (p ^ m) = x ↔ Polynomial.eval x (Polynomial.X ^ (p ^ m) - Polynomial.X) = 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.symm]
  rw [Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hP_nodup]
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits P), hP_deg]

omit h_odd in
theorem additive_subgroup_eq_F_q (m : ℕ) (hm : m ≥ 1)
    (V : Set (K p)) (hV_card : Set.ncard V = p ^ m)
    (hV_zero : (0 : K p) ∈ V)
    (hV_one : (1 : K p) ∈ V)
    (hV_stable : ∀ c : K p, c ^ (p ^ m - 1) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V) :
    V = FqInK p m := by
  have hV_subset : FqInK p m ⊆ V := fun x hx ↦ by
    rcases eq_or_ne x 0 with rfl | hx0
    · exact hV_zero
    · exact mul_one x ▸ hV_stable x
        (mul_left_cancel₀ hx0 <| by rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)), mul_one, hx])
        hx0 1 hV_one
  exact (Set.eq_of_subset_of_ncard_le hV_subset
    (hV_card.trans (F_q_card p m hm).symm).le
    (Set.finite_of_ncard_pos (hV_card.symm ▸ pow_pos (Nat.Prime.pos Fact.out) m))).symm


/-- The translation `x ↦ x + b` as the element `!![1, b; 0, 1]` of `GL₂(K p)`. -/
noncomputable def translationGL (b : K p) : GL (Fin 2) (K p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by erw [Matrix.det_fin_two, mul_zero, sub_zero, mul_one]; exact one_ne_zero)


/-- The dilation `x ↦ c x` (for `c ≠ 0`) as the element `!![c, 0; 0, 1]` of `GL₂(K p)`. -/
noncomputable def dilationGL (c : K p) (hc : c ≠ 0) : GL (Fin 2) (K p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1] (by erw [Matrix.det_fin_two, mul_zero, sub_zero, mul_one]; exact hc)


/-- The translation `x ↦ x + b` as an element of `PGL p = PGL₂(𝔽̄_p)`. -/
noncomputable def translationPGL (b : K p) : PGL p :=
  QuotientGroup.mk (translationGL p b)


/-- The dilation `x ↦ c x` (for `c ≠ 0`) as an element of `PGL p = PGL₂(𝔽̄_p)`. -/
noncomputable def dilationPGL (c : K p) (hc : c ≠ 0) : PGL p :=
  QuotientGroup.mk (dilationGL p c hc)

omit h_odd in
theorem translationPGL_zero : translationPGL p 0 = 1 := by
  change QuotientGroup.mk (translationGL p 0) = QuotientGroup.mk 1
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit h_odd in
theorem translationPGL_mul (a b : K p) :
    translationPGL p a * translationPGL p b = translationPGL p (a + b) := by
  change QuotientGroup.mk (translationGL p a * translationGL p b) = _
  congr 1
  apply Units.ext
  ext i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  match i, j with
  | 0, 0 => change (1 : K p) * 1 + a * 0 = 1; ring
  | 0, 1 => change (1 : K p) * b + a * 1 = a + b; ring
  | 1, 0 => change (0 : K p) * 1 + 1 * 0 = 0; ring
  | 1, 1 => change (0 : K p) * b + 1 * 1 = 1; ring

omit h_odd in
theorem translationPGL_inv (b : K p) :
    (translationPGL p b)⁻¹ = translationPGL p (-b) :=
  inv_eq_of_mul_eq_one_right <| by rw [translationPGL_mul, add_neg_cancel, translationPGL_zero]

theorem order_p_fixing_infinity_is_translation (g : PGL p)
    (h_fix : g • infinity p = infinity p) (h_order : orderOf g = p) :
    ∃ b : K p, b ≠ 0 ∧ g = translationPGL p b :=
  let ⟨x, hx⟩ := isUnipotent_of_fixesInfinity_orderOf p g h_fix h_order
  have hx_ne_zero : x ≠ 0 := fun hx0 ↦ by
    subst hx0
    change g = translationPGL p 0 at hx
    rw [hx, translationPGL_zero, orderOf_one] at h_order
    exact ne_of_gt (lt_trans (by norm_num : 1 < 2) Fact.out) h_order.symm
  ⟨x, hx_ne_zero, hx⟩

theorem n_p_gt_one_of_pgl_order (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1)) :
    Fintype.card (Sylow p G) > 1 := by
  by_contra h_contra
  obtain ⟨P, hP⟩ := Fintype.card_eq_one_iff.mp <|
    le_antisymm (not_lt.mp h_contra) Fintype.card_pos

  have hd : p ^ (2 * m) - 1 ∣ p ^ m - 1 := by
    have h_norm : (Subgroup.normalizer ((P : Subgroup G) : Set G)) = ⊤ := by
      refine (Subgroup.eq_top_iff' _).mpr fun g ↦ ?_
      rw [Sylow.coe_coe, ← Sylow.smul_eq_iff_mem_normalizer]
      exact hP (g • P)
    have h_dvd := normalizer_complement_divides_main p G P (hG ▸ dvd_mul_of_dvd_left (dvd_pow_self p (ne_of_gt hm)) _)
    rw [h_norm, Subgroup.card_top, hG, sylow_order_of_pgl_order p G m hm hG P] at h_dvd
    rw [Nat.mul_div_cancel_left _ (pow_pos (Nat.Prime.pos Fact.out) m)] at h_dvd
    exact h_dvd

  exact absurd hd <| Nat.not_dvd_of_pos_of_lt
    (Nat.sub_pos_of_lt (one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (ne_of_gt hm)))
    (by rw [tsub_lt_tsub_iff_right (Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out))]
        exact pow_lt_pow_right₀ (Nat.Prime.one_lt Fact.out) (by rw [two_mul]; exact lt_add_of_pos_right m hm))

theorem z1_eq_pm_minus_one (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (P : Sylow p G) (hn_p : Fintype.card (Sylow p G) > 1) :
    normalizerQuotient p G P = p ^ m - 1 := by
  have h_norm_card : Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = p ^ m * (p ^ m - 1) :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (p ^ m)) <| calc
      (p ^ m + 1) * Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))
        = Nat.card G := by
          rw [← n_p_eq_pgl p G m hm hG hn_p, ← Nat.card_eq_fintype_card, Nat.card_congr (Sylow.equivQuotientNormalizer P)]
          exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
      _ = (p ^ m + 1) * (p ^ m * (p ^ m - 1)) := by
          rw [hG, Nat.mul_comm 2 m, Nat.pow_mul, ← Nat.one_pow 2, Nat.sq_sub_sq (p ^ m) 1, ← Nat.mul_assoc, Nat.mul_comm (p ^ m) (p ^ m + 1), Nat.mul_assoc]
  rw [normalizerQuotient, h_norm_card, sylow_order_of_pgl_order p G m hm hG P]
  exact Nat.mul_div_cancel_left _ (pow_pos (Nat.Prime.pos Fact.out) m)


/-- The set of `b : K p` for which the translation `x ↦ x + b` lies in the subgroup `H`. -/
noncomputable def translationSet (H : Subgroup (PGL p)) : Set (K p) :=
  {b : K p | translationPGL p b ∈ H}

theorem p_subgroup_fixing_infinity_translations
    (H : Subgroup (PGL p)) [Finite H]
    (hH_p : IsPGroup p H) (_hH_nontrivial : Nontrivial H)
    (hH_fix : ∀ g ∈ H, g • infinity p = infinity p) :
    (∀ g ∈ H, ∃ b : K p, g = translationPGL p b) ∧
    Set.ncard (translationSet p H) = Nat.card H := by
  have h_translation_set : ∀ g ∈ H, ∃ b : K p, g = translationPGL p b := fun g hg ↦ by
    by_cases hg_one : g = 1
    · exact ⟨0, hg_one.trans (translationPGL_zero p).symm⟩
    · exact (order_p_fixing_infinity_is_translation p g (hH_fix g hg)
        (isPGroup_orderOf_eq_prime p H hH_p ⟨g, hg⟩ (fun h ↦ hg_one (congrArg Subtype.val h)))).imp fun b hb ↦ hb.2
  have h_image : (fun b ↦ translationPGL p b) '' translationSet p H = (H : Set (PGL p)) := by
    ext g
    refine ⟨fun ⟨x, hx, hg⟩ ↦ hg ▸ hx, fun hg ↦ ?_⟩
    obtain ⟨b, hb⟩ := h_translation_set g hg
    exact ⟨b, show translationPGL p b ∈ H from hb ▸ hg, hb.symm⟩
  refine ⟨h_translation_set, by
    rw [← Set.ncard_image_of_injective (translationSet p H) (fun (a b : K p) (hab : translationPGL p a = translationPGL p b) ↦ by
      let Y := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K p), 0; 1, 1] (by
        rw [Matrix.det_fin_two]; change (1 : K p) * (1 : K p) - (0 : K p) * (1 : K p) ≠ (0 : K p); rw [mul_one, zero_mul, sub_zero]; exact one_ne_zero)
      have h_comm : translationGL p (a - b) * Y = Y * translationGL p (a - b) :=
        (Subgroup.mem_center_iff.mp (by
          exact (Subgroup.center (GL (Fin 2) (K p))).inv_mem_iff.mp (mul_one (translationGL p (a - b))⁻¹ ▸ QuotientGroup.eq.mp (show translationPGL p (a - b) = 1 by
            rw [sub_eq_add_neg, ← translationPGL_mul, ← translationPGL_inv, hab, mul_inv_cancel]))) Y).symm
      have h_00 := congrFun (congrFun ((Units.val_mul (translationGL p (a - b)) Y).symm.trans ((congrArg (fun (U : GL (Fin 2) (K p)) ↦ (U : Matrix (Fin 2) (Fin 2) (K p))) h_comm).trans (Units.val_mul Y (translationGL p (a - b))))) 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at h_00
      change (1 : K p) * (1 : K p) + (a - b) * (1 : K p) = (1 : K p) * (1 : K p) + (0 : K p) * (0 : K p) at h_00
      exact eq_of_sub_eq_zero (Eq.trans
        (Eq.trans
          (show a - b = ((1 : K p) * (1 : K p) + (a - b) * (1 : K p)) - ((1 : K p) * (1 : K p) + (0 : K p) * (0 : K p)) by ring)
          (congrArg (fun x ↦ x - ((1 : K p) * (1 : K p) + (0 : K p) * (0 : K p))) h_00))
        (sub_self _))), h_image]
    rfl⟩

omit h_odd in
theorem translationSet_zero (H : Subgroup (PGL p)) :
    (0 : K p) ∈ translationSet p H :=
  show translationPGL p 0 ∈ H from (translationPGL_zero p).symm ▸ H.one_mem

omit h_odd in
theorem translationSet_add (H : Subgroup (PGL p)) (a b : K p)
    (ha : a ∈ translationSet p H) (hb : b ∈ translationSet p H) :
    a + b ∈ translationSet p H :=
  show translationPGL p (a + b) ∈ H from translationPGL_mul p a b ▸ H.mul_mem ha hb

omit h_odd in
theorem translationSet_neg (H : Subgroup (PGL p)) (b : K p)
    (hb : b ∈ translationSet p H) :
    -b ∈ translationSet p H :=
  show translationPGL p (-b) ∈ H from translationPGL_inv p b ▸ H.inv_mem hb

theorem pglMap_injective {F L : Type*} [Field F] [Field L]
    (f : F →+* L) (hf : Function.Injective f) :
    Function.Injective (pglMap f) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  erw [QuotientGroup.eq] at hxy ⊢
  rw [Subgroup.mem_center_iff] at hxy ⊢
  intro k
  have h_map := hxy (Matrix.GeneralLinearGroup.map f k)
  simp only [← map_inv, ← map_mul] at h_map
  ext i j
  apply hf
  exact congr_arg (fun m : GL (Fin 2) L ↦ m.val i j) h_map



/-- A ring embedding `GaloisField p m →+* K p` of `𝔽_{p^m}` into `𝔽̄_p`, with image `FqInK p m`. -/
noncomputable def galoisFieldRingHom (m : ℕ) : GaloisField p m →+* K p :=
  (IsAlgClosed.lift (R := ZMod p) (S := GaloisField p m) (M := K p)).toRingHom




omit h_odd in
theorem galoisFieldRingHom_range_eq_F_q (m : ℕ) (hm : m ≥ 1) :
    Set.range (galoisFieldRingHom (p := p) m) = FqInK p m := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨y, rfl⟩
    have h_y_pow : y ^ (p ^ m) = y := by
      convert FiniteField.pow_card y
      convert (Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm))).symm
    exact (map_pow (galoisFieldRingHom p m) y (p ^ m)).symm.trans <|
      congrArg (galoisFieldRingHom p m) h_y_pow
  · rw [F_q_card p m hm, Set.ncard_range_of_injective (RingHom.injective _)]
    exact le_of_eq (Nat.card_eq_fintype_card.trans
      (Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm)))).symm
  · exact Set.finite_of_ncard_pos ((F_q_card p m hm).symm ▸ pow_pos (Nat.Prime.pos Fact.out) m)

omit h_odd in
theorem translationPGL_in_range (m : ℕ) (hm : m ≥ 1) (b : K p)
    (hb : b ∈ FqInK p m) :
    translationPGL p b ∈ (pglMap (galoisFieldRingHom (p := p) m)).range := by
  obtain ⟨b', hb'⟩ := Set.mem_range.mp ((galoisFieldRingHom_range_eq_F_q p m hm).symm ▸ hb)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : GaloisField p m), b'; 0, 1] (by
    rw [Matrix.det_fin_two]
    change (1 : GaloisField p m) * 1 - b' * 0 ≠ 0
    rw [mul_one, mul_zero, sub_zero]
    exact one_ne_zero)), ?_⟩
  erw [QuotientGroup.map_mk]
  congr 1
  apply Units.ext
  ext i j
  match i, j with
  | 0, 0 => exact map_one (galoisFieldRingHom p m)
  | 0, 1 => exact hb'
  | 1, 0 => exact map_zero (galoisFieldRingHom p m)
  | 1, 1 => exact map_one (galoisFieldRingHom p m)

omit h_odd in
theorem dilationPGL_in_range (m : ℕ) (hm : m ≥ 1) (c : K p) (hc : c ≠ 0)
    (hc_mem : c ∈ FqInK p m) :
    dilationPGL p c hc ∈ (pglMap (galoisFieldRingHom (p := p) m)).range := by
  obtain ⟨c', hc'⟩ := Set.mem_range.mp ((galoisFieldRingHom_range_eq_F_q p m hm).symm ▸ hc_mem)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![c', 0; 0, 1] (by
    rw [Matrix.det_fin_two]
    change c' * 1 - 0 * 0 ≠ 0
    rw [mul_one, mul_zero, sub_zero]
    exact fun h_zero ↦ hc (hc' ▸ h_zero.symm ▸ map_zero (galoisFieldRingHom p m)))), ?_⟩
  erw [QuotientGroup.map_mk]
  congr 1
  apply Units.ext
  ext i j
  match i, j with
  | 0, 0 => exact hc'
  | 0, 1 => exact map_zero (galoisFieldRingHom p m)
  | 1, 0 => exact map_zero (galoisFieldRingHom p m)
  | 1, 1 => exact map_one (galoisFieldRingHom p m)

omit h_odd in
theorem upper_triangular_in_pgl_range (m : ℕ) (hm : m ≥ 1) (a b : K p) (ha : a ≠ 0)
    (ha_mem : a ∈ FqInK p m) (hb_mem : b ∈ FqInK p m) :
    QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![a, b; 0, (1 : K p)] (by
          rw [Matrix.det_fin_two]
          change a * 1 - b * 0 ≠ 0
          rw [mul_one, mul_zero, sub_zero]
          exact ha)) ∈
      (pglMap (galoisFieldRingHom (p := p) m)).range := by
  have hA : (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by
    rw [Matrix.det_fin_two]
    change a * 1 - b * 0 ≠ 0
    rw [mul_one, mul_zero, sub_zero]
    exact ha)) = (dilationGL p a ha) * (translationGL p (b / a)) := by
    apply Units.ext
    ext i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two];
    match i, j with
    | 0, 0 => change a = a * 1 + 0 * 0; rw [mul_one, mul_zero, add_zero]
    | 0, 1 => change b = a * (b / a) + 0 * 1; rw [zero_mul, add_zero, mul_div_cancel₀ b ha]
    | 1, 0 => change (0 : K p) = 0 * 1 + 1 * 0; rw [mul_one, mul_zero, add_zero]
    | 1, 1 => change (1 : K p) = 0 * (b / a) + 1 * 1; rw [zero_mul, mul_one, zero_add]
  have hb_div_a : b / a ∈ FqInK p m :=
    show (b / a) ^ (p ^ m) = b / a from calc
      (b / a) ^ (p ^ m) = b ^ (p ^ m) / a ^ (p ^ m) := by rw [div_pow]
      _                 = b / a ^ (p ^ m)           := by rw [hb_mem]
      _                 = b / a                     := by rw [ha_mem]
  exact hA.symm ▸ Subgroup.mul_mem _ (dilationPGL_in_range p m hm a ha ha_mem) (translationPGL_in_range p m hm (b / a) hb_div_a)

/-- The point `[c : 1]` of the projective line `ℙ¹(𝔽̄_p)` associated to `c : K p`. -/
noncomputable def P1point (c : K p) : ProjectiveLine p :=
  Projectivization.mk (K p) ![c, 1] fun h ↦ one_ne_zero (congr_fun h 1)

omit h_odd in
theorem fixes_zero_upper_triangular (a b d : K p) (h_det : a * d ≠ 0) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, b; 0, d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h_det)) : PGL p) •
        P1point p 0 = P1point p 0 → b = 0 := fun h_smul ↦ by
  rw [P1point] at h_smul
  erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h_smul
  rcases h_smul with ⟨c, hc⟩
  have h0 : (c : K p) * 0 = Matrix.mulVec !![a, b; 0, d] ![0, 1] 0 := congr_fun hc 0
  simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, zero_add, mul_one] at h0
  exact h0.symm

omit h_odd in
theorem fixes_one_diagonal (a d : K p) (h_det : a * d ≠ 0) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, (0 : K p); 0, d] (by rw [Matrix.det_fin_two]; norm_num; exact mul_ne_zero_iff.mp h_det)) : PGL p) •
        P1point p 1 = P1point p 1 →
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, (0 : K p); 0, d] (by rw [Matrix.det_fin_two]; norm_num; exact mul_ne_zero_iff.mp h_det)) : PGL p) = 1 := fun h_smul ↦ by
  rw [P1point] at h_smul
  erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h_smul
  rcases h_smul with ⟨c, hc⟩
  have h0 : (c : K p) * 1 = Matrix.mulVec !![a, 0; 0, d] ![1, 1] 0 := congr_fun hc 0
  have h1 : (c : K p) * 1 = Matrix.mulVec !![a, 0; 0, d] ![1, 1] 1 := congr_fun hc 1
  simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, add_zero, zero_add] at h0 h1
  have h_a_eq_d : a = d := h0.symm.trans h1
  erw [QuotientGroup.eq_one_iff]; rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  match i, j with
  | 0, 0 =>
    change ((g : Matrix (Fin 2) (Fin 2) (K p)) * !![a, 0; 0, d]) 0 0 = (!![a, 0; 0, d] * (g : Matrix (Fin 2) (Fin 2) (K p))) 0 0
    simp only [h_a_eq_d, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, zero_mul, add_zero, mul_comm]
  | 0, 1 =>
    change ((g : Matrix (Fin 2) (Fin 2) (K p)) * !![a, 0; 0, d]) 0 1 = (!![a, 0; 0, d] * (g : Matrix (Fin 2) (Fin 2) (K p))) 0 1
    simp only [h_a_eq_d, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, zero_mul, add_zero, zero_add, mul_comm]
  | 1, 0 =>
    change ((g : Matrix (Fin 2) (Fin 2) (K p)) * !![a, 0; 0, d]) 1 0 = (!![a, 0; 0, d] * (g : Matrix (Fin 2) (Fin 2) (K p))) 1 0
    simp only [h_a_eq_d, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, zero_mul, add_zero, zero_add, mul_comm]
  | 1, 1 =>
    change ((g : Matrix (Fin 2) (Fin 2) (K p)) * !![a, 0; 0, d]) 1 1 = (!![a, 0; 0, d] * (g : Matrix (Fin 2) (Fin 2) (K p))) 1 1
    simp only [h_a_eq_d, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, zero_mul, zero_add, mul_comm]

omit h_odd in
theorem pgl_fixes_three_points_eq_one (g : PGL p)
    (h_inf : g • infinity p = infinity p)
    (h_zero : g • P1point p 0 = P1point p 0)
    (h_one : g • P1point p 1 = P1point p 1) :
    g = 1 := by
  obtain ⟨a, b, d, h_det, rfl⟩ := (fixesInfinity_iff_upperTriangular p g).mp h_inf
  have hb := fixes_zero_upper_triangular p a b d h_det h_zero
  subst hb
  exact fixes_one_diagonal p a d h_det h_one

omit h_odd in
theorem upper_triangular_normalizes_translations
    (a b d : K p) (h_det : a * d ≠ 0) (x : K p) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, b; 0, d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h_det)) : PGL p) *
      translationPGL p x *
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![a, b; 0, d] (by rw [Matrix.det_fin_two]; change a * d - b * 0 ≠ 0; rw [mul_zero, sub_zero]; exact h_det)) : PGL p)⁻¹ =
      translationPGL p (a / d * x) := by
  rw [mul_inv_eq_iff_eq_mul, translationPGL, translationGL]
  apply congr_arg (QuotientGroup.mk : GL (Fin 2) (K p) → PGL p)
  ext i j
  match i, j with
  | 0, 0 =>
    change (!![a, b; 0, d] * !![1, x; 0, 1]) 0 0 = (!![1, a / d * x; 0, 1] * !![a, b; 0, d]) 0 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, mul_one, mul_zero, add_zero, one_mul]
  | 0, 1 =>
    change (!![a, b; 0, d] * !![1, x; 0, 1]) 0 1 = (!![1, a / d * x; 0, 1] * !![a, b; 0, d]) 0 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, mul_one, one_mul]
    rw [mul_right_comm, div_mul_cancel₀ a (right_ne_zero_of_mul h_det), add_comm]
  | 1, 0 =>
    change (!![a, b; 0, d] * !![1, x; 0, 1]) 1 0 = (!![1, a / d * x; 0, 1] * !![a, b; 0, d]) 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, mul_one, mul_zero, add_zero, zero_mul]
  | 1, 1 =>
    change (!![a, b; 0, d] * !![1, x; 0, 1]) 1 1 = (!![1, a / d * x; 0, 1] * !![a, b; 0, d]) 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, mul_one, zero_mul, zero_add, one_mul]

omit h_odd in
theorem general_matrix_in_pgl_range (m : ℕ) (hm : m ≥ 1) (a b c d : K p)
    (h_det : a * d - b * c ≠ 0)
    (ha : a ∈ FqInK p m) (hb : b ∈ FqInK p m)
    (hc : c ∈ FqInK p m) (hd : d ∈ FqInK p m) :
    (QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![a, b; c, d] (by rw [Matrix.det_fin_two]; exact h_det)) : PGL p) ∈
      (pglMap (galoisFieldRingHom (p := p) m)).range := by
  obtain ⟨a', ha'⟩ := Set.mem_range.mp (galoisFieldRingHom_range_eq_F_q p m hm ▸ ha)
  obtain ⟨b', hb'⟩ := Set.mem_range.mp (galoisFieldRingHom_range_eq_F_q p m hm ▸ hb)
  obtain ⟨c', hc'⟩ := Set.mem_range.mp (galoisFieldRingHom_range_eq_F_q p m hm ▸ hc)
  obtain ⟨d', hd'⟩ := Set.mem_range.mp (galoisFieldRingHom_range_eq_F_q p m hm ▸ hd)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a', b'; c', d'] (by
    rw [Matrix.det_fin_two]
    intro h_zero
    apply h_det
    rw [← ha', ← hb', ← hc', ← hd', ← map_mul, ← map_mul, ← map_sub]
    exact h_zero.symm ▸ map_zero _)), ?_⟩
  apply congr_arg (QuotientGroup.mk : GL (Fin 2) (K p) → PGL p)
  ext i j
  match i, j with
  | 0, 0 => exact ha'
  | 0, 1 => exact hb'
  | 1, 0 => exact hc'
  | 1, 1 => exact hd'


/-- The copy of `ℙ¹(𝔽_q)` (`q = p^m`) inside the projective line: `∞` together with the points `[c : 1]` for `c ∈ 𝔽_{p^m}`. -/
noncomputable def P1Fq (m : ℕ) : Set (ProjectiveLine p) :=
  {infinity p} ∪ (P1point p '' FqInK p m)

omit h_odd in
theorem infinity_mem_P1_Fq (m : ℕ) : infinity p ∈ P1Fq p m :=
  Set.mem_union_left _ rfl

omit h_odd in
theorem P1point_mem_P1_Fq (m : ℕ) (c : K p) (hc : c ∈ FqInK p m) :
    P1point p c ∈ P1Fq p m :=
  Set.mem_union_right _ ⟨c, hc, rfl⟩

theorem F_q_neg (m : ℕ) (x : K p) (hx : x ∈ FqInK p m) : -x ∈ FqInK p m := by
  simp only [FqInK, Set.mem_setOf_eq] at hx ⊢
  rw [neg_pow, hx, Odd.neg_one_pow (Odd.pow (Nat.Prime.odd_of_ne_two Fact.out (by exact ne_of_gt Fact.out))), neg_one_mul]

theorem F_q_sub_closed (m : ℕ) (x y : K p) (hx : x ∈ FqInK p m) (hy : y ∈ FqInK p m) :
    x - y ∈ FqInK p m :=
  (sub_eq_add_neg x y).symm ▸ F_q_add_closed p m x (-y) hx (F_q_neg p m y hy)

theorem three_transitive_case1 (m : ℕ) (hm : m ≥ 1)
    (β γ : K p) (hβ : β ∈ FqInK p m) (hγ : γ ∈ FqInK p m) (hne : β ≠ γ) :
    ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧
      h • infinity p = infinity p ∧
      h • P1point p 0 = P1point p β ∧
      h • P1point p 1 = P1point p γ := by
  have h_det : (γ - β) * 1 - β * 0 ≠ 0 := by rw [mul_one, mul_zero, sub_zero]; exact sub_ne_zero.mpr hne.symm
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![γ - β, β; 0, (1 : K p)] (by rw [Matrix.det_fin_two]; exact h_det)), ?_, ?_, ?_, ?_⟩
  · exact upper_triangular_in_pgl_range p m hm (γ - β) β (sub_ne_zero.mpr hne.symm) (F_q_sub_closed p m γ β hγ hβ) hβ
  · exact (fixesInfinity_iff_upperTriangular p _).mpr ⟨γ - β, β, 1, by rw [mul_one]; exact sub_ne_zero.mpr hne.symm, rfl⟩
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    use 1; ext i
    match i with
    | 0 =>
      change 1 * ![β, 1] 0 = Matrix.mulVec !![γ - β, β; 0, 1] ![0, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add, one_mul]
    | 1 =>
      change 1 * ![β, 1] 1 = Matrix.mulVec !![γ - β, β; 0, 1] ![0, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, zero_add]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    use 1; ext i
    match i with
    | 0 =>
      change 1 * ![γ, 1] 0 = Matrix.mulVec !![γ - β, β; 0, 1] ![1, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, one_mul]
      exact (sub_add_cancel γ β).symm
    | 1 =>
      change 1 * ![γ, 1] 1 = Matrix.mulVec !![γ - β, β; 0, 1] ![1, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, zero_add]


theorem three_transitive_case2 (m : ℕ) (hm : m ≥ 1)
    (α γ : K p) (hα : α ∈ FqInK p m) (hγ : γ ∈ FqInK p m) (hne : α ≠ γ) :
    ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧
      h • infinity p = P1point p α ∧
      h • P1point p 0 = infinity p ∧
      h • P1point p 1 = P1point p γ := by
  have h_det : α * 0 - (γ - α) * 1 ≠ 0 := by rw [mul_zero, mul_one, zero_sub, neg_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, γ - α; 1, (0 : K p)] (by rw [Matrix.det_fin_two]; exact h_det)), ?_, ?_, ?_, ?_⟩
  · exact general_matrix_in_pgl_range p m hm α (γ - α) 1 0 h_det hα (F_q_sub_closed p m γ α hγ hα) (F_q_one p m) (F_q_zero p m)
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    use 1; ext i
    match i with
    | 0 =>
      change 1 * ![α, 1] 0 = Matrix.mulVec !![α, γ - α; 1, 0] ![1, 0] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one, mul_zero, add_zero]
    | 1 =>
      change 1 * ![α, 1] 1 = Matrix.mulVec !![α, γ - α; 1, 0] ![1, 0] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (γ - α) (sub_ne_zero.mpr (Ne.symm hne))
    ext i
    match i with
    | 0 =>
      change (γ - α) * ![1, 0] 0 = Matrix.mulVec !![α, γ - α; 1, 0] ![0, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, zero_add]
    | 1 =>
      change (γ - α) * ![1, 0] 1 = Matrix.mulVec !![α, γ - α; 1, 0] ![0, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_mul, zero_add]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    use 1; ext i
    match i with
    | 0 =>
      change 1 * ![γ, 1] 0 = Matrix.mulVec !![α, γ - α; 1, 0] ![1, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, one_mul]; ring
    | 1 =>
      change 1 * ![γ, 1] 1 = Matrix.mulVec !![α, γ - α; 1, 0] ![1, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, add_zero]

theorem three_transitive_case3 (m : ℕ) (hm : m ≥ 1)
    (α β : K p) (hα : α ∈ FqInK p m) (hβ : β ∈ FqInK p m) (hne : α ≠ β) :
    ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧
      h • infinity p = P1point p α ∧
      h • P1point p 0 = P1point p β ∧
      h • P1point p 1 = infinity p := by
  have h_det : α * -1 - (-β) * 1 ≠ 0 := by rw [mul_neg_one, mul_one, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]; exact sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, -β; 1, (-1 : K p)] (by rw [Matrix.det_fin_two]; exact h_det)), ?_, ?_, ?_, ?_⟩
  · exact general_matrix_in_pgl_range p m hm α (-β) 1 (-1) h_det hα (F_q_neg p m β hβ) (F_q_one p m) (F_q_neg p m 1 (F_q_one p m))
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
    use 1; ext i
    match i with
    | 0 =>
      change 1 * ![α, 1] 0 = Matrix.mulVec !![α, -β; 1, -1] ![1, 0] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, mul_one, mul_zero, add_zero]
    | 1 =>
      change 1 * ![α, 1] 1 = Matrix.mulVec !![α, -β; 1, -1] ![1, 0] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
    ext i
    match i with
    | 0 =>
      change (-1) * ![β, 1] 0 = Matrix.mulVec !![α, -β; 1, -1] ![0, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, mul_one]; ring
    | 1 =>
      change (-1) * ![β, 1] 1 = Matrix.mulVec !![α, -β; 1, -1] ![0, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, mul_one]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (α - β) (sub_ne_zero.mpr hne)
    ext i
    match i with
    | 0 =>
      change (α - β) * ![1, 0] 0 = Matrix.mulVec !![α, -β; 1, -1] ![1, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]; ring
    | 1 =>
      change (α - β) * ![1, 0] 1 = Matrix.mulVec !![α, -β; 1, -1] ![1, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one]; ring

theorem three_transitive_case4 (m : ℕ) (hm : m ≥ 1)
    (α β γ : K p) (hα : α ∈ FqInK p m) (hβ : β ∈ FqInK p m) (hγ : γ ∈ FqInK p m)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧
      h • infinity p = P1point p α ∧
      h • P1point p 0 = P1point p β ∧
      h • P1point p 1 = P1point p γ := by
  have h_det : α * (β - γ) * (γ - α) - β * (γ - α) * (β - γ) ≠ 0 := by
    intro heq; have h1 : α * (β - γ) * (γ - α) - β * (γ - α) * (β - γ) = (α - β) * (β - γ) * (γ - α) := by ring
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hαβ) (sub_ne_zero.mpr hβγ)) (sub_ne_zero.mpr hαγ.symm) (by rw [h1] at heq; exact heq)
  refine ⟨QuotientGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero !![α * (β - γ), β * (γ - α); β - γ, γ - α] (by rw [Matrix.det_fin_two]; exact h_det)), ?_, ?_, ?_, ?_⟩
  · exact general_matrix_in_pgl_range p m hm (α * (β - γ)) (β * (γ - α)) (β - γ) (γ - α) h_det
      (F_q_mul_closed p m α (β - γ) hα (F_q_sub_closed p m β γ hβ hγ))
      (F_q_mul_closed p m β (γ - α) hβ (F_q_sub_closed p m γ α hγ hα))
      (F_q_sub_closed p m β γ hβ hγ)
      (F_q_sub_closed p m γ α hγ hα)
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (β - γ) (sub_ne_zero.mpr hβγ)
    ext i
    match i with
    | 0 =>
      change (β - γ) * ![α, 1] 0 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![1, 0] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, mul_one]; ring
    | 1 =>
      change (β - γ) * ![α, 1] 1 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![1, 0] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, mul_one]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (γ - α) (sub_ne_zero.mpr hαγ.symm)
    ext i
    match i with
    | 0 =>
      change (γ - α) * ![β, 1] 0 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![0, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, mul_one]; ring
    | 1 =>
      change (γ - α) * ![β, 1] 1 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![0, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, mul_one]
  · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]; use Units.mk0 (β - α) (sub_ne_zero.mpr hαβ.symm)
    ext i
    match i with
    | 0 =>
      change (β - α) * ![γ, 1] 0 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![1, 1] 0
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]; ring
    | 1 =>
      change (β - α) * ![γ, 1] 1 = Matrix.mulVec !![α * (β - γ), β * (γ - α); β - γ, γ - α] ![1, 1] 1
      simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]; ring


theorem pgl_Fq_three_transitive (m : ℕ) (hm : m ≥ 1)
    (a b c : ProjectiveLine p)
    (ha : a ∈ P1Fq p m) (hb : b ∈ P1Fq p m) (hc : c ∈ P1Fq p m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧
      h • infinity p = a ∧ h • P1point p 0 = b ∧ h • P1point p 1 = c := by
  simp only [P1Fq, Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at ha hb hc
  rcases ha with rfl | ⟨α, hα, rfl⟩
  · rcases hb with rfl | ⟨β, hβ, rfl⟩
    · exact absurd rfl hab
    · rcases hc with rfl | ⟨γ, hγ, rfl⟩
      · exact absurd rfl hac
      · exact three_transitive_case1 p m hm β γ hβ hγ (fun h ↦ hbc (congrArg _ h))
  · rcases hb with rfl | ⟨β, hβ, rfl⟩
    · rcases hc with rfl | ⟨γ, hγ, rfl⟩
      · exact absurd rfl hbc
      · exact three_transitive_case2 p m hm α γ hα hγ (fun h ↦ hac (congrArg _ h))
    · rcases hc with rfl | ⟨γ, hγ, rfl⟩
      · exact three_transitive_case3 p m hm α β hα hβ (fun h ↦ hab (congrArg _ h))
      · exact three_transitive_case4 p m hm α β γ hα hβ hγ
          (fun h ↦ hab (congrArg _ h)) (fun h ↦ hac (congrArg _ h)) (fun h ↦ hbc (congrArg _ h))

theorem preserves_P1Fq_in_range (m : ℕ) (hm : m ≥ 1)
    (g : PGL p) (hg : ∀ x ∈ P1Fq p m, g • x ∈ P1Fq p m) :
    g ∈ (pglMap (galoisFieldRingHom (p := p) m)).range := by
  have h_inf_ne_zero : infinity p ≠ P1point p 0 := fun heq ↦ by
    rw [infinity, P1point] at heq
    rw [Projectivization.mk_eq_mk_iff] at heq
    rcases heq with ⟨c, hc⟩
    have h1 : (c : K p) * 1 = 0 := congr_fun hc 1
    rw [mul_one] at h1; exact Units.ne_zero c h1
  have h_inf_ne_one : infinity p ≠ P1point p 1 := fun heq ↦ by
    rw [infinity, P1point] at heq
    rw [Projectivization.mk_eq_mk_iff] at heq
    rcases heq with ⟨c, hc⟩
    have h1 : (c : K p) * 1 = 0 := congr_fun hc 1
    rw [mul_one] at h1; exact Units.ne_zero c h1
  have h_zero_ne_one : P1point p 0 ≠ P1point p 1 := fun heq ↦ by
    rw [P1point, P1point, Projectivization.mk_eq_mk_iff] at heq
    rcases heq with ⟨c, hc⟩
    have h0 : (c : K p) * 1 = 0 := congr_fun hc 0
    rw [mul_one] at h0; exact Units.ne_zero c h0
  obtain ⟨h, h_range, h_fix⟩ : ∃ h : PGL p, h ∈ (pglMap (galoisFieldRingHom (p := p) m)).range ∧ h • infinity p = g • infinity p ∧ h • P1point p 0 = g • P1point p 0 ∧ h • P1point p 1 = g • P1point p 1 :=
    pgl_Fq_three_transitive p m hm _ _ _ (hg _ (infinity_mem_P1_Fq p m)) (hg _ (P1point_mem_P1_Fq p m 0 (F_q_zero p m))) (hg _ (P1point_mem_P1_Fq p m 1 (F_q_one p m)))
      (fun heq ↦ h_inf_ne_zero (by rw [← inv_smul_eq_iff, inv_smul_smul] at heq; exact heq))
      (fun heq ↦ h_inf_ne_one (by rw [← inv_smul_eq_iff, inv_smul_smul] at heq; exact heq))
      (fun heq ↦ h_zero_ne_one (by rw [← inv_smul_eq_iff, inv_smul_smul] at heq; exact heq))
  convert Subgroup.mul_mem _ h_range (show h⁻¹ * g ∈ (pglMap (galoisFieldRingHom p m)).range from ?_) using 1
  · exact (mul_inv_cancel_left h g).symm
  · exact (pgl_fixes_three_points_eq_one p _
      (by rw [mul_smul]; exact inv_smul_eq_iff.mpr h_fix.1.symm)
      (by rw [mul_smul]; exact inv_smul_eq_iff.mpr h_fix.2.1.symm)
      (by rw [mul_smul]; exact inv_smul_eq_iff.mpr h_fix.2.2.symm)).symm ▸ MonoidHom.mem_range.mpr ⟨1, map_one _⟩

omit h_odd in
theorem translation_smul_P1point (b α : K p) :
    translationPGL p b • P1point p α = P1point p (α + b) := by
  erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  use 1; ext i
  match i with
  | 0 =>
    change 1 * ![α + b, 1] 0 = Matrix.mulVec !![1, b; 0, 1] ![α, 1] 0
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  | 1 =>
    change 1 * ![α + b, 1] 1 = Matrix.mulVec !![1, b; 0, 1] ![α, 1] 1
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

omit h_odd in
theorem translation_smul_infinity (b : K p) :
    translationPGL p b • infinity p = infinity p :=
  (fixesInfinity_iff_upperTriangular p _).mpr ⟨1, b, 1, by norm_num, rfl⟩

omit h_odd in
theorem dilation_smul_P1point (c : K p) (hc : c ≠ 0) (α : K p) :
    dilationPGL p c hc • P1point p α = P1point p (c * α) := by
  erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  use 1; ext i
  match i with
  | 0 =>
    change 1 * ![c * α, 1] 0 = Matrix.mulVec !![c, 0; 0, 1] ![α, 1] 0
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  | 1 =>
    change 1 * ![c * α, 1] 1 = Matrix.mulVec !![c, 0; 0, 1] ![α, 1] 1
    simp only [Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

omit h_odd in
theorem dilation_smul_infinity (c : K p) (hc : c ≠ 0) :
    dilationPGL p c hc • infinity p = infinity p :=
  (fixesInfinity_iff_upperTriangular p _).mpr ⟨c, 0, 1, by rw [mul_one]; exact hc, rfl⟩

omit h_odd in
theorem F_q_inv (m : ℕ) (x : K p) (hx : x ∈ FqInK p m) (_hx_ne : x ≠ 0) :
    x⁻¹ ∈ FqInK p m :=
  (inv_pow x (p ^ m)).trans (congrArg (·⁻¹) hx)

omit h_odd in
theorem F_q_div (m : ℕ) (x y : K p) (hx : x ∈ FqInK p m) (hy : y ∈ FqInK p m)
    (hy_ne : y ≠ 0) : x / y ∈ FqInK p m := by
  rw [div_eq_mul_inv]
  exact F_q_mul_closed p m x y⁻¹ hx (F_q_inv p m y hy hy_ne)


omit h_odd in
theorem range_preserves_P1Fq (m : ℕ) (hm : m ≥ 1)
    (g : PGL p) (hg : g ∈ (pglMap (galoisFieldRingHom (p := p) m)).range) :
    ∀ x ∈ P1Fq p m, g • x ∈ P1Fq p m := by
  rcases hg with ⟨⟨g⟩, rfl⟩
  intro x hx
  simp only [P1Fq, Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hx ⊢
  rcases hx with rfl | ⟨a, ha, rfl⟩
  · let num := galoisFieldRingHom p m (g.1 0 0)
    let den := galoisFieldRingHom p m (g.1 1 0)
    by_cases h : den = 0
    · left
      erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
      have hnum : num ≠ 0 := by
        intro heq
        have h_det : num * galoisFieldRingHom p m (g.1 1 1) - galoisFieldRingHom p m (g.1 0 1) * den = galoisFieldRingHom p m g.1.det := by
          rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
        rw [heq, h, zero_mul, mul_zero, sub_zero] at h_det
        exact IsUnit.ne_zero (IsUnit.map (galoisFieldRingHom p m : GaloisField p m →* K p) (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero g))) h_det.symm
      use Units.mk0 num hnum
      ext i; match i with
      | 0 =>
        change num * ![1, 0] 0 = Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![1, 0] 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        change galoisFieldRingHom p m (g.1 0 0) * 1 = galoisFieldRingHom p m (g.1 0 0) * 1 + galoisFieldRingHom p m (g.1 0 1) * 0
        ring
      | 1 =>
        change num * ![1, 0] 1 = Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![1, 0] 1
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        change galoisFieldRingHom p m (g.1 0 0) * 0 = galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0
        have h_den : galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0 = den := by
          change galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0 = galoisFieldRingHom p m (g.1 1 0)
          ring
        rw [h_den, h, mul_zero]
    · right
      refine ⟨num / den, ?_, ?_⟩
      · apply F_q_div
        · exact (galoisFieldRingHom_range_eq_F_q p m hm) ▸ Set.mem_range_self _
        · exact (galoisFieldRingHom_range_eq_F_q p m hm) ▸ Set.mem_range_self _
        · exact h
      · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
        use (Units.mk0 den h)⁻¹
        ext i; match i with
        | 0 =>
          change den⁻¹ * Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![1, 0] 0 = ![num / den, 1] 0
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          change den⁻¹ * (galoisFieldRingHom p m (g.1 0 0) * 1 + galoisFieldRingHom p m (g.1 0 1) * 0) = num / den
          have h_num : galoisFieldRingHom p m (g.1 0 0) * 1 + galoisFieldRingHom p m (g.1 0 1) * 0 = num := by
            change galoisFieldRingHom p m (g.1 0 0) * 1 + galoisFieldRingHom p m (g.1 0 1) * 0 = galoisFieldRingHom p m (g.1 0 0)
            ring
          rw [h_num, div_eq_mul_inv, mul_comm]
        | 1 =>
          change den⁻¹ * Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![1, 0] 1 = ![num / den, 1] 1
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          change den⁻¹ * (galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0) = 1
          have h_den : galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0 = den := by
            change galoisFieldRingHom p m (g.1 1 0) * 1 + galoisFieldRingHom p m (g.1 1 1) * 0 = galoisFieldRingHom p m (g.1 1 0)
            ring
          rw [h_den]
          exact inv_mul_cancel₀ h
  · let num := galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1)
    let den := galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1)
    by_cases h : den = 0
    · left
      erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
      have hnum : num ≠ 0 := by
        intro heq
        have h_det : num * galoisFieldRingHom p m (g.1 1 0) - den * galoisFieldRingHom p m (g.1 0 0) = - galoisFieldRingHom p m g.1.det := by
          rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
          change (galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1)) * galoisFieldRingHom p m (g.1 1 0) - (galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1)) * galoisFieldRingHom p m (g.1 0 0) = _
          ring
        rw [heq, h, zero_mul, zero_mul, sub_zero] at h_det
        exact IsUnit.ne_zero (IsUnit.map (galoisFieldRingHom p m : GaloisField p m →* K p) (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero g))) (neg_eq_zero.mp h_det.symm)
      use Units.mk0 num hnum
      ext i; match i with
      | 0 =>
        change num * ![1, 0] 0 = Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![a, 1] 0
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        change (galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1)) * 1 = galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1) * 1
        ring
      | 1 =>
        change num * ![1, 0] 1 = Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![a, 1] 1
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        change (galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1)) * 0 = galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1
        have h_den : galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1 = den := by
          change galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1 = galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1)
          ring
        rw [h_den, h, mul_zero]
    · right
      refine ⟨num / den, ?_, ?_⟩
      · have hlin : ∀ i, galoisFieldRingHom p m (g.1 i 0) * a + galoisFieldRingHom p m (g.1 i 1) ∈ FqInK p m := fun i ↦
          F_q_add_closed p m _ _ (F_q_mul_closed p m _ _ ((galoisFieldRingHom_range_eq_F_q p m hm) ▸ Set.mem_range_self _) ha) ((galoisFieldRingHom_range_eq_F_q p m hm) ▸ Set.mem_range_self _)
        exact F_q_div p m _ _ (hlin 0) (hlin 1) h
      · erw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
        use (Units.mk0 den h)⁻¹
        ext i; match i with
        | 0 =>
          change den⁻¹ * Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![a, 1] 0 = ![num / den, 1] 0
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          change den⁻¹ * (galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1) * 1) = num / den
          have h_num : galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1) * 1 = num := by
            change galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1) * 1 = galoisFieldRingHom p m (g.1 0 0) * a + galoisFieldRingHom p m (g.1 0 1)
            ring
          rw [h_num, div_eq_mul_inv, mul_comm]
        | 1 =>
          change den⁻¹ * Matrix.mulVec (Matrix.GeneralLinearGroup.map (galoisFieldRingHom p m) g).val ![a, 1] 1 = ![num / den, 1] 1
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          change den⁻¹ * (galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1) = 1
          have h_den : galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1 = den := by
            change galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1) * 1 = galoisFieldRingHom p m (g.1 1 0) * a + galoisFieldRingHom p m (g.1 1 1)
            ring
          rw [h_den]
          exact inv_mul_cancel₀ h




theorem unique_sylow_fixing_infinity
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P Q : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G), g • infinity p = infinity p)
    (hQ_fix : ∀ g ∈ (Q : Subgroup G).map (Subgroup.subtype G), g • infinity p = infinity p) :
    P = Q :=
  sylow_fixedPoint_injective p G hG_p (
    (eq_sylow_fixedPoint p G hG_p P _ (fun _ hg ↦ hP_fix _ (Subgroup.mem_map_of_mem _ hg))).symm.trans
    (eq_sylow_fixedPoint p G hG_p Q _ (fun _ hg ↦ hQ_fix _ (Subgroup.mem_map_of_mem _ hg))))

theorem fixes_infinity_normalizes_sylow
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G), g • infinity p = infinity p)
    (g : G) (hg_fix : (g : PGL p) • infinity p = infinity p) :
    g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  rw [Sylow.coe_coe, ← Sylow.smul_eq_iff_mem_normalizer]
  apply unique_sylow_fixing_infinity p G hG_p (g • P) P
  · intro g_1 hg_1
    obtain ⟨x, hx_mem, rfl⟩ := Subgroup.mem_map.mp hg_1
    obtain ⟨k, hk_mem, rfl⟩ := hx_mem
    change ((g : PGL p) * (k : PGL p) * (g : PGL p)⁻¹) • infinity p = infinity p
    rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hg_fix.symm, hP_fix (k : PGL p) (Subgroup.mem_map.mpr ⟨k, hk_mem, rfl⟩), hg_fix]
  · exact hP_fix

/-- The orbit of `∞` under the subgroup `G'`, i.e. the set of points `g • ∞` for `g ∈ G'`. -/
def orbitInfty (G' : Subgroup (PGL p)) : Set (ProjectiveLine p) :=
  {x | ∃ g ∈ G', g • infinity p = x}


omit h_odd in
theorem preserves_orbitInfty (G' : Subgroup (PGL p))
    (h : PGL p) (hh : h ∈ G') (x : ProjectiveLine p)
    (hx : x ∈ orbitInfty p G') :
    h • x ∈ orbitInfty p G' :=
  let ⟨g, hg_mem, hg_eq⟩ := hx
  ⟨h * g, G'.mul_mem hh hg_mem, by rw [mul_smul, hg_eq]⟩


omit h_odd in
theorem infty_mem_orbitInfty (G' : Subgroup (PGL p)) :
    infinity p ∈ orbitInfty p G' :=
  ⟨1, G'.one_mem, one_smul _ _⟩

omit h_odd in
theorem orbit_closed_under_translation
    (G' : Subgroup (PGL p))
    (α : K p) (hα : P1point p α ∈ orbitInfty p G')
    (b : K p) (hb : translationPGL p b ∈ G') :
    P1point p (α + b) ∈ orbitInfty p G' :=
  translation_smul_P1point p b α ▸ preserves_orbitInfty p G' (translationPGL p b) hb (P1point p α) hα

omit h_odd in
theorem translationSet_scaled_eq_Fq (m : ℕ) (hm : m ≥ 1)
    (V : Set (K p)) (hV_card : Set.ncard V = p ^ m)
    (_hV_add : ∀ x y, x ∈ V → y ∈ V → x + y ∈ V)
    (hV_zero : (0 : K p) ∈ V) (_hV_neg : ∀ x, x ∈ V → -x ∈ V)
    (hV_stable : ∀ c : K p, c ^ (p ^ m - 1) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V)
    (v : K p) (hv : v ∈ V) (hv_ne : v ≠ 0) :
    (fun x ↦ v⁻¹ * x) '' V = FqInK p m := by
  apply additive_subgroup_eq_F_q
  · exact hm
  · rw [Set.ncard_image_of_injective]
    · exact hV_card
    · intro x y hxy
      change v⁻¹ * x = v⁻¹ * y at hxy
      rw [← one_mul x, ← mul_inv_cancel₀ hv_ne, mul_assoc, hxy, ← mul_assoc, mul_inv_cancel₀ hv_ne, one_mul]
  · exact ⟨0, hV_zero, mul_zero _⟩
  · exact ⟨v, hv, inv_mul_cancel₀ hv_ne⟩
  · rintro c hc hc_ne _ ⟨x, hx, rfl⟩
    exact ⟨c * x, hV_stable c hc hc_ne x hx, mul_left_comm v⁻¹ c x⟩

omit h_odd in
theorem orbitInfty_conj_of_fixes_infty (G' : Subgroup (PGL p))
    (g : PGL p) (hg_fix : g • infinity p = infinity p) :
    orbitInfty p (G'.map (MulEquiv.toMonoidHom (MulAut.conj g))) =
      (fun x ↦ g • x) '' orbitInfty p G' := by
  ext x
  simp only [orbitInfty, Set.mem_setOf_eq, Set.mem_image]
  have hg_inv : g⁻¹ • infinity p = infinity p := inv_smul_eq_iff.mpr hg_fix.symm
  constructor
  · rintro ⟨k, hk_mem, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hk_mem
    use a • infinity p
    constructor
    · exact ⟨a, ha, rfl⟩
    · change g • a • infinity p = (g * a * g⁻¹) • infinity p
      rw [mul_smul, mul_smul, hg_inv]
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    use MulAut.conj g a
    constructor
    · exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    · change (g * a * g⁻¹) • infinity p = g • a • infinity p
      rw [mul_smul, mul_smul, hg_inv]

omit h_odd in
theorem projLine_cases (x : ProjectiveLine p) :
    x = infinity p ∨ ∃ c : K p, x = P1point p c := by
  rcases x with ⟨v, hv⟩
  by_cases hv1 : v 1 = 0
  · left
    have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      match i with
      | 0 => exact h0
      | 1 => exact hv1
    exact Quotient.sound ⟨Units.mk0 (v 0) hv0, by
      ext i
      match i with
      | 0 => exact mul_one (v 0)
      | 1 =>
        change v 0 * 0 = v 1
        rw [hv1]
        exact mul_zero (v 0)⟩
  · right
    use v 0 / v 1
    exact Quotient.sound ⟨Units.mk0 (v 1) hv1, by
      ext i
      match i with
      | 0 => exact mul_div_cancel₀ (v 0) hv1
      | 1 => exact mul_one (v 1)⟩

omit h_odd in
theorem orbit_superset_of_translations
    (G' : Subgroup (PGL p))
    (V : Set (K p)) (hV_sub : ∀ b ∈ V, translationPGL p b ∈ G')
    (α₀ : K p) (hα₀ : P1point p α₀ ∈ orbitInfty p G') :
    {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' V)
      ⊆ orbitInfty p G' := by
  apply Set.union_subset
  · exact Set.singleton_subset_iff.mpr (infty_mem_orbitInfty p G')
  · rw [Set.image_subset_iff]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact orbit_closed_under_translation p G' α₀ hα₀ b (hV_sub b hb)

omit h_odd in
theorem finite_subgroup_eq_roots_of_unity
    (S : Finset (K p)) (n : ℕ) (hn : n ≥ 1)
    (hS_card : S.card = n)
    (_hS_subgroup : (1 : K p) ∈ S)
    (hS_mul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (_hS_inv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hS_ne_zero : ∀ a ∈ S, a ≠ 0) :
    ∀ c : K p, c ^ n = 1 → c ≠ 0 → c ∈ S := by
  intro c hc hc_ne
  have h0 : (0 : K p) ∉ S := fun h0 ↦ hS_ne_zero 0 h0 rfl
  have h_pow : ∀ a ∈ S, a ^ n = 1 := fun a ha ↦
    have h_image : Finset.image (a * ·) S = S :=
      Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.mpr (fun b hb ↦ hS_mul a ha b hb))
        (Finset.card_image_of_injective S (fun _ _ hxy ↦ mul_left_cancel₀ (fun h ↦ h0 (h ▸ ha)) hxy)).symm.le
    mul_right_cancel₀
      (Finset.prod_ne_zero_iff.mpr (fun b hb hb0 ↦ h0 (hb0 ▸ hb)))
      (calc a ^ n * ∏ b ∈ S, b = ∏ b ∈ S, (a * b) := by rw [← hS_card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
        _ = ∏ b ∈ S, b := by
          have h_pi : ∏ x ∈ S, a * x = ∏ x ∈ S.image (fun x ↦ a * x), x :=
            (Finset.prod_image (s := S) (g := fun x ↦ a * x) (f := fun x ↦ x) (fun _ _ _ _ hxy ↦ mul_left_cancel₀ (fun h ↦ h0 (h ▸ ha)) hxy)).symm
          rw [h_image] at h_pi
          exact h_pi
        _ = 1 * ∏ b ∈ S, b := (one_mul _).symm)
  have hS_eq : S = (Polynomial.nthRoots n (1 : K p)).toFinset :=
    Finset.eq_of_subset_of_card_le
      (fun a ha ↦ Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hn).mpr (h_pow a ha)))
      (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)).trans_eq hS_card.symm)
  exact hS_eq.symm ▸ Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hn).mpr hc)


omit h_odd in
theorem dilation_conjugation_formula (g : PGL p) (hg : g • infinity p = infinity p) :
    ∃ c : K p, c ≠ 0 ∧ ∀ x : K p,
      g * translationPGL p x * g⁻¹ = translationPGL p (c * x) :=
  let ⟨a, b, d, h_det, hg_eq⟩ := (fixesInfinity_iff_upperTriangular p g).mp hg
  ⟨a / d, div_ne_zero (left_ne_zero_of_mul h_det) (right_ne_zero_of_mul h_det),
    fun x ↦ hg_eq ▸ upper_triangular_normalizes_translations p a b d h_det x⟩

omit h_odd in
theorem dilation_param_mul (g₁ g₂ : PGL p) (c₁ c₂ : K p)
    (h₁ : ∀ x : K p, g₁ * translationPGL p x * g₁⁻¹ = translationPGL p (c₁ * x))
    (h₂ : ∀ x : K p, g₂ * translationPGL p x * g₂⁻¹ = translationPGL p (c₂ * x)) :
    ∀ x : K p, (g₁ * g₂) * translationPGL p x * (g₁ * g₂)⁻¹ = translationPGL p (c₁ * c₂ * x) :=
  fun x ↦ by rw [mul_inv_rev, ← mul_assoc, mul_assoc g₁, mul_assoc g₁, h₂, h₁, ← mul_assoc]

omit h_odd in
theorem dilation_param_inv (g : PGL p) (c : K p) (hc : c ≠ 0)
    (h : ∀ x : K p, g * translationPGL p x * g⁻¹ = translationPGL p (c * x)) :
    ∀ x : K p, g⁻¹ * translationPGL p x * g⁻¹⁻¹ = translationPGL p (c⁻¹ * x) :=
  fun x ↦ by
    have h1 : translationPGL p x = g * translationPGL p (c⁻¹ * x) * g⁻¹ := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [inv_inv, h1, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel, mul_one]


omit h_odd in
theorem translationPGL_injective : Function.Injective (translationPGL p) := fun a b hab ↦ by
  have h_eq := congrArg (fun M ↦ (M.val 0 0 : K p)) <| Subgroup.mem_center_iff.mp (QuotientGroup.eq.mp hab)
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K p), 0; 1, 1] (by
      simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, sub_zero, ne_eq]; exact one_ne_zero))
  have h_coe_1 : ∀ h, (↑(Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : K p), 0; 1, 1] h) : Matrix (Fin 2) (Fin 2) (K p)) = !![1, 0; 1, 1] := fun _ ↦ rfl
  have h_coe_a : (↑(translationGL p a) : Matrix (Fin 2) (Fin 2) (K p)) = !![1, a; 0, 1] := rfl
  have h_coe_b : (↑(translationGL p b) : Matrix (Fin 2) (Fin 2) (K p)) = !![1, b; 0, 1] := rfl
  simp only [h_coe_1, h_coe_a, h_coe_b, Matrix.inv_def, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, mul_one, mul_zero, add_zero, sub_zero, neg_mul, Ring.inverse_one, one_mul, neg_zero] at h_eq
  exact (calc b = 1 + (b + -a) + a - 1 := by ring
            _ = 1 + a - 1 := by rw [← h_eq]
            _ = a := by ring).symm

omit h_odd in
theorem dilation_param_one_is_translation (g : PGL p)
    (hg : g • infinity p = infinity p)
    (h : ∀ x : K p, g * translationPGL p x * g⁻¹ = translationPGL p (1 * x)) :
    ∃ β : K p, g = translationPGL p β := by
  obtain ⟨a, b, d, h_det, hg_eq⟩ := fixesInfinity_iff_upperTriangular p g |>.1 hg
  have h_conj : translationPGL p (a / d) = translationPGL p 1 := by
    have h1 := upper_triangular_normalizes_translations p a b d h_det 1
    have h2 := h 1
    rw [← hg_eq, mul_one] at h1
    rw [mul_one, h1] at h2
    exact h2
  have h_ad : a = d := eq_of_div_eq_one <| translationPGL_injective p h_conj
  use b / d
  have hd : d ≠ 0 := right_ne_zero_of_mul h_det
  rw [hg_eq, translationPGL]
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_center_iff, show b / d = d⁻¹ * b by rw [div_eq_mul_inv, mul_comm]]
  intro M
  apply Units.ext
  have h_coe_A : ∀ h, (↑(Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; (0 : K p), d] h) : Matrix (Fin 2) (Fin 2) (K p)) = !![d, b; (0 : K p), d] := by
    intro _; change !![a, b; (0 : K p), d] = !![d, b; (0 : K p), d]; rw [h_ad]
  have h_coe_B : (↑(translationGL p (d⁻¹ * b)) : Matrix (Fin 2) (Fin 2) (K p)) = !![(1 : K p), d⁻¹ * b; (0 : K p), (1 : K p)] := rfl
  have h_inv_dd : Ring.inverse (d * d) = d⁻¹ * d⁻¹ := by rw [Ring.inverse_eq_inv, mul_inv_rev, mul_comm]
  rw [← Matrix.ext_iff]
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals
    simp only [h_coe_A, h_coe_B, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, Matrix.mul_apply, Matrix.inv_def, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.det_fin_two, Matrix.adjugate_fin_two, Matrix.smul_apply, smul_eq_mul, mul_zero, sub_zero, neg_zero, h_inv_dd, inv_mul_cancel_right₀ hd]
    ring

omit h_odd in
theorem same_dilation_param_diff_translation (g₁ g₂ : PGL p) (c : K p)
    (hg₁ : g₁ • infinity p = infinity p)
    (hg₂ : g₂ • infinity p = infinity p)
    (h₁ : ∀ x : K p, g₁ * translationPGL p x * g₁⁻¹ = translationPGL p (c * x))
    (h₂ : ∀ x : K p, g₂ * translationPGL p x * g₂⁻¹ = translationPGL p (c * x)) :
    ∃ β : K p, g₁ = translationPGL p β * g₂ := by
      have h_translation : ∃ β : K p, g₁ * g₂⁻¹ = translationPGL p β := by
        apply dilation_param_one_is_translation
        · rw [mul_smul, inv_smul_eq_iff.mpr hg₂.symm, hg₁]
        · intro x
          by_cases hc : c = 0
          · have h1x := h₁ x
            rw [hc, zero_mul, translationPGL_zero] at h1x
            have h1x_simp : g₁ * translationPGL p x = g₁ := by
              rw [← mul_one (g₁ * translationPGL p x), ← inv_mul_cancel g₁, ← mul_assoc, h1x, one_mul]
            have htx : translationPGL p x = 1 := by
              rw [← one_mul (translationPGL p x), ← inv_mul_cancel g₁, mul_assoc, h1x_simp, inv_mul_cancel]
            rw [htx, one_mul, htx, mul_one, mul_inv_cancel]
          · have h_mul := dilation_param_mul p g₁ g₂⁻¹ c c⁻¹ h₁ (dilation_param_inv p g₂ c hc h₂) x
            rw [mul_inv_cancel₀ hc] at h_mul
            exact h_mul
      exact h_translation.imp fun β hβ ↦ by rw [← mul_one g₁, ← inv_mul_cancel g₂, ← mul_assoc, hβ]

/-- For `g` fixing `∞`, the nonzero scalar `c` such that conjugation by `g` sends the translation by `x` to the translation by `c x`. -/
noncomputable def dilationParam (g : PGL p) (hg : g • infinity p = infinity p) : K p :=
  (dilation_conjugation_formula p g hg).choose

omit h_odd in
theorem dilationParam_ne_zero (g : PGL p) (hg : g • infinity p = infinity p) :
    dilationParam p g hg ≠ 0 :=
  (dilation_conjugation_formula p g hg).choose_spec.1

omit h_odd in
theorem dilationParam_action (g : PGL p) (hg : g • infinity p = infinity p) :
    ∀ x : K p, g * translationPGL p x * g⁻¹ = translationPGL p (dilationParam p g hg * x) :=
  (dilation_conjugation_formula p g hg).choose_spec.2

omit h_odd in
theorem dilationParam_mul_eq (g₁ g₂ : PGL p)
    (hg₁ : g₁ • infinity p = infinity p) (hg₂ : g₂ • infinity p = infinity p)
    (hg₁₂ : (g₁ * g₂) • infinity p = infinity p) :
    dilationParam p (g₁ * g₂) hg₁₂ = dilationParam p g₁ hg₁ * dilationParam p g₂ hg₂ := by
  have h1 := dilation_param_mul p g₁ g₂ (dilationParam p g₁ hg₁) (dilationParam p g₂ hg₂) (dilationParam_action p g₁ hg₁) (dilationParam_action p g₂ hg₂) 1
  rw [dilationParam_action p (g₁ * g₂) hg₁₂ 1] at h1
  exact (mul_one _).symm.trans ((translationPGL_injective p h1).trans (mul_one _))

omit h_odd in
theorem dilationParam_one (h1 : (1 : PGL p) • infinity p = infinity p) :
    dilationParam p 1 h1 = 1 := by
  have h := dilationParam_action p 1 h1 1
  rw [inv_one, mul_one, one_mul] at h
  exact (mul_one _).symm.trans (translationPGL_injective p h.symm)

omit h_odd in
theorem dilationParam_eq_one_iff (g : PGL p) (hg : g • infinity p = infinity p) :
    dilationParam p g hg = 1 ↔ ∃ β : K p, g = translationPGL p β := by
  refine ⟨fun h ↦ dilation_param_one_is_translation p g hg (fun x ↦ by
    have h1 := dilationParam_action p g hg x
    rw [h] at h1
    exact h1), fun ⟨β, h⟩ ↦ by
      have h1 : g * translationPGL p 1 * g⁻¹ = translationPGL p 1 := by
        rw [h, translationPGL_inv, translationPGL_mul, translationPGL_mul]
        exact congrArg _ (by ring)
      rw [dilationParam_action p g hg 1] at h1
      exact (mul_one _).symm.trans (translationPGL_injective p h1)⟩

theorem normalizer_element_fixes_infinity
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g : G) (hg : g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G))) :
    (g : PGL p) • infinity p = infinity p := by
  have h_inf_eq : infinity p = sylowFixedPoint p G hG_p P :=
    eq_sylow_fixedPoint p G hG_p P _ (fun g hg ↦ hP_fix _ (Subgroup.mem_map_of_mem _ hg))
  rw [h_inf_eq]
  exact normalizer_stabilizes_fixedPoint p G P (sylowFixedPoint p G hG_p P)
    (sylow_element_fixes p G hG_p P)
    (eq_sylow_fixedPoint p G hG_p P)
    g hg

theorem dilationParam_scales_translationSet
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g : G) (hg : g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G))) :
    ∀ x ∈ translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G)),
      dilationParam p (g : PGL p) (normalizer_element_fixes_infinity p G hG_p P hP_fix g hg) * x ∈
        translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G)) := by
  intro x hx
  obtain ⟨y, hy, hy_eq⟩ := hx
  have h_conj : (g : PGL p) * translationPGL p x * (g : PGL p)⁻¹ ∈ Subgroup.map (Subgroup.subtype G) (P : Subgroup G) := by
    refine ⟨g * y * g⁻¹, (hg y).1 hy, ?_⟩
    change (g : PGL p) * G.subtype y * (g : PGL p)⁻¹ = (g : PGL p) * translationPGL p x * (g : PGL p)⁻¹
    rw [hy_eq]
  have h_action := dilationParam_action p (g : PGL p) (normalizer_element_fixes_infinity p G hG_p P hP_fix g hg) x
  rw [h_action] at h_conj
  exact h_conj

/-- The dilation parameter of an element `g` of the normalizer of the Sylow `p`-subgroup `P`, as a scalar in `K p`. -/
noncomputable def normDilationParam
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g : (Subgroup.normalizer ((P : Subgroup G) : Set G))) : K p :=
  dilationParam p (g : PGL p)
    (normalizer_element_fixes_infinity p G hG_p P hP_fix g g.prop)

theorem normDilationParam_of_P
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g : (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (hg : (g : G) ∈ (P : Subgroup G)) :
    normDilationParam p G hG_p P hP_fix g = 1 := by
  apply (dilationParam_eq_one_iff p (g : PGL p) (normalizer_element_fixes_infinity p G hG_p P hP_fix g g.prop)).mpr
  haveI h_P_nontrivial : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp <| by
    have h : Nat.card P = p ^ (Nat.factorization (Nat.card G) p) := by convert P.card_eq_multiplicity
    exact h.symm ▸ one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (Finsupp.mem_support_iff.mp <|
      Nat.mem_primeFactors.mpr ⟨Fact.out, hG_p, Nat.ne_of_gt Nat.card_pos⟩)
  haveI h_map_finite : Finite ((P : Subgroup G).map (Subgroup.subtype G)) :=
    Set.Finite.to_subtype <| Set.Finite.subset (Set.toFinite <| Set.range fun x : G ↦ x.val) (Set.image_subset_range G.subtype _)
  exact (p_subgroup_fixing_infinity_translations p ((P : Subgroup G).map (Subgroup.subtype G))
    (P.2.map G.subtype)
    (Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype (Subgroup.subtype_injective G)).toEquiv.symm.nontrivial
    hP_fix).1 (g : PGL p) (Subgroup.mem_map_of_mem _ hg)

theorem same_normDilationParam_imp_coset
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g₁ g₂ : (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (heq : normDilationParam p G hG_p P hP_fix g₁ =
           normDilationParam p G hG_p P hP_fix g₂) :
    (g₁ : G) * (g₂ : G)⁻¹ ∈ (P : Subgroup G) := by
  have h_translation : ∃ β : K p, ((g₁ : G) * (g₂ : G)⁻¹ : PGL p) = translationPGL p β :=
    (same_dilation_param_diff_translation p g₁.val g₂.val
      (normDilationParam p G hG_p P hP_fix g₁)
      (normalizer_element_fixes_infinity p G hG_p P hP_fix g₁ g₁.prop)
      (normalizer_element_fixes_infinity p G hG_p P hP_fix g₂ g₂.prop)
      (dilationParam_action p _ (normalizer_element_fixes_infinity p G hG_p P hP_fix g₁ g₁.prop))
      (fun x ↦ by rw [heq]; exact dilationParam_action p _ (normalizer_element_fixes_infinity p G hG_p P hP_fix g₂ g₂.prop) x)).imp
      fun β hβ ↦ mul_inv_eq_of_eq_mul hβ
  have h_pow : ((g₁ : G) * (g₂ : G)⁻¹ : PGL p) ^ p = 1 := by
    obtain ⟨β, hβ⟩ := h_translation
    have h_translation_pow : ∀ n : ℕ, (translationPGL p β) ^ n = translationPGL p (n • β) := by
      intro n; induction n with
      | zero => rw [pow_zero, zero_smul]; exact (translationPGL_zero p).symm
      | succ n ih => rw [pow_succ', ih, translationPGL_mul, add_smul, one_smul, add_comm]
    rw [hβ, h_translation_pow p, nsmul_eq_mul, CharP.cast_eq_zero (K p) p, zero_mul]
    exact translationPGL_zero p
  exact order_one_or_p_in_sylow p G hG_p P ((g₁ : G) * (g₂ : G)⁻¹) (Subgroup.mul_mem _ g₁.2 (Subgroup.inv_mem _ g₂.2))
    ((Nat.dvd_prime Fact.out).mp (orderOf_dvd_iff_pow_eq_one.mpr h_pow))

theorem normDilationParam_P_mul
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g : (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (h : G) (hh : h ∈ (P : Subgroup G)) :
    normDilationParam p G hG_p P hP_fix
      ⟨h * g, (Subgroup.normalizer ((P : Subgroup G) : Set G)).mul_mem (Subgroup.le_normalizer hh) g.prop⟩ =
    normDilationParam p G hG_p P hP_fix g := by
  have h_norm : h ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)) := Subgroup.le_normalizer hh
  have h_P := normDilationParam_of_P p G hG_p P hP_fix ⟨h, h_norm⟩ hh
  rw [normDilationParam, normDilationParam]
  rw [normDilationParam] at h_P
  change dilationParam p ((h : PGL p) * (g : PGL p)) _ = _
  rw [dilationParam_mul_eq p (h : PGL p) (g : PGL p)
    (normalizer_element_fixes_infinity p G hG_p P hP_fix h h_norm)
    (normalizer_element_fixes_infinity p G hG_p P hP_fix g.val g.prop)]
  rw [h_P, one_mul]

theorem normDilationParam_mul
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (g₁ g₂ : (Subgroup.normalizer ((P : Subgroup G) : Set G))) :
    normDilationParam p G hG_p P hP_fix (g₁ * g₂) =
    normDilationParam p G hG_p P hP_fix g₁ *
    normDilationParam p G hG_p P hP_fix g₂ := by
  apply dilationParam_mul_eq


theorem normDilationParam_image_card
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    Set.ncard (Set.range (normDilationParam p G hG_p P hP_fix)) = p ^ m - 1 := by
  set S := Set.range (normDilationParam p G hG_p P hP_fix)
  have h_fiber_card : ∀ y ∈ S, Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g = y} = Nat.card (P : Subgroup G) := by
    intro y hy
    obtain ⟨g, hg⟩ : ∃ g : (Subgroup.normalizer ((P : Subgroup G) : Set G)), normDilationParam p G hG_p P hP_fix g = y := hy
    calc
      Set.ncard {x : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix x = y}
        = Set.ncard (Set.image (fun h : (P : Subgroup G) ↦ (⟨h.val * g.val, Subgroup.mul_mem _ (Subgroup.le_normalizer h.prop) g.prop⟩ : (Subgroup.normalizer ((P : Subgroup G) : Set G)))) Set.univ) := by
          congr 1
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_univ, true_and]
          constructor
          · intro hx
            exact Exists.intro ⟨(x : G) * (g : G)⁻¹, same_normDilationParam_imp_coset p G hG_p P hP_fix x g (hx.trans hg.symm)⟩ (Subtype.ext (inv_mul_cancel_right (x : G) (g : G)))
          · rintro ⟨h, rfl⟩
            exact (normDilationParam_P_mul p G hG_p P hP_fix g h.val h.prop).trans hg
      _ = Set.ncard (Set.univ : Set (P : Subgroup G)) :=
          Set.ncard_image_of_injective (f := fun h : (P : Subgroup G) ↦ (⟨h.val * g.val, Subgroup.mul_mem _ (Subgroup.le_normalizer h.prop) g.prop⟩ : (Subgroup.normalizer ((P : Subgroup G) : Set G)))) Set.univ (fun h₁ h₂ h_eq ↦ Subtype.ext (mul_right_cancel (Subtype.ext_iff.mp h_eq)))
      _ = Nat.card (P : Subgroup G) := Set.ncard_univ (P : Subgroup G)
  have h_card_S_mul : Set.ncard S * Nat.card (P : Subgroup G) = Nat.card ((Subgroup.normalizer ((P : Subgroup G) : Set G))) := by
    have h_sum : ∀ s : Finset (K p), (∑ y ∈ s, Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g = y}) = Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g ∈ s} := by
      intro s
      induction' s using Finset.induction with y s hy ih
      · calc
          (∑ y ∈ (∅ : Finset (K p)), Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g = y})
            = 0 := Finset.sum_empty
          _ = Set.ncard (∅ : Set ((Subgroup.normalizer ((P : Subgroup G) : Set G)))) := Eq.symm (Set.ncard_empty ((Subgroup.normalizer ((P : Subgroup G) : Set G))))
          _ = Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g ∈ (∅ : Finset (K p))} := by
            congr 1
            ext g
            rw [Set.mem_empty_iff_false, Set.mem_setOf_eq]
            exact (iff_false_intro (Finset.notMem_empty _)).symm
      · rw [Finset.sum_insert hy, ih, ← Set.ncard_union_eq]
        · congr 1
          ext g
          rw [Set.mem_setOf_eq, Finset.mem_insert, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        · exact Set.disjoint_left.mpr fun x hx1 hx2 ↦ hy (hx1.symm ▸ hx2)
    calc
      Set.ncard S * Nat.card (P : Subgroup G)
        = (Set.toFinite S).toFinset.card * Nat.card (P : Subgroup G) := by
          congr 1
          have h_coe : S = ↑(Set.toFinite S).toFinset := by
            ext x
            simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
          exact (congrArg Set.ncard h_coe).trans (Set.ncard_coe_finset (Set.toFinite S).toFinset)
      _ = ∑ y ∈ (Set.toFinite S).toFinset, Nat.card (P : Subgroup G) := by
          simp only [Finset.sum_const, smul_eq_mul]
      _ = ∑ y ∈ (Set.toFinite S).toFinset, Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g = y} := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Set.Finite.mem_toFinset] at hy
          exact (h_fiber_card y hy).symm
      _ = Set.ncard {g : (Subgroup.normalizer ((P : Subgroup G) : Set G)) | normDilationParam p G hG_p P hP_fix g ∈ (Set.toFinite S).toFinset} := h_sum (Set.toFinite S).toFinset
      _ = Set.ncard (Set.univ : Set ((Subgroup.normalizer ((P : Subgroup G) : Set G)))) := by
          congr 1
          ext g
          rw [Set.mem_setOf_eq, Set.Finite.mem_toFinset]
          exact iff_of_true ⟨g, rfl⟩ (Set.mem_univ g)
      _ = Nat.card ((Subgroup.normalizer ((P : Subgroup G) : Set G))) := Set.ncard_univ ((Subgroup.normalizer ((P : Subgroup G) : Set G)))
  exact ((Nat.div_eq_of_eq_mul_left Nat.card_pos h_card_S_mul.symm).symm : Set.ncard S = normalizerQuotient p G P).trans (z1_eq_pm_minus_one p G m hm hG P (n_p_gt_one_of_pgl_order p G m hm hG))

theorem dilation_params_cover
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    ∃ S : Finset (K p),
      S.card = p ^ m - 1 ∧
      (1 : K p) ∈ S ∧
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧
      (∀ a ∈ S, a⁻¹ ∈ S) ∧
      (∀ a ∈ S, a ≠ 0) ∧
      (∀ c ∈ S, ∃ g : G, g ∈ (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∧
        ∀ x ∈ translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G)),
          c * x ∈ translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) := by
  have hG_p : p ∣ Nat.card G := by
    rw [hG]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) (p ^ (2 * m) - 1)
  have h_S_fin : (Set.range (normDilationParam p G hG_p P hP_fix)).Finite := Set.toFinite _
  set S := h_S_fin.toFinset
  use S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h_coe : ↑S = Set.range (normDilationParam p G hG_p P hP_fix) := Set.Finite.coe_toFinset _
    rw [← Set.ncard_coe_finset, h_coe]
    exact normDilationParam_image_card p G m hm hG hG_p P hP_fix
  · rw [Set.Finite.mem_toFinset, Set.mem_range]
    use 1
    exact normDilationParam_of_P p G hG_p P hP_fix 1 (Subgroup.one_mem (P : Subgroup G))
  · intro a ha b hb
    rw [Set.Finite.mem_toFinset, Set.mem_range] at ha hb ⊢
    obtain ⟨g_a, h_ga⟩ := ha
    obtain ⟨g_b, h_gb⟩ := hb
    use g_a * g_b
    rw [normDilationParam_mul p G hG_p P hP_fix g_a g_b, h_ga, h_gb]
  · intro a ha
    rw [Set.Finite.mem_toFinset, Set.mem_range] at ha ⊢
    obtain ⟨g_a, h_ga⟩ := ha
    use g_a⁻¹
    have h_mul := normDilationParam_mul p G hG_p P hP_fix g_a⁻¹ g_a
    rw [inv_mul_cancel, normDilationParam_of_P p G hG_p P hP_fix 1 (Subgroup.one_mem (P : Subgroup G))] at h_mul
    have h_a_mul : normDilationParam p G hG_p P hP_fix g_a⁻¹ * a = 1 := by
      rw [← h_ga, ← h_mul]
    rw [eq_comm, inv_eq_of_mul_eq_one_left]
    exact h_a_mul
  · intro a ha
    rw [Set.Finite.mem_toFinset, Set.mem_range] at ha
    obtain ⟨g_a, h_ga⟩ := ha
    rw [← h_ga]
    exact dilationParam_ne_zero p _ (normalizer_element_fixes_infinity p G hG_p P hP_fix g_a.val g_a.prop)
  · intro c hc
    rw [Set.Finite.mem_toFinset, Set.mem_range] at hc
    obtain ⟨g_c, h_gc⟩ := hc
    use g_c.val, g_c.prop
    intro x hx
    rw [← h_gc]
    exact dilationParam_scales_translationSet p G hG_p P hP_fix g_c.val g_c.prop x hx



theorem translationSet_card_eq_P
    (G : Subgroup (PGL p)) [Finite G]
    (_hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    Set.ncard (translationSet p (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) =
      Nat.card (P : Subgroup G) := by
  set H := Subgroup.map (Subgroup.subtype G) (P : Subgroup G)
  have h_iso : (P : Subgroup G) ≃* H := Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype (Subgroup.subtype_injective G)
  have h_card_eq : Nat.card H = Nat.card (P : Subgroup G) := Nat.card_congr h_iso.symm.toEquiv
  by_cases h_card : Nat.card (P : Subgroup G) = 1
  · haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp (h_card_eq.trans h_card)).1
    have h_eq_zero : translationSet p H = {0} := Set.ext fun b ↦
      ⟨fun hb ↦ translationPGL_injective p ((congrArg Subtype.val (Subsingleton.elim (⟨translationPGL p b, hb⟩ : H) 1)).trans (translationPGL_zero p).symm),
      fun h ↦ h.symm ▸ translationSet_zero p H⟩
    rw [h_eq_zero, Set.ncard_singleton 0, h_card]
  · haveI : Finite H := Finite.of_equiv (P : Subgroup G) h_iso.toEquiv
    have h_nontrivial : Nontrivial H := by
      contrapose! h_card
      exact h_card_eq.symm.trans (Nat.card_eq_one_iff_unique.mpr ⟨h_card, ⟨1, H.one_mem⟩⟩)
    exact (p_subgroup_fixing_infinity_translations p H (P.2.map (Subgroup.subtype G)) h_nontrivial hP_fix).2.trans h_card_eq

theorem orbitInfty_ncard
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    Set.ncard (orbitInfty p G) = Fintype.card (Sylow p G) := by
  have h_stab_eq : MulAction.stabilizer G (infinity p) = (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
    Subgroup.ext fun g ↦ ⟨fixes_infinity_normalizes_sylow p G hG_p P hP_fix g, normalizer_element_fixes_infinity p G hG_p P hP_fix g⟩
  have h_orbit_eq : orbitInfty p G = MulAction.orbit G (infinity p) :=
    Set.ext fun x ↦ ⟨fun ⟨g, hg, h⟩ ↦ ⟨⟨g, hg⟩, h⟩, fun ⟨g, h⟩ ↦ ⟨g.val, g.prop, h⟩⟩
  rw [h_orbit_eq, ← Nat.card_coe_set_eq, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G (infinity p))]
  rw [h_stab_eq, ← Nat.card_eq_fintype_card, Nat.card_congr (Sylow.equivQuotientNormalizer P)]
  rfl

theorem orbit_eq_infty_union_translations
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p)
    (α₀ : K p) (hα₀ : P1point p α₀ ∈ orbitInfty p G) :
    orbitInfty p G =
      {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p
        (Subgroup.map (Subgroup.subtype G) (P : Subgroup G))) := by
  set H := Subgroup.map (Subgroup.subtype G) (P : Subgroup G)
  have h_P1_inj : Function.Injective (P1point p) := fun a1 a2 h ↦ by
    rw [P1point, P1point] at h
    simp only [Projectivization.mk_eq_mk_iff, Units.smul_def] at h
    obtain ⟨x, hx⟩ := h
    have h1 := congr_fun hx 0
    have h2 := congr_fun hx 1
    change (x : K p) * a2 = a1 at h1
    change (x : K p) * 1 = 1 at h2
    rw [mul_one] at h2
    rw [h2, one_mul] at h1
    exact h1.symm
  have h_add_inj : Function.Injective (fun b ↦ α₀ + b) := fun _ _ h ↦ add_left_cancel h
  have h_disj : Disjoint {infinity p} (P1point p '' ((fun b ↦ α₀ + b) '' translationSet p H)) := by
    simp only [Set.disjoint_singleton_left, Set.mem_image, not_exists, not_and]
    rintro b _ h_eq
    simp only [P1point, infinity, Projectivization.mk_eq_mk_iff, Units.smul_def] at h_eq
    obtain ⟨x, hx⟩ := h_eq
    have h2 := congr_fun hx 1
    change (x : K p) * 0 = 1 at h2
    rw [mul_zero] at h2
    exact zero_ne_one h2
  have h_fin_H : (translationSet p H).Finite := Set.finite_of_ncard_pos <| by
    rw [translationSet_card_eq_P p G hG_p P hP_fix]
    exact Nat.card_pos
  have h_fin_A : (orbitInfty p G).Finite := by
    apply Set.finite_of_ncard_pos
    rw [orbitInfty_ncard p G hG_p P hP_fix]
    have h_pos : 0 < p ^ m + 1 := by positivity
    exact (n_p_eq_pgl p G m hm hG (n_p_gt_one_of_pgl_order p G m hm hG)).symm ▸ h_pos
  have h_card_A : Set.ncard (orbitInfty p G) = p ^ m + 1 := by
    rw [orbitInfty_ncard p G hG_p P hP_fix]
    exact n_p_eq_pgl p G m hm hG (n_p_gt_one_of_pgl_order p G m hm hG)
  have h_card_B : Set.ncard ({infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p H)) = p ^ m + 1 := by
    rw [Set.ncard_union_eq h_disj (Set.finite_singleton _) (Set.Finite.image _ <| Set.Finite.image _ h_fin_H)]
    rw [Set.ncard_singleton, Set.ncard_image_of_injective _ h_P1_inj, Set.ncard_image_of_injective _ h_add_inj, translationSet_card_eq_P p G hG_p P hP_fix]
    have := sylow_order_of_pgl_order p G m hm hG P
    omega
  have h_sub : {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p H) ⊆ orbitInfty p G := by
    apply orbit_superset_of_translations
    · intro b hb
      obtain ⟨g, _, hg_eq⟩ := Subgroup.mem_map.mp hb
      exact hg_eq ▸ g.prop
    · exact hα₀
  have h_card_eq : Set.ncard (orbitInfty p G) = Set.ncard ({infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' translationSet p H)) :=
    h_card_A.trans h_card_B.symm
  exact Eq.symm <| Set.eq_of_subset_of_ncard_le h_sub h_card_eq.le h_fin_A

omit h_odd in
theorem orbit_translate_conj (G' : Subgroup (PGL p))
    (α₀ : K p)
    (V : Set (K p))
    (hOrb : orbitInfty p G' =
      {infinity p} ∪ P1point p '' ((fun b ↦ α₀ + b) '' V)) :
    orbitInfty p (G'.map (MulEquiv.toMonoidHom (MulAut.conj (translationPGL p (-α₀))))) =
      {infinity p} ∪ P1point p '' V := by
  rw [orbitInfty_conj_of_fixes_infty p G' (translationPGL p (-α₀)) (translation_smul_infinity p (-α₀))]
  rw [hOrb, Set.image_union, Set.image_singleton, translation_smul_infinity p (-α₀)]
  congr 1
  rw [Set.image_image, Set.image_image]
  refine Set.image_congr (fun v _ ↦ ?_)
  exact (translation_smul_P1point p (-α₀) (α₀ + v)).trans <| congrArg (P1point p) <|
    (congrArg (· + -α₀) (add_comm α₀ v)).trans <|
    (add_assoc v α₀ (-α₀)).trans <|
    (congrArg (v + ·) (add_neg_cancel α₀)).trans (add_zero v)

omit h_odd in
theorem orbit_dilation_conj (G' : Subgroup (PGL p))
    (c : K p) (hc : c ≠ 0)
    (V : Set (K p))
    (hOrb : orbitInfty p G' = {infinity p} ∪ P1point p '' V) :
    orbitInfty p (G'.map (MulEquiv.toMonoidHom (MulAut.conj (dilationPGL p c hc)))) =
      {infinity p} ∪ P1point p '' ((fun x ↦ c * x) '' V) := by
  rw [orbitInfty_conj_of_fixes_infty p G' (dilationPGL p c hc) (dilation_smul_infinity p c hc)]
  rw [hOrb, Set.image_union, Set.image_singleton, dilation_smul_infinity p c hc]
  rw [Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr (fun v _ ↦ dilation_smul_P1point p c hc v)


theorem orbit_infty_eq_P1Fq_core
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hP_fix : ∀ g ∈ (P : Subgroup G).map (Subgroup.subtype G),
      g • infinity p = infinity p) :
    ∃ g : PGL p,
      g • infinity p = infinity p ∧
      orbitInfty p (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = P1Fq p m := by
  set H := Subgroup.map (Subgroup.subtype G) (P : Subgroup G)
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : K p, P1point p α₀ ∈ orbitInfty p G := by
    by_contra h
    have h_eq : orbitInfty p G = {infinity p} := Set.eq_singleton_iff_unique_mem.mpr
      ⟨infty_mem_orbitInfty p G, fun x hx ↦ match projLine_cases p x with
        | Or.inl e => e
        | Or.inr ⟨c, e⟩ => absurd ⟨c, e.symm ▸ hx⟩ h⟩
    have h_card_one : Set.ncard (orbitInfty p G) = 1 := h_eq.symm ▸ Set.ncard_singleton _
    have h_np_eq_one : Fintype.card (Sylow p G) = 1 := (orbitInfty_ncard p G hG_p P hP_fix).symm.trans h_card_one
    exact lt_irrefl 1 <| h_np_eq_one ▸ n_p_gt_one_of_pgl_order p G m hm hG

  have h_stable_translation : ∀ c : K p, c ^ (p ^ m - 1) = 1 → c ≠ 0 → ∀ x, x ∈ translationSet p H → c * x ∈ translationSet p H :=
    fun c hc hc_ne ↦ by
      obtain ⟨S, hS_card, hS_subgroup, hS_mul, hS_inv, hS_ne_zero, hS_dilation⟩ := dilation_params_cover p G m hm hG P hP_fix
      exact (hS_dilation c (finite_subgroup_eq_roots_of_unity p S (p ^ m - 1)
        (Nat.le_sub_one_of_lt (one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (by omega)))
        hS_card hS_subgroup hS_mul hS_inv hS_ne_zero c hc hc_ne)).choose_spec.2

  obtain ⟨V, rfl, hV_card, hV_add, hV_zero, hV_neg, hV_stable⟩ : ∃ V : Set (K p), V = translationSet p H ∧ Set.ncard V = p ^ m ∧ (∀ x y, x ∈ V → y ∈ V → x + y ∈ V) ∧ (0 : K p) ∈ V ∧ (∀ x, x ∈ V → -x ∈ V) ∧ (∀ c : K p, c ^ (p ^ m - 1) = 1 → c ≠ 0 → ∀ x, x ∈ V → c * x ∈ V) :=
    ⟨translationSet p H, rfl, (translationSet_card_eq_P p G hG_p P hP_fix).trans (sylow_order_of_pgl_order p G m hm hG P), translationSet_add p H, translationSet_zero p H, translationSet_neg p H, h_stable_translation⟩

  obtain ⟨v₀, hv₀_mem, hv₀_ne⟩ : ∃ v₀ : K p, v₀ ∈ translationSet p H ∧ v₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hV_eq : translationSet p H = {0} := Set.eq_singleton_iff_unique_mem.mpr ⟨hV_zero, h⟩
    have h_card_one : Set.ncard (translationSet p H) = 1 := hV_eq.symm ▸ Set.ncard_singleton _
    have h_pow_eq_one : p ^ m = 1 := hV_card.symm.trans h_card_one
    have hp_gt_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
    exact lt_irrefl 1 <| h_pow_eq_one ▸ hp_gt_one.trans_le ((pow_one p).symm.trans_le (Nat.pow_le_pow_right hp_gt_one.le hm))

  use dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne) * translationPGL p (-α₀)
  refine ⟨?_, ?_⟩
  · exact (mul_smul (dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne)) (translationPGL p (-α₀)) (infinity p)).trans <|
      (congrArg (fun x ↦ dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne) • x) (translation_smul_infinity p (-α₀))).trans <|
      dilation_smul_infinity p v₀⁻¹ (inv_ne_zero hv₀_ne)
  · have h_map_eq : G.map (MulEquiv.toMonoidHom (MulAut.conj (dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne) * translationPGL p (-α₀)))) =
      (G.map (MulEquiv.toMonoidHom (MulAut.conj (translationPGL p (-α₀))))).map (MulEquiv.toMonoidHom (MulAut.conj (dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne)))) := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      let B := dilationPGL p v₀⁻¹ (inv_ne_zero hv₀_ne)
      let A := translationPGL p (-α₀)
      exact congrArg (fun y ↦ y * (B * A)⁻¹) (mul_assoc B A x) |>.trans <|
        congrArg (fun y ↦ (B * (A * x)) * y) (mul_inv_rev B A) |>.trans <|
        (mul_assoc (B * (A * x)) A⁻¹ B⁻¹).symm |>.trans <|
        congrArg (fun y ↦ y * B⁻¹) (mul_assoc B (A * x) A⁻¹)
    have h_orbit := orbit_translate_conj p G α₀ (translationSet p H) (orbit_eq_infty_union_translations p G m hm hG hG_p P hP_fix α₀ hα₀)
    have h_orbit_dilation := orbit_dilation_conj p _ v₀⁻¹ (inv_ne_zero hv₀_ne) (translationSet p H) h_orbit
    have h_orbit_dilation_eq := translationSet_scaled_eq_Fq p m hm (translationSet p H) hV_card hV_add hV_zero hV_neg hV_stable v₀ hv₀_mem hv₀_ne
    rw [h_map_eq, h_orbit_dilation, h_orbit_dilation_eq]
    rfl

/-- The multiplicative isomorphism between `G` and its image `k₀ G k₀⁻¹` under conjugation by `k₀`. -/
def conjEquiv (G : Subgroup (PGL p)) (k₀ : PGL p) :
    G ≃* (G.map (MulEquiv.toMonoidHom (MulAut.conj k₀))) :=
  G.equivMapOfInjective _ (MulEquiv.injective _)


/-- The image of the Sylow `p`-subgroup `P` under conjugation by `k₀`, as a Sylow `p`-subgroup of the conjugate group `k₀ G k₀⁻¹`. -/
@[nolint unusedArguments]
def sylowMap (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G) (k₀ : PGL p) :
    Sylow p (G.map (MulEquiv.toMonoidHom (MulAut.conj k₀))) :=
  let e := conjEquiv p G k₀
  ⟨(P : Subgroup G).map e.toMonoidHom, P.isPGroup'.map e.toMonoidHom, fun {Q} hQ hle ↦ by
    have h_comap : Subgroup.comap e.toMonoidHom Q = P.1 :=
      P.is_maximal' (hQ.comap_of_injective e.toMonoidHom e.injective)
        (fun _ hx ↦ Subgroup.mem_comap.mpr (hle (Subgroup.mem_map_of_mem _ hx)))
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Q, h_comap]⟩


theorem exists_conj_sylow_fixing_infty
    (G : Subgroup (PGL p)) [Finite G]
    (_hG_p : p ∣ Nat.card G) :
    ∃ (k₀ : PGL p) (P₁ : Sylow p (G.map (MulEquiv.toMonoidHom (MulAut.conj k₀)))),
      ∀ g ∈ (P₁ : Subgroup (G.map (MulEquiv.toMonoidHom (MulAut.conj k₀)))).map
        (Subgroup.subtype _), g • infinity p = infinity p := by
  let P := Classical.arbitrary (Sylow p G)
  have hP_le : (P : Subgroup G).map (Subgroup.subtype G) ≤ G := Subgroup.map_subtype_le P.1
  haveI : Finite ↥((P : Subgroup G).map (Subgroup.subtype G)) :=
    Finite.of_injective (Subgroup.inclusion hP_le) (Subgroup.inclusion_injective hP_le)
  obtain ⟨α, hα⟩ := isPGroup_exists_common_fixedPoint p ((P : Subgroup G).map (Subgroup.subtype G))
    ‹_› (P.isPGroup'.map _)
  obtain ⟨k₀, hk₀⟩ := exists_smul_eq_infinity p α
  refine ⟨k₀, sylowMap p G P k₀, fun g hg ↦ ?_⟩
  obtain ⟨⟨g', hg'_mem⟩, hg'_in_sylow, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨x, hx_in_P, hx_eq⟩ := Subgroup.mem_map.mp hg'_in_sylow
  have hg'_val : g' = k₀ * ↑x * k₀⁻¹ := (congrArg Subtype.val hx_eq).symm
  calc g' • infinity p
    _ = (k₀ * ↑x * k₀⁻¹) • infinity p := congrArg (fun y ↦ y • infinity p) hg'_val
    _ = k₀ • ↑x • k₀⁻¹ • infinity p := (mul_smul (k₀ * ↑x) k₀⁻¹ (infinity p)).trans (mul_smul k₀ (↑x) (k₀⁻¹ • infinity p))
    _ = k₀ • ↑x • α := congrArg (fun y ↦ k₀ • ↑x • y) (hk₀ ▸ inv_smul_smul k₀ α)
    _ = k₀ • α := congrArg (fun y ↦ k₀ • y) (hα ↑x (Subgroup.mem_map_of_mem _ hx_in_P))
    _ = infinity p := hk₀

theorem orbit_infty_eq_P1Fq
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1)) :
    ∃ g : PGL p,
      orbitInfty p (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = P1Fq p m := by
  have hG_p : p ∣ Nat.card G :=
    hG.symm ▸ dvd_mul_of_dvd_left (dvd_pow_self p (ne_of_gt hm)) _

  obtain ⟨k₀, P₁, hP₁⟩ := exists_conj_sylow_fixing_infty p G hG_p
  let G₁ := G.map (MulEquiv.toMonoidHom (MulAut.conj k₀))
  haveI h_finite_G1 : Finite G₁ := Finite.of_equiv G (conjEquiv p G k₀).toEquiv

  have h_card : Nat.card G₁ = Nat.card G := (Nat.card_congr (conjEquiv p G k₀).toEquiv).symm
  have hG₁ : Nat.card G₁ = p ^ m * (p ^ (2 * m) - 1) := h_card.trans hG
  have hG_p₁ : p ∣ Nat.card G₁ := h_card.symm ▸ hG_p

  obtain ⟨g, _, hg_eq⟩ := orbit_infty_eq_P1Fq_core p G₁ m hm hG₁ hG_p₁ P₁ hP₁

  have h_map_eq : G₁.map (MulEquiv.toMonoidHom (MulAut.conj g)) = G.map (MulEquiv.toMonoidHom (MulAut.conj (g * k₀))) := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    exact (congrArg (fun y ↦ y * (g * k₀)⁻¹) (mul_assoc g k₀ x) |>.trans <|
      congrArg (fun y ↦ (g * (k₀ * x)) * y) (mul_inv_rev g k₀) |>.trans <|
      (mul_assoc (g * (k₀ * x)) k₀⁻¹ g⁻¹).symm |>.trans <|
      congrArg (fun y ↦ y * g⁻¹) (mul_assoc g (k₀ * x) k₀⁻¹)).symm

  exact ⟨g * k₀, h_map_eq ▸ hg_eq⟩



theorem pgl_conjugate_to_standard
    (G : Subgroup (PGL p)) [Finite G]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1)) :
    ∃ g : PGL p, G.map (MulEquiv.toMonoidHom (MulAut.conj g)) =
      (pglMap (galoisFieldRingHom (p := p) m)).range := by
  obtain ⟨g, hg⟩ := orbit_infty_eq_P1Fq p G m hm hG
  use g
  have h_le : G.map (MulEquiv.toMonoidHom (MulAut.conj g)) ≤ (pglMap (galoisFieldRingHom (p := p) m)).range :=
    fun h hh ↦ preserves_P1Fq_in_range p m hm h (fun x hx ↦ hg ▸ preserves_orbitInfty p _ h hh x (hg ▸ hx))
  have h_card_Gmap : Nat.card (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = Nat.card G :=
    (Nat.card_congr (conjEquiv p G g).toEquiv).symm
  have h_card_range : Nat.card ((pglMap (galoisFieldRingHom (p := p) m)).range) = Nat.card G :=
    (Nat.card_congr (Equiv.ofInjective _ (pglMap_injective (galoisFieldRingHom (p := p) m) (RingHom.injective _)))).symm.trans (by rw [card_PGL2, Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm)), ← pow_mul', ← hG])
  have h_card_eq : Nat.card (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) = Nat.card ((pglMap (galoisFieldRingHom (p := p) m)).range) :=
    h_card_Gmap.trans h_card_range.symm
  by_contra h_neq
  have h_ssubset : (G.map (MulEquiv.toMonoidHom (MulAut.conj g)) : Set (PGL p)) ⊂ ((pglMap (galoisFieldRingHom (p := p) m)).range : Set (PGL p)) :=
    Set.ssubset_iff_subset_ne.mpr ⟨h_le, fun h_set_eq ↦ h_neq (Subgroup.ext (Set.ext_iff.mp h_set_eq))⟩
  have h_lt : Nat.card (G.map (MulEquiv.toMonoidHom (MulAut.conj g))) < Nat.card ((pglMap (galoisFieldRingHom (p := p) m)).range) :=
    Set.ncard_lt_ncard h_ssubset (Set.finite_range _)
  exact (ne_of_lt h_lt) h_card_eq

theorem pgl_subgroups_conjugate
    (G H : Subgroup (PGL p))
    [Finite G] [Finite H]
    (m : ℕ) (hm : m ≥ 1)
    (hG : Nat.card G = p ^ m * (p ^ (2 * m) - 1))
    (hH : Nat.card H = p ^ m * (p ^ (2 * m) - 1)) :
    ∃ g : PGL p, G.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H := by
  obtain ⟨g₁, hg₁⟩ := pgl_conjugate_to_standard p G m hm hG
  obtain ⟨g₂, hg₂⟩ := pgl_conjugate_to_standard p H m hm hH
  use g₂⁻¹ * g₁
  have h_map_comp : MulEquiv.toMonoidHom (MulAut.conj (g₂⁻¹ * g₁)) =
      (MulEquiv.toMonoidHom (MulAut.conj g₂).symm).comp (MulEquiv.toMonoidHom (MulAut.conj g₁)) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply]
    group
  have h_symm_comp : (MulEquiv.toMonoidHom (MulAut.conj g₂).symm).comp (MulEquiv.toMonoidHom (MulAut.conj g₂)) = MonoidHom.id _ :=
    MonoidHom.ext fun x ↦ (MulAut.conj g₂).symm_apply_apply x
  calc G.map (MulEquiv.toMonoidHom (MulAut.conj (g₂⁻¹ * g₁)))
    _ = (G.map (MulEquiv.toMonoidHom (MulAut.conj g₁))).map (MulEquiv.toMonoidHom (MulAut.conj g₂).symm) := by rw [h_map_comp, ← Subgroup.map_map]
    _ = ((pglMap (galoisFieldRingHom (p := p) m)).range).map (MulEquiv.toMonoidHom (MulAut.conj g₂).symm) := by rw [hg₁]
    _ = (H.map (MulEquiv.toMonoidHom (MulAut.conj g₂))).map (MulEquiv.toMonoidHom (MulAut.conj g₂).symm) := by rw [← hg₂]
    _ = H := by rw [Subgroup.map_map, h_symm_comp, Subgroup.map_id]

end

end Dickson
