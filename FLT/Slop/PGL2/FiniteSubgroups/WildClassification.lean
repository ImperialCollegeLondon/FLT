/-
Copyright (c) 2026 Duxing Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Duxing Yang
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic.NormNum.Prime
public import FLT.Slop.PGL2.FiniteSubgroups.PSLBasic
public import FLT.Slop.PGL2.FiniteSubgroups.PSLRecognition
public import FLT.Slop.PGL2.FiniteSubgroups.PartitionProof

/-!
# Dickson's classification: the wild case

This file classifies the finite subgroups `G` of `PGL p = PGL₂(𝔽̄_p)` of order
divisible by `p` (the *wild* case): the main theorem `Dickson.classification_wild_slop`
shows any such `G` is

* a semidirect product of an elementary abelian `p`-group by a cyclic group of order
  prime to `p` (the case where `G` fixes a point of `ℙ¹(𝔽̄_p)`), or
* isomorphic to `A₄`, `S₄` or `A₅`, or
* isomorphic to `PSL₂(𝔽_q)` or `PGL₂(𝔽_q)` for some power `q = p^m`.

The proof combines the partition equation from
`FLT.Slop.PGL2.FiniteSubgroups.PartitionProof` with the recognition theorems for `A₅`
(`FLT.Slop.PGL2.FiniteSubgroups.RecognitionA5`) and for `PSL₂(𝔽_q)`/`PGL₂(𝔽_q)`
(`FLT.Slop.PGL2.FiniteSubgroups.PSLRecognition` and the field reconstruction in
`FLT.Slop.PGL2.FiniteSubgroups.FieldReconstruction`).
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

noncomputable section DiagRatio

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]


/-- The group homomorphism from a finite subgroup `H` of `PGL p` fixing `infinity` to `(K p)ˣ`,
sending each element to its dilation parameter. -/
@[nolint unusedArguments]
noncomputable def dilationHomOfFix (H : Subgroup (PGL p)) [Finite H]
    (hH_fix : ∀ g : H, (g : PGL p) • infinity p = infinity p) :
    H →* (K p)ˣ where
  toFun g := Units.mk0 (dilationParam p ↑g (hH_fix g)) (dilationParam_ne_zero p ↑g (hH_fix g))
  map_one' := Units.ext (dilationParam_one p (hH_fix 1))
  map_mul' g₁ g₂ := Units.ext (dilationParam_mul_eq p ↑g₁ ↑g₂ (hH_fix g₁) (hH_fix g₂) (hH_fix (g₁ * g₂)))

omit h_odd in
theorem dilationHom_ker_order (H : Subgroup (PGL p)) [Finite H]
    (hH_fix : ∀ g : H, (g : PGL p) • infinity p = infinity p)
    (g : H) (hg : g ∈ (dilationHomOfFix p H hH_fix).ker) :
    orderOf g ∣ p := by
  obtain ⟨β, hβ⟩ := (dilationParam_eq_one_iff p (g : PGL p) (hH_fix g)).mp (congr_arg Units.val hg)
  have h_order_translation : ∀ n : ℕ, (translationPGL p β) ^ n = translationPGL p (n • β) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, zero_smul, ← translationPGL_zero p]
    | succ n ih =>
      rw [pow_succ, ih, translationPGL_mul]
      apply congr_arg
      rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
  rw [orderOf_dvd_iff_pow_eq_one, Subtype.ext_iff]
  change (g : PGL p) ^ p = 1
  rw [hβ, h_order_translation, show p • β = 0 by rw [nsmul_eq_mul, CharP.cast_eq_zero (K p) p, zero_mul], translationPGL_zero p]

omit h_odd in
theorem fixes_infinity_coprime_isCyclic (H : Subgroup (PGL p)) [Finite H]
    (hH_fix : ∀ g : H, (g : PGL p) • infinity p = infinity p)
    (hH_coprime : Nat.Coprime (Nat.card H) p) :
    IsCyclic H := by
  let f := dilationHomOfFix p H hH_fix
  have h_kernel_trivial : f.ker = ⊥ :=
    eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr <|
      let n : ℕ := @orderOf H H.toGroup.toMonoid g
      have h_order_card : n ∣ Nat.card H := by
        dsimp [n]
        exact @orderOf_dvd_natCard H H.toGroup g
      have h_order_p : n ∣ p := by
        dsimp [n]
        simpa using dilationHom_ker_order p H hH_fix g hg
      have h_gcd : Nat.gcd n p = 1 := (hH_coprime.coprime_dvd_left h_order_card).gcd_eq_one
      have h_dvd_one : n ∣ 1 := by
        rw [← h_gcd]
        exact Nat.dvd_gcd (dvd_refl n) h_order_p
      have h_order_one : @orderOf H H.toGroup.toMonoid g = 1 := by
        dsimp [n] at h_dvd_one
        exact Nat.dvd_one.mp h_dvd_one
      orderOf_eq_one_iff.mp h_order_one
  have h_inj : Function.Injective f := fun x y hxy ↦
    mul_inv_eq_one.mp <| Subgroup.mem_bot.mp <| h_kernel_trivial ▸
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
  let h_equiv : H ≃ f.range :=
    Equiv.ofBijective (fun x ↦ ⟨f x, ⟨x, rfl⟩⟩) ⟨
      fun _ _ hxy ↦ h_inj (congr_arg Subtype.val hxy),
      fun ⟨_, ⟨x, hx⟩⟩ ↦ ⟨x, Subtype.ext hx⟩
    ⟩
  have h_iso : H ≃* f.range := {
    h_equiv with
    map_mul' := fun x y ↦ Subtype.ext (map_mul f x y)
  }
  haveI h_finite : Finite f.range := h_iso.finite_iff.mp inferInstance
  exact (MulEquiv.isCyclic h_iso).mpr inferInstance

end DiagRatio

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]


/-- A single summand `1 / sᵢ * (1 - 1 / zᵢ)` appearing in the class-equation sum. -/
abbrev partitionTerm (si zi : ℕ) : ℚ := 1 / (si : ℚ) * (1 - 1 / (zi : ℚ))



theorem sylow_comm_exp_p (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) :
    (∀ g h : P.toSubgroup, g * h = h * g) ∧ (∀ g : P.toSubgroup, g ^ p = 1) := by
  let H := P.toSubgroup.map G.subtype
  haveI : Finite H := Finite.of_surjective
    (fun g : P.toSubgroup ↦ (⟨g.1.1, Subgroup.mem_map_of_mem G.subtype g.2⟩ : H))
    (fun ⟨y, hy⟩ ↦ by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩)
  have hH_pgroup : IsPGroup p H := P.2.map G.subtype
  by_cases hH_nontriv : Nontrivial H
  · have h_fixed := isPGroup_comm_exponent_fixedPoint p H hH_pgroup hH_nontriv
    have h_comm : ∀ g h : P.toSubgroup, g * h = h * g := by
      intro g h
      let g' : H := ⟨g.val.val, Subgroup.mem_map_of_mem G.subtype g.property⟩
      let h' : H := ⟨h.val.val, Subgroup.mem_map_of_mem G.subtype h.property⟩
      have heq : g' * h' = h' * g' := h_fixed.1 g' h'
      have pf := congrArg Subtype.val heq
      apply Subtype.ext; apply Subtype.ext
      exact pf
    have h_exp : ∀ g : P.toSubgroup, g ^ p = 1 := by
      intro g
      let g' : H := ⟨g.val.val, Subgroup.mem_map_of_mem G.subtype g.property⟩
      have h_pow : g' ^ p = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        exact (Monoid.order_dvd_exponent g').trans h_fixed.2.1
      have pf := congrArg Subtype.val h_pow
      apply Subtype.ext; apply Subtype.ext
      exact pf
    exact ⟨h_comm, h_exp⟩
  · have h_sub : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH_nontriv
    have h_one : ∀ g : P.toSubgroup, g = 1 := by
      intro g
      let g' : H := ⟨g.val.val, Subgroup.mem_map_of_mem G.subtype g.property⟩
      have heq : g' = 1 := match h_sub with | ⟨h_allEq⟩ => h_allEq g' 1
      have pf := congrArg Subtype.val heq
      apply Subtype.ext; apply Subtype.ext
      exact pf
    exact ⟨fun g h ↦ by rw [h_one g, h_one h], fun g ↦ by rw [h_one g, one_pow]⟩

theorem group_fixes_sylow_point (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) (hP_normal : (P : Subgroup G).Normal)
    (g : G) : (g : PGL p) • sylowFixedPoint p G hG_p P = sylowFixedPoint p G hG_p P := by
  let H := (P : Subgroup G).map (Subgroup.subtype G)
  let x := sylowFixedPoint p G hG_p P
  have hx_spec := (sylow_unique_fixedPoint p G hG_p P).choose_spec
  have h_conj_fixedPoint : ∀ h ∈ H, h • ((g : PGL p) • x) = (g : PGL p) • x := by
    intro h hh
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
    have hk : (g : PGL p)⁻¹ * (h' : PGL p) * (g : PGL p) ∈ H :=
      Subgroup.mem_map_of_mem (Subgroup.subtype G) (inv_inv g ▸ hP_normal.conj_mem h' hh' g⁻¹)
    have h_mul : (h' : PGL p) * (g : PGL p) = (g : PGL p) * ((g : PGL p)⁻¹ * (h' : PGL p) * (g : PGL p)) := by
      rw [mul_assoc (g : PGL p)⁻¹, mul_inv_cancel_left]
    change (h' : PGL p) • ((g : PGL p) • x) = (g : PGL p) • x
    rw [← mul_smul, h_mul, mul_smul]
    exact congrArg _ (hx_spec.1 _ hk)
  exact hx_spec.2 ((g : PGL p) • x) h_conj_fixedPoint

omit h_odd in
theorem fixes_point_coprime_isCyclic (H : Subgroup (PGL p)) [Finite H]
    (x : ProjectiveLine p)
    (hH_fix : ∀ g : H, (g : PGL p) • x = x)
    (hH_coprime : Nat.Coprime (Nat.card H) p) :
    IsCyclic H := by
  obtain ⟨c, hc⟩ : ∃ c : PGL p, c • x = infinity p := exists_smul_eq_infinity p x
  let e := MulEquiv.subgroupMap (MulAut.conj c) H
  let H' := H.map (MulAut.conj c).toMonoidHom
  haveI : Finite H' := Finite.of_equiv H e.toEquiv
  have hH'_fix : ∀ g : H', (g : PGL p) • infinity p = infinity p := by
    intro ⟨g, hg⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
    have heq : (c * h * c⁻¹ : PGL p) • c • x = c • x := by
      rw [← mul_smul, inv_mul_cancel_right, mul_smul, hH_fix ⟨h, hh⟩]
    exact hc ▸ heq
  have h_card : Nat.card H = Nat.card H' := Nat.card_congr e.toEquiv
  exact (MulEquiv.isCyclic e).mpr <|
    fixes_infinity_coprime_isCyclic p H' hH'_fix (h_card ▸ hH_coprime)

omit h_odd in
theorem complement_order_coprime (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G)
    (K : Subgroup G) (hK : P.toSubgroup.IsComplement' K) :
    Nat.Coprime (Nat.card K) p := by
  have h_card_G : Nat.card G = p ^ (Nat.factorization (Nat.card G) p) * Nat.card K := by
    have h1 : Nat.card G = Nat.card P * Nat.card K := hK.card_mul.symm
    rw [P.card_eq_multiplicity] at h1
    exact h1
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr fun h ↦
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' (Fact.out : Nat.Prime p) <|
      h_card_G.symm ▸ mul_dvd_mul_left _ h

theorem complement_isCyclic (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) (hP_normal : (P : Subgroup G).Normal)
    (K : Subgroup G) (hK : P.toSubgroup.IsComplement' K) :
    IsCyclic K := by
  let K' := K.map G.subtype
  let e : K ≃* K' := Subgroup.equivMapOfInjective K G.subtype Subtype.coe_injective
  haveI : Finite K' := Finite.of_equiv K e.toEquiv
  let x := sylowFixedPoint p G hG_p P
  have hK'_fix : ∀ g : K', (g : PGL p) • x = x := fun ⟨_, hg⟩ ↦ by
    obtain ⟨k, _, rfl⟩ := Subgroup.mem_map.mp hg
    exact group_fixes_sylow_point p G hG_p P hP_normal k
  exact (MulEquiv.isCyclic e).mpr <|
    fixes_point_coprime_isCyclic p K' x hK'_fix <|
      Nat.card_congr e.toEquiv ▸ complement_order_coprime p G P K hK

omit h_odd in
theorem mul_elem_abelian_iso (G : Type*) [CommGroup G]
    [Finite G] (hexp : ∀ x : G, x ^ p = 1) :
    ∃ m : ℕ, Nonempty (G ≃* Multiplicative (Fin m → ZMod p)) := by
  haveI : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (fun x ↦ hexp (Additive.toMul x))
  exact ⟨Module.finrank (ZMod p) (Additive G),
    ⟨(Module.finBasis (ZMod p) (Additive G)).equivFun.toAddEquiv.toMultiplicative⟩⟩

theorem semidirect_of_complement_iso
    {G : Type*} [Group G]
    {N K : Subgroup G} [N.Normal] (hc : N.IsComplement' K)
    {A B : Type*} [Group A] [Group B]
    (fN : ↥N ≃* A) (fK : ↥K ≃* B) :
    ∃ (φ : B →* MulAut A), Nonempty (G ≃* A ⋊[φ] B) :=
  ⟨_, ⟨(SemidirectProduct.mulEquivSubgroup hc).symm.trans (SemidirectProduct.congr' fN fK)⟩⟩


theorem branch1_semidirect (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) (hP_normal : (P : Subgroup G).Normal)
    (hG_p : p ∣ Nat.card G) :
    ∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t)) := by
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (Sylow.card_coprime_index P)
  have ⟨hP_comm, hP_exp⟩ := sylow_comm_exp_p p G P
  letI : CommGroup P.toSubgroup := { (inferInstance : Group P.toSubgroup) with mul_comm := hP_comm }
  obtain ⟨m, ⟨fP⟩⟩ := mul_elem_abelian_iso p P.toSubgroup hP_exp
  haveI hK_cyclic := complement_isCyclic p G hG_p P hP_normal K hK
  have hK_coprime := complement_order_coprime p G P K hK
  have ⟨fK⟩ : Nonempty (K ≃* Multiplicative (ZMod (Nat.card K))) := ⟨(zmodCyclicMulEquiv ‹IsCyclic K›).symm⟩
  obtain ⟨φ, hφ⟩ := semidirect_of_complement_iso hK fP fK
  have hP_card : Nat.card P.toSubgroup = p ^ m := by
    rw [Nat.card_congr fP.toEquiv]
    change Nat.card (Fin m → ZMod p) = _
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hm_ge : m ≥ 1 :=
    (Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le <| P.card_eq_multiplicity.symm.trans hP_card) ▸
      (Fact.out : Nat.Prime p).factorization_pos_of_dvd Nat.card_pos.ne' hG_p
  have ht_div : Nat.card K ∣ p ^ m - 1 := by
    have hdvd := normalizer_complement_divides_main p G P hG_p
    have h_card_norm : Nat.card (Subgroup.normalizer (SetLike.coe P.toSubgroup)) = Nat.card G := by
      haveI := hP_normal
      rw [Subgroup.normalizer_eq_top]
      exact Nat.card_congr ⟨fun x ↦ x.1, fun x ↦ ⟨x, trivial⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    have h_card_G : Nat.card G = p ^ m * Nat.card K := by
      rw [(Subgroup.card_mul_index K).symm, hK.index_eq_card, hP_card, mul_comm]
    rw [h_card_norm, hP_card, h_card_G, Nat.mul_div_cancel_left _ (hP_card ▸ Nat.card_pos)] at hdvd
    exact hdvd
  exact ⟨m, Nat.card K, hm_ge, hK_coprime, ht_div, φ, hφ⟩

theorem branch2a_constraints
    (pm : ℕ) (n : ℕ) (r : ℕ)
    (z : Fin r → ℕ) (s : Fin r → ℕ)
    (hpm : pm ≥ 3) (hn_pos : n > 0) (hn_gt_pm : n > pm)
    (hs_bound : ∀ i, s i = 1 ∨ s i = 2)
    (hz_pos : ∀ i, z i ≥ 2)
    (h_eq : (1 : ℚ) / pm - 1 / n =
        ∑ i : Fin r, partitionTerm (s i) (z i)) :
    pm = 3 ∧ r = 1 ∧ n = 12 := by
  have hpm_inv : 1 / (pm : ℚ) ≤ 1 / 3 := by rw [one_div, one_div]; exact inv_anti₀ zero_lt_three (Nat.cast_le.mpr hpm)
  have hn_inv_pos : 1 / (n : ℚ) > 0 := one_div_pos.mpr (Nat.cast_pos.mpr hn_pos)
  have h_term_ge : ∀ i, (1 / 4 : ℚ) ≤ partitionTerm (s i) (z i) := fun i ↦ by
    have hz_inv : 1 / (z i : ℚ) ≤ 1 / 2 := by rw [one_div, one_div]; exact inv_anti₀ zero_lt_two (Nat.cast_le.mpr (hz_pos i))
    rcases hs_bound i with h | h <;> (rw [h, partitionTerm]; linarith only [hz_inv])
  have h_lhs_lt : (1 : ℚ) / pm - 1 / n < 1 / 2 := by linarith only [hpm_inv, hn_inv_pos]

  have hr_pos : r > 0 := by
    by_contra! h; obtain rfl : r = 0 := by omega
    rw [Fintype.sum_empty] at h_eq
    have : pm = n := Nat.cast_inj.mp <| inv_inj.mp (by rw [← one_div, ← one_div]; linarith only [h_eq] : (pm : ℚ)⁻¹ = (n : ℚ)⁻¹)
    omega
  have hr_eq_one : r = 1 := by
    by_contra! h_ne; have h_ge : r ≥ 2 := by omega
    have h_lt: (r : ℚ) / 4 < 1 / 2 :=
      calc (r : ℚ) / 4 = ∑ i : Fin r, (1 / 4 : ℚ) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ ∑ i, partitionTerm (s i) (z i) := Finset.sum_le_sum fun i _ ↦ h_term_ge i
        _ = (1 : ℚ) / pm - 1 / n := h_eq.symm
        _ < 1 / 2 := h_lhs_lt
    have h_geq : (r : ℚ) ≥ 2 := Nat.cast_le.mpr h_ge
    linarith only [h_lt, h_geq]
  subst hr_eq_one; rw [Fin.sum_univ_one] at h_eq
  rcases hs_bound 0 with h | h
  · rw [h, partitionTerm] at h_eq
    have h_leq : 1 / (z 0 : ℚ) ≤ 1 / 2 := by rw [one_div, one_div]; exact inv_anti₀ zero_lt_two (Nat.cast_le.mpr (hz_pos 0))
    linarith only [h_lhs_lt, h_eq, h_leq]
  · rw [h, partitionTerm] at h_eq
    have hz_eq : z 0 = 2 := by
      by_contra! h_ne; have h_ge : z 0 ≥ 3 := by have : z 0 ≥ 2 := hz_pos 0; omega
      have h_leq : 1 / (z 0 : ℚ) ≤ 1 / 3 := by rw [one_div, one_div]; exact inv_anti₀ zero_lt_three (Nat.cast_le.mpr h_ge)
      linarith only [hpm_inv, hn_inv_pos, h_eq, h_leq]
    rw [hz_eq, (by norm_num : 1 / ((2 : ℕ) : ℚ) * (1 - 1 / ((2 : ℕ) : ℚ)) = 1 / 4)] at h_eq
    have hpm_eq : pm = 3 := by
      by_contra! h_ne; have h_ge : pm ≥ 4 := by omega
      have h_leq: 1 / (pm : ℚ) ≤ 1 / 4 := by rw [one_div, one_div]; exact inv_anti₀ zero_lt_four (Nat.cast_le.mpr h_ge)
      linarith only [h_eq, h_leq, hn_inv_pos]
    rw [hpm_eq] at h_eq
    have hn_inv_eq : (n : ℚ)⁻¹ = (12 : ℚ)⁻¹ := by rw [← one_div, ← one_div]; linarith only [h_eq]
    exact ⟨hpm_eq, rfl, Nat.cast_inj.mp <| inv_inj.mp hn_inv_eq⟩

omit h_odd in
theorem recognition_A4 (G : Subgroup (PGL p))
    [hfin : Finite G] (hp3 : p = 3) (hn : Nat.card G = 12)
    (hn3 : Fintype.card (Sylow p G) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  have h_subgroup_eq : ∀ {H K : Subgroup G}, H ≤ K → Nat.card H = Nat.card K → H = K := fun hHK hcard ↦ SetLike.ext' (Set.eq_of_subset_of_ncard_le hHK hcard.ge)
  have h_card_val : ∀ P' : Sylow p G, Nat.card (P' : Subgroup G) = 3 := fun P' ↦
    (Sylow.card_eq_multiplicity P').trans (by rw [hn, hp3, Nat.factorization_eq_one (m := 4) rfl Nat.prime_three (by norm_num), pow_one])
  have h_norm : ∀ P : Sylow p G, Subgroup.normalizer ((P : Subgroup G) : Set G) = P := fun P ↦ by
    refine Eq.symm (h_subgroup_eq Subgroup.le_normalizer ?_)
    have h_card_G := Subgroup.index_mul_card (Subgroup.normalizer ((P : Subgroup G) : Set G))
    have e : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = Fintype.card (Sylow p G) := by
      rw [← Nat.card_eq_fintype_card]; exact (Sylow.card_eq_index_normalizer P).symm
    rw [e, hn3, hn] at h_card_G
    have hP := h_card_val P
    omega
  let ϕ := MulAction.toPermHom G (Sylow p G)
  have h_ker : ϕ.ker = ⊥ := eq_bot_iff.mpr fun g hg ↦ Subgroup.mem_bot.mpr (by
    have hg_norm : ∀ P : Sylow p G, g ∈ (P : Subgroup G) := fun P ↦ by
      exact h_norm P ▸ Sylow.smul_eq_iff_mem_normalizer.mp (DFunLike.ext_iff.mp (MonoidHom.mem_ker.mp hg) P)
    obtain ⟨P, Q, hPQ⟩ : ∃ P Q : Sylow p G, P ≠ Q := Fintype.one_lt_card_iff.mp (by rw [hn3]; norm_num)
    have h_inter : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) = 1 := by
      have h_dvd := Subgroup.card_dvd_of_le (inf_le_left : (P : Subgroup G) ⊓ (Q : Subgroup G) ≤ P)
      rw [h_card_val P] at h_dvd
      rcases (Nat.dvd_prime Nat.prime_three).mp h_dvd with h_eq_1 | h3
      · exact h_eq_1
      · have h_inf_eq : (P : Subgroup G) ⊓ (Q : Subgroup G) = (P : Subgroup G) := h_subgroup_eq inf_le_left (by rw [h3, h_card_val P])
        have h_eq : (P : Subgroup G) = (Q : Subgroup G) := h_subgroup_eq (h_inf_eq ▸ inf_le_right) (by rw [h_card_val P, h_card_val Q])
        exact absurd (by cases P; cases Q; congr) hPQ
    have h_sub : Subsingleton ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) := (Nat.card_eq_one_iff_unique.mp h_inter).1
    exact congrArg Subtype.val <| match h_sub with
      | ⟨h_allEq⟩ => h_allEq (⟨g, Subgroup.mem_inf.mpr ⟨hg_norm P, hg_norm Q⟩⟩ : ↥((P : Subgroup G) ⊓ (Q : Subgroup G))) ⟨1, Subgroup.one_mem _⟩
  )
  have h_inj := (MonoidHom.ker_eq_bot_iff ϕ).mp h_ker
  have h_range : Nat.card ϕ.range = 12 := hn ▸ Nat.card_congr (MonoidHom.ofInjective h_inj).symm.toEquiv
  have h_perm : Nat.card (Equiv.Perm (Sylow p G)) = 24 := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hn3]; rfl
  have h_index : ϕ.range.index = 2 := by
    have h_mul := Subgroup.index_mul_card ϕ.range
    rw [h_range, h_perm] at h_mul
    omega
  exact ⟨(MonoidHom.ofInjective h_inj).trans
    ((MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h_index)).trans
    (Equiv.altCongrHom (Fintype.equivOfCardEq (by rw [hn3, Fintype.card_fin]))))⟩


theorem pgl_unique_index_two_subgroup (m : ℕ) (hm : m ≥ 1) (hpm : p ^ m ≥ 5)
    (H : Subgroup (PGL p))
    (hH_le : H ≤ (pglMap (galoisFieldRingHom (p := p) m)).range)
    (hH_card : Nat.card H = p ^ m * (p ^ (2 * m) - 1) / 2) :
    Nonempty (H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  let φ := pglMap (galoisFieldRingHom (p := p) m)
  let H' := H.comap φ
  have h_equiv : H' ≃* H :=
    (H'.equivMapOfInjective φ (pglMap_injective _ (RingHom.injective _))).trans (MulEquiv.subgroupCongr (by
      ext x; rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; obtain ⟨y, rfl⟩ := hH_le hx; exact ⟨y, hx, rfl⟩))
  have hH'_index : H'.index = 2 := by
    have h_card : Nat.card (PGLOf (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) := by
      rw [card_PGL2, Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm)), pow_mul']
    have hp_gt_two : p > 2 := Fact.out
    have h_even : 2 ∣ p ^ (2 * m) - 1 := by
      rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (Nat.le_trans (by norm_num : 1 ≤ 2) hp_gt_two.le))]
      have h_odd : ¬ Even p := fun h ↦ ne_of_gt hp_gt_two ((Nat.Prime.even_iff Fact.out).mp h)
      exact iff_of_false (fun h ↦ h_odd (Nat.even_pow.mp h).1) (by norm_num)
    have h_dvd : 2 ∣ p ^ m * (p ^ (2 * m) - 1) := dvd_mul_of_dvd_right h_even _
    have hp2m : 1 < p ^ (2 * m) := one_lt_pow₀ (Nat.Prime.one_lt Fact.out) (by omega)
    have h_nz : p ^ m * (p ^ (2 * m) - 1) / 2 ≠ 0 :=
      ne_of_gt (Nat.div_pos (Nat.le_of_dvd (mul_pos (show 0 < p ^ m by omega) (Nat.sub_pos_of_lt hp2m)) h_dvd) (by norm_num))
    exact mul_right_cancel₀ h_nz <|
      calc H'.index * (p ^ m * (p ^ (2 * m) - 1) / 2)
        _ = H'.index * Nat.card H' := by rw [Nat.card_congr h_equiv.toEquiv, hH_card]
        _ = Nat.card (PGLOf (GaloisField p m)) := Subgroup.index_mul_card H'
        _ = p ^ m * (p ^ (2 * m) - 1) := h_card
        _ = (p ^ m * (p ^ (2 * m) - 1) / 2) * 2 := (Nat.div_mul_cancel h_dvd).symm
        _ = 2 * (p ^ m * (p ^ (2 * m) - 1) / 2) := mul_comm _ _
  have h_iso := index_two_subgroup_iso_PSL p (GaloisField p m) (by
    rw [Fintype.card_eq_nat_card, GaloisField.card p m (by omega)]
    exact hpm) H' hH'_index
  exact ⟨h_equiv.symm.trans h_iso.some⟩

omit [Fact (Nat.Prime p)] h_odd in
theorem m_ge_one_of_pow_ge_three (m : ℕ) (hm : p ^ m ≥ 3) : m ≥ 1 := by
  cases m
  · exact absurd hm (Nat.not_le_of_gt (Nat.le.step Nat.le.refl))
  · exact Nat.succ_pos _

theorem recognition_PSL_iso (G : Subgroup (PGL p))
    [Finite G] (m : ℕ) (hm : p ^ m ≥ 5)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  have hm1 : m ≥ 1 := m_ge_one_of_pow_ge_three p m (Nat.le_trans (Nat.le.step (Nat.le.step Nat.le.refl)) hm)
  obtain ⟨g, hg⟩ := psl_G_le_pgl_range_from_orbit p G m hm1 hm hn
  obtain ⟨iso'⟩ := pgl_unique_index_two_subgroup p m hm1 hm _ hg (by
    rw [← Nat.card_congr (G.equivMapOfInjective (MulEquiv.toMonoidHom (MulAut.conj g)) (MulEquiv.injective _)).toEquiv, hn])
  exact ⟨(G.equivMapOfInjective _ (MulEquiv.injective _)).trans iso'⟩

theorem recognition_PGL_iso (G : Subgroup (PGL p))
    [Finite G] (m : ℕ) (hm : p ^ m ≥ 3)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1)) :
    Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m)))) := by
  have hm1 : m ≥ 1 := m_ge_one_of_pow_ge_three p m hm
  let H := (pglMap (galoisFieldRingHom (p := p) m)).range
  haveI : Finite H := Set.finite_range _ |>.to_subtype
  obtain ⟨g, hg⟩ := pgl_subgroups_conjugate p G H m hm1 hn <|
    (Nat.card_congr (Equiv.ofInjective (pglMap (galoisFieldRingHom (p := p) m)) (pglMap_injective _ (RingHom.injective (galoisFieldRingHom (p := p) m)))).symm).trans (by rw [card_PGL2, Fintype.card_eq_nat_card.trans (GaloisField.card p m (ne_of_gt hm1)), pow_mul'])
  have h_pgl_iso_H : PGLOf (GaloisField p m) ≃* ↥H :=
    MonoidHom.ofInjective (f := pglMap (galoisFieldRingHom (p := p) m))
      (pglMap_injective _ (RingHom.injective _))
  exact ⟨(Subgroup.equivMapOfInjective G _ (MulEquiv.injective _)).trans <|
    (MulEquiv.subgroupCongr hg).trans h_pgl_iso_H.symm⟩

theorem recognition_PSL_pm3 (G : Subgroup (PGL p))
    [Finite G] (hp3 : p = 3)
    (hn : Nat.card G = 12)
    (hn3 : Fintype.card (Sylow p G) = 4) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1)) := by
  obtain ⟨isoA4⟩ := recognition_A4 p G hp3 hn hn3
  obtain ⟨isoPSL⟩ := A4_iso_PSL2_GF31
  subst hp3
  exact ⟨isoA4.trans isoPSL⟩

omit h_odd in
theorem sylow_count_of_order_12 (G : Subgroup (PGL p))
    [Finite G] (hp3 : p = 3)
    (hn : Nat.card G = 12)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Fintype.card (Sylow p G) = 4 := by
  have h_card_div : Fintype.card (Sylow p G) ∣ 4 := by
    have h_idx : ∀ P : Sylow p G, Nat.card (G ⧸ P.toSubgroup) = Nat.card G / p ^ Nat.factorization (Nat.card G) p := by
      intro P
      have h_card_eq : Nat.card P.toSubgroup = p ^ Nat.factorization (Nat.card G) p := by
        convert P.card_eq_multiplicity
      rw [← h_card_eq, Subgroup.card_eq_card_quotient_mul_card_subgroup P.toSubgroup, Nat.mul_div_cancel _ Nat.card_pos]
    have h_dvd : ∀ P : Sylow p G, Fintype.card (Sylow p G) ∣ Nat.card (G ⧸ P.toSubgroup) := by
      intro P
      have h_norm : Fintype.card (Sylow p G) = Nat.card (G ⧸ (Subgroup.normalizer (SetLike.coe P))) := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_congr (Sylow.equivQuotientNormalizer P)
      rw [h_norm]
      exact Subgroup.index_dvd_of_le Subgroup.le_normalizer
    have P := Classical.arbitrary (Sylow p G)
    have h_eq : Nat.card G / p ^ Nat.factorization (Nat.card G) p = 4 := by
      rw [hn, hp3, Nat.factorization_eq_one (m := 4) rfl Nat.prime_three (by norm_num), pow_one]
    exact h_eq ▸ h_idx P ▸ h_dvd P
  have h_card_mod : Fintype.card (Sylow p G) ≡ 1 [MOD p] := by
    rw [← Nat.card_eq_fintype_card]
    exact card_sylow_modEq_one p ↥G
  have h_le : Fintype.card (Sylow p G) ≤ 4 := Nat.le_of_dvd (by norm_num) h_card_div
  interval_cases Fintype.card (Sylow p G)
  · rw [hp3] at h_card_mod
    change 2 % 3 = 1 % 3 at h_card_mod
    omega
  · revert h_card_div; norm_num
  · rfl


theorem recognition_PSL_general (G : Subgroup (PGL p))
    [Finite G] (m : ℕ) (hm : p ^ m ≥ 3)
    (hn : Nat.card G = p ^ m * (p ^ (2 * m) - 1) / 2)
    (hG_p : p ∣ Nat.card G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  by_cases h5 : p ^ m ≥ 5
  · exact recognition_PSL_iso p G m h5 hn
  · have hp3 : p = 3 := by
      have hp := (Fact.out : Nat.Prime p)
      have h1 : p > 2 := Fact.out
      have h2 : p ≤ 4 := (Nat.le_self_pow (show m ≠ 0 by linarith only [m_ge_one_of_pow_ge_three p m hm]) p).trans (by linarith only [h5])
      interval_cases p
      · rfl
      · revert hp; norm_num
    subst hp3
    have hm1 : m = 1 := le_antisymm (by
      by_contra hc
      have h_pow : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 2 ≤ m by linarith only [hc])
      change 9 ≤ 3 ^ m at h_pow
      linarith only [h5, h_pow]) (m_ge_one_of_pow_ge_three 3 m hm)
    subst hm1
    have hn12 : Nat.card G = 12 := by rw [hn]; norm_num
    exact recognition_PSL_pm3 3 G rfl hn12 (sylow_count_of_order_12 3 G rfl hn12 hn_p_gt1)


theorem partition_equation
    (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G)
    (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    ∃ (pm z1 n r : ℕ) (z : Fin r → ℕ) (s : Fin r → ℕ),
      pm = Nat.card P ∧
      n = Nat.card G ∧
      pm ≥ 3 ∧
      z1 ≥ 1 ∧
      z1 ∣ (pm - 1) ∧
      (∀ i, s i = 1 ∨ s i = 2) ∧
      (∀ i, z i ≥ 2) ∧
      n > pm * z1 ∧
      ((1 : ℚ) - 1 / n = 1 / z1 - 1 / (pm * z1) +
          partitionTerm (if z1 = 1 then 1 else 2) z1 +
          ∑ i : Fin r, partitionTerm (s i) (z i)) := by
  let pm := Nat.card P
  let z1 := normalizerQuotient p G P
  let np := Fintype.card (Sylow p G)
  let n := Nat.card G
  let D := (pm - 2) * np + 2
  have hD_dvd : D ∣ n := nonsplit_torus_divides_geo p G hG_p P hn_p_gt1
  let z2 := n / D
  refine ⟨pm, z1, n, 1, fun _ ↦ z2, fun _ ↦ 2, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sylow_card_ge_3 p G hG_p P
  · exact Nat.div_pos (Subgroup.card_le_of_le Subgroup.le_normalizer) Nat.card_pos
  · exact normalizer_complement_divides_main p G P hG_p
  · intro i; right; rfl
  · intro i; exact nonsplit_torus_ge_two p G hG_p P hn_p_gt1
  · exact group_order_gt_normalizer p G P hn_p_gt1
  ·
    have hpm3 : 3 ≤ pm := sylow_card_ge_3 p G hG_p P
    have hnp_gt1 : np > 1 := hn_p_gt1
    have hz1_ge1 : 1 ≤ z1 := Nat.div_pos (Subgroup.card_le_of_le Subgroup.le_normalizer) Nat.card_pos
    have hpm_pos : (pm : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hz1_pos : (z1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnp_pos : (np : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h_n_nat : n = pm * z1 * np := card_eq_pm_z1_np' p G P
    have h_n_eq : (n : ℚ) = (pm : ℚ) * (z1 : ℚ) * (np : ℚ) := by
      rw [h_n_nat, Nat.cast_mul, Nat.cast_mul]
    have h_D_eq : (D : ℚ) = ((pm : ℚ) - 2) * (np : ℚ) + 2 := by
      have h2pm : 2 ≤ pm := by omega
      change (((pm - 2) * np + 2 : ℕ) : ℚ) = _
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub h2pm]
      push_cast
      rfl
    have hz2_eq : (z2 : ℚ) = (n : ℚ) / (D : ℚ) := by
      have hD_pos : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h_mul : (z2 : ℚ) * (D : ℚ) = (n : ℚ) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hD_dvd]
      rw [← mul_div_cancel_right₀ (z2 : ℚ) hD_pos, h_mul]
    by_cases hz1 : z1 = 1
    · simp only [partitionTerm, if_pos hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one, Nat.cast_ofNat, one_mul]
      rw [hz2_eq, h_n_eq, h_D_eq, hz1]
      simp only [Nat.cast_one, mul_one]
      field_simp [hpm_pos, hz1_pos, hnp_pos]
      ring
    · simp only [partitionTerm, if_neg hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one, Nat.cast_ofNat, one_mul]
      rw [hz2_eq, h_n_eq, h_D_eq]
      field_simp [hpm_pos, hz1_pos, hnp_pos]
      ring

theorem dickson_branch2_z1_eq_1 (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1)
    (pm z1 n r : ℕ) (z : Fin r → ℕ) (s : Fin r → ℕ)
    (hpm_eq : pm = Nat.card P) (hn_eq : n = Nat.card G)
    (hpm : pm ≥ 3) (hz1_ge : z1 ≥ 1) (hz1_dvd : z1 ∣ pm - 1)
    (hs_bound : ∀ i, s i = 1 ∨ s i = 2) (hz_pos : ∀ i, z i ≥ 2)
    (hn_gt : n > pm * z1)
    (h_eq : (1 : ℚ) - 1 / n = 1 / z1 - 1 / (pm * z1) +
        partitionTerm (if z1 = 1 then 1 else 2) z1 +
        ∑ i : Fin r, partitionTerm (s i) (z i))
    (hz1_eq : z1 = 1) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  subst hz1_eq
  have h_eq_subst : (1 : ℚ) / pm - 1 / n = ∑ i, partitionTerm (s i) (z i) := by
    have h_eval : partitionTerm (if 1 = 1 then 1 else 2) 1 = 0 := by
      rw [if_pos rfl, partitionTerm]
      norm_num
    rw [h_eval] at h_eq
    push_cast at h_eq
    rw [mul_one, div_one] at h_eq
    linarith only [h_eq]
  have h_branch2a : pm = 3 ∧ r = 1 ∧ n = 12 :=
    branch2a_constraints pm n r z s hpm (by linarith only [hn_gt, hpm]) (by linarith only [hn_gt]) hs_bound hz_pos h_eq_subst
  have hp_eq_3 : p = 3 := by
    have h_p_dvd : p ∣ pm := by
      have h_pow := hpm_eq.trans (Sylow.card_eq_multiplicity P)
      exact h_pow.symm ▸ dvd_pow_self p fun h ↦ by rw [h, pow_zero] at h_pow; linarith only [h_branch2a.1, h_pow]
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp (h_branch2a.1 ▸ h_p_dvd)
  subst hp_eq_3
  refine Or.inr <| Or.inl ⟨1, by norm_num, ?_⟩
  apply recognition_PSL_general
  · rfl
  · exact hn_eq.symm.trans h_branch2a.2.2
  · exact hG_p
  · exact hn_p_gt1


theorem dickson_branch2_z1_ge_2 (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1)
    (pm : ℕ) (hpm_eq : pm = Nat.card P) (hpm : pm ≥ 3):
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  rcases branch2_params p G hG_p P hn_p_gt1 with h | h | h | h
  · have h_pow := Sylow.card_eq_multiplicity P
    have hp_eq_3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp <|
      h.1 ▸ (h_pow ▸ dvd_pow_self p fun hm ↦ by rw [hm, pow_zero] at h_pow; omega)
    exact Or.inr <| Or.inl ⟨1, le_refl 1, recognition_PSL_pm3 p G hp_eq_3 (by rw [card_eq_pm_z1_np' p G P, h.1, h.2.1, h.2.2]) h.2.2⟩
  · obtain ⟨m, hm⟩ : ∃ m, pm = p ^ m := ⟨_, hpm_eq.trans (Sylow.card_eq_multiplicity P)⟩
    have h2_dvd : 2 ∣ p ^ m - 1 := by
      rw [← even_iff_two_dvd, Nat.even_sub (Nat.one_le_pow _ _ (by linarith only [h_odd.1]))]
      exact iff_of_false (fun h_e ↦ ne_of_gt h_odd.1 <| (Nat.Prime.even_iff Fact.out).mp (Nat.even_pow.mp h_e).1) (by norm_num)
    obtain ⟨k, hk⟩ : ∃ k, p ^ m = k * 2 + 1 := by obtain ⟨c, hc⟩ := h2_dvd; exact ⟨c, by omega⟩
    refine Or.inr <| Or.inl ⟨m, m_ge_one_of_pow_ge_three p m (by linarith only [hm, hpm]), ?_⟩
    apply recognition_PSL_general
    · by_contra h_m
      have hm_zero : m = 0 := by omega
      have hpm_one : pm = 1 := by rw [hm, hm_zero, pow_zero]
      linarith only [hpm, hpm_one]
    · rw [card_eq_pm_z1_np' p G P, h.2.1, h.2.2, ← hpm_eq, hm, hk]
      rw [show k * 2 + 1 - 1 = k * 2 from rfl, Nat.mul_div_cancel _ (by norm_num : 2 > 0)]
      have : p ^ (2 * m) = (k * 2 + 1) ^ 2 := by rw [mul_comm 2, Nat.pow_mul, hk]
      rw [this]
      have : (k * 2 + 1) ^ 2 - 1 = (k * 2 * (k + 1)) * 2 := by
        rw [show (k * 2 + 1) ^ 2 = (k * 2 * (k + 1)) * 2 + 1 by ring, Nat.add_sub_cancel]
      rw [this, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num : 2 > 0)]
      ring
    · exact hG_p
    · exact hn_p_gt1
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, pm = p ^ m := ⟨_, hpm_eq.trans (Sylow.card_eq_multiplicity P)⟩
    refine Or.inr <| Or.inr <| Or.inl ⟨m, m_ge_one_of_pow_ge_three p m (by linarith only [hm, hpm]), recognition_PGL_iso p G m (by linarith only [hm, hpm]) ?_⟩
    rw [card_eq_pm_z1_np' p G P, h.1, h.2, ← hpm_eq, hm]
    have : p ^ (2 * m) = (p ^ m) ^ 2 := by rw [← Nat.pow_mul, mul_comm 2, Nat.pow_mul]
    rw [this]
    obtain ⟨k, hk⟩ : ∃ k, p ^ m = k + 1 := ⟨p ^ m - 1, by have := Nat.one_le_pow m p (by linarith only [h_odd.1]); omega⟩
    rw [hk, show k + 1 - 1 = k from rfl]
    have : (k + 1) ^ 2 - 1 = k * (k + 2) := by
      rw [show (k + 1) ^ 2 = k * (k + 2) + 1 by ring, Nat.add_sub_cancel]
    rw [this]
    ring
  · have h_pow := Sylow.card_eq_multiplicity P
    have hp_eq_3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp <|
      h.1 ▸ (h_pow ▸ dvd_pow_self p fun hm ↦ by rw [hm, pow_zero] at h_pow; linarith only [h.1, h_pow])
    exact Or.inr <| Or.inr <| Or.inr ⟨hp_eq_3, recognition_A5_proof p G hp_eq_3 (by rw [card_eq_pm_z1_np' p G P, h.1, h.2.1, h.2.2]) h.2.2⟩

theorem classification_wild_slop (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  have ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  by_cases h_sylow : Fintype.card (Sylow p G) = 1
  · have : Subsingleton (Sylow p G) := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_sylow)
    exact Or.inl <| branch1_semidirect p G P (Sylow.normal_of_subsingleton P) hG_p
  · have hn_p_gt1 : Fintype.card (Sylow p G) > 1 :=
      lt_of_le_of_ne (Fintype.card_pos_iff.mpr inferInstance) (Ne.symm h_sylow)
    obtain ⟨pm, z1, n, r, z, s, hpm_eq, hn_eq, hpm, hz1_ge, hz1_dvd, hs_bound, hz_pos, hn_gt, h_eq⟩ :=
      partition_equation p G hG_p P hn_p_gt1
    by_cases hz1_eq : z1 = 1
    · exact dickson_branch2_z1_eq_1 p G hG_p P hn_p_gt1 pm z1 n r z s hpm_eq hn_eq hpm hz1_ge hz1_dvd hs_bound hz_pos hn_gt h_eq hz1_eq
    · exact dickson_branch2_z1_ge_2 p G hG_p P hn_p_gt1 pm hpm_eq hpm

end

end Dickson
