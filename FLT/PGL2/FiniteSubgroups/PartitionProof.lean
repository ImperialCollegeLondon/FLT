/-
Copyright (c) 2026 Dokying Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dokying Yang
-/
module

public import FLT.PGL2.FiniteSubgroups.PartitionHelpers
public import FLT.PGL2.FiniteSubgroups.RecognitionA5
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Geometric Partition Proofs for Finite Subgroups of PGL₂

This file derives the Diophantine constraints that govern finite
subgroups `G` of `PGL(2, K)` whose order is divisible by `p` and
which do not fix a point. The argument proceeds in three stages:

1. **Double counting on `Phi`.** The set `Phi` of points on the
   projective line fixed by some non-identity element of `G` carries
   a natural `G`-action. A double-counting argument (Burnside's
   lemma applied to `Phi`) shows `G` has exactly two orbits on `Phi`:
   the orbit of Sylow fixed points and one complementary orbit.
2. **Orbit–stabiliser identity.** The stabiliser of a Sylow fixed
   point equals the Sylow normaliser, producing the identity
   `|G| = p^m · z₁ · n_p` relating the group order to the Sylow
   size, normaliser quotient, and number of Sylow subgroups.
3. **Diophantine resolution.** A divisibility condition on the
   complementary orbit size reduces the parameter space to exactly
   four cases, enumerated in `branch2_params`.

## Main definitions

- `Phi`: the set of points on the projective line fixed by at least one non-identity element of `G`.

## Main results

- `sylow_distinct_fixedPoints`: distinct Sylow `p`-subgroups have distinct fixed points.
- `stabilizer_sylowFixedPoint_eq_normalizer`: the stabiliser in `G` of a Sylow fixed point is
                                              exactly the Sylow normaliser.
- `num_orbits_eq_two`: `G` has exactly two orbits on `Phi`.
- `card_eq_pm_z1_np'`: an identity between the order of `G` to the sizes of the two orbits in `Phi`.
- `nonsplit_torus_divides_geo`: a divisibility condition on the order of the normaliser quotient.
- `branch2_params`: derives the exact geometric parameters for a non-elementary subgroup.
-/

@[expose] public section

namespace Dickson

noncomputable section DoubleCounting

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

/-- The set of points on the projective line fixed by at least one non-identity element of `G`. -/
def Phi (G : Subgroup (PGL p)) : Set (ProjectiveLine p) :=
  ⋃ (g : G) (_ : g ≠ 1), {x : ProjectiveLine p | (g : PGL p) • x = x}

lemma Phi_finite (G : Subgroup (PGL p)) [Finite G] : (Phi p G).Finite := by
  refine Set.Finite.biUnion (Set.toFinite _) fun g hg ↦ ?_
  have h_order : IsOfFinOrder (g : PGL p) := by
    obtain ⟨n, hn_pos, hn_eq⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite g)
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, Subtype.ext_iff.mp hn_eq⟩
  have h_dichotomy := fixedPoints_dichotomy p (g : PGL p) (fun h ↦ hg (Subtype.ext h)) h_order
  have h_ncard_pos : 0 < Set.ncard {x : ProjectiveLine p | (g : PGL p) • x = x} := by
    change 0 < Set.ncard (fixedPoints p (g : PGL p))
    rcases element_dichotomy p G g with hp | hcoprime
    · rw [h_dichotomy.1.mpr hp]
      norm_num
    · rw [h_dichotomy.2.mpr hcoprime.symm]
      norm_num
  exact Set.finite_of_ncard_pos h_ncard_pos

omit h_odd in
lemma Phi_smul_mem (G : Subgroup (PGL p)) (h : G) {x : ProjectiveLine p}
    (hx : x ∈ Phi p G) : (h : PGL p) • x ∈ Phi p G := by
  simp only [Phi, Set.mem_iUnion, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨g, hg_ne, hgx⟩ := hx
  exact ⟨h * g * h⁻¹,
    fun heq ↦ hg_ne (by rw [← inv_mul_cancel_left h g, mul_inv_eq_one.mp heq, inv_mul_cancel]),
    by rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, Subgroup.coe_inv,
      inv_smul_smul, hgx]⟩

abbrev PhiType (G : Subgroup (PGL p)) := ↥(Phi p G)

noncomputable instance phiFintype (G : Subgroup (PGL p)) [Finite G] :
    Fintype (PhiType p G) := (Phi_finite p G).fintype

instance phiMulAction (G : Subgroup (PGL p)) : MulAction G (PhiType p G) where
  smul h x := ⟨(h : PGL p) • x.val, Phi_smul_mem p G h x.prop⟩
  one_smul x := Subtype.ext (one_smul (PGL p) x.val)
  mul_smul g₁ g₂ x := Subtype.ext (mul_smul (g₁ : PGL p) (g₂ : PGL p) x.val)

lemma sylow_fixedPt_mem_Phi (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    sylow_fixedPoint p G hG_p P ∈ Phi p G := by
  obtain ⟨g, hg_mem, hg_ne⟩ : ∃ g : G, g ∈ (P : Subgroup G) ∧ g ≠ 1 := by
    by_contra! h
    exact absurd (sylow_card_ge_3 p G hG_p P) (by
      rw [(eq_bot_iff.mpr h : (P : Subgroup G) = ⊥)]
      norm_num)
  exact Set.mem_iUnion₂.mpr ⟨g, hg_ne, sylow_element_fixes p G hG_p P g hg_mem⟩

open Classical in
lemma Phi_card_le (G : Subgroup (PGL p)) [Finite G] :
    Fintype.card (PhiType p G) ≤ 2 * (Nat.card G - 1) := by
  have h_fixed : ∀ (g : G), g ≠ 1 → Set.ncard {x : ProjectiveLine p | (g : PGL p) • x = x} ≤ 2 := by
    intro g hg
    have h_dich := fixedPoints_dichotomy p (g : PGL p) (fun h ↦ hg (Subtype.ext h))
      (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite g))
    rcases element_dichotomy p G g with hp | hcop
    · exact (h_dich.1.mpr hp).symm ▸ by norm_num
    · exact (h_dich.2.mpr hcop.symm).symm ▸ le_rfl
  have h_card : ∀ s : Finset G, 1 ∉ s →
      Set.ncard (⋃ g ∈ (s : Set G), {x : ProjectiveLine p | (g : PGL p) • x = x}) ≤ 2 * s.card := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro _
      simp only [Finset.coe_empty, Set.biUnion_empty, Set.ncard_empty, Finset.card_empty, mul_zero,
        le_refl]
    | insert a s ha ih =>
      intro h
      rw [Finset.mem_insert, not_or] at h
      rw [Finset.coe_insert, Set.biUnion_insert, Finset.card_insert_of_notMem ha, mul_add, mul_one,
        add_comm]
      exact (Set.ncard_union_le _ _).trans (add_le_add (h_fixed a (fun eq ↦ h.1 eq.symm)) (ih h.2))
  rw [← Nat.card_eq_fintype_card]
  change Set.ncard (Phi p G) ≤ _
  have h_phi : Phi p G = ⋃ g ∈ (Finset.univ.erase (1 : G) : Set G), {x | (g : PGL p) • x = x} := by
    ext x
    rw [Phi]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨g, hg, hx_eq⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨g, Finset.mem_erase.mpr ⟨hg, Finset.mem_univ g⟩, hx_eq⟩
    · obtain ⟨g, hg, hx_eq⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨g, (Finset.mem_erase.mp hg).1, hx_eq⟩
  rw [h_phi]
  have h_bound := h_card (Finset.univ.erase (1 : G)) (Finset.notMem_erase (1 : G) Finset.univ)
  rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : G)), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at h_bound
  exact h_bound

/-- Distinct Sylow `p`-subgroups of `G` have distinct fixed points on the projective line. -/
theorem sylow_distinct_fixedPoints (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P Q : Sylow p G) (hPQ : P ≠ Q) :
    sylow_fixedPoint p G hG_p P ≠ sylow_fixedPoint p G hG_p Q := by
  intro h_eq
  have h_comm : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (Q : Subgroup G), a * b = b * a := by
    intros a ha b hb
    by_cases ha1 : a = 1; · rw [ha1, one_mul, mul_one]
    by_cases hb1 : b = 1; · rw [hb1, mul_one, one_mul]
    exact Subtype.ext <| commute_of_orderOf_prime_common_fixedPoint p _ _
      (sylow_fixedPoint p G hG_p Q) (sylow_element_order_p p G P a ha ha1)
      (sylow_element_order_p p G Q b hb hb1)
      (h_eq ▸ sylow_element_fixes p G hG_p P a ha) (sylow_element_fixes p G hG_p Q b hb)
  let S : Subgroup G := {
    carrier := { g | ∃ a ∈ P, ∃ b ∈ Q, g = a * b }
    one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
    mul_mem' := by
      rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
      exact ⟨a * c, P.mul_mem ha hc, b * d, Q.mul_mem hb hd, by
        calc a * b * (c * d) = a * (b * c) * d := by group
        _ = a * (c * b) * d := by rw [h_comm c hc b hb]
        _ = a * c * (b * d) := by group⟩
    inv_mem' := by
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, by
        rw [mul_inv_rev, h_comm a⁻¹ (P.inv_mem ha) b⁻¹ (Q.inv_mem hb)]⟩
  }
  have hP_le_S : (P : Subgroup G) ≤ S := fun x hx ↦ ⟨x, hx, 1, Q.one_mem, (mul_one x).symm⟩
  have hQ_le_S : (Q : Subgroup G) ≤ S := fun x hx ↦ ⟨1, P.one_mem, x, hx, (one_mul x).symm⟩
  have hPQ_eq : (P : Subgroup G) ⊔ Q = P := by
    refine P.is_maximal' ?_ le_sup_left
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := sup_le hP_le_S hQ_le_S hg
    obtain ⟨k, hk⟩ := P.2 ⟨a, ha⟩; obtain ⟨l, hl⟩ := Q.2 ⟨b, hb⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    push_cast
    rw [Commute.mul_pow (h_comm a ha b hb)]
    have ha_pow : (a : G) ^ p ^ (k + l) = 1 := by
      rw [pow_add, pow_mul, show (a:G)^p^k = 1 from Subtype.ext_iff.mp hk, one_pow]
    have hb_pow : (b : G) ^ p ^ (k + l) = 1 := by
      rw [pow_add, mul_comm, pow_mul, show (b:G)^p^l = 1 from Subtype.ext_iff.mp hl, one_pow]
    rw [ha_pow, hb_pow, mul_one]
  have hQ_le_P : (Q : Subgroup G) ≤ (P : Subgroup G) := hPQ_eq ▸ le_sup_right
  have h_card : Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) :=
    (Sylow.card_eq_multiplicity Q).trans (Sylow.card_eq_multiplicity P).symm
  have hQ_eq_P : (Q : Subgroup G) = (P : Subgroup G) :=
    SetLike.ext' (Set.eq_of_subset_of_ncard_le hQ_le_P h_card.ge)
  exact hPQ (Sylow.ext hQ_eq_P.symm)

theorem fixes_sylowPoint_normalizes (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (g : G) (hg : (g : PGL p) • sylow_fixedPoint p G hG_p P = sylow_fixedPoint p G hG_p P) :
    g ∈ Subgroup.normalizer (P : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff]
  have h_map : Subgroup.map (MulAut.conj g) (P : Subgroup G) = (P : Subgroup G) :=
    congrArg Sylow.toSubgroup <| by
      by_contra h_neq
      refine sylow_distinct_fixedPoints p G hG_p (MulAut.conj g • P) P h_neq <| Eq.symm <|
        eq_sylow_fixedPoint p G hG_p _ _ <| by
          intro q hq
          rw [Sylow.pointwise_smul_def] at hq
          obtain ⟨r, hr, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists q _ _).mp hq
          simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hg.symm,
            sylow_element_fixes p G hG_p P r hr, hg]
  intro n
  refine ⟨fun hn ↦ h_map ▸ ⟨n, hn, rfl⟩, fun hn ↦ ?_⟩
  obtain ⟨y, hy, hy_eq⟩ := Subgroup.mem_map.mp (h_map.symm ▸ hn)
  change g * y * g⁻¹ = _ at hy_eq
  rw [show n = y by calc
    n = g⁻¹ * (g * n * g⁻¹) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [← hy_eq]
    _ = y := by group]
  exact hy

/-- The stabiliser in `G` of the unique fixed point of a Sylow `p`-subgroup is exactly
the normaliser of that Sylow `p`-subgroup. -/
theorem stabilizer_sylowFixedPoint_eq_normalizer (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    {g : G | (g : PGL p) • sylow_fixedPoint p G hG_p P = sylow_fixedPoint p G hG_p P} =
    (Subgroup.normalizer (P : Set G)) := by
  have h_norm := normalizer_stabilizes_fixedPoint p G P _
    (sylow_element_fixes p G hG_p P)
    (eq_sylow_fixedPoint p G hG_p P)
  exact Set.ext fun g ↦ ⟨fixes_sylowPoint_normalizes p G hG_p P g, h_norm g⟩

lemma sylow_fixedPt_injective (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    Function.Injective (fun P : Sylow p G ↦
      (⟨sylow_fixedPoint p G hG_p P, sylow_fixedPt_mem_Phi p G hG_p P⟩ : PhiType p G)) := by
  exact fun P Q h ↦ not_imp_not.mp (sylow_distinct_fixedPoints p G hG_p P Q) (Subtype.ext_iff.mp h)

open Classical in
lemma fixedBy_eq_fixedPoints (G : Subgroup (PGL p)) [Finite G]
    (g : G) (hg : g ≠ 1) :
    Fintype.card (MulAction.fixedBy (PhiType p G) g) =
    Set.ncard (fixedPoints p (g : PGL p)) := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
  exact Nat.card_congr {
    toFun := fun x ↦ ⟨x.1.1, Subtype.ext_iff.mp x.2⟩
    invFun := fun y ↦ ⟨⟨y.1, Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, y.2⟩⟩⟩, Subtype.ext y.2⟩
    left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ ↦ Subtype.ext rfl
  }

theorem count_elements_order_p (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p} =
      Fintype.card (Sylow p G) * (Nat.card P - 1) := by
  rw [← count_order_p_elements p G hG_p P]
  congr with g
  rw [Subgroup.orderOf_coe]
  refine and_iff_right_of_imp ?_
  rintro h rfl
  rw [orderOf_one] at h
  exact Nat.Prime.ne_one Fact.out h.symm

open Classical in
lemma element_fixedPt_sum (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∑ g ∈ (Finset.univ : Finset G).erase 1,
      Set.ncard (fixedPoints p ((g : G) : PGL p)) =
    2 * (Nat.card G - 1) -
      Fintype.card (Sylow p G) * (Nat.card P - 1) := by
  refine eq_tsub_of_add_eq ?_
  have h_eq : ∀ g ∈ (Finset.univ : Finset G).erase 1,
      Set.ncard (fixedPoints p (g : PGL p)) =
        if orderOf (g : PGL p) = p then 1 else 2 := fun g hg ↦ by
    have hg_ne : g ≠ 1 := Finset.ne_of_mem_erase hg
    have h_dich := fixedPoints_dichotomy p (g : PGL p) (fun h ↦ hg_ne (Subtype.ext h))
      (Submonoid.isOfFinOrder_coe.mpr (isOfFinOrder_of_finite g))
    split_ifs with h_p
    · exact h_dich.1.mpr h_p
    · exact h_dich.2.mpr ((element_dichotomy p G g).resolve_left h_p).symm
  rw [Finset.sum_congr rfl h_eq, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul, mul_one]
  have h_card_p : Nat.card ↥(((Finset.univ : Finset G).erase 1).filter
      (fun (x : G) ↦ orderOf (x : PGL p) = p)) =
      Nat.card {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p} := by
    have h_set : ((((Finset.univ : Finset G).erase 1).filter
        (fun (x : G) ↦ orderOf (x : PGL p) = p)) : Set G) =
        {g : G | g ≠ 1 ∧ orderOf (g : PGL p) = p} := by
      ext g
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_erase]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, Finset.mem_univ g⟩, h.2⟩⟩
    exact congrArg (fun (s : Set G) ↦ Nat.card ↥s) h_set
  have h_card_cop : Nat.card ↥(((Finset.univ : Finset G).erase 1).filter
      (fun (x : G) ↦ ¬orderOf (x : PGL p) = p)) =
      Nat.card {g : G | g ≠ 1 ∧ Nat.Coprime (orderOf (g : PGL p)) p} := by
    have h_set : ((((Finset.univ : Finset G).erase 1).filter
        (fun (x : G) ↦ ¬orderOf (x : PGL p) = p)) : Set G) =
        {g : G | g ≠ 1 ∧ Nat.Coprime (orderOf (g : PGL p)) p} := by
      ext g
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq, Finset.mem_erase]
      exact ⟨fun h ↦ ⟨h.1.1, (element_dichotomy p G g).resolve_left h.2⟩,
             fun ⟨h_ne, h_cop⟩ ↦ ⟨⟨h_ne, Finset.mem_univ g⟩, fun h_p ↦ by
               rw [h_p] at h_cop
               have : Nat.gcd p p = p := Nat.gcd_self p
               have : p > 2 := Fact.out
               omega⟩⟩
    exact congrArg (fun (s : Set G) ↦ Nat.card ↥s) h_set
  rw [← Nat.card_eq_finsetCard, ← Nat.card_eq_finsetCard, h_card_p, h_card_cop,
    ← count_elements_order_p p G hG_p P, element_partition_count p G]
  omega

omit h_odd in
lemma phi_stab_card_ge_two (G : Subgroup (PGL p)) [Finite G]
    (x : PhiType p G) :
    2 ≤ Nat.card (MulAction.stabilizer G x) := by
  obtain ⟨g, hg_ne, hgx⟩ := Set.mem_iUnion₂.mp x.prop
  exact Set.ncard_pair hg_ne ▸ Nat.card_mono (Set.toFinite _) (by
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨MulAction.mem_stabilizer_iff.mpr (Subtype.ext hgx), Subgroup.one_mem _⟩)

open Classical in
lemma orbit_count_mul_card (G : Subgroup (PGL p)) [Finite G] :
    Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) * Nat.card G =
    ∑ x : PhiType p G, Nat.card (MulAction.stabilizer G x) := by
  simp only [Nat.card_eq_fintype_card]
  rw [← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
  simp only [Fintype.card_subtype]
  exact (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun x g ↦ g • x = x).symm

lemma nonsplit_D_lt_n (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    (Nat.card P - 2) * Fintype.card (Sylow p G) + 2 < Nat.card G := by
  have h_n_gt_pm : Nat.card P ≥ 3 := sylow_card_ge_3 p G hG_p P
  have h_n_gt_2p : Fintype.card (Sylow p G) ≥ Nat.card P + 1 := by
    have h_le := Nat.le_of_dvd (Nat.sub_pos_of_lt hn_p_gt1) (card_sylow_mod_card p G hG_p P)
    omega
  have h_dvd_both : Nat.card P ∣ Nat.card G ∧ Fintype.card (Sylow p G) ∣ Nat.card G := by
    refine ⟨Subgroup.card_subgroup_dvd_card (P : Subgroup G), ?_⟩
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Sylow.equivQuotientNormalizer P)]
    exact Subgroup.card_quotient_dvd_card (Subgroup.normalizer (P : Set G))
  have h_copr : Nat.Coprime (Fintype.card (Sylow p G) - 1) (Fintype.card (Sylow p G)) := by
    apply Nat.coprime_of_dvd
    intro k h1 h2 h3
    have h_dvd : k ∣ Fintype.card (Sylow p G) - (Fintype.card (Sylow p G) - 1) := Nat.dvd_sub h3 h2
    have h_k_eq_1 : k = 1 := Nat.eq_one_of_dvd_one <|
      (by omega : Fintype.card (Sylow p G) - (Fintype.card (Sylow p G) - 1) = 1) ▸ h_dvd
    subst h_k_eq_1
    exact Nat.not_prime_one h1
  have h_coprime_full := Nat.Coprime.coprime_dvd_left (card_sylow_mod_card p G hG_p P) h_copr
  have h_mul_le_card : Nat.card P * Fintype.card (Sylow p G) ≤ Nat.card G :=
    Nat.le_of_dvd Nat.card_pos
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime_full h_dvd_both.1 h_dvd_both.2)
  nlinarith only [h_n_gt_pm, h_n_gt_2p, h_mul_le_card,
    Nat.sub_add_cancel (by omega : 2 ≤ Nat.card P)]

open Classical in
lemma fixedBy_sum_eq (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∑ g : G, Fintype.card (MulAction.fixedBy (PhiType p G) g) =
    Fintype.card (PhiType p G) +
      (2 * (Nat.card G - 1) -
       Fintype.card (Sylow p G) * (Nat.card P - 1)) := by
  have h_one : Fintype.card (MulAction.fixedBy (PhiType p G) (1 : G)) =
      Fintype.card (PhiType p G) :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun x ↦ one_smul G x)
  rw [← Finset.insert_erase (Finset.mem_univ (1 : G)),
      Finset.sum_insert (Finset.notMem_erase 1 Finset.univ),
      h_one,
      Finset.sum_congr rfl fun g hg ↦ fixedBy_eq_fixedPoints p G g (Finset.ne_of_mem_erase hg),
      element_fixedPt_sum p G hG_p P]

open Classical in
lemma stab_sum_eq_phi_plus_element (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∑ x : PhiType p G, Nat.card (MulAction.stabilizer G x) =
    Fintype.card (PhiType p G) +
      (2 * (Nat.card G - 1) -
       Fintype.card (Sylow p G) * (Nat.card P - 1)) := by
  rw [Finset.sum_congr rfl fun _ _ ↦ Nat.card_eq_fintype_card,
      show ∑ x : PhiType p G, Fintype.card (MulAction.stabilizer G x) =
        ∑ g : G, Fintype.card (MulAction.fixedBy (PhiType p G) g) by
        simp only [Fintype.card_subtype]
        exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow fun x g ↦ g • x = x,
      fixedBy_sum_eq p G hG_p P]

open Classical in
lemma sylow_orbit_size (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    Fintype.card (MulAction.orbit G
      (⟨sylow_fixedPoint p G hG_p P,
        sylow_fixedPt_mem_Phi p G hG_p P⟩ : PhiType p G)) =
    Fintype.card (Sylow p G) := by
  let x : PhiType p G := ⟨sylow_fixedPoint p G hG_p P, sylow_fixedPt_mem_Phi p G hG_p P⟩
  have h_stab : MulAction.stabilizer G x = Subgroup.normalizer (P : Set G) :=
    SetLike.ext fun g ↦ Subtype.ext_iff.trans
      (Set.ext_iff.mp (stabilizer_sylowFixedPoint_eq_normalizer p G hG_p P) g)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x), h_stab,
    ← Nat.card_congr (Sylow.equivQuotientNormalizer P)]

open Classical in
lemma sylow_fixedPt_phiStab (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (Q : Sylow p G) :
    let x : PhiType p G := ⟨sylow_fixedPoint p G hG_p Q, sylow_fixedPt_mem_Phi p G hG_p Q⟩
    Nat.card (MulAction.stabilizer G x) = Nat.card G / Fintype.card (Sylow p G) := by
  intro x
  exact Eq.symm <| Nat.div_eq_of_eq_mul_left (Fintype.card_pos_iff.mpr ⟨Q⟩) <| by
    rw [mul_comm, ← sylow_orbit_size p G hG_p Q]
    simp only [Nat.card_eq_fintype_card]
    exact (MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x).symm

open Classical in
lemma stab_sum_lower_bound (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G) :
    ∑ x : PhiType p G, Nat.card (MulAction.stabilizer G x) ≥
    Nat.card G + 2 * (Fintype.card (PhiType p G) - Fintype.card (Sylow p G)) := by
  let f : Sylow p G → PhiType p G := fun Q ↦
    ⟨sylow_fixedPoint p G hG_p Q, sylow_fixedPt_mem_Phi p G hG_p Q⟩
  let S : Finset (PhiType p G) := Finset.image f Finset.univ
  have h_inj : Function.Injective f := sylow_fixedPt_injective p G hG_p
  have h_split : ∑ x : PhiType p G, Nat.card (MulAction.stabilizer G x) =
      (∑ x ∈ S, Nat.card (MulAction.stabilizer G x)) +
      ∑ x ∈ Finset.univ \ S, Nat.card (MulAction.stabilizer G x) :=
    (Finset.sum_sdiff (Finset.subset_univ S)).symm.trans (add_comm _ _)
  have h_S : ∑ x ∈ S, Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    have h_dvd : Fintype.card (Sylow p G) ∣ Nat.card G := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (Sylow.equivQuotientNormalizer P)]
      exact Subgroup.card_quotient_dvd_card (Subgroup.normalizer (P : Set G))
    rw [Finset.sum_image (fun _ _ _ _ h ↦ h_inj h)]
    rw [Finset.sum_congr rfl (fun Q _ ↦ sylow_fixedPt_phiStab p G hG_p Q)]
    rw [Finset.sum_const, Finset.card_univ]
    change Fintype.card (Sylow p G) * (Nat.card G / Fintype.card (Sylow p G)) = Nat.card G
    exact Nat.mul_div_cancel' h_dvd
  have h_Sc : 2 * (Fintype.card (PhiType p G) - Fintype.card (Sylow p G)) ≤
      ∑ x ∈ Finset.univ \ S, Nat.card (MulAction.stabilizer G x) := by
    have h_eq : (∑ _ ∈ Finset.univ \ S, 2) =
        2 * (Fintype.card (PhiType p G) - Fintype.card (Sylow p G)) := by
      rw [Finset.sum_const]
      change (Finset.univ \ S).card * 2 = _
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      rw [Finset.card_image_of_injective Finset.univ h_inj]
      rw [Finset.card_univ, Finset.card_univ, mul_comm]
    rw [← h_eq]
    exact Finset.sum_le_sum (fun x _ ↦ phi_stab_card_ge_two p G x)
  rw [h_split, h_S]
  exact Nat.add_le_add_left h_Sc _

open Classical in
/-- The subgroup `G` has exactly two orbits acting on the set `Phi`. -/
lemma num_orbits_eq_two (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) = 2 := by
  have h1 : Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) * Nat.card G =
      Fintype.card (PhiType p G) +
      (2 * (Nat.card G - 1) - Fintype.card (Sylow p G) * (Nat.card P - 1)) := by
    rw [orbit_count_mul_card p G, stab_sum_eq_phi_plus_element p G hG_p P]
  have h2 : Nat.card G + 2 * (Fintype.card (PhiType p G) - Fintype.card (Sylow p G)) ≤
      Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) * Nat.card G := by
    rw [orbit_count_mul_card p G]
    exact stab_sum_lower_bound p G hG_p P
  have h3 := Phi_card_le p G
  have h4 : Fintype.card (Sylow p G) ≤ Fintype.card (PhiType p G) :=
    Fintype.card_le_of_injective _ (sylow_fixedPt_injective p G hG_p)
  have h5 := nonsplit_D_lt_n p G hG_p P hn_p_gt1
  have h_mul1 : Fintype.card (Sylow p G) * (Nat.card P - 1) =
      Fintype.card (Sylow p G) * Nat.card P - Fintype.card (Sylow p G) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  have h_mul2 : (Nat.card P - 2) * Fintype.card (Sylow p G) =
      Fintype.card (Sylow p G) * Nat.card P - 2 * Fintype.card (Sylow p G) := by
    rw [Nat.mul_sub_right_distrib, mul_comm (Nat.card P)]
  have h6 : 3 * Fintype.card (Sylow p G) ≤ Fintype.card (Sylow p G) * Nat.card P := by
    rw [mul_comm 3]
    exact Nat.mul_le_mul_left _ (sylow_card_ge_3 p G hG_p P)
  rw [h_mul1] at h1
  rw [h_mul2] at h5
  apply le_antisymm
  · by_contra h_gt
    have : 3 * Nat.card G ≤
        Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) * Nat.card G :=
      Nat.mul_le_mul_right _ (by exact Nat.lt_of_not_le h_gt)
    omega
  · by_contra h_lt
    have : Fintype.card (Quotient (MulAction.orbitRel G (PhiType p G))) * Nat.card G ≤
        1 * Nat.card G :=
      Nat.mul_le_mul_right _ (by exact Nat.le_of_lt_succ (Nat.lt_of_not_le h_lt))
    omega

end DoubleCounting

noncomputable section PartitionProof

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

omit h_odd in
/-- An identity relating the order of `G` to the geometric parameters (Sylow sizes and orbits). -/
theorem card_eq_pm_z1_np' (G : Subgroup (PGL p)) [Finite G]
    (P : Sylow p G) :
    Nat.card G = Nat.card P * normalizerQuotient p G P *
      Fintype.card (Sylow p G) := by
  rw [normalizerQuotient,
    Nat.mul_div_cancel' (by exact Subgroup.card_dvd_of_le Subgroup.le_normalizer),
    mul_comm (Nat.card _), ← Nat.card_eq_fintype_card,
    Nat.card_congr (Sylow.equivQuotientNormalizer P)]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.normalizer (P : Set G))

theorem branch2_params_of_divisibility
    (pm z₁ n_p : ℕ)
    (hpm_ge3 : pm ≥ 3)
    (hpm_odd : ¬ 2 ∣ pm)
    (hz₁_ge1 : z₁ ≥ 1)
    (hz₁_dvd : z₁ ∣ pm - 1)
    (hn_p_gt1 : n_p > 1)
    (hn_p_cong : pm ∣ n_p - 1)
    (hD_dvd : ((pm - 2) * n_p + 2) ∣ (pm * z₁ * n_p))
    (hz₂_ge2 : pm * z₁ * n_p / ((pm - 2) * n_p + 2) ≥ 2) :
    (pm = 3 ∧ z₁ = 1 ∧ n_p = 4) ∨
    (pm ≥ 5 ∧ z₁ = (pm - 1) / 2 ∧ n_p = pm + 1) ∨
    (z₁ = pm - 1 ∧ n_p = pm + 1) ∨
    (pm = 3 ∧ z₁ = 2 ∧ n_p = 10) := by
  obtain ⟨a, rfl⟩ : ∃ a, n_p = pm * a + 1 := let ⟨v, h⟩ := hn_p_cong; ⟨v, by omega⟩
  have hpm_ge2 : 2 ≤ pm := by omega
  have h_div : 1 + a * (pm - 2) ∣ 2 * z₁ := by
    have h_div1 : pm * (1 + a * (pm - 2)) ∣ pm * z₁ * (pm * a + 1) := by
      convert hD_dvd using 1
      zify [hpm_ge2]; ring
    have h_coprime : Nat.gcd (1 + a * (pm - 2)) (pm * a + 1) ∣ 2 := by
      have h1 : pm * a + 1 - (1 + a * (pm - 2)) = 2 * a := by
        apply Nat.sub_eq_of_eq_add
        zify [hpm_ge2]; ring
      have h2 : Nat.gcd (pm * a + 1) (2 * a) = Nat.gcd (pm * a + 1) 2 := by
        apply Nat.Coprime.gcd_mul_right_cancel_right
        have hg : Nat.gcd (pm * a + 1) a ∣ pm * a + 1 - pm * a :=
          Nat.dvd_sub (Nat.gcd_dvd_left _ _)
            (dvd_trans (Nat.gcd_dvd_right _ _) (dvd_mul_left a pm))
        rw [show pm * a + 1 - pm * a = 1 by rw [add_comm (pm * a) 1, add_tsub_cancel_right],
          Nat.gcd_comm] at hg
        exact Nat.eq_one_of_dvd_one hg
      exact Nat.dvd_trans
        (Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
          (h1 ▸ Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)))
        (h2.symm ▸ Nat.gcd_dvd_right _ _)
    exact mul_comm z₁ 2 ▸ dvd_trans
      (Nat.dvd_mul_gcd_iff_dvd_mul.mpr
        (Nat.dvd_of_mul_dvd_mul_left (by omega) (mul_assoc pm z₁ _ ▸ h_div1)))
      (mul_dvd_mul_left z₁ h_coprime)
  have h_z1_le : 2 * z₁ ≤ 2 * pm - 2 := by
    have := Nat.le_of_dvd (by omega) hz₁_dvd; omega
  have h_le : 1 + a * (pm - 2) ≤ 2 * pm - 2 :=
    le_trans (Nat.le_of_dvd (by omega) h_div) h_z1_le
  have h_a_cases : a = 1 ∨ (a = 3 ∧ pm = 3) := by
    rcases a with _ | _ | _ | _ | a
    · exfalso; revert hn_p_gt1; omega
    · left; rfl
    · exfalso; obtain ⟨k, hk⟩ := h_div
      obtain ⟨x, rfl⟩ : ∃ x, pm = x + 3 := ⟨pm - 3, by omega⟩
      rcases k with _ | _ | k
      · omega
      · omega
      · rw [show 2 * (x + 3) - 2 = 2 * x + 4 by omega] at h_z1_le
        change 2 * z₁ = (1 + 2 * (x + 1)) * (k + 2) at hk
        nlinarith only [h_z1_le, hk]
    · right; exact ⟨rfl, by omega⟩
    · exfalso
      obtain ⟨x, rfl⟩ : ∃ x, pm = x + 3 := ⟨pm - 3, by rw [tsub_add_cancel_of_le hpm_ge3]⟩
      change 1 + (a + 4) * (x + 1) ≤ 2 * x + 4 at h_le
      nlinarith only [h_le]
  rcases h_a_cases with rfl | ⟨rfl, rfl⟩
  · obtain ⟨k, hk⟩ := show pm - 1 ∣ 2 * z₁ from (show 1 + 1 * (pm - 2) = pm - 1 by omega) ▸ h_div
    have hk_le : k ≤ 2 := by
      by_contra h; push Not at h
      have h1 : 3 * (pm - 1) ≤ k * (pm - 1) := Nat.mul_le_mul_right _ h
      have h2 : k * (pm - 1) = 2 * z₁ := by rw [mul_comm, ← hk]
      omega
    rcases k with _ | _ | _ | k
    · omega
    · rcases eq_or_lt_of_le hpm_ge3 with rfl | hpm_gt
      · left; exact ⟨rfl, by omega, rfl⟩
      · right; left; exact ⟨by omega, by omega, by rw [mul_one]⟩
    · right; right; left; exact ⟨by omega, by rw [mul_one]⟩
    · omega
  · have hz1_cases : z₁ = 1 ∨ z₁ = 2 := by omega
    rcases hz1_cases with rfl | rfl
    · exfalso; revert h_div; norm_num
    · right; right; right; exact ⟨rfl, rfl, rfl⟩

open Classical in
/-- A crucial divisibility condition bounding the normaliser quotient and Sylow parameters. -/
theorem nonsplit_torus_divides_geo (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    ((Nat.card P - 2) * Fintype.card (Sylow p G) + 2) ∣ Nat.card G := by
  have h_orbits := num_orbits_eq_two p G hG_p P hn_p_gt1
  obtain ⟨x, hx⟩ : ∃ x : PhiType p G,
      x ∉ MulAction.orbit G
        (⟨sylow_fixedPoint p G hG_p P, sylow_fixedPt_mem_Phi p G hG_p P⟩ : PhiType p G) := by
    by_contra h_all
    revert h_orbits
    rw [Fintype.card_eq_one_iff.mpr
      ⟨⟦⟨sylow_fixedPoint p G hG_p P, sylow_fixedPt_mem_Phi p G hG_p P⟩⟧, fun y ↦ by
      obtain ⟨z, rfl⟩ := Quotient.exists_rep y
      apply Quotient.sound
      by_contra hz
      exact h_all ⟨z, hz⟩⟩]
    omega
  have h_orbit_size : Fintype.card (MulAction.orbit G x) =
      Fintype.card (PhiType p G) - Fintype.card (Sylow p G) := by
    let x₀ : PhiType p G := ⟨sylow_fixedPoint p G hG_p P, sylow_fixedPt_mem_Phi p G hG_p P⟩
    have h_union : Fintype.card (MulAction.orbit G x) + Fintype.card (MulAction.orbit G x₀) =
        Fintype.card (PhiType p G) := by
      rw [Fintype.card_ofFinset, Fintype.card_ofFinset, ← Finset.card_union_of_disjoint]
      · convert Finset.card_univ
        ext y
        refine iff_of_true ?_ (Finset.mem_univ y)
        apply Finset.mem_union.mpr
        let Q := Quotient (MulAction.orbitRel G (PhiType p G))
        have h_univ_eq : ({(⟦x⟧ : Q), ⟦x₀⟧} : Finset Q) = Finset.univ := by
          apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          rw [Finset.card_univ, h_orbits,
            Finset.card_insert_of_notMem
              (fun h_eq_in ↦ hx (Quotient.exact (Finset.mem_singleton.mp h_eq_in))),
            Finset.card_singleton]
        rcases Finset.mem_insert.mp (h_univ_eq ▸ Finset.mem_univ (⟦y⟧ : Q)) with h_eq | h_eq_in
        · left
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, Quotient.exact h_eq⟩
        · right
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ y, Quotient.exact (Finset.mem_singleton.mp h_eq_in)⟩
      · rw [Finset.disjoint_left]
        rintro y hy_x hy_x₀
        obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hy_x).2
        obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hy_x₀).2
        change g • x = y at hg
        change k • x₀ = y at hk
        apply hx
        use g⁻¹ * k
        calc (g⁻¹ * k : G) • x₀ = g⁻¹ • k • x₀ := mul_smul _ _ _
          _ = g⁻¹ • y := by rw [hk]
          _ = x := (eq_inv_smul_iff.mpr hg).symm
    rw [← h_union, sylow_orbit_size p G hG_p P, Nat.add_sub_cancel]
  have h_orbit_size_eq : Fintype.card (PhiType p G) - Fintype.card (Sylow p G) =
      (Nat.card P - 2) * Fintype.card (Sylow p G) + 2 := by
    have h_orbit_size_eq_aux : Fintype.card (PhiType p G) =
        Fintype.card (Sylow p G) * (Nat.card P - 1) + 2 := by
      have h1 := stab_sum_eq_phi_plus_element p G hG_p P
      have h2 := orbit_count_mul_card p G
      have h3 := element_partition_count p G
      have h4 := count_elements_order_p p G hG_p P
      have h5 : 1 ≤ Nat.card G := Nat.card_pos
      rw [h_orbits] at h2
      omega
    have h_P_ge : 2 ≤ Nat.card P := by
      have := sylow_card_ge_3 p G hG_p P
      omega
    have h_P_sub : Nat.card P - 1 = Nat.card P - 2 + 1 :=
      (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two h_P_ge))).symm
    have h_alg : Fintype.card (Sylow p G) * (Nat.card P - 1) =
        (Nat.card P - 2) * Fintype.card (Sylow p G) + Fintype.card (Sylow p G) := by
      rw [mul_comm, h_P_sub, add_mul, one_mul]
    rw [h_orbit_size_eq_aux, h_alg]
    omega
  have h_dvd : Fintype.card (MulAction.orbit G x) ∣ Nat.card G := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)]
    exact Subgroup.card_quotient_dvd_card (MulAction.stabilizer G x)
  exact h_orbit_size_eq ▸ h_orbit_size ▸ h_dvd

theorem nonsplit_torus_ge_two_arith
    (pm z₁ n_p : ℕ) (hpm : pm ≥ 3) (hz₁ : z₁ ≥ 1) (hn_p : n_p ≥ 4)
    (hD_dvd : ((pm - 2) * n_p + 2) ∣ (pm * z₁ * n_p)) :
    pm * z₁ * n_p / ((pm - 2) * n_p + 2) ≥ 2 := by
  rcases pm with _ | _ | pm
  · exfalso; omega
  · exfalso; omega
  obtain ⟨k, hk⟩ := hD_dvd
  change (pm + 2) * z₁ * n_p = (pm * n_p + 2) * k at hk
  change (pm + 2) * z₁ * n_p / (pm * n_p + 2) ≥ 2
  have hc : 0 < pm * n_p + 2 := by omega
  rw [hk, Nat.mul_div_cancel_left _ hc]
  rcases k with rfl | rfl | k
  · rw [mul_zero] at hk
    have h_pos : (pm + 2) * z₁ * n_p > 0 :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    omega
  · rw [Nat.mul_succ, mul_zero, zero_add] at hk
    rcases z₁ with rfl | z₁
    · exfalso; omega
    · have hk_exp : (pm + 2) * z₁ * n_p + pm * n_p + 2 * n_p = pm * n_p + 2 := by
        calc (pm + 2) * z₁ * n_p + pm * n_p + 2 * n_p = (pm + 2) * (z₁ + 1) * n_p := by ring
          _ = pm * n_p + 2 := hk
      omega
  · exact Nat.le_add_left 2 k

/-- Derives the exact geometric parameters (Sylow size `p^m`, number of Sylows `p^m+1`, etc.)
for a subgroup of `PGL(2, K)` whose order is divisible by `p` and which does not fix a point. -/
theorem branch2_params (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    let pm := Nat.card P
    let z₁ := normalizerQuotient p G P
    let n_p := Fintype.card (Sylow p G)
    (pm = 3 ∧ z₁ = 1 ∧ n_p = 4) ∨
    (pm ≥ 5 ∧ z₁ = (pm - 1) / 2 ∧ n_p = pm + 1) ∨
    (z₁ = pm - 1 ∧ n_p = pm + 1) ∨
    (pm = 3 ∧ z₁ = 2 ∧ n_p = 10) := by
  intro pm z₁ n_p
  have hpm_ge3 := sylow_card_ge_3 p G hG_p P
  have hz₁_ge1 : z₁ ≥ 1 := Nat.div_pos (Subgroup.card_le_of_le Subgroup.le_normalizer) Nat.card_pos
  have hz₁_dvd := normalizer_complement_divides_main p G P hG_p
  have hn_p_cong := card_sylow_mod_card p G hG_p P
  have hpm_odd : ¬ 2 ∣ pm := fun h2 ↦ by
    obtain ⟨k, _, hk_eq⟩ := sylow_card_prime_pow p G hG_p P
    have hp_gt2 : p > 2 := Fact.out
    have h2_pow : 2 ∣ p ^ k := by rw [← hk_eq]; exact h2
    rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd 2
      (Nat.prime_two.dvd_of_dvd_pow h2_pow) with h | h <;> omega
  have hn_p_ge : n_p ≥ pm + 1 := by
    obtain ⟨a, ha⟩ := hn_p_cong
    rcases a with _ | a
    · rw [Nat.mul_zero] at ha
      omega
    · have h_le: pm ≤ n_p - 1 := by
        rw [ha]
        exact Nat.le_mul_of_pos_right pm (by exact Nat.succ_pos')
      exact Nat.add_le_of_le_sub (le_of_lt hn_p_gt1) h_le
  have hD_dvd : ((pm - 2) * n_p + 2) ∣ (pm * z₁ * n_p) :=
    card_eq_pm_z1_np' p G P ▸ nonsplit_torus_divides_geo p G hG_p P hn_p_gt1
  exact branch2_params_of_divisibility pm z₁ n_p hpm_ge3 hpm_odd hz₁_ge1 hz₁_dvd
    hn_p_gt1 hn_p_cong hD_dvd
      (nonsplit_torus_ge_two_arith pm z₁ n_p hpm_ge3 hz₁_ge1 (by omega) hD_dvd)

theorem nonsplit_torus_ge_two (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) (P : Sylow p G)
    (hn_p_gt1 : Fintype.card (Sylow p G) > 1) :
    Nat.card G / ((Nat.card P - 2) * Fintype.card (Sylow p G) + 2) ≥ 2 := by
  have hpm_ge3 := sylow_card_ge_3 p G hG_p P
  have hn_p_ge4 : Fintype.card (Sylow p G) ≥ 4 := by
    obtain ⟨a, ha⟩ := card_sylow_mod_card p G hG_p P
    rcases a with _ | a
    · omega
    · nlinarith only [ha, Nat.sub_add_cancel (Nat.le_of_lt hn_p_gt1), hpm_ge3]
  rw [card_eq_pm_z1_np' p G P]
  exact nonsplit_torus_ge_two_arith _ _ _ hpm_ge3
    (Nat.div_pos (Subgroup.card_le_of_le Subgroup.le_normalizer) Nat.card_pos) hn_p_ge4
    (card_eq_pm_z1_np' p G P ▸ nonsplit_torus_divides_geo p G hG_p P hn_p_gt1)

end PartitionProof

end Dickson
