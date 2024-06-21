/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Commensurable
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Finsupp
/-

# Construction of Hecke rings following Shimura

We define Hecke rings abstractly as a ring of formal sums of double cosets `HgH`, with H a subgroup
of a group G, and `g` in a submonoid `Δ` of the commensurator of `H`.

In practice we might have `G = GL₂(ℚ)` (which will also be the relevant commensurator)
and `H = SL₂(ℤ)`, and `Δ = Δ₀(N)` (this is where the condition on the determininat being positive
comes in).

## TODO

show they are rings (associativity is gonna be hard). golf/clean everything

-/
open Commensurable Classical Doset MulOpposite Set

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

lemma ConjAct_smul_coe_Eq (g : G) :  ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x
  refine ⟨ ?_, ?_⟩ <;>  intro h
  · rw [mem_smul_set] at h
    obtain ⟨a, ha⟩ := h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha
    rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      inv_mul_cancel_right, inv_mul_cancel_left, SetLike.mem_coe, ha.1]
  · rw [mem_smul_set]
    use g⁻¹ * x * g
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    group
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      SetLike.mem_coe, Int.reduceNeg, zpow_neg, zpow_one, and_true] at *
    rw [← mul_assoc] at h
    exact h

lemma ConjAct_smul_elt_eq (h : H) : ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [ConjAct_smul_coe_Eq,Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this
  norm_cast at *


/-maybe call this commensurable pair??-/
/-- This is a pair cosisting of a subgroup `H` and a submonoid `Δ` of some group, such that
`H ≤ Δ ≤ commensurator H`. -/
structure ArithmeticGroupPair (G : Type*) [Group G]  where
  H : Subgroup G
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/--Given an arithmetic pair `P`, consisting of a subgroup `H` of `G` and a submonoid `Δ` of
the commensurator of H, this is  the data of a set in `G` equal to some double coset
`HgH`, with `g : Δ`. -/
structure T' (P : ArithmeticGroupPair G) where
  set : Set G
  eql : ∃ elt : P.Δ,  set = Doset.doset (elt : G) P.H P.H

@[ext]
lemma ext (P : ArithmeticGroupPair G) (D1 D2 : T' P) (h : D1.set = D2.set):
  D1 = D2 := by
  cases D1
  cases D2
  simp at *
  exact h


/--Make an element of `T' H Δ` given an element `g : Δ`, i.e make `HgH`.  -/
def T_mk (P : ArithmeticGroupPair G) (g : P.Δ) : T' P := ⟨doset g P.H P.H, g, rfl⟩

/--The multiplicative identity. -/
def T_one (P : ArithmeticGroupPair G) : T' P := T_mk P (1 : P.Δ)

lemma smul_eq_mul_singleton (s : Set G) (g : G) : g • s = {g} * s := by
    rw [← Set.singleton_smul]
    exact rfl

lemma set_eq_iUnion_leftCosets (K : Subgroup G) (hK : K ≤ H) : (H : Set G) = ⋃ (i : H ⧸ K.subgroupOf H),
    (i.out' : G) • (K : Set G) := by
  ext a
  constructor
  · intro ha
    simp only [mem_iUnion]
    use (⟨a, ha⟩ : H)
    have := QuotientGroup.mk_out'_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    obtain ⟨h, hh⟩ := this
    rw [hh]
    simp
    refine mem_smul_set.mpr ?h.intro.a
    have : (h : H) • (K : Set G) = K := by
      apply smul_coe_set
      simp
      refine Subgroup.mem_subgroupOf.mp ?ha.a
      simp only [SetLike.coe_mem]
    use h⁻¹
    simp
    refine Subgroup.mem_subgroupOf.mp ?h.a
    exact SetLike.coe_mem h
  · intro ha
    simp only [mem_iUnion] at ha
    obtain ⟨i, hi⟩ := ha
    have :  Quotient.out' i • (K : Set G) ⊆ (H : Set G) := by
      intro a ha
      rw [mem_smul_set] at ha
      obtain ⟨h, hh⟩ := ha
      rw [← hh.2]
      simp
      rw [show  Quotient.out' i • h =  Quotient.out' i * h by rfl]
      apply mul_mem
      simp
      apply hK hh.1
    exact this hi

lemma ConjAct_mul_self_eq_self (g : G) : ((ConjAct.toConjAct g • H) : Set G) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  rw [ConjAct_smul_coe_Eq , show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) = {g} * ↑H *
      (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by simp_rw [← mul_assoc],Set.singleton_mul_singleton ]
  conv =>
    enter [1,1,2]
    simp
  conv =>
    enter [1,1]
    rw [mul_assoc, coe_mul_coe H]

lemma inter_mul_conjact_eq_conjact (g : G) : ((H : Set G) ∩ (ConjAct.toConjAct g • H)) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  have := Set.inter_mul_subset (s₁ := (H : Set G)) (s₂ := (ConjAct.toConjAct g • H))
    (t := (ConjAct.toConjAct g • H))
  apply Subset.antisymm
  · apply le_trans this
    simp only [ConjAct_mul_self_eq_self, le_eq_subset, inter_subset_right]
  · refine subset_mul_right (ConjAct.toConjAct g • (H : Set G)) ?h₂.hs
    simp only [mem_inter_iff, SetLike.mem_coe]
    refine ⟨  Subgroup.one_mem H, Subgroup.one_mem (ConjAct.toConjAct g • H)⟩

lemma mul_singleton_cancel (g : G) (K L : Set G)  (h:  K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2
  simpa using h2

lemma doset_eq_iUnion_leftCosets (g : G) : doset g H H =
  ⋃ (i : (H ⧸ (ConjAct.toConjAct g • H).subgroupOf H)), (i.out' * g) • (H : Set G) := by
  rw [doset]
  have := set_eq_iUnion_leftCosets H (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this) ((ConjAct.toConjAct g • H) : Set G)
  rw [iUnion_mul, inter_comm] at h2
  apply mul_singleton_cancel g⁻¹
  rw [ConjAct_smul_coe_Eq ] at *
  simp_rw [← mul_assoc] at h2
  rw [h2]
  have : (Subgroup.map H.subtype ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H := by
    simp
  rw [this]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
    ((i.out') : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out' i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjact_eq_conjact H g
    rw [ConjAct_smul_coe_Eq ] at this
    have hr : ((i.out' ) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (i.out' : G) • (((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹}) := by
      simp_rw [smul_mul_assoc]
    rw [hr]
    simp_rw [← mul_assoc] at this
    conv =>
      enter [1,2]
      rw [this]
    simp_rw [smul_eq_mul_singleton, ← singleton_mul_singleton, ← mul_assoc]
  have := iUnion_congr h1
  convert this
  rw [iUnion_mul]

lemma doset_mul_doset_left (g h : G) :
    (doset g H H) * (doset h H H) = (doset (g) H H) * {h} * H := by
  simp_rw [doset, show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
    H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H]

lemma doset_mul_doset_right (g h : G) :
    (doset g H H) * (doset h H H) = H * {g} * (doset (h) H H) := by
  simp_rw [doset, show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
    H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H, ← mul_assoc]

lemma doset_mul_doset_eq_union_doset (g h : G) :
    (doset (g : G) (H : Set G) H) * doset (h : G) (H : Set G) H =
        ⋃ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H), doset (g * i.out' * h : G) H H := by
  rw [doset_mul_doset_right, doset_eq_iUnion_leftCosets, Set.mul_iUnion]
  simp_rw [doset]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
    (H : Set G) * {g} * (↑(Quotient.out' i) * h) • ↑H = ↑H * {g * ↑(Quotient.out' i) * h} * ↑H := by
    intro i
    rw [smul_eq_mul_singleton, show (H : Set G) * {g} * ({↑(Quotient.out' i) * h} * ↑H) =
      H * {g} * {↑(Quotient.out' i) * h} * ↑H by simp_rw [← mul_assoc],
        ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton]
    simp_rw [← mul_assoc]
  apply iUnion_congr h1


/--Finite linear combinations of double cosets `HgH` with `g` in the commensurator of `H`. -/
def 𝕋 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (T' P) Z

variable  (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z]

noncomputable instance (P : ArithmeticGroupPair G) (D : T' P) :
    Fintype (P.H ⧸ ((ConjAct.toConjAct (D.eql.choose : G)) • P.H).subgroupOf P.H) := by
  apply Subgroup.fintypeOfIndexNeZero (P.h₁ D.eql.choose.2 ).1

lemma rep_mem (a b : Δ) (i : H) : (a : G) * i * b ∈ Δ := by
  rw [mul_assoc]
  apply Submonoid.mul_mem _ (a.2) (Submonoid.mul_mem _ (h₀ i.2) b.2)

/-Test func. not needed
noncomputable def mul' (D1 D2 : T' H Δ) : 𝕋 H Δ :=
    ((∑ (i : H ⧸ (ConjAct.toConjAct (D2.elt : G) • H).subgroupOf H),
      Finsupp.single (T_mk H Δ D1.h₀ D1.h₁ ⟨((D1.elt : G) * (i.out' : G) * (D2.elt : G)),
        rep_mem H Δ D1.h₀ D1.elt D2.elt i.out'⟩) (1 : ℤ) : (T' H Δ) →₀ ℤ))
-/

noncomputable instance addCommMonoid : AddCommMonoid (𝕋 P Z) :=
  inferInstanceAs (AddCommMonoid ((T' P) →₀ Z))

/-- Take two doble cosets `HgH` and `HhH`, we define `HgH`*`HhH` by the sum over the double cosets
in `HgHhH`, i.e., if `HgHhH = ⋃ i, HiH` , then `HgH * HhH = ∑ i, HiH` and then extends
linearly to get multiplication on the finite formal sums of double cosets. -/
noncomputable instance (P : ArithmeticGroupPair G) : Mul (𝕋 P Z) where
 mul f g := Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (b₁ * b₂ : Z)) : (T' P) →₀ Z))

lemma mul_def (f g : 𝕋 P Z) : f * g = Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ =>
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (b₁ * b₂ : Z)) : (T' P) →₀ Z)) := rfl

noncomputable abbrev T_single (a : T' P) (b : Z) : (𝕋 P Z) := Finsupp.single a b

lemma 𝕋_mul_singleton (D1 D2 : (T' P)) (a b : Z) :
  (T_single P Z D1 a) * (T_single P Z D2 b) =
    ((∑ (i : P.H ⧸ (ConjAct.toConjAct (D2.eql.choose : G) • P.H).subgroupOf P.H),
      Finsupp.single (T_mk P ⟨((D1.eql.choose : G) * (i.out' : G) * (D2.eql.choose : G)),
        rep_mem P.H P.Δ P.h₀ D1.eql.choose D2.eql.choose i.out'⟩) (a * b : Z)) : (T' P) →₀ Z) := by
  rw [T_single, mul_def]
  simp only [mul_zero, Finsupp.single_zero, Finset.sum_const_zero, Finsupp.sum_single_index,
    zero_mul, Int.cast_mul]

open Finsupp

noncomputable instance nonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (𝕋 P Z) :=
  {  (addCommMonoid P Z) with
    left_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f) (funext₂ fun a₁ b₁ => Finsupp.sum_add_index ?_ ?_))
        ?_ <;>
        simp
      intro D1 _ a b
      rw [← Finset.sum_add_distrib ]
      congr
      group
      simp only [Finsupp.single_add]
    right_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index ?_ ?_) ?_ <;>
        simp
      intro D1 _ a b
      rw [← Finsupp.sum_add]
      apply congr_arg
      ext i
      rw [← Finset.sum_add_distrib ]
      congr
      group
      simp only [Finsupp.single_add]
    zero_mul := fun f => by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero }


noncomputable instance nonUnitalSemiring : NonUnitalSemiring (𝕋 P Z) :=
  {nonUnitalNonAssocSemiring P Z  with
    mul_assoc := fun f g h => by sorry} -- known in the 1980s so Kevin can't complain.


/- The identity is `H1H`. -/
noncomputable instance one : One (𝕋 P Z) := ⟨T_single P Z (T_one P) (1 : Z)⟩

theorem one_def : (1 : (𝕋 P Z)) = T_single P Z (T_one P) (1 : Z):=
  rfl

noncomputable instance nonAssocSemiring : NonAssocSemiring (𝕋 P Z) :=
  { nonUnitalNonAssocSemiring P Z with
    natCast := fun n => T_single P Z (T_one P) (n : Z)
    natCast_zero := by simp
    natCast_succ := fun _ => by simp; rfl
    one_mul :=  fun f => by sorry
      /-
      simp [one_def, mul_def, one_mul, zero_mul, single_zero,
        Finset.sum_const_zero, sum_zero, sum_single_index, T_one, T_mk]

      have := Finsupp.sum_single  f
      nth_rw 2 [← this]
      congr
      ext D z v
      rw [Finsupp.finset_sum_apply]
      simp_rw [Finsupp.single_apply]
      by_cases h : D = v
      rw [if_pos h]
      have h1 : D.elt = v.elt := by
        rw [h]
      have h2 : D.set = v.set := by
        rw [h]
      simp_rw [h1]
      sorry
      sorry
      -/








    mul_one :=sorry }

noncomputable instance semiring : Semiring (𝕋 P Z) :=
  {HeckeRing.nonUnitalSemiring P Z,
    (HeckeRing.nonAssocSemiring P Z) with}

noncomputable instance addCommGroup : AddCommGroup (𝕋 P Z) :=
  Finsupp.instAddCommGroup

noncomputable instance nonAssocRing : NonAssocRing (𝕋 P Z) :=
  { HeckeRing.addCommGroup P Z,
    (HeckeRing.nonAssocSemiring P Z) with
    intCast := sorry
    intCast_ofNat := sorry
    intCast_negSucc := sorry }

noncomputable instance ring : Ring (𝕋 P Z) :=
    {HeckeRing.nonAssocRing P Z, HeckeRing.semiring P Z with }


end HeckeRing
