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
# Conjugacy and centralizers

This file contains helper lemmas about conjugacy, centralizers, conjugacy
classes, and the orbit-stabilizer formula for the conjugation action.
-/

universe u
variable {G : Type u} [Group G]

/--
Taking inverses preserves conjugacy: `a` is conjugate to `b` iff `a⁻¹` is
conjugate to `b⁻¹`.
-/
lemma IsConj.inv {a b : G} : IsConj a b ↔ IsConj a⁻¹ b⁻¹  := by
  simp only [isConj_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩  := h
    use c
    rw[← hc, conj_inv]
  · intro h
    obtain ⟨c, hc⟩  := h
    use c
    have h := congr_arg (fun x => x⁻¹) hc
    simp only [mul_inv_rev, inv_inv, ← mul_assoc] at h
    exact h

/--
Conjugacy in a subgroup implies conjugacy in the ambient group.
-/
lemma IsConj.of_subgroup {H : Subgroup G} {x y : H} (h : IsConj x y) :
    IsConj (x : G) (y : G) := by
  rcases h with ⟨c, hc⟩
  use Units.map H.subtype c
  simp only [Units.coe_map, Subgroup.subtype_apply]
  unfold SemiconjBy at *
  -- Now norm_cast can see "↑(c * x) = ↑(y * c)" and pull the arrows out
  norm_cast

/-- Conjugate elements have the same order. -/
lemma IsConj.orderOf_eq
   {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  rw [isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  apply SemiconjBy.orderOf_eq c
  simp only [SemiconjBy, ← hc, inv_mul_cancel_right]

/--
The chosen representative of a conjugacy class maps back to that conjugacy
class.
-/
@[simp]
lemma ConjClasses.mk_out (C : ConjClasses G) :
    ConjClasses.mk C.out = C := by
      apply Quotient.out_eq C

namespace Subgroup

/--
The centralizer of the singleton `{1}` is the whole group.
-/
lemma centralizer_singleton_one :
    Subgroup.centralizer ({1} : Set G) = ⊤ := by
  ext x
  simp [Subgroup.mem_centralizer_iff]

/--
The centralizer of `g⁻¹` is the same as the centralizer of `g`.
-/
lemma centralizer_singleton_inv (g : G) :
    Subgroup.centralizer ({g⁻¹} : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

lemma card_centralizer_inv (g : G) :
    Nat.card (Subgroup.centralizer ({g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  rw [Subgroup.centralizer_singleton_inv]


/--
Conjugation by `x` gives an equivalence between the centralizer of
`x⁻¹ * g * x` and the centralizer of `g`.
-/
noncomputable def centralizerEquiv (x g : G) :
    centralizer {x⁻¹ * g * x} ≃ centralizer {g} := by
  let φ : G ≃* G := MulAut.conj x
  refine
  { toFun := ?toFun
    , invFun := ?invFun
    , left_inv := ?left_inv
    , right_inv := ?right_inv }
  · intro h
    rcases h with ⟨h, hh⟩
    refine ⟨φ h, ?_⟩
    rw [mem_centralizer_singleton_iff] at hh
    have hx : (x * h * x⁻¹) * g = g * (x * h * x⁻¹) := by
          have := congrArg (fun t => x * t * x⁻¹) hh
          group at this
          group
          exact this
    rw [mem_centralizer_singleton_iff]
    exact SemiconjBy.eq hx
  · intro h
    rcases h with ⟨h, hh⟩
    refine ⟨φ.symm h, ?_⟩
    rw [mem_centralizer_singleton_iff] at hh
    have hx : (x⁻¹ * h * x) * (x⁻¹ * g * x) = (x⁻¹ * g * x) * (x⁻¹ * h * x) := by
      group
      rw[mul_assoc (b:= h), hh]
      simp[mul_assoc]
    rw [mem_centralizer_singleton_iff]
    exact hx
  · intro h; simp [φ, ← mul_assoc]
  · intro h; simp [φ, ← mul_assoc]

/--
Conjugate elements have equivalent centralizers.
-/
noncomputable def centralizerEquivOfIsConj
    {g h : G} (h_conj : IsConj g h) :
    centralizer ({g} : Set G) ≃
      centralizer ({h} : Set G) := by
  let c := Classical.choose h_conj
  have hc := Classical.choose_spec h_conj
  have hh :
      h = (c : G) * g * (c : G)⁻¹ := by
    calc
      h = (h * (c : G)) * (c : G)⁻¹ := by
        simp
      _ = ((c : G) * g) * (c : G)⁻¹ := by
        rw [hc.eq]
      _ = (c : G) * g * (c : G)⁻¹ := by
        rw [mul_assoc]
  rw[hh]
  simpa only [inv_inv] using
    (centralizerEquiv ((c : G)⁻¹) g).symm

/--
Conjugate elements have centralizers of the same cardinality.
-/
lemma card_centralizer_of_isConj
    {g h : G} (h_conj : IsConj g h) :
    Nat.card (centralizer ({g} : Set G)) =
      Nat.card (centralizer ({h} : Set G)) :=
  Nat.card_congr (centralizerEquivOfIsConj h_conj)

open Classical in
/--
A finite sum of the constant value `orderOf a` over the centralizer of `a`.

The left-hand side is written as a sum over all of `G` with an `if` selecting
the centralizer.
-/
lemma sum_ite_mem_centralizer_mul (k : Type*) [Semiring k]
    [Fintype G] {a : G} :
    (∑ x : G,
        (if x ∈ centralizer ({a} : Set G) then (orderOf a : k) else 0))
      =
    (Nat.card (centralizer ({a} : Set G)) : k) * (orderOf a : k) := by
  calc
    (∑ x, if x ∈ centralizer {a} then (orderOf a : k) else 0)
      = ∑ x ∈ Finset.univ.filter (fun x => x ∈ centralizer {a}), (orderOf a : k) := by
          rw [Finset.sum_filter]
    _ = (Finset.univ.filter (fun x => x ∈ centralizer {a})).card • (orderOf a : k) := by
          rw [Finset.sum_const]
    _ = ((Finset.univ.filter (fun x => x ∈ centralizer {a})).card : k) * (orderOf a : k) := by
          rw [nsmul_eq_mul]
    _ = (Nat.card (centralizer ({a} : Set G)) : k) * (orderOf a : k) := by
          congr 1
          have h_card : (Finset.univ.filter (fun x => x ∈ centralizer {a})).card =
                        Nat.card ↥(centralizer {a}) := by
            rw [Nat.card_eq_fintype_card]
            exact (Fintype.card_subtype (fun x => x ∈ centralizer {a})).symm
          rw [h_card]


/--
An element `x : G` such that `x⁻¹ * u * x ∈ H` is equivalently a fixed point of
the action of `u` on `G ⧸ H`, together with an element of `H`.

The map sends `x` to the coset of `x` and the correction term obtained by
comparing `x` with the chosen representative of that coset.
-/
noncomputable def conjMemEquiv_fixedPointsProd
  (H : Subgroup G) (u : G) :
    { x : G // x⁻¹ * u * x ∈ H } ≃ { c : G ⧸ H // u • c = c } × H where
  toFun x :=
    let q := QuotientGroup.mk x.val
    have hq : u • q = q := by
      apply QuotientGroup.eq.mpr
      change (u * x.val)⁻¹ * x.val ∈ H
      have h_eq : (u * x.val)⁻¹ * x.val = (x.val⁻¹ * u * x.val)⁻¹ := by group
      rw [h_eq]
      exact H.inv_mem x.property
    let rep := Quotient.out q
    have h_rep_eq : QuotientGroup.mk rep = q := Quotient.out_eq' q
    have h_rep : rep⁻¹ * x.val ∈ H := by
      apply QuotientGroup.eq.mp
      rw [h_rep_eq]
    (⟨q, hq⟩, ⟨rep⁻¹ * x.val, h_rep⟩)
  invFun p :=
    let q := p.1.val
    let rep := Quotient.out q
    let h_val := p.2.val
    have h_rep_eq : QuotientGroup.mk rep = q := Quotient.out_eq' q
    have hx : (rep * h_val)⁻¹ * u * (rep * h_val) ∈ H := by
      have h_rep_u_inv : (u * rep)⁻¹ * rep ∈ H := by
        apply QuotientGroup.eq.mp
        calc QuotientGroup.mk (u * rep)
          _ = u • (QuotientGroup.mk rep) := rfl
          _ = u • q := by rw [h_rep_eq]
          _ = q := p.1.property
          _ = QuotientGroup.mk rep := h_rep_eq.symm
      have h_rep_u : rep⁻¹ * u * rep ∈ H := by
        have h1 := H.inv_mem h_rep_u_inv
        have h2 : ((u * rep)⁻¹ * rep)⁻¹ = rep⁻¹ * u * rep := by group
        rw [h2] at h1
        exact h1
      have h_eq : (rep * h_val)⁻¹ * u * (rep * h_val)
          = h_val⁻¹ * (rep⁻¹ * u * rep) * h_val := by group
      rw [h_eq]
      exact H.mul_mem (H.mul_mem (H.inv_mem p.2.property) h_rep_u) p.2.property
    ⟨rep * h_val, hx⟩
  left_inv x := by
    ext
    dsimp
    exact mul_inv_cancel_left _ _
  right_inv p := by
    ext
    · dsimp
      let q := p.1.val
      let rep := Quotient.out q
      have h_rep_eq : QuotientGroup.mk rep = q := Quotient.out_eq' q
      have h_mk_eq : QuotientGroup.mk (rep * p.2.val) = q := by
        calc QuotientGroup.mk (rep * p.2.val)
          _ = QuotientGroup.mk rep := by
            apply QuotientGroup.eq.mpr
            have h_inv_mul : rep⁻¹ * (rep * p.2.val) = p.2.val := by group
            rw [← h_inv_mul]
            simp only [inv_mul_cancel_left, mul_inv_rev, inv_mul_cancel_right,
              inv_mem_iff, SetLike.coe_mem]
          _ = q := h_rep_eq
      exact h_mk_eq
    · dsimp
      simp only [SetLike.coe_mem, QuotientGroup.mk_mul_of_mem,
        Quotient.out_eq, inv_mul_cancel_left]

end Subgroup

/--
For the conjugation action of a finite group on itself, the size of the
conjugacy class of `g` times the size of the centralizer of `g` is the order of
the group.
-/
lemma MulAction.card_conjClass_mul_card_centralizer [Fintype G] (g : G) :
    (Nat.card (MulAction.orbit (ConjAct G) g)) *
        (Nat.card ↥(Subgroup.centralizer ({g} : Set G)))
      = Fintype.card G := by
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  change
    (MulAction.orbit (ConjAct G) g).ncard *
        Nat.card ↥(MulAction.stabilizer (ConjAct G) g)
      = Fintype.card G
  haveI : Fintype ↥(MulAction.orbit (ConjAct G) g) :=
    Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.stabilizer (ConjAct G) g) :=
    Fintype.ofFinite _
  have horbit :
      (MulAction.orbit (ConjAct G) g).ncard =
        Fintype.card ↥(MulAction.orbit (ConjAct G) g) := by
    change
      Nat.card ↥(MulAction.orbit (ConjAct G) g) =
        Fintype.card ↥(MulAction.orbit (ConjAct G) g)
    exact Nat.card_eq_fintype_card
  have hstab :
      Nat.card ↥(MulAction.stabilizer (ConjAct G) g) =
        Fintype.card ↥(MulAction.stabilizer (ConjAct G) g) := by
    exact Nat.card_eq_fintype_card
  rw [horbit, hstab]
  exact
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) g
