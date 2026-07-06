/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.Basic

@[expose] public section

/-!
# Coset and quotient helper lemmas

This file contains auxiliary equivalences and finite-sum decompositions for left
and right cosets. These lemmas are used in the induced-character and double-coset
arguments.
-/

universe u
variable {G : Type u} [Group G]

namespace Subgroup

open Classical in
/--
The fibre of the quotient map `G → G / H` over a right coset is equivalent to
`H`.

The equivalence sends an element `x` in the fibre over the coset represented by
`x₀` to `x * x₀⁻¹ ∈ H`.
-/
noncomputable def rightRelFiberEquiv
    (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    {x : G // Quotient.mk (QuotientGroup.rightRel H) x = q} ≃ H := by
  let x0 : G := q.out
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    refine ⟨x.1 * x0⁻¹, ?_⟩
    have hxπ :
        Quotient.mk (QuotientGroup.rightRel H) x.1
          = Quotient.mk (QuotientGroup.rightRel H) x0 := by
      simpa [x0] using x.2.trans (Quotient.out_eq q).symm
    have h_rel : QuotientGroup.rightRel H x.1 x0 := Quotient.exact hxπ
    have hxH' : x0 * x.1⁻¹ ∈ H := by
      simpa [QuotientGroup.rightRel_apply] using h_rel
    have : x.1 * x0⁻¹ = (x0 * x.1⁻¹)⁻¹ := by
      group
    rw [this]
    exact H.inv_mem hxH'
  · intro h
    refine ⟨(h : G) * x0, ?_⟩
    have h_rel : QuotientGroup.rightRel H ((h : G) * x0) x0 := by
      rw [QuotientGroup.rightRel_apply]
      simp only [mul_inv_rev, mul_inv_cancel_left, H.inv_mem h.2]
    calc
      Quotient.mk (QuotientGroup.rightRel H) ((h : G) * x0)
          = Quotient.mk (QuotientGroup.rightRel H) x0 := Quotient.sound h_rel
      _ = q := Quotient.out_eq q
  · intro x
    ext
    simp only [inv_mul_cancel_right, x0]
  · intro h
    ext
    simp only [mul_assoc, mul_inv_cancel, mul_one, x0]

open Classical in
/--
If a function is constant on every fibre of the right-coset quotient map
`G → G / H`, then its sum over `G` is the sum over right cosets multiplied by
`|H|`.

The constant value on a coset is evaluated at the chosen representative
`q.out`.
-/
lemma sum_of_right_coset_constant {k : Type*} [Semiring k] [Fintype G]
    (H : Subgroup G) (f : G → k)
    (h_const : ∀ (x : G) (h : H), f ((h : G) * x) = f x) :
    ∑ x : G, f x
      = (Nat.card H : k) * ∑ q : Quotient (QuotientGroup.rightRel H), f (q.out) := by
  let π : G → Quotient (QuotientGroup.rightRel H) := Quotient.mk _
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (π x)) f]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  let fiber := {x : G // π x = q}
  let e : fiber ≃ H := Subgroup.rightRelFiberEquiv H q
  have h_inner_const : ∀ x : fiber, f x.1 = f q.out := by
    intro x
    have hx : (e x : G) * q.out = x.1 := congrArg Subtype.val (e.left_inv x)
    simpa [hx] using h_const q.out (e x)
  rw [Finset.sum_congr rfl (fun x hx => h_inner_const ⟨x, (Finset.mem_filter.mp hx).2⟩)]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Fintype.card_coe, ← Fintype.card_eq_nat_card]
  exact congrArg (fun n : ℕ => (n : k)) (by simpa [fiber] using Fintype.card_congr e)

open Classical in
/--
If a function is constant on every left coset of `H`, then its sum over `G` is
the sum over left cosets multiplied by `|H|`.

This is the left-coset analogue of `Subgroup.sum_of_right_coset_constant`.
-/
lemma sum_of_left_coset_constant {k : Type*} [Semiring k] [Fintype G]
    (H : Subgroup G) (f : G → k)
    (h_const : ∀ (x : G) (h : H), f (x * (h : G)) = f x) :
    ∑ x : G, f x = (Nat.card H : k) * ∑ q : G ⧸ H, f q.out := by
  let π : G → G ⧸ H := Quotient.mk _
  rw [← Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_univ (π x)) f]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  let fiber := {x : G // π x = q}
  -- The core bijection between a left coset fiber and the subgroup H
  let e : fiber ≃ H :=
  { toFun := fun x => ⟨q.out⁻¹ * x.1, by
      have h_eq : ⟦q.out⟧ = ⟦x.1⟧ :=
        calc ⟦q.out⟧ = q := Quotient.out_eq q
             _ = ⟦x.1⟧ := x.property.symm
      exact QuotientGroup.eq.mp h_eq⟩
    invFun := fun h => ⟨q.out * (h : G), by
      change ⟦q.out * (h : G)⟧ = q
      rw [← Quotient.out_eq q, QuotientGroup.eq]
      simp only [Quotient.out_eq, mul_inv_rev, inv_mul_cancel_right, inv_mem_iff, SetLike.coe_mem]⟩
    left_inv := fun x => Subtype.ext (by dsimp; group)
    right_inv := fun h => Subtype.ext (by dsimp; group) }
  have h_inner_const : ∀ x : fiber, f x.1 = f q.out := by
    intro x
    let h : H := e x
    have hx : q.out * (h : G) = x.1 := congrArg Subtype.val (e.left_inv x)
    have h_eq := h_const q.out h
    rw [hx] at h_eq
    exact h_eq
  rw [Finset.sum_congr rfl (fun x hx => h_inner_const ⟨x, (Finset.mem_filter.mp hx).2⟩)]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Fintype.card_coe, ← Fintype.card_eq_nat_card]
  exact congrArg (fun n : ℕ => (n : k)) (by simpa [fiber] using Fintype.card_congr e)

end Subgroup

namespace QuotientGroup

/--
The chosen representative of the right coset of `h` is right-related to `h`.
-/
lemma rightRel_out_mk
    (I : Subgroup G)
    (h : G) :
    QuotientGroup.rightRel I
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel I) h))
      h := by
  exact Quotient.exact
    (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel I) h))

/--
For the chosen representative of the right coset of `h`, the element
`h * out(mk h)⁻¹` lies in the subgroup.
-/
lemma rightRel_mk_mul_out_inv_mem
    (I : Subgroup G)
    (h : G) :
    h * (Quotient.out (Quotient.mk (QuotientGroup.rightRel I) h))⁻¹ ∈ I := by
  have hrel := rightRel_out_mk (G := G) I h
  rw [QuotientGroup.rightRel_apply] at hrel
  exact hrel

/--
For the chosen representative of the right coset of `h`, the element
`out(mk h) * h⁻¹` lies in the subgroup.
-/
lemma rightRel_out_mul_mk_inv_mem
    (I : Subgroup G)
    (h : G) :
    Quotient.out (Quotient.mk (QuotientGroup.rightRel I) h) * h⁻¹ ∈ I := by
  have hrel :
      h * (Quotient.out (Quotient.mk (QuotientGroup.rightRel I) h))⁻¹ ∈ I :=
      rightRel_mk_mul_out_inv_mem (G := G) I h
  have hinv :
      (h * (Quotient.out (Quotient.mk (QuotientGroup.rightRel I) h))⁻¹)⁻¹ ∈ I :=
    I.inv_mem hrel
  simpa [mul_inv_rev] using hinv

/--
Two elements are equivalent for the right-coset relation modulo `H` iff
`a * b⁻¹ ∈ H`.
-/
lemma rightRel_iff_mul_inv_mem (H : Subgroup G) (a b : G) :
    QuotientGroup.rightRel H a b ↔ a * b⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh⟩
    have hh' : (h : G) * b = a := by
      simpa [MulAction.subgroup_smul_def] using hh
    have : (h : G) = a * b⁻¹ := by
      have := congrArg (fun t => t * b⁻¹) hh'
      simpa [mul_assoc] using this
    simp only [← this, h.property]
  · intro hab
    refine ⟨⟨a * b⁻¹, hab⟩, ?_⟩
    simp [MulAction.subgroup_smul_def, mul_assoc]

/--
For `H : Subgroup K`, quotienting `G` by the image of `H` in `G` is equivalent
to first quotienting by `K` and then quotienting `K` by `H`.

More precisely,
`G ⧸ H.map K.subtype ≃ Σ (_ : G ⧸ K), K ⧸ H`.
-/
noncomputable def equivSigmaQuotient {K : Subgroup G} (H : Subgroup K) :
    (G ⧸ H.map K.subtype) ≃ Σ (_q : G ⧸ K), K ⧸ H :=
  (Subgroup.quotientEquivProdOfLE (Subgroup.map_subtype_le H)).trans <|
    (Equiv.prodCongr (Equiv.refl _) (Subgroup.quotientEquivOfEq (
        Subgroup.subgroupOf_map_subtype_eq_self H))).trans (Equiv.sigmaEquivProd _ _).symm

/--
Right cosets of the comap subgroup `Q.comap π` in `G` are equivalent to right
cosets of `Q` in `G ⧸ K`, where `π : G →* G ⧸ K` is the quotient map.
-/
noncomputable def rightRel_comap_quotient_equiv
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) :
    let π : G →* G ⧸ K := QuotientGroup.mk' K
    Quotient (QuotientGroup.rightRel (Q.comap π)) ≃
      Quotient (QuotientGroup.rightRel Q) := by
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  let f :
      Quotient (QuotientGroup.rightRel (Q.comap π)) →
        Quotient (QuotientGroup.rightRel Q) :=
    Quotient.map π (by
      intro x y hxy
      change QuotientGroup.rightRel (Q.comap π) x y at hxy
      change QuotientGroup.rightRel Q (π x) (π y)
      rw [rightRel_iff_mul_inv_mem] at hxy
      rw [rightRel_iff_mul_inv_mem]
      change π (x * y⁻¹) ∈ Q
      simpa [map_mul, map_inv] using hxy)
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        apply Quotient.sound
        change QuotientGroup.rightRel (Q.comap π) x y
        have hrel : QuotientGroup.rightRel Q (π x) (π y) := by
          apply Quotient.exact
          simpa [f] using hab
        rw [rightRel_iff_mul_inv_mem]
        change π (x * y⁻¹) ∈ Q
        rw [rightRel_iff_mul_inv_mem] at hrel
        simpa [map_mul, map_inv] using hrel
  · intro q
    induction q using Quotient.inductionOn with
    | h y =>
      obtain ⟨x, hx⟩ := Quotient.exists_rep y
      refine ⟨Quotient.mk (QuotientGroup.rightRel (Q.comap π)) x, ?_⟩
      change Quotient.mk (QuotientGroup.rightRel Q) (π x) =
        Quotient.mk (QuotientGroup.rightRel Q) y
      have hxπ : π x = y := by
        simpa [π, QuotientGroup.mk'_apply] using hx
      rw [hxπ]

end QuotientGroup
