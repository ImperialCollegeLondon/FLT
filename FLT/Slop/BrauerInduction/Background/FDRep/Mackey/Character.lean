/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Mackey.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Orthogonality
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Induced
public import FLT.Slop.BrauerInduction.Background.Fintype.Basic

/-! # Character computation for Mackey Hom terms

This file computes the dimensions of the Mackey Hom terms introduced in
`FDRep.Mackey.Basic` using character inner products.

The final result expresses

`finrank End(Ind_I^G σ)`

as a sum over double cosets of the dimensions of the corresponding Mackey Hom
terms. -/

@[expose] public section

namespace Slop
open Slop

open CategoryTheory BigOperators

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The dimension of a Mackey Hom term, cast to `k`, as the character inner
product of the two representations on the Mackey intersection.
-/
lemma finrank_mackeyHomTerm_cast_eq_char_sum
    [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    let H : Subgroup G := mackeyIntersection I g
    letI : Fintype H := Fintype.ofFinite H
    ((Module.finrank k (mackeyHomTerm (k := k) I σ g)) : k)
      =
    (Nat.card H : k)⁻¹ *
      ∑ h : H,
        (mackeyConjRes (k := k) I σ g).character h *
          (mackeyLeftRes (k := k) I σ g).character h⁻¹ := by
  intro H
  letI : Fintype H := Fintype.ofFinite H
  have hcard0H : (Fintype.card H : k) ≠ 0 := by
    exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
  letI : Invertible (Fintype.card H : k) :=
    invertibleOfNonzero hcard0H
  let V : FDRep k H := mackeyLeftRes (k := k) I σ g
  let W : FDRep k H := mackeyConjRes (k := k) I σ g
  change
    ((Module.finrank k (V ⟶ W)) : k)
      =
    (Nat.card H : k)⁻¹ *
      ∑ h : H, W.character h * V.character h⁻¹
  rw [← Fintype.card_eq_nat_card]
  exact (char_scalarProduct_eq_finrank_hom W V).symm

/--
The character of the left Mackey restriction is the restriction of `σ.character`
through the left inclusion into `I`.
-/
@[simp] lemma char_mackeyLeftRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyLeftRes (k := k) I σ g).character h
      =
    σ.character ⟨(h : G), h.2.1⟩ := by
  rfl

/--
The Mackey Hom-term dimension formula with the two restricted characters
expanded explicitly in terms of `σ.character`.
-/
@[simp] lemma char_mackeyConjRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyConjRes (k := k) I σ g).character h
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩) := by
  change
    (FDRep.conjMap (k := k) I g σ).character
      ⟨(h : G), h.2.2⟩
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩)
  rfl

/--
The Mackey Hom-term dimension formula with the two restricted characters
expanded explicitly in terms of `σ.character`.
-/
lemma finrank_mackeyHomTerm_cast_eq_expanded
    [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    let H : Subgroup G := mackeyIntersection I g
    letI : Fintype H := Fintype.ofFinite H
    ((Module.finrank k (mackeyHomTerm (k := k) I σ g)) : k)
      =
    (Nat.card H : k)⁻¹ *
      ∑ h : H,
        σ.character
          (((MulAut.conj g).subgroupMap I).symm
            ⟨(h : G), h.2.2⟩)
        *
        σ.character
          (⟨(h⁻¹ : G), by
              exact I.inv_mem h.2.1⟩) := by
  intro H
  rw [finrank_mackeyHomTerm_cast_eq_char_sum (k := k) (G := G) I σ g]
  congr 1

/--
The dimension of `Hom(σ, Res_I^G Ind_I^G σ)`, cast to `k`, as the usual
character inner product.
-/
lemma finrank_hom_res_ind_cast_eq_char_sum
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    letI : Fintype I := Fintype.ofFinite I
    ((Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I)) : k)
      =
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹ := by
  letI : Fintype I := Fintype.ofFinite I
  have h :=
    FDRep.char_scalarProduct_eq_finrank_hom
      (k := k) (G := I)
      (V := FDRep.res (FDRep.ind I σ) I) (W := σ)
  change
    ((Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I)) : k)
      =
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹
  rw [← Fintype.card_eq_nat_card]
  exact h.symm

open Classical in
/--
The character of `Res_I^G Ind_I^G σ`, written as the induced-character average
over conjugates `x * i * x⁻¹`.
-/
lemma char_res_ind_as_avg_mul_inv
    {G : Type u} [Group G] [Fintype G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (i : I) :
    (FDRep.res (FDRep.ind I σ) I).character i =
      (Nat.card I : k)⁻¹ * ∑ x : G,
        if h : x * (i : G) * x⁻¹ ∈ I
        then σ.character ⟨x * (i : G) * x⁻¹, h⟩
        else 0 := by
  change (FDRep.ind I σ).character (i : G) =
      (Nat.card I : k)⁻¹ * ∑ x : G,
        if h : x * (i : G) * x⁻¹ ∈ I
        then σ.character ⟨x * (i : G) * x⁻¹, h⟩
        else 0
  exact FDRep.char_ind_as_avg_mul_inv I σ (i : G)

/--
For fixed `g : G` and `(a, b) : I × I`, the inner summation condition in the
double-coset parameterization is equivalent to membership in the Mackey
intersection `I ∩ gIg⁻¹`.
-/
noncomputable def mackeyParameterizationInnerEquiv
    (I : Subgroup G)
    (g : G)
    (p : I × I) :
    { i : I //
        DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I }
      ≃
    mackeyIntersection I g := by
  rcases p with ⟨a, b⟩
  let H : Subgroup G := mackeyIntersection I g
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro i
    let hG : G := g * (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G) * g⁻¹
    have hI : hG ∈ I := by
      have hi :
          ((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
            (b : G) * g⁻¹ * (a : G)) ∈ I := by
        simpa [DoubleCoset.parameterization, mul_assoc] using i.2
      have hi_inv :
          (((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
            (b : G) * g⁻¹ * (a : G))⁻¹) ∈ I :=
        I.inv_mem hi
      have hconj :
          (a : G) *
            (((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
              (b : G) * g⁻¹ * (a : G))⁻¹) *
            (a : G)⁻¹ ∈ I :=
        I.mul_mem (I.mul_mem a.2 hi_inv) (I.inv_mem a.2)
      simpa [hG, mul_assoc] using hconj
    have hIg : hG ∈ I.map (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.mem_map).2 ?_
      refine ⟨(b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G),
        I.mul_mem (I.mul_mem (I.inv_mem b.2) (I.inv_mem i.1.2)) b.2, ?_⟩
      simp [hG, MulAut.conj_apply, mul_assoc]
    exact ⟨hG, ⟨hI, hIg⟩⟩
  · intro h
    let iG : G := (b : G) * g⁻¹ * (h : G)⁻¹ * g * (b : G)⁻¹
    have hi_mem : iG ∈ I := by
      have hhIg : (h : G) ∈ I.map (MulAut.conj g).toMonoidHom := h.2.2
      have hpre :
          (MulAut.conj g).symm (h : G) ∈ I :=
        (Subgroup.mem_map_equiv
          (f := MulAut.conj g) (K := I) (x := (h : G))).1 hhIg
      have hpre_inv :
          ((MulAut.conj g).symm (h : G))⁻¹ ∈ I :=
        I.inv_mem hpre
      have hpre_inv' : g⁻¹ * (h : G)⁻¹ * g ∈ I := by
        simpa [MulAut.conj_symm_apply, mul_assoc] using hpre_inv
      have hleft :
          (b : G) * (g⁻¹ * (h : G)⁻¹ * g) ∈ I :=
        I.mul_mem b.2 hpre_inv'
      simpa [iG, mul_assoc] using
        I.mul_mem hleft (I.inv_mem b.2)
    refine ⟨⟨iG, hi_mem⟩, ?_⟩
    have hhI : (h : G) ∈ I := h.2.1
    have hcond :
        (a : G)⁻¹ * (h : G)⁻¹ * (a : G) ∈ I :=
      I.mul_mem (I.mul_mem (I.inv_mem a.2) (I.inv_mem hhI)) a.2
    simpa [DoubleCoset.parameterization, iG, mul_assoc] using hcond
  · intro i
    apply Subtype.ext
    apply Subtype.ext
    simp [DoubleCoset.parameterization, mul_assoc]
  · intro h
    apply Subtype.ext
    simp [mul_assoc]

/--
Under `mackeyParameterizationInnerEquiv`, the inner summand in the double-coset
parameterization agrees with the expanded Mackey Hom-term summand.
-/
lemma mackey_parameterization_inner_summand_eq_expanded
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (p : I × I)
    (i :
      {i : I //
        DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I}) :
    let h : mackeyIntersection I g :=
      (mackeyParameterizationInnerEquiv
        (I := I) (g := g) (p := p)) i
    σ.character
        ⟨DoubleCoset.parameterization I g p * (i.1 : G) *
          (DoubleCoset.parameterization I g p)⁻¹, i.2⟩ *
      σ.character i.1⁻¹
      =
    σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
  intro h
  rcases p with ⟨a, b⟩
  have h_val : (h : G) = g * (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G) * g⁻¹ := by
    dsimp [h, mackeyParameterizationInnerEquiv]
  have h_left :
      (⟨DoubleCoset.parameterization I g (a, b) * (i.1 : G) *
        (DoubleCoset.parameterization I g (a, b))⁻¹, i.2⟩ : I)
        =
      a⁻¹ * ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ * a := by
    ext
    dsimp [DoubleCoset.parameterization]
    rw [h_val]
    group
  have h_right :
      (((MulAut.conj g).subgroupMap I).symm ⟨(h : G), h.2.2⟩)
        =
      b⁻¹ * i.1⁻¹ * b := by
    ext
    change (MulAut.conj g).symm (h : G) = (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G)
    rw [h_val]
    simp [MulAut.conj_symm_apply]
    group
  rw [h_left, h_right]
  have h_char_a :
      σ.character (a⁻¹ * ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ * a)
        =
      σ.character ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ := by
    simpa [mul_assoc] using FDRep.char_conj σ ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ a⁻¹
  have h_char_b :
      σ.character (b⁻¹ * i.1⁻¹ * b)
        =
      σ.character i.1⁻¹ := by
    simpa [mul_assoc] using FDRep.char_conj σ i.1⁻¹ b⁻¹
  rw [h_char_a, h_char_b, mul_comm]

open Classical in
/--
The inner sum over `I` in the double-coset parameterization is equal to the
expanded character sum over the Mackey intersection.
-/
lemma mackey_parameterization_inner_sum_eq_expanded
    [Fintype G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (p : I × I) :
    let H : Subgroup G := mackeyIntersection I g
    (∑ i : I,
      if h : DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I
      then
        σ.character
          ⟨DoubleCoset.parameterization I g p * (i : G) *
            (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
          σ.character i⁻¹
      else 0)
    =
    (∑ h : H,
      σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)) := by
  intro H
  let P : I → Prop := fun i =>
    DoubleCoset.parameterization I g p * (i : G) *
      (DoubleCoset.parameterization I g p)⁻¹ ∈ I
  let T : {i : I // P i} → k := fun i =>
    σ.character
        ⟨DoubleCoset.parameterization I g p * (i.1 : G) *
          (DoubleCoset.parameterization I g p)⁻¹, i.2⟩ *
      σ.character i.1⁻¹
  let U : H → k := fun h =>
    σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)
  let e : {i : I // P i} ≃ H := by
    simpa [H, P] using
      (mackeyParameterizationInnerEquiv
        (I := I) (g := g) (p := p))
  have hsplit :
      (∑ i : I,
        if h : P i
        then
          σ.character
            ⟨DoubleCoset.parameterization I g p * (i : G) *
              (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
            σ.character i⁻¹
        else 0)
        =
      ∑ i : {i : I // P i}, T i := by
    simpa [T, P] using
      (Fintype.sum_dite_eq_sum_subtype
        (P := P)
        (f := fun i h =>
          σ.character
            ⟨DoubleCoset.parameterization I g p * (i : G) *
              (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
            σ.character i⁻¹))
  have hpoint :
      ∀ i : {i : I // P i}, T i = U (e i) := by
    intro i
    dsimp [T, U, e]
    simpa [P, H] using
      (mackey_parameterization_inner_summand_eq_expanded
        (I := I) (σ := σ) (g := g) (p := p) i)
  calc
    (∑ i : I,
      if h : DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I
      then
        σ.character
          ⟨DoubleCoset.parameterization I g p * (i : G) *
            (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
          σ.character i⁻¹
      else 0)
        =
      ∑ i : {i : I // P i}, T i := by
        simpa [P] using hsplit
    _ =
      ∑ h : H, U h := by
        exact Fintype.sum_equiv e T U hpoint
    _ =
      ∑ h : H,
        σ.character
          (((MulAut.conj g).subgroupMap I).symm
            ⟨(h : G), h.2.2⟩)
        *
        σ.character
          (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
        rfl

open Classical in
/--
The product sum over `I × I` associated to a double-coset representative is
`|I|²` times the expanded Mackey-intersection character sum.
-/
lemma mackey_product_sum_eq_card_sq_mul_expanded_sum
    [Fintype G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    let H : Subgroup G := mackeyIntersection I g
    let F : G → k := fun x =>
      ∑ i : I,
        if h : x * (i : G) * x⁻¹ ∈ I
        then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
        else 0
    ∑ p : I × I, F (DoubleCoset.parameterization I g p)
      =
    (Nat.card I : k) * (Nat.card I : k) *
      ∑ h : H,
        σ.character
          (((MulAut.conj g).subgroupMap I).symm
            ⟨(h : G), h.2.2⟩)
        *
        σ.character
          (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
  intro H F
  have hpoint :
      ∀ p : I × I,
        F (DoubleCoset.parameterization I g p)
          =
        ∑ h : H,
          σ.character
            (((MulAut.conj g).subgroupMap I).symm
              ⟨(h : G), h.2.2⟩)
          *
          σ.character
            (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
    intro p
    simpa [F, H] using
      (mackey_parameterization_inner_sum_eq_expanded
        (I := I) (σ := σ) (g := g) p)
  simp only [hpoint, MulEquiv.subgroupMap_symm_apply, MulAut.conj_symm_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, Nat.card_eq_fintype_card]

open Classical in
/--
The Mackey Hom-term dimension, cast to `k`, expressed through the product sum
over `I × I`.
-/
lemma finrank_mackeyHomTerm_cast_eq_product_sum
    [Fintype G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    let H : Subgroup G := mackeyIntersection I g
    let F : G → k := fun x =>
      ∑ i : I,
        if h : x * (i : G) * x⁻¹ ∈ I
        then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
        else 0
    ((Module.finrank k
      (mackeyHomTerm (k := k) I σ g)) : k)
      =
    (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
      (Nat.card H : k)⁻¹ *
      ∑ p : I × I, F (DoubleCoset.parameterization I g p) := by
  intro H F
  let Sprod : k :=
    ∑ h : H,
      σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)
  have h_product :
      ∑ p : I × I, F (DoubleCoset.parameterization I g p)
        =
      (Nat.card I : k) * (Nat.card I : k) * Sprod := by
    simpa [H, F, Sprod] using
      (mackey_product_sum_eq_card_sq_mul_expanded_sum
        (k := k) I σ g)
  letI : Fintype H := Fintype.ofFinite H
  let Sexp : k :=
    ∑ h : H,
      σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)
  have h_expanded :
      ((Module.finrank k
        (mackeyHomTerm (k := k) I σ g)) : k)
        =
      (Nat.card H : k)⁻¹ * Sexp := by
    simpa [H, Sexp] using (finrank_mackeyHomTerm_cast_eq_expanded (k := k) I σ g)
  have hS : Sexp = Sprod := by
    dsimp [Sexp, Sprod]
    apply Finset.sum_congr
    · ext h
      simp
    · intro h _
      rfl
  rw [h_expanded, h_product, ← hS]
  field_simp

open Classical in
/--
The Mackey Hom-term dimension, cast to `k`, expressed as an explicit sum over
the double coset of `g`.
-/
lemma finrank_mackeyHomTerm_cast_eq_doubleCoset_sum
    [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    ((Module.finrank k
      (mackeyHomTerm (k := k) I σ g)) : k)
      =
    let D : Set G := DoubleCoset.doubleCoset g I I
    letI : Fintype G := Fintype.ofFinite G
    (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
      ∑ x ∈ D.toFinset,
        ∑ i : I,
          if h : x * (i : G) * x⁻¹ ∈ I
          then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
          else 0 := by
  letI : Fintype G := Fintype.ofFinite G
  let F : G → k := fun x =>
    ∑ i : I,
      if h : x * (i : G) * x⁻¹ ∈ I
      then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
      else 0
  let Ig : Subgroup G := I.map (MulAut.conj g).toMonoidHom
  let H : Subgroup G := I ⊓ Ig
  let D : Set G := DoubleCoset.doubleCoset g I I
  have hprod :
      ((Module.finrank k
        (mackeyHomTerm (k := k) I σ g)) : k)
        =
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        (Nat.card H : k)⁻¹ *
          ∑ p : I × I, F (DoubleCoset.parameterization I g p) := by
    simpa [F, Ig, H, mul_assoc] using (finrank_mackeyHomTerm_cast_eq_product_sum (k := k) I σ g)
  have hdc :
      ∑ x ∈ D.toFinset, F x
        =
      (Nat.card H : k)⁻¹ *
        ∑ p : I × I, F (DoubleCoset.parameterization I g p) := by
    let h :=
      DoubleCoset.sum_eq_sum_over_product
        (k := k) I g F
    change
      ∑ x ∈ D.toFinset, F x
        =
      (Nat.card H : k)⁻¹ *
        ∑ p : I × I, F (DoubleCoset.parameterization I g p)
    exact h
  calc
    ((Module.finrank k
      (mackeyHomTerm (k := k) I σ g)) : k)
        =
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        (Nat.card H : k)⁻¹ *
          ∑ p : I × I, F (DoubleCoset.parameterization I g p) := hprod
    _ =
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        ((Nat.card H : k)⁻¹ *
          ∑ p : I × I, F (DoubleCoset.parameterization I g p)) := by
        ring
    _ =
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        ∑ x ∈ D.toFinset, F x := by
        rw [← hdc]
    _ =
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        ∑ x ∈ D.toFinset,
          ∑ i : I,
            if h : x * (i : G) * x⁻¹ ∈ I
            then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
            else 0 := by
        rfl


/--
The inner character sum appearing in the Mackey character computation. For fixed
`x : G`, this is the sum over `i : I` occurring inside the double-coset element
sum.
-/
noncomputable def mackeyCharacterInnerSum
    [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (x : G) : k := by
  letI : Fintype G := Fintype.ofFinite G
  classical
  exact
    ∑ i : I,
      if h : x * (i : G) * x⁻¹ ∈ I
      then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
      else 0

/--
The explicit element sum over the double coset of a representative `g`.
-/
noncomputable def mackeyDoubleCosetElementSum
    [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) : k := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact
    ∑ x ∈ (DoubleCoset.doubleCoset g I I).toFinset,
      mackeyCharacterInnerSum I σ x

open Classical in
/--
The character inner product of `Res_I^G Ind_I^G σ` with `σ` is the sum over
double cosets of the corresponding explicit element sums.
-/
lemma inner_char_res_ind_eq_sum_doubleCoset_element_sums
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
      DoubleCoset.quotientFintype I I
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹
      =
    ∑ d : DoubleCoset.Quotient (G := G) I I,
      (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        mackeyDoubleCosetElementSum
          (k := k) I σ (Quotient.out d) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
    DoubleCoset.quotientFintype I I
  let c : k := (Nat.card I : k)
  let A : G → I → k := fun x i =>
    if h : x * (i : G) * x⁻¹ ∈ I
    then σ.character ⟨x * (i : G) * x⁻¹, h⟩
    else 0
  let B : I → k := fun i =>
    σ.character i⁻¹
  let K : G → k := fun x =>
    ∑ i : I, A x i * B i
  have h_to_G :
      c⁻¹ *
        ∑ i : I,
          (FDRep.res (FDRep.ind I σ) I).character i *
            σ.character i⁻¹
        =
      c⁻¹ * c⁻¹ * ∑ x : G, K x := by
    calc
      c⁻¹ *
        ∑ i : I,
          (FDRep.res (FDRep.ind I σ) I).character i *
            σ.character i⁻¹
          =
        c⁻¹ *
          ∑ i : I,
            (c⁻¹ * ∑ x : G, A x i) * B i := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            have hχ :
                (FDRep.res (FDRep.ind I σ) I).character i
                  =
                c⁻¹ * ∑ x : G, A x i := by
              simpa [c, A] using
                (FDRep.char_res_ind_as_avg_mul_inv
                  (k := k) I σ i)
            rw [hχ]
      _ =
        c⁻¹ *
          ∑ i : I,
            c⁻¹ * (∑ x : G, A x i * B i) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [mul_assoc, Finset.sum_mul]
      _ =
        c⁻¹ * (c⁻¹ *
          ∑ i : I,
            ∑ x : G, A x i * B i) := by
            congr 1
            rw [← Finset.mul_sum]
      _ =
        c⁻¹ * c⁻¹ *
          ∑ i : I,
            ∑ x : G, A x i * B i := by
            ring
      _ =
        c⁻¹ * c⁻¹ *
          ∑ x : G,
            ∑ i : I, A x i * B i := by
            rw [Finset.sum_comm]
      _ =
        c⁻¹ * c⁻¹ *
          ∑ x : G, K x := by
            rfl
  have h_by_double :
      ∑ x : G, K x
        =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        mackeyDoubleCosetElementSum
          (k := k) I σ (Quotient.out d) := by
    have hdc :=
      DoubleCoset.sum_over_G_eq_sum_double_cosets
        (G := G) (k := k) I K
    calc
      ∑ x : G, K x
          =
        ∑ d : DoubleCoset.Quotient (G := G) I I,
          ∑ x ∈ (DoubleCoset.quotToDoubleCoset I I d).toFinset,
            K x := by
            simpa using hdc
        _ =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        mackeyDoubleCosetElementSum
          (k := k) I σ (Quotient.out d) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [DoubleCoset.quotToDoubleCoset_eq_doubleCoset_out]
          unfold mackeyDoubleCosetElementSum mackeyCharacterInnerSum
          apply Finset.sum_congr rfl
          intro x _
          simp only [K, A, B]
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : x * (i : G) * x⁻¹ ∈ I
          · simp [h]
          · simp [h]
  calc
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹
        =
      c⁻¹ * c⁻¹ * ∑ x : G, K x := by
        simpa [c] using h_to_G
    _ =
      c⁻¹ * c⁻¹ *
        ∑ d : DoubleCoset.Quotient (G := G) I I,
          mackeyDoubleCosetElementSum
            (k := k) I σ (Quotient.out d) := by
        rw [h_by_double]
    _ =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        c⁻¹ * c⁻¹ *
          mackeyDoubleCosetElementSum
            (k := k) I σ (Quotient.out d) := by
        rw [Finset.mul_sum]
    _ =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
          mackeyDoubleCosetElementSum
            (k := k) I σ (Quotient.out d) := by
        rfl

/--
Each explicit double-coset element sum is equal to the dimension, cast to `k`,
of the corresponding Mackey Hom term.
-/
lemma doubleCoset_element_sum_eq_mackeyHomTerm
    [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
        mackeyDoubleCosetElementSum
          (k := k) I σ g
      =
    ((Module.finrank k
      (mackeyHomTerm (k := k) I σ g)) : k) := by
  symm
  simpa [mackeyDoubleCosetElementSum,
    mackeyCharacterInnerSum] using
    (FDRep.finrank_mackeyHomTerm_cast_eq_doubleCoset_sum
      (k := k) I σ g)

open Classical in
/--
Mackey decomposition of the character inner product into the dimensions of the
Mackey Hom terms.
-/
lemma inner_char_res_ind_eq_sum_mackeyHomTerm
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
      DoubleCoset.quotientFintype I I
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹
      =
    ∑ d : DoubleCoset.Quotient (G := G) I I,
      ((Module.finrank k
        (mackeyHomTerm (k := k) I σ (Quotient.out d))) : k) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
    DoubleCoset.quotientFintype I I
  calc
    (Nat.card I : k)⁻¹ *
      ∑ i : I,
        (FDRep.res (FDRep.ind I σ) I).character i *
          σ.character i⁻¹
        =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        (Nat.card I : k)⁻¹ * (Nat.card I : k)⁻¹ *
          mackeyDoubleCosetElementSum
            (k := k) I σ (Quotient.out d) := by
        simpa using
          FDRep.inner_char_res_ind_eq_sum_doubleCoset_element_sums
            (k := k) I σ
    _ =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        ((Module.finrank k
          (mackeyHomTerm (k := k) I σ (Quotient.out d))) : k) := by
        apply Finset.sum_congr rfl
        intro d _
        exact
          FDRep.doubleCoset_element_sum_eq_mackeyHomTerm
            (k := k) I σ (Quotient.out d)

open Classical in
/--
The dimension of `Hom(σ, Res_I^G Ind_I^G σ)`, cast to `k`, is the sum over
double cosets of the Mackey Hom-term dimensions, cast to `k`.

The preceding character-sum lemmas use the `Fintype` instance on `I` inherited
as a subtype of `G`, while the finrank lemma uses `Fintype.ofFinite I`. We spell
out the `Finset.univ` bridge to avoid relying on definitional equality of these
instances.
-/
lemma finrank_hom_res_ind_cast_eq_sum_mackeyHomTerm
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    ((Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I)) : k)
      =
    letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
      DoubleCoset.quotientFintype I I
    ∑ d : DoubleCoset.Quotient (G := G) I I,
      ((Module.finrank k
        (mackeyHomTerm (k := k) I σ (Quotient.out d))) : k) := by
  letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
    DoubleCoset.quotientFintype I I
  letI : Fintype G := Fintype.ofFinite G
  let f : I → k := fun i =>
    (FDRep.res (FDRep.ind I σ) I).character i * σ.character i⁻¹
  have hsumI :
      (∑ i ∈ (@Finset.univ I (Fintype.ofFinite I)), f i)
        =
      ∑ i : I, f i := by
    apply Finset.sum_congr
    · ext i
      simp
    · intro i hi
      rfl
  calc
    ((Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I)) : k)
        =
      (Fintype.card I : k)⁻¹ *
        ∑ i ∈ (@Finset.univ I (Fintype.ofFinite I)), f i := by
        simpa [f] using
          (FDRep.finrank_hom_res_ind_cast_eq_char_sum
            (k := k) I σ)
    _ =
      (Nat.card I : k)⁻¹ *
        ∑ i : I, f i := by
        rw [← Nat.card_eq_fintype_card, hsumI]
    _ =
      ∑ d : DoubleCoset.Quotient (G := G) I I,
        ((Module.finrank k
          (mackeyHomTerm (k := k) I σ (Quotient.out d))) : k) := by
        simpa [f] using
          (FDRep.inner_char_res_ind_eq_sum_mackeyHomTerm
            (k := k) I σ)

open Classical in
/--
The dimension of `Hom(σ, Res_I^G Ind_I^G σ)` is the sum over double cosets of
the Mackey Hom-term dimensions.
-/
lemma finrank_hom_res_ind_eq_sum_mackeyHomTerm
    {G : Type u} [Group G] [Finite G] [CharZero k]
    (I : Subgroup G)
    (σ : FDRep k I) :
    Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I)
      =
    letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
      DoubleCoset.quotientFintype I I
    ∑ d : DoubleCoset.Quotient (G := G) I I,
      Module.finrank k
        (mackeyHomTerm (k := k) I σ (Quotient.out d)) := by
  letI : Fintype (DoubleCoset.Quotient (G := G) I I) :=
    DoubleCoset.quotientFintype I I
  apply Nat.cast_injective (R := k)
  simpa [Nat.cast_sum] using
    (FDRep.finrank_hom_res_ind_cast_eq_sum_mackeyHomTerm
      (k := k) I σ)

/--
By Frobenius reciprocity, the endomorphism dimension of `Ind_I^G σ` agrees with
the dimension of `Hom(σ, Res_I^G Ind_I^G σ)`.
-/
lemma finrank_end_ind_eq_hom_res_ind
    {G : Type u} [Group G] [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I) :
    Module.finrank k (FDRep.ind I σ ⟶ FDRep.ind I σ)
      =
    Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I) := by
  let τ : FDRep k G := FDRep.ind I σ
  exact LinearEquiv.finrank_eq
    (FDRep.indResEquiv I σ τ)

end FDRep

end Slop
