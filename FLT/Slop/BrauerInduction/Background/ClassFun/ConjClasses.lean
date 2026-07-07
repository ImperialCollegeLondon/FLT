/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.ClassFun.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Class functions as functions on conjugacy classes

This file provides the linear equivalence `ClassFun.linearEquivConjClasses`
between class functions and functions on conjugacy classes, together with the
resulting reindexing of sums over the group as sums over conjugacy classes.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

namespace ClassFun

/-- The explicit linear equivalence between ClassFun and functions on ConjClasses. -/
noncomputable def linearEquivConjClasses :
    ClassFun k G ≃ₗ[k] (ConjClasses G → k) where
  toFun f := f.toFun
  invFun F := ⟨F⟩
  left_inv f := by cases f; rfl
  right_inv F := rfl
  map_add' f g := rfl
  map_smul' m f := rfl

open Classical in
noncomputable instance instFintypeConjClasses
    {G : Type v} [Group G] [Fintype G] :
    Fintype (ConjClasses G) :=
  Quotient.fintype (IsConj.setoid G)

open Classical in
/--
A sum of a class function over a finite group may be evaluated by summing over
conjugacy classes, weighted by the cardinality of each conjugacy class.
-/
theorem sum_eq_sum_conjClasses
    [Fintype G]
    (f : ClassFun k G) :
    ∑ g : G, f g =
      ∑ c : ConjClasses G,
        (Nat.card (MulAction.orbit (ConjAct G) c.out) : k) * f c.out := by
  calc
    ∑ g : G, f g
        =
      ∑ c : ConjClasses G,
        ∑ g ∈ Finset.univ.filter
          (fun x => ConjClasses.mk x = c), f g := by
            rw [Finset.sum_fiberwise]
    _ =
      ∑ c : ConjClasses G,
        (Nat.card (MulAction.orbit (ConjAct G) c.out) : k) * f c.out := by
      apply Finset.sum_congr rfl
      intro c _
      let s : Finset G := Finset.univ.filter (fun x => ConjClasses.mk x = c)
      change
        (∑ g ∈ s, f g) =
          (Nat.card (MulAction.orbit (ConjAct G) c.out) : k) * f c.out
      have h_const : ∀ g ∈ s, f g = f c.out := by
        intro g hg
        have hg_class : ConjClasses.mk g = c := by
          simpa [s] using hg
        apply f.map_conj
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        exact hg_class.trans (Quotient.out_eq c).symm
      rw [Finset.sum_congr rfl h_const]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have e_filter : ↥s ≃ ↥c.carrier :=
        Equiv.subtypeEquivRight fun g => by
          simp [s, ConjClasses.mem_carrier_iff_mk_eq]
      have hcarrier :
          Nat.card ↥c.carrier =
            Nat.card (MulAction.orbit (ConjAct G) c.out) := by
        rw [ConjAct.orbit_eq_carrier_conjClasses]
        have hc : ConjClasses.mk c.out = c := Quotient.out_eq c
        rw [hc]
      have hcard :
          s.card = Nat.card (MulAction.orbit (ConjAct G) c.out) := by
        calc
          s.card = Nat.card ↥s := by
            rw [ Nat.card_eq_fintype_card, Fintype.card_coe ]
          _ = Nat.card ↥c.carrier :=
            Nat.card_congr e_filter
          _ = Nat.card (MulAction.orbit (ConjAct G) c.out) :=
            hcarrier
      rw [hcard]

open Classical in
/--
For a class function over a finite group, summing one representative from
each conjugacy class with weight `|C_G(g)|⁻¹` equals the normalized sum over
the whole group.
-/
theorem sum_inv_card_centralizer
    [Fintype G] [CharZero k]
    (f : ClassFun k G) :
    ∑ c : ConjClasses G,
        (Nat.card
          (Subgroup.centralizer ({c.out} : Set G)) : k)⁻¹ * f c.out
      =
    (Fintype.card G : k)⁻¹ * ∑ g : G, f g := by
  rw [sum_eq_sum_conjClasses f]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  field_simp [MulAction.card_conjClass_mul_card_centralizer c.out]
  rw [← MulAction.card_conjClass_mul_card_centralizer c.out]
  rw [Nat.card_eq_fintype_card]
  grind

end ClassFun

end Slop
