/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.ClassFun.Maps
public import FLT.Slop.BrauerInduction.Background.ClassFun.Induced

/-!

# Integer-valued class functions

This file contains basic API for class functions whose values are integers, and
for casting such functions to other coefficient rings.

The main constructions are:

* `ClassFun.mapIntCast`: pointwise casting of a `ℤ`-valued class function to a
  `k`-valued class function.
* `ClassFun.IsIntValued`: the predicate that a `k`-valued class function takes
  values in the image of `ℤ → k`.
* `ClassFun.C_Z`: the additive subgroup/submodule of integer-valued class
  functions.

The main closure results show that integer-valued class functions are stable
under the basic class-function operations used in Brauer induction, including
restriction and induction.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

namespace ClassFun

section IntegerCoefficients

variable {k : Type u} {G : Type v} [Group G] [Ring k]

/--
Cast an integer-valued class function pointwise into a class function over `k`.
-/
def mapIntCast
    {k : Type u} [Ring k]
    {G : Type v} [Group G]
    (ψ : ClassFun ℤ G) :
    ClassFun k G :=
  ψ.postcomp fun z => (z : k)

/-- Evaluation of a pointwise-cast integer-valued class function. -/
@[simp]
lemma mapIntCast_apply
    {H : Type v} [Group H]
    (ψ : ClassFun ℤ H) (h : H) :
    mapIntCast (k := k) ψ h = (ψ h : k) :=
  rfl

/--
Pointwise casting of integer-valued class functions commutes with integer
scalar multiplication.
-/
lemma intCast_zsmul
    {H : Type v} [Group H]
    (n : ℤ) (ψ : ClassFun ℤ H) :
    (n : k) • mapIntCast (k := k) ψ =
      mapIntCast (k := k) (n • ψ) := by
  ext h
  simp only [smul_apply, mapIntCast_apply, smul_eq_mul, zsmul_eq_mul, mul_apply,
    intCast_apply, Int.cast_eq, Int.cast_mul]

/--
A class function is integer-valued if each of its values is the image of an
integer.
-/
def IsIntValued (f : ClassFun k G) : Prop :=
  ∀ g : G, ∃ n : ℤ, f g = (n : k)

/--
Induction commutes with pointwise casting of integer-valued class functions.
-/
@[simp]
lemma ind_mapIntCast
    (H : Subgroup G) [Fintype G]
    (ψ : ClassFun ℤ H) :
    ind H (mapIntCast (k := k) ψ) =
      mapIntCast (k := k) (ind H ψ) := by
  simpa [mapIntCast] using
    (ind_postcomp
      (G := G)
      (F := (Int.castRingHom k).toAddMonoidHom)
      (H := H)
      (φ := ψ))

end IntegerCoefficients

section C_Z

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
`C_Z(H)`: the set of integer-valued class functions on `H`.
-/
abbrev C_Z (k : Type u) [CommRing k]
    (G : Type v) [Group G] : Set (ClassFun k G) :=
  { f | ClassFun.IsIntValued f }

@[simp]
lemma mem_C_Z {f : ClassFun k G} :
    f ∈ C_Z k G ↔ ClassFun.IsIntValued f :=
  Iff.rfl

namespace C_Z

lemma zero_mem :
    (0 : ClassFun k G) ∈ C_Z k G := by
  intro g
  refine ⟨0, ?_⟩
  simp

lemma one_mem :
    (1 : ClassFun k G) ∈ C_Z k G := by
  intro g
  refine ⟨1, ?_⟩
  simp

lemma add_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f + g ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  rcases hg x with ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  simp [ClassFun.add_apply, hm, hn]

lemma neg_mem {f : ClassFun k G}
    (hf : f ∈ C_Z k G) :
    -f ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  refine ⟨-m, ?_⟩
  simp [hm]

lemma sub_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f - g ∈ C_Z k G := by
  simpa [sub_eq_add_neg] using add_mem hf (neg_mem hg)

lemma zsmul_mem (n : ℤ) {f : ClassFun k G}
    (hf : f ∈ C_Z k G) :
    n • f ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  refine ⟨n * m, ?_⟩
  simp [hm]

lemma mul_mem {f g : ClassFun k G}
    (hf : f ∈ C_Z k G) (hg : g ∈ C_Z k G) :
    f * g ∈ C_Z k G := by
  intro x
  rcases hf x with ⟨m, hm⟩
  rcases hg x with ⟨n, hn⟩
  refine ⟨m * n, ?_⟩
  simp [ClassFun.mul_apply, hm, hn]

lemma pow_mem {f : ClassFun k G}
    (hf : f ∈ ClassFun.C_Z k G) :
    ∀ n : ℕ, f ^ n ∈ ClassFun.C_Z k G := by
  intro n
  induction n with
  | zero => simp only [pow_zero, Set.mem_setOf_eq]; apply one_mem
  | succ n ih => simpa [pow_succ] using mul_mem ih hf

/-- Integer-valued class functions remain integer-valued after restriction. -/
lemma res
    {G : Type v} [Group G]
    {H : Subgroup G} {g : ClassFun k G}
    (hg : g ∈ C_Z k G) :
    ClassFun.res H g ∈ C_Z k H := by
  intro h
  exact hg h


/--
A finite sum of elements lying in the image of `ℤ` again lies in the image of
`ℤ`.
-/
private lemma exists_int_cast_sum
    {k : Type u} [AddCommGroupWithOne k]
    {ι : Type*} (s : Finset ι) (f : ι → k)
    (hf : ∀ i, i ∈ s → ∃ z : ℤ, f i = (z : k)) :
    ∃ z : ℤ, s.sum f = (z : k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp⟩
  | insert a s ha ih =>
      rcases hf a (by simp [ha]) with ⟨za, hza⟩
      rcases ih (by
        intro i hi
        exact hf i (by simp [hi])) with ⟨zs, hzs⟩
      refine ⟨za + zs, ?_⟩
      simp only [ha, not_false_eq_true, Finset.sum_insert, hza, hzs, Int.cast_add]

/--
Induction preserves integer-valued class functions.

The result is stated after restricting the induced class function to `⊤`, so
that it is an element of `C_Z k (⊤ : Subgroup G)`.
-/
lemma ind_mem_C_Z
    {G : Type v} [Group G] [Fintype G]
    {H : Subgroup G} {q : ClassFun k H}
    (hq : q ∈ C_Z k H) :
    ClassFun.res (G := G) (k := k) (⊤ : Subgroup G)
      (ClassFun.ind (G := G) (k := k) H q)
      ∈ C_Z k (⊤ : Subgroup G) := by
  classical
  intro g_top
  let g : G := g_top
  change ∃ z : ℤ,
    ClassFun.ind (G := G) (k := k) H q g = (z : k)
  simp only [ClassFun.ind_apply]
  refine exists_int_cast_sum
    (s := Finset.univ)
    (f := fun x : G ⧸ H =>
      if hx : (Quotient.out x)⁻¹ * g * Quotient.out x ∈ H
      then q ⟨(Quotient.out x)⁻¹ * g * Quotient.out x, hx⟩
      else 0)
    ?_
  intro x hx
  by_cases hmem : (Quotient.out x)⁻¹ * g * Quotient.out x ∈ H
  · rcases hq ⟨(Quotient.out x)⁻¹ * g * Quotient.out x, hmem⟩ with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simp [hmem, hz]
  · refine ⟨0, ?_⟩
    simp [hmem]

end C_Z
end C_Z

end ClassFun

end Slop
