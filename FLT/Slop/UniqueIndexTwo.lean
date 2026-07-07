/-
Copyright (c) 2026 baimurzzin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: baimurzzin
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Uniqueness of the index-two subgroup of a finite cyclic group

A finite cyclic group has at most one subgroup of index two (`index_two_eq`); if the order is
even, exactly one, namely the subgroup of squares (`existsUnique_index_two`).  The relative
versions (`index_two_eq_over`, `existsUnique_index_two_over`) transport this along the quotient
correspondence to subgroups containing a normal `H ◁ G` with `G ⧸ H` cyclic.

Finiteness is essential for the counting argument used here (index times card equals card);
note that evenness of the order is automatic from the *existence* of an index-two subgroup, so
the pairwise-uniqueness statements carry no evenness hypothesis.

`index_two_eq_over` discharges the `hK_unique` hypothesis of
`Representation.theorem_1_6_induced_form` in `FLT.Slop.Clifford`, which is how the two combine
in `FLT.KnownIn1980s.RepresentationTheory.ConjugateCharactersInduced`.
-/

@[expose] public section

open Subgroup

namespace CliffordInduced

variable {A : Type*} [Group A] [Finite A] [IsCyclic A]

/-- In a finite cyclic group of even order there is a unique subgroup of index two,
namely the subgroup of squares. -/
theorem existsUnique_index_two (h2 : Even (Nat.card A)) :
    ∃! K : Subgroup A, K.index = 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  set n := Nat.card A with hn
  have hnpos : 0 < n := Nat.card_pos
  have hn2 : 2 ∣ n := h2.two_dvd
  have hgcd : Nat.gcd n 2 = 2 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right n 2) (Nat.dvd_gcd hn2 dvd_rfl)
  have hcard_sq : Nat.card (zpowers (g ^ 2)) = n / 2 := by
    rw [Nat.card_zpowers, orderOf_pow, hg, hgcd]
  have h2pos : 0 < n / 2 := Nat.div_pos (Nat.le_of_dvd hnpos hn2) two_pos
  have hne : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even h2
  have hidx_sq : (zpowers (g ^ 2)).index = 2 := by
    have hmul := Subgroup.index_mul_card (zpowers (g ^ 2))
    rw [hcard_sq, ← hn] at hmul
    have hcancel : (zpowers (g ^ 2)).index * (n / 2) = 2 * (n / 2) := by rw [hmul, hne]
    exact Nat.eq_of_mul_eq_mul_right h2pos hcancel
  refine ⟨zpowers (g ^ 2), hidx_sq, ?_⟩
  intro K hK
  have hg2mem : g ^ 2 ∈ K := Subgroup.sq_mem_of_index_two hK g
  have hsq_le : zpowers (g ^ 2) ≤ K := by rw [zpowers_le]; exact hg2mem
  have hcardK : Nat.card K = n / 2 := by
    have hmul := Subgroup.index_mul_card K
    rw [hK, ← hn] at hmul
    omega
  have hcards : Nat.card K ≤ Nat.card (zpowers (g ^ 2)) := by rw [hcardK, hcard_sq]
  exact (Subgroup.eq_of_le_of_card_ge hsq_le hcards).symm

/-- A finite cyclic group has at most one subgroup of index two.  No evenness hypothesis:
the existence of an index-two subgroup already forces the order to be even. -/
theorem index_two_eq {K₁ K₂ : Subgroup A} (h1 : K₁.index = 2) (h2 : K₂.index = 2) :
    K₁ = K₂ := by
  have hmul := Subgroup.index_mul_card K₁
  rw [h1] at hmul
  have hev : Even (Nat.card A) := ⟨Nat.card K₁, by omega⟩
  obtain ⟨K, -, hK⟩ := existsUnique_index_two hev
  rw [hK K₁ h1, hK K₂ h2]

variable {G : Type*} [Group G]

/-- Relative version of `index_two_eq`: if `G ⧸ H` is cyclic and finite, two index-two
subgroups of `G` containing `H` are equal. -/
theorem index_two_eq_over (H : Subgroup G) [H.Normal]
    [Finite (G ⧸ H)] [IsCyclic (G ⧸ H)] {K₁ K₂ : Subgroup G}
    (hHK₁ : H ≤ K₁) (hHK₂ : H ≤ K₂) (h1 : K₁.index = 2) (h2 : K₂.index = 2) :
    K₁ = K₂ := by
  classical
  set f := QuotientGroup.mk' H with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective H
  have hker : f.ker = H := QuotientGroup.ker_mk' H
  have hmap : ∀ K : Subgroup G, H ≤ K → K.index = 2 → (K.map f).index = 2 := by
    intro K hHK hK2
    rw [Subgroup.index_map_eq _ hsurj (by rw [hker]; exact hHK)]; exact hK2
  have hq : K₁.map f = K₂.map f := index_two_eq (hmap K₁ hHK₁ h1) (hmap K₂ hHK₂ h2)
  have hcm : ∀ K : Subgroup G, H ≤ K → (K.map f).comap f = K := by
    intro K hHK
    rw [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hHK]
  rw [← hcm K₁ hHK₁, ← hcm K₂ hHK₂, hq]

/-- Relative version of `existsUnique_index_two`: if `G ⧸ H` is cyclic of even order, there is
a unique index-two subgroup of `G` containing `H`. -/
theorem existsUnique_index_two_over (H : Subgroup G) [H.Normal]
    [Finite (G ⧸ H)] [IsCyclic (G ⧸ H)] (h2 : Even (Nat.card (G ⧸ H))) :
    ∃! K : Subgroup G, H ≤ K ∧ K.index = 2 := by
  classical
  set f := QuotientGroup.mk' H with hf
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective H
  have hker : f.ker = H := QuotientGroup.ker_mk' H
  obtain ⟨T, hT2, -⟩ := existsUnique_index_two (A := G ⧸ H) h2
  have hHT : H ≤ T.comap f := by
    intro h hh
    rw [Subgroup.mem_comap]
    have hf1 : f h = 1 := by rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hh
    rw [hf1]; exact one_mem T
  have hTidx : (T.comap f).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hsurj]; exact hT2
  exact ⟨T.comap f, ⟨hHT, hTidx⟩,
    fun K ⟨hHK, hK2⟩ => index_two_eq_over H hHK hHT hK2 hTidx⟩

end CliffordInduced
