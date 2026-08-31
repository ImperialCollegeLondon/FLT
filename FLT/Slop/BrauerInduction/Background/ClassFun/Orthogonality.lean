/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.ClassFun.Action
public import FLT.Slop.BrauerInduction.Background.ClassFun.Character.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Orthogonality
public import FLT.Slop.BrauerInduction.Background.Fintype.Basic

/-!
# Orthogonality and duality for class functions

This file proves that the character pairing on class functions is
nondegenerate.

The unnormalised pairing is

`⟪f, φ⟫ = ∑ g : G, f g * φ g⁻¹`.

A class function whose pairing with every irreducible character vanishes is
shown to be zero. The proof uses the action of class functions on
representations: the hypothesis implies that the class function acts trivially
on every simple summand of the left regular representation, and hence acts
trivially on the regular representation itself.

The pairing is then bundled as a linear map from `ClassFun k G` to its dual
and shown to be an isomorphism.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

open Fintype CategoryTheory CategoryTheory.Limits

namespace ClassFun

/--
If a class function has zero pairing with the characters of every
representation in a finite family of simple representations, then it acts as
the zero endomorphism on each member of that family.

The pairing used here is the unnormalised sum
`∑ g : G, f g * (S i).character g⁻¹`.
-/
lemma action_eq_zero_of_pairing_eq_zero
    [Fintype G] [IsAlgClosed k] [CharZero k]
    {κ : Type} (S : κ → FDRep k G)
    [hS : ∀ i, CategoryTheory.Simple (S i)]
    (f : ClassFun k G)
    (h_ortho : ∀ i : κ, ∑ x : G, f x * (S i).character x⁻¹ = 0)
    (i : κ) :
    ClassFun.action f (S i) = 0 := by
  -- 1. Schur: the class-function action is scalar.
  obtain ⟨lambda, h_hom⟩ := actionHom_is_scalar f (S i)
  -- 2. Compare trace computations.
  have h_trace := trace_action f (S i)
  rw [h_ortho i] at h_trace
  have h_dim := trace_action_eq_scalar_mul_finrank f (S i) lambda h_hom
  rw [h_trace] at h_dim
  -- 3. A simple object is not zero, hence its underlying vector space is nontrivial.
  have h_finrank_ne_zero :
      (Module.finrank k (S i) : k) ≠ 0 := by
    have h_not_zero : ¬ Limits.IsZero (S i) :=
      CategoryTheory.Simple.not_isZero (S i)
    haveI : Nontrivial (S i) :=
      (FDRep.nontrivial_iff_not_IsZero (S i)).mpr h_not_zero
    exact Nat.cast_ne_zero.mpr
      (Module.finrank_pos_iff.mpr inferInstance).ne'
  -- 4. Since `lambda * dim = 0` and `dim ≠ 0`, `lambda = 0`.
  have h_lambda_zero : lambda = 0 := by
    cases mul_eq_zero.mp h_dim.symm with
    | inl h => exact h
    | inr h => exact (h_finrank_ne_zero h).elim
  -- 5. Project the categorical endomorphism down to its underlying linear map.
  let F : (S i ⟶ S i) → ((S i) →ₗ[k] (S i)) :=
    fun m => FDRep.homToLinearMap m
  have h_map_eq :
      F (ClassFun.actionHom f (S i)) = F (lambda • 𝟙 (S i)) :=
    congrArg F h_hom
  have h_LHS :
      F (ClassFun.actionHom f (S i)) = ClassFun.action f (S i) := by
    rfl
  have h_RHS :
      F (lambda • 𝟙 (S i)) =
        lambda • (LinearMap.id : (S i) →ₗ[k] (S i)) := by
    rfl
  rw [h_LHS, h_RHS, h_lambda_zero, zero_smul] at h_map_eq
  exact h_map_eq

open Classical in
/--
A class function is zero if its pairing with the character of every simple
representation vanishes.

The proof decomposes the left regular representation into simple summands and
uses the resulting action of the class function on those summand.
-/
lemma classFun_eq_zero_of_orthogonal_simples
    {G : Type u} [Group G] [Fintype G] [CharZero k] [IsAlgClosed k]
    (f : ClassFun k G)
    (h_ortho :
      ∀ (S : FDRep k G), Simple S →
        ∑ x : G, f x * S.character x⁻¹ = 0) :
    f = 0 := by
  haveI : NeZero (Nat.card G : k) :=
    ⟨One.natCast_natCard_ne_zero_of_finite G k⟩
  obtain ⟨ι, S, hι, hSimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition
      (FDRep.leftRegular k G)
  letI : Fintype ι := hι
  haveI : ∀ i, Simple (S i) := hSimple
  have hS_zero :
      ∀ i, ClassFun.action f (S i) = 0 := by
    intro i
    exact
      action_eq_zero_of_pairing_eq_zero S f
        (fun j => h_ortho (S j) (hSimple j)) i
  have h_bip :
      ClassFun.action f (biproduct S) = 0 :=
    ClassFun.action_zero_of_biproduct f S hS_zero
  have h_left :
      ClassFun.action f (FDRep.leftRegular k G) = 0 :=
    ClassFun.action_zero_of_iso f e h_bip
  exact ClassFun.eq_zero_of_action_leftRegular_eq_zero f h_left

/--
The unnormalised character pairing, bundled as a linear map from class
functions to their linear dual.
-/
noncomputable def characterPairingLeft
    (k : Type u) [Field k]
    (G : Type v) [Group G] [Fintype G] :
    ClassFun k G →ₗ[k] Module.Dual k (ClassFun k G) where
  toFun f :=
    { toFun := fun φ => ∑ x : G, f x * φ x⁻¹
      map_add' := by
        intro φ ψ
        simp only [add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_add]
      map_smul' := by
        intro c φ
        simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
        calc
          (∑ x : G, f x * (c * φ x⁻¹))
              =
            ∑ x : G, c * (f x * φ x⁻¹) := by
              apply Finset.sum_congr rfl
              intro x _
              ac_rfl
          _ = c * ∑ x : G, f x * φ x⁻¹ := by
              rw [Finset.mul_sum] }
  map_add' := by
    intro f g
    ext φ
    simp only [add_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [add_mul]
  map_smul' := by
    intro c f
    ext φ
    simp only [
      smul_apply,
      smul_eq_mul,
      RingHom.id_apply,
      LinearMap.smul_apply
    ]
    calc
      (∑ x : G, (c * f x) * φ x⁻¹)
          =
        ∑ x : G, c * (f x * φ x⁻¹) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [mul_assoc]
      _ = c * ∑ x : G, f x * φ x⁻¹ := by
          rw [Finset.mul_sum]

@[simp]
theorem characterPairingLeft_apply [Fintype G]
    (f φ : ClassFun k G) :
    characterPairingLeft k G f φ =
      ∑ x : G, f x * φ x⁻¹ :=
  rfl

open Classical in
/-- The indicator class function of the conjugacy class of `a`. -/
noncomputable def conjClassIndicator
    (k : Type u) [Zero k] [One k]
    {G : Type v} [Group G] (a : G) :
    ClassFun k G :=
  ofFun (fun x => if IsConj x a then 1 else 0)
    (by
      intro x g hxg
      have hiff : IsConj x a ↔ IsConj g a := by
        constructor
        · intro hxa
          exact hxg.symm.trans hxa
        · intro hga
          exact hxg.trans hga
      by_cases hxa : IsConj x a
      · have hga : IsConj g a := hiff.mp hxa
        simp only [hxa, hga]
      · have hga : ¬ IsConj g a := by
          intro hg
          exact hxa (hiff.mpr hg)
        simp only [hxa, hga])

open Classical in
@[simp]
lemma conjClassIndicator_apply
    (k : Type u) [Zero k] [One k]
    {G : Type v} [Group G] (a x : G) :
    conjClassIndicator k a x =
      if IsConj x a then 1 else 0 :=
  rfl

open BigOperators Classical in
/--
Pairing a class function `f` with the indicator of the conjugacy class of `a⁻¹`
gives the size of the conjugacy class of `a` multiplied by `f a`.
-/
lemma characterPairingLeft_conjClassIndicator
    [Fintype G]
    (f : ClassFun k G) (a : G) :
    ((characterPairingLeft k G) f) (conjClassIndicator k a⁻¹)
      =
    ((Finset.univ.filter fun x : G => IsConj x a).card : k) * f a := by
  rw [characterPairingLeft_apply]
  have h_inv_iff : ∀ x : G, IsConj x⁻¹ a⁻¹ ↔ IsConj x a := by
    intro x
    constructor
    · intro h
      exact IsConj.inv.mpr h
    · intro h
      exact IsConj.inv.mp h
  have h_summand :
      ∀ x : G,
        f x * (conjClassIndicator k a⁻¹) x⁻¹ =
          if IsConj x a then f a else 0 := by
    intro x
    by_cases hx : IsConj x a
    · have hx_inv : IsConj x⁻¹ a⁻¹ := (h_inv_iff x).mpr hx
      have hfx : f x = f a := f.map_conj x a hx
      simp only [conjClassIndicator_apply, hx, hx_inv, if_true, mul_one, hfx]
    · have hx_inv : ¬ IsConj x⁻¹ a⁻¹ := by
        intro h
        exact hx ((h_inv_iff x).mp h)
      simp only [conjClassIndicator_apply, hx, hx_inv, if_false, mul_zero]
  calc
    (∑ x : G, f x * (conjClassIndicator k a⁻¹) x⁻¹)
        =
      ∑ x : G, if IsConj x a then f a else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        exact h_summand x
    _ =
      Finset.sum
        (Finset.univ.filter (fun x : G => IsConj x a))
        (fun _ : G => f a) := by
        simpa using
          (Finset.sum_filter
            (s := (Finset.univ : Finset G))
            (p := fun x : G => IsConj x a)
            (f := fun _ : G => f a)).symm
    _ =
      ((Finset.univ.filter fun x : G => IsConj x a).card : k) * f a := by
        simp [Finset.sum_const, nsmul_eq_mul]

open Classical in
private lemma conjClass_card_cast_ne_zero
    [Fintype G] [CharZero k] (a : G) :
    ((Finset.univ.filter fun x : G => IsConj x a).card : k) ≠ 0 := by
  have hpos :
      0 < (Finset.univ.filter fun x : G => IsConj x a).card := by
    apply Finset.card_pos.mpr
    exact ⟨a, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsConj.refl a⟩
  exact_mod_cast Nat.ne_of_gt hpos

open Classical in
/--
The unnormalised character pairing is nondegenerate in its left argument.
-/
lemma characterPairingLeft_injective
    [Fintype G] [CharZero k] :
    Function.Injective
      (characterPairingLeft (k := k) (G := G)) := by
  intro f g hfg
  ext a
  have h_eval :=
    DFunLike.congr_fun hfg (conjClassIndicator k a⁻¹)
  rw [characterPairingLeft_conjClassIndicator f a,
      characterPairingLeft_conjClassIndicator g a] at h_eval
  exact mul_left_cancel₀ (conjClass_card_cast_ne_zero (k := k) a) h_eval


/--
The unnormalised character pairing identifies the space of class functions
with its linear dual.
-/
lemma characterPairingLeft_surjective
    [Fintype G] [CharZero k] :
    Function.Surjective
      (characterPairingLeft (k := k) (G := G)) := by
  have hinj :
    Function.Injective
      (characterPairingLeft (k := k) (G := G)) :=
    characterPairingLeft_injective (k := k) (G := G)
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := characterPairingLeft (k := k) (G := G))
      Subspace.dual_finrank_eq.symm).mp hinj

/--
The unnormalised character pairing as a linear equivalence from class functions
to their linear dual.
-/
noncomputable def characterPairingLinearEquiv
    [Fintype G] [CharZero k] :
    ClassFun k G ≃ₗ[k] Module.Dual k (ClassFun k G) :=
  LinearEquiv.ofBijective
    (characterPairingLeft (k := k) (G := G))
    ⟨characterPairingLeft_injective,
      characterPairingLeft_surjective⟩

open Classical in
/--
The unnormalised pairing of two characters is the group order times the
dimension of the corresponding Hom space.
-/
lemma characterPairingLeft_character_eq_card_mul_finrank_hom
    [Fintype G] [CharZero k]
    (V W : FDRep k G) :
    characterPairingLeft k G
        (ClassFun.character V)
        (ClassFun.character W)
      =
    (Fintype.card G : k) * (Module.finrank k (W ⟶ V) : k) := by
  have h := FDRep.char_scalarProduct_eq_finrank_hom V W
  have h_mul :=
    congrArg (fun z : k => (Fintype.card G : k) * z) h
  simpa only [
    characterPairingLeft_apply,
    ClassFun.char_apply,
    isUnit_iff_ne_zero,
    ne_eq,
    Nat.cast_eq_zero,
    Fintype.card_ne_zero,
    not_false_eq_true,
    IsUnit.mul_inv_cancel_left
  ] using h_mul

open Classical in
/--
The unnormalised pairing of two simple characters is the group order if the
representations are isomorphic, and zero otherwise.

This is the algebraically closed specialization of
`characterPairingLeft_character_eq_card_mul_finrank_hom`.
-/
lemma characterPairingLeft_character
    [Fintype G] [CharZero k] [IsAlgClosed k]
    (V W : FDRep k G)
    [Simple V] [Simple W] :
    characterPairingLeft k G
        (ClassFun.character V)
        (ClassFun.character W)
      =
    if Nonempty (V ≅ W) then
      (Fintype.card G : k)
    else
      0 := by
  rw [characterPairingLeft_character_eq_card_mul_finrank_hom V W]
  rw [FDRep.finrank_hom_simple W V]
  by_cases hWV : Nonempty (W ≅ V)
  · have hVW : Nonempty (V ≅ W) := by
      rcases hWV with ⟨e⟩
      exact ⟨e.symm⟩
    simp only [hWV, ↓reduceIte, Nat.cast_one, mul_one, hVW]
  · have hVW : ¬ Nonempty (V ≅ W) := by
      intro h
      rcases h with ⟨e⟩
      exact hWV ⟨e.symm⟩
    have hEmptyWV : IsEmpty (W ≅ V) := ⟨by
      intro e
      exact hWV ⟨e⟩⟩
    simp only [hWV, ↓reduceIte, CharP.cast_eq_zero, mul_zero, hVW]

end ClassFun

end Slop
