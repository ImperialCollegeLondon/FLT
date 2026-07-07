/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.Group.Basic
public import FLT.Slop.Background.FDRep.SimpleDecomposition
public import FLT.Slop.Background.Fintype.Basic

@[expose] public section

/-!
# Simple finite-dimensional representations

This file collects facts about simple objects in `FDRep`.

It includes Schur-type lemmas for simple representations over algebraically
closed fields, a Maschke-style rank-one characterization of simple
representations, and a quotient-lift result for representations trivial on a
normal subgroup.
-/

namespace FDRep

open CategoryTheory CategoryTheory.Limits

universe u v w

section Schur

/--
The identity linear map on the underlying module of a simple object of `FDRep`
is nonzero.
-/
lemma linearMap_id_ne_zero_of_simple
    {k : Type u} [CommRing k] {G : Type v} [Monoid G]
    (ρ : FDRep k G) [Simple ρ] :
    (LinearMap.id : ρ →ₗ[k] ρ) ≠ 0 := by
  have hid_cat : (𝟙 ρ : ρ ⟶ ρ) ≠ 0 := by
    exact id_nonzero ρ
  intro h0
  apply hid_cat
  apply FDRep.hom_ext
  intro x
  change (LinearMap.id : ρ →ₗ[k] ρ) x = (0 : ρ →ₗ[k] ρ) x
  exact congrArg (fun L : ρ →ₗ[k] ρ => L x) h0

/--
A simple object of `FDRep` has nontrivial underlying module.
-/
theorem nontrivial_of_simple
    {k : Type u} [CommRing k] {G : Type v} [Monoid G]
    (V : FDRep k G) [Simple V] :
    Nontrivial V := by
  by_contra hnt
  have hsub : Subsingleton V :=
    not_nontrivial_iff_subsingleton.mp hnt
  have h_id :
      (LinearMap.id : V →ₗ[k] V) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  exact linearMap_id_ne_zero_of_simple V h_id

/--
Scalar multiplication of the identity linear map is injective for a simple
FD representation.

Equivalently, if `a • id = b • id` as endomorphisms of the underlying module,
then `a = b`.
-/
lemma smul_id_injective
    {k : Type u} [Field k] {G : Type v} [Monoid G]
    (ρ : FDRep k G) [Simple ρ] :
    Function.Injective
      (fun a : k => a • (LinearMap.id : ρ →ₗ[k] ρ)) := by
  let I : ρ →ₗ[k] ρ := LinearMap.id
  have hid : I ≠ 0 := by
    simpa [I] using FDRep.linearMap_id_ne_zero_of_simple ρ
  intro a b hab
  have hsub : (a - b) • I = 0 := by
    have : a • I - b • I = 0 := by
      simpa using sub_eq_zero.mpr hab
    simpa [sub_smul] using this
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact (hid h).elim

/--
Schur's lemma for simple finite-dimensional representations:
every endomorphism of a simple `FDRep` is a scalar multiple of the identity.

This is the representation-theoretic form used later to show that central
group elements act by scalars.
-/
lemma end_eq_smul_id_of_simple
   {k : Type u} [Field k] [IsAlgClosed k]
   {G : Type v} [Monoid G]
   (ρ : FDRep k G) [Simple ρ] :
   ∀ f : ρ ⟶ ρ, ∃ a : k, f = a • 𝟙 ρ := by
  have hfin : Module.finrank k (ρ ⟶ ρ) = 1 := by
    simpa using
      (CategoryTheory.finrank_endomorphism_simple_eq_one (C := FDRep k G) (𝕜 := k) ρ)
  have hid : (𝟙 ρ : ρ ⟶ ρ) ≠ 0 := by exact id_nonzero ρ
  have hspan : (Submodule.span k ({(𝟙 ρ)} : Set (ρ ⟶ ρ))) = ⊤ := by
    have hspan_fin :
        Module.finrank k (Submodule.span k ({(𝟙 ρ)} : Set (ρ ⟶ ρ))) = 1 :=
          finrank_span_singleton hid
    apply Submodule.eq_top_of_finrank_eq
    rw [hspan_fin, ← hfin]
  intro f
  have hfmem : f ∈ Submodule.span k ({(𝟙 ρ)} : Set (ρ ⟶ ρ)) := by
    have hf_top : f ∈ (⊤ : Submodule k (ρ ⟶ ρ)) := _root_.trivial
    simp only [hspan, hf_top]
  rcases (Submodule.mem_span_singleton.mp hfmem) with ⟨a, rfl⟩
  exact ⟨a, by simp⟩

open Classical in
/--
Schur's lemma in dimension form: the Hom space between two simple
representations has dimension `1` if they are isomorphic and `0` otherwise.
-/
lemma finrank_hom_simple
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Type v} [Monoid G]
    (S T : FDRep k G) [Simple S] [Simple T] :
    Module.finrank k (S ⟶ T) =
      (if Nonempty (S ≅ T) then 1 else 0) := by
  by_cases hIso : Nonempty (S ≅ T)
  · simp only [hIso, ↓reduceIte]
    obtain ⟨e⟩ := hIso
    let E : (S ⟶ T) ≃ₗ[k] (S ⟶ S) :=
      { toFun := fun f => f ≫ e.inv
        invFun := fun f => f ≫ e.hom
        left_inv := by
          intro f
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        right_inv := by
          intro f
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        map_add' := by
          intro f g
          simp
        map_smul' := by
          intro c f
          simp only [Linear.smul_comp, RingHom.id_apply] }
    calc
      Module.finrank k (S ⟶ T)
          = Module.finrank k (S ⟶ S) := LinearEquiv.finrank_eq E
      _ = 1 := CategoryTheory.finrank_endomorphism_simple_eq_one k S
  · simp only [hIso, ↓reduceIte]
    have hsub : Subsingleton (S ⟶ T) := by
      refine ⟨fun f g => ?_⟩
      have hf0 : f = 0 := by
        by_contra hf_ne
        haveI : IsIso f := by exact isIso_of_hom_simple hf_ne
        exact False.elim (hIso ⟨asIso f⟩)
      have hg0 : g = 0 := by
        by_contra hg_ne
        haveI : IsIso g := by exact isIso_of_hom_simple hg_ne
        exact False.elim (hIso ⟨asIso g⟩)
      rw [hf0, hg0]
    exact Module.finrank_zero_iff.mpr hsub

open Classical in
/--
The dimension of maps from a simple representation into a finite biproduct of
simple representations is the number of summands isomorphic to it.
-/
lemma finrank_hom_to_biproduct_simple
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Type v} [Monoid G]
    {ι : Type w} [Fintype ι]
    (S : FDRep k G) [Simple S]
    (f : ι → FDRep k G) [HasBiproduct f]
    (hf : ∀ i, Simple (f i)) :
    Module.finrank k (S ⟶ ⨁ f) =
      ∑ i, (if Nonempty (S ≅ f i) then 1 else 0) := by
  haveI : ∀ i, Simple (f i) := hf
  calc
    Module.finrank k (S ⟶ ⨁ f)
        = ∑ i, Module.finrank k (S ⟶ f i) :=
          finrank_hom_to_biproduct_eq_sum (S := S) (f := f)
    _ = ∑ i, (if Nonempty (S ≅ f i) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact finrank_hom_simple S (f i)

end Schur

section homSpace
/--
There are no nonzero morphisms between nonisomorphic simple FD representations.
-/
lemma hom_eq_zero_of_not_iso_simple
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    {S T : FDRep k G} [Simple S] [Simple T]
    (h : IsEmpty (S ≅ T)) :
    ∀ f : S ⟶ T, f = 0 := by
  intro f
  by_contra hf
  haveI : IsIso f := isIso_of_hom_simple hf
  exact h.false (asIso f)

/--
There are no nonzero morphisms between nonisomorphic simple FD representations.
-/
lemma hom_subsingleton_of_not_iso_simple
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    {S T : FDRep k G} [Simple S] [Simple T]
    (h : IsEmpty (S ≅ T)) :
    Subsingleton (S ⟶ T) := by
  refine ⟨fun f g => ?_⟩
  have hf0 : f = 0 := by
    by_contra hf_ne
    haveI : IsIso f := isIso_of_hom_simple hf_ne
    exact h.false (asIso f)
  have hg0 : g = 0 := by
    by_contra hg_ne
    haveI : IsIso g := isIso_of_hom_simple hg_ne
    exact h.false (asIso g)
  rw [hf0, hg0]

/--
The Hom space between two nonisomorphic simple FD representations has dimension
zero.
-/
lemma finrank_hom_eq_zero_of_not_iso_simple
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    {S T : FDRep k G} [Simple S] [Simple T]
    (h : IsEmpty (S ≅ T)) :
    Module.finrank k (S ⟶ T) = 0 := by
  haveI : Subsingleton (S ⟶ T) :=
    hom_subsingleton_of_not_iso_simple h
  exact Module.finrank_zero_of_subsingleton

/--
The identity endomorphism of a simple FD representation is nonzero.

This is the categorical version of `linearMap_id_ne_zero_of_simple`.
-/
lemma id_hom_ne_zero_of_simple
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    (S : FDRep k G) [Simple S] :
    (𝟙 S : S ⟶ S) ≠ 0 := by
  intro h
  apply linearMap_id_ne_zero_of_simple S
  have hlin :
      FDRep.homToLinearMap (𝟙 S : S ⟶ S) = 0 := by
    exact congrArg (fun f : S ⟶ S => FDRep.homToLinearMap f) h
  simpa using hlin

/--
The endomorphism space of a simple FD representation has nonzero dimension.
-/
lemma finrank_end_ne_zero_of_simple
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    (S : FDRep k G) [Simple S] :
    Module.finrank k (S ⟶ S) ≠ 0 := by
  have hpos : 0 < Module.finrank k (S ⟶ S) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨𝟙 S, id_hom_ne_zero_of_simple S⟩
  exact Nat.ne_of_gt hpos
end homSpace

lemma finrank_end_cast_ne_zero_of_simple
    {k : Type u} [Field k] [CharZero k]
    {G : Type v} [Monoid G]
    (S : FDRep k G) [Simple S] :
    (Module.finrank k (S ⟶ S) : k) ≠ 0 := by
  exact_mod_cast finrank_end_ne_zero_of_simple S

section QuotientLift

lemma lift_simple_of_simple
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    [Finite G] [IsAlgClosed k] [CharZero k]
    (ρ : FDRep k G) (K : Subgroup G) [K.Normal]
    (h_triv : ∀ x ∈ K, ρ.ρ x = 1) [Simple ρ] :
    Simple (FDRep.lift ρ K h_triv) := by
  let ρ' : FDRep k (G ⧸ K) := FDRep.lift ρ K h_triv
  have hρ'_mk :
      ∀ g : G, ρ'.ρ (QuotientGroup.mk' K g) = ρ.ρ g := by
    intro g
    dsimp [ρ', FDRep.lift]
    rfl
  have hρ'_lift :
      ∀ q : G ⧸ K, ρ'.ρ q = (QuotientGroup.lift K ρ.ρ (by
        intro x hx
        exact h_triv x hx)) q := by
    intro q
    dsimp [ρ', FDRep.lift]
    rfl
  let toEnd : (ρ' ⟶ ρ') →ₗ[k] (ρ ⟶ ρ) :=
  { toFun := fun f =>
      FDRep.forget₂HomLinearEquiv ρ ρ
        (Rep.ofHom
          { toLinearMap := by
              change ρ →ₗ[k] ρ
              exact FDRep.homToLinearMap (H := G ⧸ K) f
            isIntertwining' := by
              intro g
              ext x
              change
                FDRep.homToLinearMap (H := G ⧸ K) f ((ρ.ρ g) x)
                  =
                (ρ.ρ g) (FDRep.homToLinearMap (H := G ⧸ K) f x)
              have h :=
                FDRep.homToLinearMap_comm f (QuotientGroup.mk' K g) x
              rw [← hρ'_mk g]
              exact h })
    map_add' := by
      intro f g
      apply FDRep.hom_ext
      intro x
      rfl
    map_smul' := by
      intro c f
      apply FDRep.hom_ext
      intro x
      rfl }
  let fromEnd : (ρ ⟶ ρ) →ₗ[k] (ρ' ⟶ ρ') :=
  { toFun := fun f =>
      FDRep.forget₂HomLinearEquiv ρ' ρ'
        (Rep.ofHom
          { toLinearMap := by
              change ρ' →ₗ[k] ρ'
              exact FDRep.homToLinearMap (H := G) f
            isIntertwining' := by
              intro q
              refine Quotient.inductionOn q ?_
              intro g
              ext x
              change
                FDRep.homToLinearMap (H := G) f ((ρ'.ρ (QuotientGroup.mk' K g)) x)
                  =
                (ρ'.ρ (QuotientGroup.mk' K g)) (FDRep.homToLinearMap f x)
              rw [hρ'_mk g]
              exact FDRep.homToLinearMap_comm (G := G) f g x })
    map_add' := by
      intro f g
      apply FDRep.hom_ext
      intro x
      rfl
    map_smul' := by
      intro c f
      apply FDRep.hom_ext
      intro x
      rfl }
  let eEnd : (ρ' ⟶ ρ') ≃ₗ[k] (ρ ⟶ ρ) :=
  { toFun := toEnd
    invFun := fromEnd
    left_inv := by
      intro f
      apply FDRep.hom_ext
      intro x
      rfl
    right_inv := by
      intro f
      apply FDRep.hom_ext
      intro x
      rfl
    map_add' := by
      intro f g
      rfl
    map_smul' := by
      intro c f
      rfl }
  haveI : NeZero (Nat.card G : k) := by
    exact ⟨by
      exact_mod_cast One.natCard_ne_zero_of_finite G⟩
  have hρ : Module.finrank k (ρ ⟶ ρ) = 1 := by
    exact finrank_endomorphism_simple_eq_one k ρ
  have hEq :
      Module.finrank k (ρ' ⟶ ρ') =
        Module.finrank k (ρ ⟶ ρ) := by
    simpa using LinearEquiv.finrank_eq eEnd
  have hρ' : Module.finrank k (ρ' ⟶ ρ') = 1 := by
    simpa [hρ] using hEq
  haveI : NeZero (Nat.card (G ⧸ K) : k) := by
    exact ⟨by
      exact_mod_cast One.natCard_ne_zero_of_finite (G ⧸ K)⟩
  exact (FDRep.simple_iff_end_is_rank_one (V := ρ')).2 hρ'

end QuotientLift

end FDRep
