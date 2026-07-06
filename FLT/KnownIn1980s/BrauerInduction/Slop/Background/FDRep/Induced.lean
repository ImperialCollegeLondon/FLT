/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.CategoryTheory.Adjunction.Unique
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Res

@[expose] public section

/-!
# Induction and coinduction of finite-dimensional representations

This file defines induction and coinduction for `FDRep`.

Main definitions:

* `FDRep.indHom`: induction along a group homomorphism;
* `FDRep.ind`: induction from a subgroup;
* `FDRep.coindHom`: coinduction along a group homomorphism;
* `FDRep.coind`: coinduction from a subgroup;
* `FDRep.indIsoCoind`: the finite-group isomorphism between induction and
  coinduction;
* Frobenius reciprocity for induction and restriction;
* induction from the top subgroup;
* transitivity of induction.

Several subgroup-level statements require the ambient group to be in the same
universe as the coefficient ring.  This reflects the universe shape of Mathlib
`FDRep`: the carrier of an object of `FDRep k G` lives in the coefficient
universe, while induced and coinduced `Rep`s are built from the target group.

-/

universe u v v' w

open CategoryTheory

namespace FDRep

/-! ### Induction along an arbitrary group homomorphism -/

section HomInduction

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H]

/--
Induction of a finite-dimensional representation along a group homomorphism.

The target group is assumed finite so that the induced representation has
finitely generated underlying module.
-/
noncomputable def indHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    FDRep k H := by
  let A : Rep k G := asRep σ
  let τind : Rep k H := Rep.ind φ A
  have h_fin_τ : Module.Finite k τind.V := by
    letI : Fintype H := Fintype.ofFinite H
    haveI : Module.Finite k A.V := by
      change Module.Finite k σ
      infer_instance
    exact Module.Finite.of_surjective
      (Representation.Coinvariants.mk _) (Submodule.mkQ_surjective _)
  haveI : Module.Finite k τind.V := h_fin_τ
  exact FDRep.of τind.ρ

@[simp]
lemma forget₂_obj_indHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    (forget₂ (FDRep k H) (Rep k H)).obj (indHom φ σ) =
      Rep.ind φ (asRep σ) := by
  rfl

/-- Induction along a homomorphism on morphisms. -/
noncomputable def indHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    indHom φ A ⟶ indHom φ B :=
  FDRep.forget₂HomLinearEquiv (indHom φ A) (indHom φ B)
    (Rep.indMap φ ((forget₂ (FDRep k G) (Rep k G)).map f))

@[simp]
lemma forget₂_map_indHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    (forget₂ (FDRep k H) (Rep k H)).map (indHomMap φ f) =
      Rep.indMap φ ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

/-- Induction along a homomorphism as a functor. -/
@[simps obj map]
noncomputable def indHomFunctor [Finite H]
    (φ : G →* H) :
    FDRep k G ⥤ FDRep k H where
  obj A := indHom φ A
  map f := indHomMap φ f
  map_id X := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.indFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (𝟙 X)) = 𝟙 (F.obj (U_G.obj X))
    simp only [CategoryTheory.Functor.map_id, F.map_id (U_G.obj X)]
  map_comp {X Y Z} f g := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.indFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (f ≫ g)) = F.map (U_G.map f) ≫ F.map (U_G.map g)
    rw [Functor.map_comp]
    exact F.map_comp (U_G.map f) (U_G.map g)

end HomInduction


/-! ### Subgroup induction as a special case -/

section SubgroupInduction

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- Induction from a subgroup, defined a special case of `indHom`. -/
noncomputable abbrev ind [Finite G] (H : Subgroup G) (σ : FDRep k H) : FDRep k G :=
  indHom H.subtype σ

/-- Map on subgroup-induced morphisms. -/
noncomputable abbrev indMap [Finite G] (H : Subgroup G) {A B : FDRep k H} (f : A ⟶ B) :
    ind H A ⟶ ind H B :=
  indHomMap H.subtype f

/-- Induction from a subgroup as a functor. -/
@[simps!]
noncomputable abbrev indFunctor [Finite G] (H : Subgroup G) : FDRep k H ⥤ FDRep k G :=
  indHomFunctor H.subtype

@[simp]
lemma forget₂_obj_ind [Finite G] (H : Subgroup G) (σ : FDRep k H) :
    (forget₂ (FDRep k G) (Rep k G)).obj (ind H σ) =
      Rep.ind H.subtype (asRep σ) := by
  rfl

/-- Functoriality: Induction preserves isomorphisms in FDRep. -/
noncomputable def indMapIso [Finite G] (H : Subgroup G) {V W : FDRep k H} (e : V ≅ W) :
    ind H V ≅ ind H W :=
  (indFunctor H).mapIso e

end SubgroupInduction

section HomCoinduction

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H]

/--
Coinduction of a finite-dimensional representation along a group homomorphism.

The target group is assumed finite, and the coefficient ring is assumed
Noetherian so that the coinduced representation, realized as a submodule of a
finite product, is again finitely generated.
-/
noncomputable def coindHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    FDRep k H := by
  let A : Rep k G := asRep σ
  let τcoind : Rep k H := Rep.coind φ A
  have h_fin_τ : Module.Finite k τcoind.V := by
    letI : Fintype H := Fintype.ofFinite H
    haveI : Module.Finite k A.V := by
      change Module.Finite k σ
      infer_instance
    -- The ambient function space is finite as `H` is finite.
    haveI : Module.Finite k (H → A.V) :=
      Module.Finite.pi_iff.mpr fun _ => inferInstance
    -- The coinduced space is a submodule of this finite module.
    exact Module.Finite.of_injective
      (Submodule.subtype (Representation.coindV φ A.ρ))
      (by
        intro x y h
        exact Subtype.ext h)
  haveI : Module.Finite k τcoind.V := h_fin_τ
  exact FDRep.of τcoind.ρ

@[simp]
lemma forget₂_obj_coindHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    (forget₂ (FDRep k H) (Rep k H)).obj (coindHom φ σ) =
      Rep.coind φ (asRep σ) := by
  rfl

/-- Coinduction along a homomorphism on morphisms. -/
noncomputable def coindHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    coindHom φ A ⟶ coindHom φ B :=
  FDRep.forget₂HomLinearEquiv (coindHom φ A) (coindHom φ B)
    (Rep.coindMap φ ((forget₂ (FDRep k G) (Rep k G)).map f))

@[simp]
lemma forget₂_map_coindHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    (forget₂ (FDRep k H) (Rep k H)).map (coindHomMap φ f) =
      Rep.coindMap φ ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

/-- Coinduction along a homomorphism as a functor. -/
@[simps obj map]
noncomputable def coindHomFunctor [Finite H]
    (φ : G →* H) :
    FDRep k G ⥤ FDRep k H where
  obj A := coindHom φ A
  map f := coindHomMap φ f
  map_id X := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.coindFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (𝟙 X)) = 𝟙 (F.obj (U_G.obj X))
    simp only [CategoryTheory.Functor.map_id, F.map_id (U_G.obj X)]
  map_comp {X Y Z} f g := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.coindFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (f ≫ g)) = F.map (U_G.map f) ≫ F.map (U_G.map g)
    rw [Functor.map_comp]
    exact F.map_comp (U_G.map f) (U_G.map g)

end HomCoinduction

/-! ### Subgroup coinduction as a special case -/

section SubgroupCoinduction

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- Coinduction from a subgroup, defined as a special case of `coindHom`. -/
noncomputable abbrev coind [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) (σ : FDRep k H) : FDRep k G :=
  coindHom H.subtype σ

/-- Map on subgroup-coinduced morphisms. -/
noncomputable abbrev coindMap [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) {A B : FDRep k H} (f : A ⟶ B) :
    coind H A ⟶ coind H B :=
  coindHomMap H.subtype f

/-- Coinduction from a subgroup as a functor. -/
@[simps!]
noncomputable abbrev coindFunctor [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) : FDRep k H ⥤ FDRep k G :=
  coindHomFunctor H.subtype

@[simp]
lemma forget₂_obj_coind [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) (σ : FDRep k H) :
    (forget₂ (FDRep k G) (Rep k G)).obj (coind H σ) =
      Rep.coind H.subtype (asRep σ) := by
  rfl

/-- Functoriality: coinduction preserves isomorphisms in `FDRep`. -/
noncomputable def coindMapIso [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) {V W : FDRep k H} (e : V ≅ W) :
    coind H V ≅ coind H W :=
  (coindFunctor H).mapIso e

end SubgroupCoinduction

section indIsoCoind

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
variable {G : Type u} [Group G]

open Classical in
/--
The isomorphism `Ind ≅ Coind` in `FDRep` for finite groups.
-/
noncomputable def indIsoCoind [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I) :
    FDRep.ind I σ ≅ FDRep.coind I σ := by
  letI : DecidableRel (QuotientGroup.rightRel I) := Classical.decRel _
  haveI : I.FiniteIndex := by infer_instance
  let A : Rep k I := asRep σ
  let e : Rep.ind I.subtype A ≅ Rep.coind I.subtype A :=
    Rep.indCoindIso (S := I) A
  refine
    { hom :=
        FDRep.forget₂HomLinearEquiv
          (FDRep.ind I σ) (FDRep.coind I σ) e.hom
      inv :=
        FDRep.forget₂HomLinearEquiv
          (FDRep.coind I σ) (FDRep.ind I σ) e.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change e.hom ≫ e.inv = 𝟙 (Rep.ind I.subtype A)
    exact e.hom_inv_id
  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change e.inv ≫ e.hom = 𝟙 (Rep.coind I.subtype A)
    exact e.inv_hom_id

end indIsoCoind

section HomFrobeniusReciprocity

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H] [Finite H]

/--
Frobenius reciprocity for induction and pullback along a group homomorphism.

For `φ : G →* H`, morphisms from the induced representation `indHom φ σ` to
`ρ` correspond linearly to morphisms from `σ` to the pulled-back representation
`comap φ ρ`.
-/
noncomputable def indHomComapEquiv
    (φ : G →* H)
    (σ : FDRep k G)
    (ρ : FDRep k H) :
    (indHom φ σ ⟶ ρ) ≃ₗ[k]
      (σ ⟶ comap (G := H) (H := G) φ ρ) := by
  let UG : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
  let UH : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
  let A : Rep k G := UG.obj σ
  let B : Rep k H := UH.obj ρ
  let ρres : FDRep k G := comap (G := H) (H := G) φ ρ
  let e₁ : (indHom φ σ ⟶ ρ) ≃ₗ[k] (Rep.ind φ A ⟶ B) :=
    (FDRep.forget₂HomLinearEquiv (indHom φ σ) ρ).symm
  let e₂ : (Rep.ind φ A ⟶ B) ≃ₗ[k] (A ⟶ Rep.res φ B) :=
    Rep.indResHomEquiv φ A B
  let e₃ : (A ⟶ Rep.res φ B) ≃ₗ[k] (σ ⟶ ρres) :=
    FDRep.forget₂HomLinearEquiv σ ρres
  exact e₁.trans (e₂.trans e₃)

end HomFrobeniusReciprocity

/-! ### Frobenius reciprocity for subgroup induction -/

section SubgroupFrobeniusReciprocity

variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G] [Finite G]

variable (I : Subgroup G)

/--
Frobenius reciprocity for induction from a subgroup.
-/
noncomputable def indResHomEquiv
    (σ : FDRep k I) (ρ : FDRep k G) :
    (FDRep.ind I σ ⟶ ρ) ≃ₗ[k] (σ ⟶ FDRep.res ρ I) :=
  indHomComapEquiv
    (G := I) (H := G)
    I.subtype σ ρ

noncomputable def indResUnit (σ : FDRep k I) :
    σ ⟶ res (G := G) (FDRep.ind (G := G) I σ) I :=
  FDRep.indResHomEquiv (I := I) σ (FDRep.ind (G := G) I σ) (𝟙 _)

noncomputable def indResCounit (ρ : FDRep k G) :
    FDRep.ind (G := G) I
        (res (G := G) ρ I) ⟶ ρ :=
  (FDRep.indResHomEquiv (I := I)
      (res (G := G) ρ I) ρ).symm (𝟙 _)

@[simp]
lemma indResHomEquiv_id
    (σ : FDRep k I) :
    FDRep.indResHomEquiv I σ (FDRep.ind I σ) (𝟙 _) =
      FDRep.indResUnit I σ := by
  rfl

@[simp]
lemma indResHomEquiv_symm_id
    (ρ : FDRep k G) :
    (FDRep.indResHomEquiv I (FDRep.res ρ I) ρ).symm (𝟙 _) =
      FDRep.indResCounit I ρ := by
  rfl

/-- The Hom-set equivalence for Frobenius reciprocity on subgroups. -/
noncomputable def indResEquiv
    (H : Subgroup G)
    (σ : FDRep k H)
    (ρ : FDRep k G) :
    (FDRep.ind H σ ⟶ ρ) ≃ₗ[k] (σ ⟶ FDRep.res ρ H) :=
  indHomComapEquiv H.subtype σ ρ

@[simp]
lemma forget₂_map_indResHomEquiv
    (σ : FDRep k I) (ρ : FDRep k G)
    (f : FDRep.ind I σ ⟶ ρ) :
    (forget₂ (FDRep k I) (Rep k I)).map
        (FDRep.indResHomEquiv (k := k) (G := G) I σ ρ f)
      =
    Rep.indResHomEquiv I.subtype
      ((forget₂ (FDRep k I) (Rep k I)).obj σ)
      ((forget₂ (FDRep k G) (Rep k G)).obj ρ)
      ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

@[simp]
lemma forget₂_map_indResHomEquiv_symm
    (σ : FDRep k I) (ρ : FDRep k G)
    (f : σ ⟶ FDRep.res ρ I) :
    (forget₂ (FDRep k G) (Rep k G)).map
        ((FDRep.indResHomEquiv (k := k) (G := G) I σ ρ).symm f)
      =
    (Rep.indResHomEquiv I.subtype
      ((forget₂ (FDRep k I) (Rep k I)).obj σ)
      ((forget₂ (FDRep k G) (Rep k G)).obj ρ)).symm
      ((forget₂ (FDRep k I) (Rep k I)).map f) := by
  rfl

end SubgroupFrobeniusReciprocity

section top

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G] [Finite G]

/--
The equivalence between representations of the top subgroup and representations
of the group, viewed as an adjunction.
-/
noncomputable def ofTopResAdjunction :
    FDRep.ofTopFunctor (k:= k) (G := G) ⊣
      FDRep.resFunctor (⊤ : Subgroup G) :=
  (FDRep.ofTopEquivalence (G := G)).toAdjunction

end top

section transitivity

variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G] [Finite G]

/--
Transitivity of subgroup induction.

If `H ≤ I ≤ G`, then induction from `H` to `I` followed by induction from `I`
to `G` is isomorphic to induction from the image of `H` in `G`, after
transporting the representation along the canonical isomorphism
`H ≃* H.map I.subtype`.

This proof works at the `Rep` level and then lifts the resulting isomorphism
through the fully faithful forgetful functor `FDRep k G ⥤ Rep k G`.
-/
noncomputable def indTrans
    {I : Subgroup G} {H : Subgroup I}
    (V : FDRep k H) :
    FDRep.ind (G := G) I
        (FDRep.ind (G := I) H V)
      ≅
    FDRep.ind (G := G) (H.map I.subtype)
      (FDRep.transport
        (H.equivMapOfInjective I.subtype Subtype.coe_injective) V) := by
  let H' : Subgroup G := H.map I.subtype
  let e : H ≃* H' := H.equivMapOfInjective I.subtype Subtype.coe_injective
  let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
  let U_I : FDRep k I ⥤ Rep k I := forget₂ (FDRep k I) (Rep k I)
  let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
  let L1 : Rep k I ⥤ Rep k G := Rep.indFunctor k I.subtype
  let L2 : Rep k H ⥤ Rep k I := Rep.indFunctor k H.subtype
  let L3 : Rep k H' ⥤ Rep k G := Rep.indFunctor k H'.subtype
  let T_trans : Rep k H ⥤ Rep k H' := Rep.resFunctor e.symm.toMonoidHom
  let T_inv : Rep k H' ⥤ Rep k H := Rep.resFunctor e.toMonoidHom
  let R1 : Rep k G ⥤ Rep k I := Rep.resFunctor I.subtype
  let R2 : Rep k I ⥤ Rep k H := Rep.resFunctor H.subtype
  let R3 : Rep k G ⥤ Rep k H' := Rep.resFunctor H'.subtype
  let iso_R : (R1 ⋙ R2) ≅ (R3 ⋙ T_inv) := Iso.refl _
  let adj_T : T_trans ⊣ T_inv :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun X Y =>
          { toFun := fun f =>
              Rep.ofHom
                { toLinearMap := f.hom
                  isIntertwining' := by
                    intro h
                    ext x
                    have hf := Rep.hom_comm_apply f (e h) x
                    change f.hom ((X.ρ h) x) = Y.ρ (e h) (f.hom x)
                    have hact : ((T_trans.obj X).ρ (e h)) x = (X.ρ h) x := by
                      change (X.ρ (e.symm (e h))) x = (X.ρ h) x
                      simp only [MulEquiv.symm_apply_apply]
                    rw [← hact]
                    exact hf }

            invFun := fun g =>
              Rep.ofHom
                { toLinearMap := g.hom
                  isIntertwining' := by
                    intro h'
                    ext x
                    have hg := Rep.hom_comm_apply g (e.symm h') x
                    change g.hom ((X.ρ (e.symm h')) x) = Y.ρ h' (g.hom x)
                    have hact :
                        ((T_inv.obj Y).ρ (e.symm h')) (g.hom x) =
                          (Y.ρ h') (g.hom x) := by
                      change (Y.ρ (e (e.symm h'))) (g.hom x) = (Y.ρ h') (g.hom x)
                      simp only [MulEquiv.apply_symm_apply]
                    rw [← hact]
                    exact hg }
            left_inv := by intro f; apply Rep.hom_ext; rfl
            right_inv := by intro f; apply Rep.hom_ext; rfl } }
  let adj₁ : L2 ⋙ L1 ⊣ R1 ⋙ R2 :=
    (Rep.indResAdjunction k H.subtype).comp (Rep.indResAdjunction k I.subtype)
  let adjIndH' : L3 ⊣ R3 := Rep.indResAdjunction k H'.subtype
  let adj₂pre : T_trans ⋙ L3 ⊣ R3 ⋙ T_inv := adj_T.comp adjIndH'
  let adj₂ := Adjunction.ofNatIsoRight adj₂pre iso_R.symm
  let isoRep := (Adjunction.leftAdjointUniq adj₁ adj₂).app (U_H.obj V)
  exact isoOfAsRepIso isoRep

end transitivity

section top

variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G] [Finite G]

section top

variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G] [Finite G]

def topSubgroupMulEquiv (G : Type u) [Group G] :
    (⊤ : Subgroup G) ≃* G where
  toFun x := x
  invFun g := ⟨g, by simp⟩
  left_inv x := by
    ext
    rfl
  right_inv g := rfl
  map_mul' x y := rfl

/--
Induction from the top subgroup agrees with transporting a representation of
`⊤` to a representation of `G`.
-/
noncomputable def indTopIsoOfTop
    (V : FDRep k (⊤ : Subgroup G)) :
    FDRep.ind (k := k) (G := G) (⊤ : Subgroup G) V ≅
      FDRep.ofTop (G := G) (k := k) V := by
  let T : Subgroup G := ⊤
  let e : T ≃* G := topSubgroupMulEquiv G
  let U_T : FDRep k T ⥤ Rep k T :=
    forget₂ (FDRep k T) (Rep k T)
  let U_G : FDRep k G ⥤ Rep k G :=
    forget₂ (FDRep k G) (Rep k G)
  let L_ind : Rep k T ⥤ Rep k G :=
    Rep.indFunctor k T.subtype
  let R_ind : Rep k G ⥤ Rep k T :=
    Rep.resFunctor T.subtype
  let T_top : Rep k T ⥤ Rep k G :=
    Rep.resFunctor e.symm.toMonoidHom
  let T_inv : Rep k G ⥤ Rep k T :=
    Rep.resFunctor e.toMonoidHom
  let iso_R : R_ind ≅ T_inv := Iso.refl _
  let adj_T : T_top ⊣ T_inv :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun X Y =>
          { toFun := fun f =>
              Rep.ofHom
                { toLinearMap := f.hom
                  isIntertwining' := by
                    intro h
                    ext x
                    have hf := Rep.hom_comm_apply f (e h) x
                    change f.hom ((X.ρ h) x) = Y.ρ (e h) (f.hom x)
                    have hact :
                        ((T_top.obj X).ρ (e h)) x = (X.ρ h) x := by
                      change (X.ρ (e.symm (e h))) x = (X.ρ h) x
                      simp only [MulEquiv.symm_apply_apply]
                    rw [← hact]
                    exact hf }

            invFun := fun g =>
              Rep.ofHom
                { toLinearMap := g.hom
                  isIntertwining' := by
                    intro h'
                    ext x
                    have hg := Rep.hom_comm_apply g (e.symm h') x
                    change g.hom ((X.ρ (e.symm h')) x) = Y.ρ h' (g.hom x)
                    have hact :
                        ((T_inv.obj Y).ρ (e.symm h')) (g.hom x) =
                          (Y.ρ h') (g.hom x) := by
                      change
                        (Y.ρ (e (e.symm h'))) (g.hom x) =
                          (Y.ρ h') (g.hom x)
                      simp only [MulEquiv.apply_symm_apply]
                    rw [← hact]
                    exact hg }

            left_inv := by
              intro f
              apply Rep.hom_ext
              rfl

            right_inv := by
              intro f
              apply Rep.hom_ext
              rfl } }
  let adj_ind : L_ind ⊣ R_ind :=
    Rep.indResAdjunction k T.subtype
  let adj_top : T_top ⊣ R_ind :=
    Adjunction.ofNatIsoRight adj_T iso_R.symm
  let isoRep :=
    (Adjunction.leftAdjointUniq adj_ind adj_top).app (U_T.obj V)
  exact isoOfAsRepIso isoRep

end top



end top

end FDRep
