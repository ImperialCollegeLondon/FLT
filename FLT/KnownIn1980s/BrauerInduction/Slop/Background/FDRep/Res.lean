/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Basic
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.Basic

@[expose] public section

/-!
# Restriction and transport of finite-dimensional representations

This file defines pullback of finite-dimensional representations along monoid
homomorphisms, restriction to subgroups, and transport along monoid
isomorphisms.

Main definitions:

* `FDRep.comap`: pull back a representation along a monoid homomorphism;
* `FDRep.res`: restrict a representation of a group to a subgroup;
* `FDRep.transport`: transport a representation along a monoid isomorphism;
* `FDRep.transportEquiv`: transport along a monoid isomorphism as an
  equivalence of categories;
* `FDRep.ofTop`: identify representations of the top subgroup with
  representations of the ambient group.
-/

universe u v w x

variable {k : Type u} {G : Type v}

namespace FDRep

open CategoryTheory

section Comap

variable {H : Type w} [CommRing k] [Monoid G] [Monoid H]

/--
Pull back a finite-dimensional representation along a monoid homomorphism.

If `ρ` is a representation of `G` and `φ : H →* G`, then `comap φ ρ`
is the representation of `H` in which `h : H` acts as `ρ (φ h)`.
-/
noncomputable def comap (φ : H →* G) (ρ : FDRep k G) : FDRep k H :=
  FDRep.of (ρ.ρ.comp φ)

@[simp]
lemma comap_ρ (φ : H →* G) (ρ : FDRep k G) :
    (comap φ ρ).ρ = ρ.ρ.comp φ := by
  simp only [comap, FGModuleCat.of_carrier, FDRep.of_ρ' (ρ.ρ.comp φ)]

/-- The dimension of a representation remains the same upon homomorphism restriction. -/
lemma finrank_comap (φ : H →* G) (σ : FDRep k G) :
    Module.finrank k (comap φ σ) = Module.finrank k σ := by
  rfl

/--
Pull back a morphism of finite-dimensional representations along a monoid
homomorphism. The underlying linear map is unchanged.
-/
noncomputable def comapMap (φ : H →* G) {ρ σ : FDRep k G} (f : ρ ⟶ σ) :
    comap φ ρ ⟶ comap φ σ :=
  FDRep.forget₂HomLinearEquiv (comap φ ρ) (comap φ σ)
    (Rep.ofHom
      { toLinearMap := FDRep.homToLinearMap (H := G) f
        isIntertwining' := by
          intro h
          ext x
          exact FDRep.homToLinearMap_comm f (φ h) x })

@[simp]
lemma comapMap_homToLinearMap_apply
    (φ : H →* G) {ρ σ : FDRep k G} (f : ρ ⟶ σ)
    (x : comap φ ρ) :
    FDRep.homToLinearMap (H := H) (comapMap φ f) x =
      FDRep.homToLinearMap (H := G) f x := by
  rfl

@[simp] lemma comapMap_hom_toLinearMap (φ : H →* G) {ρ σ : FDRep k G} (f : ρ ⟶ σ) :
    FDRep.homToLinearMap (comapMap φ f) = FDRep.homToLinearMap f := rfl

/--
Pullback of finite-dimensional representations along a monoid homomorphism,
as a functor.
-/
@[simps obj map]
noncomputable def comapFunctor (φ : H →* G) : FDRep k G ⥤ FDRep k H where
  obj ρ := comap φ ρ
  map f := comapMap φ f
  map_id ρ := by
    apply FDRep.hom_ext
    intro x
    dsimp [comap, comapMap, FDRep.homToLinearMap]
    rfl
  map_comp f g := by
    apply FDRep.hom_ext
    intro x
    change
      FDRep.homToLinearMap (H := G) (f ≫ g) x =
        FDRep.homToLinearMap (H := G) g
          (FDRep.homToLinearMap (H := G) f x)
    rw [FDRep.homToLinearMap_comp]
    rfl

/-- Restricting an isomorphism along a homomorphism gives an isomorphism. -/
noncomputable def comapMapIso (φ : H →* G) {V W : FDRep k G} (i : V ≅ W) :
    comap φ V ≅ comap φ W :=
  (comapFunctor φ).mapIso i

/--
Pullback along a composite homomorphism is naturally isomorphic to iterated pullback.
-/
noncomputable def comapFunctorCompIso
    {H : Type w} {K : Type x} [Monoid H] [Monoid K]
    (φ : H →* G) (ψ : K →* H) :
    comapFunctor (k := k) φ ⋙ comapFunctor (k := k) ψ
      ≅ comapFunctor (k := k) (φ.comp ψ) :=
  NatIso.ofComponents (fun ρ ↦ Iso.refl _) (fun f ↦ by
    apply FDRep.hom_ext
    intro x
    rfl)

end Comap

section SubgroupRestriction

variable [CommRing k] [Group G]

/--
Restrict a finite-dimensional representation of `G` to a subgroup `I`.
-/
noncomputable def res (ρ : FDRep k G) (I : Subgroup G) : FDRep k I :=
  comap I.subtype ρ

@[simp]
lemma res_ρ (ρ : FDRep k G) (I : Subgroup G) :
    (res ρ I).ρ = ρ.ρ.comp I.subtype := by
  rfl

lemma finrank_res (σ : FDRep k G) (I : Subgroup G) :
    Module.finrank k (res σ I) = Module.finrank k σ := rfl

/-- Restriction to a subgroup as a functor. -/
noncomputable def resFunctor (I : Subgroup G) : FDRep k G ⥤ FDRep k I :=
  comapFunctor I.subtype

/-- Restricting an isomorphism to a subgroup gives an isomorphism. -/
noncomputable def resMapIso (I : Subgroup G) {V W : FDRep k G} (i : V ≅ W) :
    res V I ≅ res W I :=
  (resFunctor I).mapIso i

end SubgroupRestriction

section Transport

variable {H : Type w} [CommRing k] [Monoid G] [Monoid H]

/-- Transport a representation along a monoid isomorphism `e : G ≃* H`. -/
noncomputable def transport (e : G ≃* H) (V : FDRep k G) : FDRep k H :=
  comap e.symm.toMonoidHom V

/-- The dimension of a representation remains the same upon transport. -/
lemma finrank_transport (e : G ≃* H) (σ : FDRep k G) :
    Module.finrank k (transport e σ) = Module.finrank k σ := rfl

@[simp]
lemma transport_ρ (e : G ≃* H) (V : FDRep k G) :
    (transport e V).ρ = V.ρ.comp e.symm.toMonoidHom := by
  rfl

/--
Transport along a composite monoid isomorphism agrees definitionally with iterated transport.
-/
lemma transport_trans {K : Type*} [Monoid K]
    (e₁ : G ≃* H) (e₂ : H ≃* K) (V : FDRep k G) :
    transport (e₁.trans e₂) V = transport e₂ (transport e₁ V) := rfl

/-- Transport along a monoid isomorphism on morphisms. -/
noncomputable def transportMap (e : G ≃* H) {V W : FDRep k G} (f : V ⟶ W) :
    transport e V ⟶ transport e W :=
  comapMap e.symm.toMonoidHom f

@[simp] lemma transportMap_hom_toLinearMap (e : G ≃* H) {V W : FDRep k G} (f : V ⟶ W) :
   FDRep.homToLinearMap (transportMap e f) = FDRep.homToLinearMap f := rfl

/-- Transport along a monoid isomorphism as a functor. -/
noncomputable def transportFunctor (e : G ≃* H) : FDRep k G ⥤ FDRep k H :=
  comapFunctor e.symm.toMonoidHom

/-- Transporting along the identity isomorphism is naturally isomorphic to the identity functor. -/
noncomputable def transportFunctorRefl :
    transportFunctor (MulEquiv.refl G) ≅ 𝟭 (FDRep k G) :=
  NatIso.ofComponents (fun ρ ↦ Iso.refl _) (fun f ↦ by
    apply FDRep.hom_ext
    intro x
    exact ConcreteCategory.congr_hom rfl x
  )

/--
Transporting along a composition of isomorphisms is naturally isomorphic to the
composition of transport functors.
-/
noncomputable def transportFunctorTrans {K : Type*} [Monoid K]
    (e₁ : G ≃* H) (e₂ : H ≃* K) :
    transportFunctor (k := k) e₁ ⋙ transportFunctor e₂ ≅
      transportFunctor (e₁.trans e₂) := by
  change
    comapFunctor (k := k) e₁.symm.toMonoidHom ⋙
      comapFunctor e₂.symm.toMonoidHom ≅
        comapFunctor ((e₁.trans e₂).symm.toMonoidHom)
  have h :
      e₁.symm.toMonoidHom.comp e₂.symm.toMonoidHom =
        (e₁.trans e₂).symm.toMonoidHom := by
    ext x
    rfl
  rw [← h]
  exact
    comapFunctorCompIso
      (k := k)
      e₁.symm.toMonoidHom
      e₂.symm.toMonoidHom

/-- Transporting an isomorphism gives an isomorphism between the transported representations. -/
noncomputable def transportMapIso (e : G ≃* H) {V W : FDRep k G} (i : V ≅ W) :
    transport e V ≅ transport e W :=
  (transportFunctor e).mapIso i

end Transport

section top

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
Transport a representation of `⊤` to `G` via the canonical isomorphism.
This allows us to compare objects in `FDRep k ⊤` with objects in `FDRep k G`.
-/
noncomputable def ofTop (ρ : FDRep k (⊤ : Subgroup G)) : FDRep k G :=
  FDRep.transport
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    ρ

/--
Map a morphism of `FDRep k ⊤` across `FDRep.ofTop`.
-/
noncomputable def ofTopMap
    {σ τ : FDRep k (⊤ : Subgroup G)}
    (f : σ ⟶ τ) :
    FDRep.ofTop σ ⟶ FDRep.ofTop τ :=
  FDRep.transportMap
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    Subgroup.topEquiv
    f

@[simp]
lemma ofTopMap_homToLinearMap_apply
    {σ τ : FDRep k (⊤ : Subgroup G)}
    (f : σ ⟶ τ) (x : ofTop σ) :
    FDRep.homToLinearMap (H := G) (FDRep.ofTopMap f) x =
      FDRep.homToLinearMap (H := (⊤ : Subgroup G)) f x := by
  rfl

/--
Transport representations of the top subgroup `⊤` to representations of `G`.
This is the functorial version of `FDRep.ofTop`.
-/
noncomputable def ofTopFunctor :
    FDRep k (⊤ : Subgroup G) ⥤ FDRep k G :=
  FDRep.transportFunctor
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

end top

section TransportEquiv

variable {k : Type u} {G : Type v} {H : Type w}
variable [CommRing k] [Monoid G] [Monoid H]

/--
The unit component for the equivalence induced by transport along a monoid
isomorphism.
-/
noncomputable def transportUnitIsoApp
    (e : G ≃* H) (V : FDRep k G) :
    V ≅ transport e.symm (transport e V) := by
  refine
    { hom :=
        FDRep.forget₂HomLinearEquiv V (transport e.symm (transport e V))
          (Rep.ofHom
            { toLinearMap := LinearMap.id
              isIntertwining' := by
                intro g
                ext x
                change V.ρ g x = V.ρ (e.symm (e g)) x
                simp })
      inv :=
        FDRep.forget₂HomLinearEquiv (transport e.symm (transport e V)) V
          (Rep.ofHom
            { toLinearMap := LinearMap.id
              isIntertwining' := by
                intro g
                ext x
                change V.ρ (e.symm (e g)) x = V.ρ g x
                simp })
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply FDRep.hom_ext
    intro x
    dsimp [FDRep.homToLinearMap]
    rfl
  · apply FDRep.hom_ext
    intro x
    dsimp [FDRep.homToLinearMap]
    rfl

/--
The counit component for the equivalence induced by transport along a monoid
isomorphism.
-/
noncomputable def transportCounitIsoApp (e : G ≃* H) (V : FDRep k H) :
    transport e (transport e.symm V) ≅ V := by
  refine
    { hom :=
        FDRep.forget₂HomLinearEquiv
          (transport e (transport e.symm V)) V
          (Rep.ofHom
            { toLinearMap := LinearMap.id
              isIntertwining' := by
                intro g
                ext x
                change V.ρ (e (e.symm g)) x = V.ρ g x
                simp })
      inv :=
        FDRep.forget₂HomLinearEquiv
          V (transport e (transport e.symm V))
          (Rep.ofHom
            { toLinearMap := LinearMap.id
              isIntertwining' := by
                intro g
                ext x
                change V.ρ g x = V.ρ (e (e.symm g)) x
                simp })
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply FDRep.hom_ext
    intro x
    dsimp [transport, comap, comapMap, FDRep.homToLinearMap]
    rfl
  · apply FDRep.hom_ext
    intro x
    dsimp [transport, comap, comapMap, FDRep.homToLinearMap]
    rfl

/-- Transport along a group isomorphism is an equivalence of categories. -/
noncomputable def transportEquiv (e : G ≃* H) : FDRep k G ≌ FDRep k H where
  functor := transportFunctor e
  inverse := transportFunctor e.symm
  unitIso :=
    NatIso.ofComponents
      (transportUnitIsoApp (k := k) e)
      (by
        intro V W f
        apply FDRep.hom_ext
        intro x
        dsimp [transportFunctor, transportMap, comapFunctor, comapMap,
          transportUnitIsoApp, transport, comap, FDRep.homToLinearMap]
        rfl)
  counitIso :=
    NatIso.ofComponents
      (transportCounitIsoApp (k := k) e)
      (by
        intro V W f
        apply FDRep.hom_ext
        intro x
        dsimp [transportFunctor, transportMap, comapFunctor, comapMap,
          transportCounitIsoApp, transport, comap, FDRep.homToLinearMap]
        rfl)
  functor_unitIso_comp := by
    intro V
    apply FDRep.hom_ext
    intro x
    dsimp [transportFunctor, transportMap, comapFunctor, comapMap,
      transportUnitIsoApp, transportCounitIsoApp, transport, comap,
      FDRep.homToLinearMap]
    rfl

end TransportEquiv

section Top

variable {k : Type u} {G : Type v}
variable [CommRing k] [Group G]

/--
Restricting a representation transported from `⊤` back to `G` recovers the
original representation of `⊤`.
-/
noncomputable def res_top_ofTop_iso
     (σ : FDRep k (⊤ : Subgroup G)) :
    (FDRep.ofTop σ).res (⊤ : Subgroup G) ≅ σ :=
  (FDRep.transportUnitIsoApp
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    σ).symm


/--
Transporting the restriction of a representation to `⊤` back to `G` recovers
the original representation.
-/
noncomputable def ofTop_res_top_iso
    (ρ : FDRep k G) :
    FDRep.ofTop (ρ.res (⊤ : Subgroup G)) ≅ ρ :=
  FDRep.transportCounitIsoApp
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    ρ

/--
Representations of the top subgroup `⊤ : Subgroup G` are equivalent to
representations of `G`.
-/
noncomputable def ofTopEquivalence
    {k : Type u} {G : Type v}
    [CommRing k] [Group G] :
    FDRep k (⊤ : Subgroup G) ≌ FDRep k G :=
  FDRep.transportEquiv
    (k := k)
    (G := (⊤ : Subgroup G))
    (H := G)
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)

end Top

end FDRep
