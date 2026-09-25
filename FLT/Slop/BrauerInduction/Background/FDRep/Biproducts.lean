/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Biproducts of finite-dimensional representations

This file constructs binary and finite biproducts in `FDRep k G`.

The concrete binary biproduct is given by the product of the underlying modules,
with the product representation. We also provide linear equivalences describing
the underlying module of a biproduct and helper lemmas for morphisms into finite
biproducts.
-/

@[expose] public section

namespace Slop
open Slop

namespace FDRep

open CategoryTheory
open CategoryTheory.Limits

universe u v w wι

section BinaryBiproducts

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]


noncomputable instance instHasBinaryBiproductsFDRep :
  HasBinaryBiproducts (FDRep k G) := HasBinaryBiproducts.of_hasBinaryCoproducts

end BinaryBiproducts

section FiniteBiproducts

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι}

noncomputable instance instHasTerminal :
    HasTerminal (FDRep k G) := by
  apply HasZeroObject.hasTerminal

/--
The category `FDRep k G` has finite products.
-/
noncomputable instance instHasFiniteProducts :
    HasFiniteProducts (FDRep k G) :=
  hasFiniteProducts_of_has_binary_and_terminal

/--
The concrete product of two finite-dimensional representations.

The underlying module is `V × W`, and the action is the product action
`V.ρ.prod W.ρ`.
-/
noncomputable def prod (V W : FDRep k G) : FDRep k G := by
  exact FDRep.of (Representation.prod V.ρ W.ρ)

@[simp]
lemma prod_ρ (V W : FDRep k G) :
    (FDRep.prod V W).ρ = Representation.prod V.ρ W.ρ := by
  simp only [prod, FGModuleCat.of_carrier,
    FDRep.of_ρ' (Representation.prod V.ρ W.ρ)]

lemma prod_ρ_apply (V W : FDRep k G) (g : G) (x : V × W) :
    (FDRep.prod V W).ρ g x =
      (V.ρ g x.1, W.ρ g x.2) := by
  rw [FDRep.prod_ρ]
  exact Representation.prod_apply_apply V.ρ W.ρ g x

private lemma hom_hom_apply_eq_of_eq
    {X Y : FDRep k G} {f g : X ⟶ Y}
    (h : f = g) (x : X.V.obj) :
    f.hom.hom x = g.hom.hom x := by
  subst h
  rfl


/-- Helper: The underlying vector space of a biproduct is linearly equivalent to the product. -/
noncomputable def linearEquivBiprod (X Y : FDRep k G) :
    (Limits.biprod X Y).V.obj ≃ₗ[k] X.V.obj × Y.V.obj :=
  { toFun := fun v =>
      ((Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom v,
       (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom v)
    map_add' := fun x y => by
      simp only [map_add, Prod.mk_add_mk]
    map_smul' := fun c x => by
      simp only [LinearMap.map_smul, Prod.smul_mk]
      simp only [FGModuleCat.obj_carrier, RingHom.id_apply]
    invFun := fun ⟨x, y⟩ =>
      (Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x +
      (Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y
    left_inv := by
      intro v
      have htotal :
          Limits.biprod.fst ≫ Limits.biprod.inl
            + Limits.biprod.snd ≫ Limits.biprod.inr
            =
          (𝟙 (X ⊞ Y) : X ⊞ Y ⟶ X ⊞ Y) :=
        Limits.biprod.total
      exact congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y => f.hom.hom v)  htotal

    right_inv := fun ⟨x, y⟩ => by
      have h1 : (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom
        ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x) = x := by
        have h := Limits.biprod.inl_fst (X := X) (Y := Y)
        calc (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x)
          _ = (Limits.biprod.inl ≫ Limits.biprod.fst : X ⟶ X).hom.hom x := rfl
          _ = (𝟙 X : X ⟶ X).hom.hom x := by rw [h]
          _ = x := rfl
      have h2 : (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom
        ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y) = 0 := by
        have h := Limits.biprod.inr_fst (X := X) (Y := Y)
        calc (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y)
          _ = (Limits.biprod.inr ≫ Limits.biprod.fst : Y ⟶ X).hom.hom y := rfl
          _ = (0 : Y ⟶ X).hom.hom y := by rw [h]
          _ = 0 := rfl
      have h3 : (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom
        ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x) = 0 := by
        have h := Limits.biprod.inl_snd (X := X) (Y := Y)
        calc (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x)
          _ = (Limits.biprod.inl ≫ Limits.biprod.snd : X ⟶ Y).hom.hom x := rfl
          _ = (0 : X ⟶ Y).hom.hom x := by rw [h]
          _ = 0 := rfl
      have h4 : (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom
        ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y) = y := by
        have h := Limits.biprod.inr_snd (X := X) (Y := Y)
        calc (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y)
          _ = (Limits.biprod.inr ≫ Limits.biprod.snd : Y ⟶ Y).hom.hom y := rfl
          _ = (𝟙 Y : Y ⟶ Y).hom.hom y := by rw [h]
          _ = y := rfl
      ext
      · simp only [map_add, h1,h2, AddMonoid.add_zero x]
      · simp only [map_add, h3,h4, AddZeroClass.zero_add y]
  }

/-- The categorical biproduct of two finite-dimensional representations is isomorphic to
their product representation. -/
noncomputable def biprodIsoProd (V W : FDRep k G) :
    (V ⊞ W) ≅ (FDRep.prod (k:=k) (G:=G) V W) := by
  -- Use your existing linear equivalence
  let e := linearEquivBiprod (X := V) (Y := W)
  -- Use your helper to construct the FDRep iso from a LinearEquiv
  refine FDRep.isoOfLinearEquiv e (fun g => ?_)
  apply LinearMap.ext; intro x
  dsimp [FDRep.prod, Representation.prod]
  -- The target is a product (V × W), check components separately
  apply Prod.ext
  · -- 1. First component (V)
    -- This is exactly the commutativity of the first projection
    -- We need: ρ_V g (lin biprod.fst x) = lin biprod.fst ((V ⊞ W).ρ g x)
    exact LinearMap.congr_fun (FDRep.hom_comp_ρ Limits.biprod.fst g).symm x
  · -- 2. Second component (W)
    -- Similarly for the second projection
    exact LinearMap.congr_fun (FDRep.hom_comp_ρ Limits.biprod.snd g).symm x

/--
The category `FDRep k G` has finite biproducts.
-/
noncomputable instance instHasFiniteBiproducts :
    HasFiniteBiproducts (FDRep k G) := HasFiniteBiproducts.of_hasFiniteProducts

/--
The biproduct over the empty indexing type is a zero object.
-/
lemma IsZero_biproduct_empty
    (f : PEmpty → FDRep k G) : IsZero (⨁ f) := by
  refine ⟨?_, ?_⟩
  · intro X
    refine ⟨⟨biproduct.desc (fun i : PEmpty => PEmpty.elim i)⟩, ?_⟩
    intro g
    apply biproduct.hom_ext'
    intro i
    cases i
  · intro X
    refine ⟨⟨biproduct.lift (fun i : PEmpty => PEmpty.elim i)⟩, ?_⟩
    intro g
    apply biproduct.hom_ext
    intro i
    cases i


/--
Construct an isomorphism between finite biproducts from a reindexing of the
summands together with componentwise isomorphisms.
-/
noncomputable def biproductIsoOfReindex
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → FDRep k G) (g : κ → FDRep k G)
    (σ : ι ≃ κ)
    (hσ : ∀ i, Nonempty (f i ≅ g (σ i))) :
    Limits.biproduct f ≅ Limits.biproduct g :=
  Limits.biproduct.mapIso (fun i => Classical.choice (hσ i)) ≪≫
    Limits.biproduct.reindex σ g


open Classical in
/--
If two finite families have the same multiplicities in each isomorphism class
represented by either family, then their index types are equivalent in a way
that matches isomorphic summands.
-/
lemma exists_equiv_of_iso_counts
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → FDRep k G) (g : κ → FDRep k G)
    (hcount_f :
      ∀ i₀ : ι,
        (∑ i, if Nonempty (f i₀ ≅ f i) then 1 else 0)
          =
        (∑ j, if Nonempty (f i₀ ≅ g j) then 1 else 0))
    (hcount_g :
      ∀ j₀ : κ,
        (∑ i, if Nonempty (g j₀ ≅ f i) then 1 else 0)
          =
        (∑ j, if Nonempty (g j₀ ≅ g j) then 1 else 0)) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (f i ≅ g (σ i)) := by
  let Setoid_ι : Setoid ι :=
    { r := fun i i' => Nonempty (f i ≅ f i')
      iseqv :=
        ⟨ fun _ => ⟨Iso.refl _⟩,
          fun ⟨h⟩ => ⟨h.symm⟩,
          fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩ ⟩ }
  let Classes := Quotient Setoid_ι
  let classOf : ι → Classes := Quotient.mk Setoid_ι
  have h_surj (j : κ) : ∃ i, Nonempty (f i ≅ g j) := by
    by_contra h_none
    push Not at h_none
    have h_lhs_zero :
        (∑ i, if Nonempty (g j ≅ f i) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro h
      rcases h with ⟨e⟩
      exact @IsEmpty.false (f i ≅ g j) (h_none i) e.symm
    have h_rhs_pos :
        1 ≤ ∑ x : κ, if Nonempty (g j ≅ g x) then 1 else 0 := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem]
      · rw [if_pos ⟨Iso.refl _⟩]
        exact Nat.le_add_right 1 _
      · simp
    have h_eq := hcount_g j
    rw [h_lhs_zero] at h_eq
    rw [← h_eq] at h_rhs_pos
    exact Nat.not_succ_le_zero 0 h_rhs_pos
  let classOf' (j : κ) : Classes :=
    Quotient.mk Setoid_ι (Classical.choose (h_surj j))
  have card_fibers_eq :
      ∀ c : Classes,
        Fintype.card { i // classOf i = c } =
          Fintype.card { j // classOf' j = c } := by
    intro c
    obtain ⟨rep, rfl⟩ := Quotient.exists_rep c
    have hS := hcount_f rep
    simp only [Finset.sum_boole] at hS
    rw [Fintype.card_subtype (fun i => classOf i = ⟦rep⟧),
        Fintype.card_subtype (fun j => classOf' j = ⟦rep⟧)]
    have h_left :
        (Finset.univ.filter (fun x => Nonempty (f rep ≅ f x))).card =
          (Finset.univ.filter (fun i => classOf i = ⟦rep⟧)).card := by
      apply congrArg
      apply Finset.filter_congr
      intro i _
      rw [Quotient.eq]
      constructor
      · intro h
        exact ⟨h.some.symm⟩
      · intro h
        exact ⟨h.some.symm⟩
    have h_right :
        (Finset.univ.filter (fun x => Nonempty (f rep ≅ g x))).card =
          (Finset.univ.filter (fun j => classOf' j = ⟦rep⟧)).card := by
      apply congrArg
      apply Finset.filter_congr
      intro j _
      rw [Quotient.eq]
      constructor
      · intro h
        have h_link := Classical.choose_spec (h_surj j)
        exact ⟨h_link.some.trans h.some.symm⟩
      · intro h
        have h_link := Classical.choose_spec (h_surj j)
        exact ⟨h.some.symm.trans h_link.some⟩
    rw [h_left, h_right] at hS
    exact hS
  let e1 : ι ≃ (c : Classes) × { i // classOf i = c } :=
    (Equiv.sigmaFiberEquiv classOf).symm
  let e_mid :
      ((c : Classes) × { i // classOf i = c }) ≃
        ((c : Classes) × { j // classOf' j = c }) :=
    Equiv.sigmaCongrRight
      (fun c => Fintype.equivOfCardEq (card_fibers_eq c))
  let e2 : κ ≃ (c : Classes) × { j // classOf' j = c } :=
    (Equiv.sigmaFiberEquiv classOf').symm
  let σ := e1.trans (e_mid.trans e2.symm)
  refine ⟨σ, ?_⟩
  intro i
  have h_classes_eq : classOf' (σ i) = classOf i := by
    let y := e_mid (e1 i)
    have h_proj : classOf' (e2.symm y) = y.1 := by
      change classOf' (Equiv.sigmaFiberEquiv classOf' y) = y.1
      rw [Equiv.sigmaFiberEquiv_apply]
      exact y.snd.property
    have h_mid : y.1 = (e1 i).1 := rfl
    have h_first : (e1 i).1 = classOf i := by
      rw [Equiv.sigmaFiberEquiv_symm_apply_fst]
    dsimp [σ]
    rw [h_proj, h_mid, h_first]
  rw [Quotient.eq] at h_classes_eq
  obtain ⟨h_iso_fiber⟩ := h_classes_eq
  obtain ⟨h_link⟩ := Classical.choose_spec (h_surj (σ i))
  exact ⟨h_iso_fiber.symm.trans h_link⟩

open Classical in
/--
Two finite biproducts are isomorphic if their summands have the same
multiplicities in every isomorphism class represented by either family.
-/
theorem biproduct_iso_of_iso_counts
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → FDRep k G) (g : κ → FDRep k G)
    [HasBiproduct f] [HasBiproduct g]
    (hcount_f :
      ∀ i₀ : ι,
        (∑ i, if Nonempty (f i₀ ≅ f i) then 1 else 0)
          =
        (∑ j, if Nonempty (f i₀ ≅ g j) then 1 else 0))
    (hcount_g :
      ∀ j₀ : κ,
        (∑ i, if Nonempty (g j₀ ≅ f i) then 1 else 0)
          =
        (∑ j, if Nonempty (g j₀ ≅ g j) then 1 else 0)) :
    Nonempty ((⨁ f) ≅ (⨁ g)) := by
  rcases exists_equiv_of_iso_counts f g hcount_f hcount_g with ⟨σ, hσ⟩
  exact ⟨FDRep.biproductIsoOfReindex
    (k := k) (G := G) (f := f) (g := g) σ hσ⟩

end FiniteBiproducts

section HomToBiproduct

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι} [Finite ι]

/--
Morphisms into a finite biproduct are linearly equivalent to families of
morphisms into each summand.
-/
noncomputable def homToBiproductLinearEquiv
    (S : FDRep k G) (f : ι → FDRep k G)
    [HasBiproduct f] :
    (S ⟶ (⨁ f : FDRep k G)) ≃ₗ[k] (∀ i, S ⟶ f i) where
  toFun g i := g ≫ biproduct.π (f := f) i
  invFun p := biproduct.lift (f := f) p
  map_add' := by
    intro g h
    ext i
    simp
  map_smul' := by
    intro c g
    ext i
    simp
  left_inv := by
    intro g
    apply biproduct.hom_ext
    intro i
    simp
  right_inv := by
    intro p
    funext i
    simp

/--
The dimension of the morphism space into a finite biproduct is the sum of the
dimensions of the morphism spaces into the summands.
-/
lemma finrank_hom_to_biproduct_eq_sum
    {ι : Type wι} [Fintype ι]
    {k : Type u} {G : Type v} [Field k] [Monoid G]
    (S : FDRep k G) (f : ι → FDRep k G)
    [HasBiproduct f] :
    Module.finrank k (S ⟶ ⨁ f) =
      ∑ i, Module.finrank k (S ⟶ f i) := by
  let e := homToBiproductLinearEquiv (k := k) (G := G) S f
  calc
    Module.finrank k (S ⟶ ⨁ f)
        = Module.finrank k (∀ i, S ⟶ f i) := LinearEquiv.finrank_eq e
    _ = ∑ i, Module.finrank k (S ⟶ f i) := by
        simpa using
          (Module.finrank_pi_fintype k :
            Module.finrank k (∀ i, S ⟶ f i) =
              ∑ i, Module.finrank k (S ⟶ f i))

end HomToBiproduct

section finrank

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

lemma finrank_biprod (X Y : FDRep k G) :
      (X ⊞ Y).finrank = X.finrank + Y.finrank := by
  have e := FDRep.linearEquivBiprod (X := X) (Y := Y)
  have h :
      (X ⊞ Y).finrank = Module.finrank k ( X.V.obj × Y.V.obj ) := LinearEquiv.finrank_eq e
  rw [h,Module.finrank_prod]

end finrank

section OptionBiproduct

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι} [Finite ι]

/--
Adjoining one extra summand to a finite biproduct.

The biproduct over `Option ι`, with `none` corresponding to `S` and `some i`
corresponding to `K i`, is isomorphic to `S ⊞ ⨁ K`.
-/
noncomputable def biproductOptionIso
    (S : FDRep k G) (K : ι → FDRep k G) :
    (S ⊞ Limits.biproduct K) ≅ Limits.biproduct (Option.rec S K) := by
  let F : Option ι → FDRep k G := @Option.rec ι (fun _ => FDRep k G) S K
  let fwd : S ⊞ Limits.biproduct K ⟶ Limits.biproduct F :=
    Limits.biprod.desc
      (Limits.biproduct.ι F none)
      (Limits.biproduct.desc (fun i => Limits.biproduct.ι F (some i)))
  let inv : Limits.biproduct F ⟶ S ⊞ Limits.biproduct K :=
    Limits.biproduct.desc (fun o => match o with
      | none   => Limits.biprod.inl
      | some i => Limits.biproduct.ι K i ≫ Limits.biprod.inr)
  refine Iso.mk fwd inv ?_ ?_  <;> dsimp [fwd, inv]
  · apply Limits.biprod.hom_ext'
    · rw [←Category.assoc, Limits.biprod.inl_desc]
      simp only [Limits.biproduct.ι_desc]
      rfl
    · rw [←Category.assoc, Limits.biprod.inr_desc]
      apply Limits.biproduct.hom_ext'; intro i
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Limits.biproduct.ι_desc]
      rfl
  · apply Limits.biproduct.hom_ext'; intro o
    cases o with
    | none =>
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Limits.biprod.inl_desc]
      rfl
    | some i =>
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Category.assoc, Limits.biprod.inr_desc]
      rw [Limits.biproduct.ι_desc]
      rfl

end OptionBiproduct

end FDRep

end Slop
