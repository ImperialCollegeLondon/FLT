-- **Modified from `Subpresheaf.lean` in mathlib**
-- The only addition is `ofIsTerminal`.
import Mathlib.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Set.Lattice.Image

/-!

# Subfunctor of types

We define the Subfunctor of a type valued functor.

## Main results

- `CategoryTheory.Subfunctor` :
  A Subfunctor of a functor of types.

-/


universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A Subfunctor of a functor consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
structure Subfunctor (F : C ⥤ Type w) where
  /-- If `G` is a sub-functor of `F`, then the sections of `G` on `U` forms a subset of sections of
    `F` on `U`. -/
  obj : ∀ U, Set (F.obj U)
  /-- If `G` is a sub-functor of `F` and `i : U ⟶ V`, then for each `G`-sections on `U` `x`,
    `F i x` is in `F(V)`. -/
  map : ∀ {U V : C} (i : U ⟶ V), (obj U).MapsTo (F.map i) (obj V)

@[deprecated (since := "2025-01-08")] alias GrothendieckTopology.Subfunctor := Subfunctor

variable {F F' F'' : C ⥤ Type w} (G G' : Subfunctor F)

instance : PartialOrder (Subfunctor F) :=
  PartialOrder.lift Subfunctor.obj (fun _ _ => Subfunctor.ext)

instance : CompleteLattice (Subfunctor F) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h|h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h|h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  le_sSup _ _ _ _ _ := by aesop
  sSup_le _ _ _ _ _ := by aesop
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  sInf_le _ _ _ _ _ := by aesop
  le_sInf _ _ _ _ _ := by aesop
  bot :=
    { obj U := ⊥
      map := by simp }
  bot_le _ _ := bot_le
  top :=
    { obj U := ⊤
      map := by simp }
  le_top _ _ := le_top

namespace Subfunctor

lemma le_def (S T : Subfunctor F) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

variable (F)

@[simp] lemma top_obj (i : C) : (⊤ : Subfunctor F).obj i = ⊤ := rfl
@[simp] lemma bot_obj (i : C) : (⊥ : Subfunctor F).obj i = ⊥ := rfl

variable {F}

lemma sSup_obj (S : Set (Subfunctor F)) (U : C) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl

lemma sInf_obj (S : Set (Subfunctor F)) (U : C) :
    (sInf S).obj U = sInf (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
lemma iSup_obj {ι : Type*} (S : ι → Subfunctor F) (U : C) :
    (⨆ i, S i).obj U = ⋃ i, (S i).obj U := by
  simp [iSup, sSup_obj]

@[simp]
lemma iInf_obj {ι : Type*} (S : ι → Subfunctor F) (U : C) :
    (⨅ i, S i).obj U = ⋂ i, (S i).obj U := by
  simp [iInf, sInf_obj]

@[simp]
lemma max_obj (S T : Subfunctor F) (i : C) :
    (S ⊔ T).obj i = S.obj i ∪ T.obj i := rfl

@[simp]
lemma min_obj (S T : Subfunctor F) (i : C) :
    (S ⊓ T).obj i = S.obj i ∩ T.obj i := rfl

lemma max_min (S₁ S₂ T : Subfunctor F) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop

lemma iSup_min {ι : Type*} (S : ι → Subfunctor F) (T : Subfunctor F) :
    (⨆ i, S i) ⊓ T = ⨆ i, S i ⊓ T := by
  aesop

instance : Nonempty (Subfunctor F) :=
  inferInstance

variable (F) in
/-- The subfunctor defined by pulling back a subset of the terminal component. -/
def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [Set.mapsTo_iff_subset_preimage, ← Set.preimage_comp,
      ← hX.comp_from i, F.map_comp]
    rfl

/-- The Subfunctor as a functor. -/
@[simps!]
def toFunctor : C ⥤ Type w where
  obj U := G.obj U
  map := @fun _ _ i x => ⟨F.map i x, G.map i x.prop⟩
  map_id X := by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_id_apply]
  map_comp := @fun X Y Z i j => by
    ext ⟨x, _⟩
    dsimp
    simp only [FunctorToTypes.map_comp_apply]

instance {U} : CoeHead (G.toFunctor.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a Subfunctor to the original functor. -/
@[simps]
def ι : G.toFunctor ⟶ F where app _ x := x

instance : Mono G.ι :=
  ⟨@fun _ _ _ e =>
    NatTrans.ext <|
      funext fun U => funext fun x => Subtype.ext <| congr_fun (congr_app e U) x⟩

/-- The inclusion of a Subfunctor to a larger Subfunctor -/
@[simps]
def homOfLe {G G' : Subfunctor F} (h : G ≤ G') : G.toFunctor ⟶ G'.toFunctor where
  app U x := ⟨x, h U x.prop⟩

instance {G G' : Subfunctor F} (h : G ≤ G') : Mono (Subfunctor.homOfLe h) :=
  ⟨fun _ _ e =>
    NatTrans.ext <|
      funext fun U =>
        funext fun x =>
          Subtype.ext <| (congr_arg Subtype.val <| (congr_fun (congr_app e U) x :) :)⟩

@[reassoc (attr := simp)]
theorem homOfLe_ι {G G' : Subfunctor F} (h : G ≤ G') :
    Subfunctor.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl

instance : IsIso (Subfunctor.ι (⊤ : Subfunctor F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
theorem eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2

theorem nat_trans_naturality (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congr_arg Subtype.val (FunctorToTypes.naturality _ _ f i x)

end Subfunctor

@[deprecated (since := "2025-01-23")] alias top_Subfunctor_obj := Subfunctor.top_obj

end CategoryTheory
