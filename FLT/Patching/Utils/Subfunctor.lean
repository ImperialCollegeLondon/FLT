import Mathlib.CategoryTheory.Types
import Mathlib.Algebra.Order.Group.CompleteLattice

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

@[ext]
structure Functor.Subfunctor where
  obj : ∀ X, Set (F.obj X)
  map : ∀ {X Y : C} (f : X ⟶ Y), Set.MapsTo (F.map f) (obj X) (obj Y)

variable {F}

@[simps]
def Functor.Subfunctor.toFunctor (G : F.Subfunctor) : C ⥤ Type w where
  obj X := G.obj X
  map f := (G.map f).restrict

open Functor.Subfunctor in
instance : CompleteLattice F.Subfunctor where
  __ := PartialOrder.lift obj fun _ _ ↦ Functor.Subfunctor.ext
  sup G₁ G₂ := ⟨G₁.obj ⊔ G₂.obj, fun f ↦ (G₁.map f).union_union (G₂.map f)⟩
  le_sup_left G₁ G₂ := le_sup_left (a := G₁.obj)
  le_sup_right G₁ G₂ := le_sup_right (a := G₁.obj)
  sup_le G₁ G₂ G₃ := sup_le (a := G₁.obj)
  inf G₁ G₂ := ⟨G₁.obj ⊓ G₂.obj, fun f ↦ (G₁.map f).inter_inter (G₂.map f)⟩
  inf_le_left G₁ G₂ := inf_le_left (a := G₁.obj)
  inf_le_right G₁ G₂ := inf_le_right (a := G₁.obj)
  le_inf G₁ G₂ G₃ := le_inf (a := G₁.obj)
  sSup s := ⟨fun X ↦ ⋃ G ∈ s, G.obj X, fun f ↦ Set.mapsTo_iUnion₂_iUnion₂ fun G _ ↦ G.map f⟩
  le_sSup s G hGs X := Set.subset_biUnion_of_mem (u := (obj · X)) hGs
  sSup_le s G hG X := Set.iUnion₂_subset (hG · · X)
  sInf s := ⟨fun X ↦ ⋂ G ∈ s, G.obj X, fun f ↦ Set.mapsTo_iInter₂_iInter₂ fun G _ ↦ G.map f⟩
  sInf_le s G hGs X := Set.biInter_subset_of_mem (t := (obj · X)) hGs
  le_sInf s G hG X := Set.subset_iInter₂ (hG · · X)
  top := ⟨⊤, by simp⟩
  bot := ⟨⊥, by simp⟩
  le_top G := le_top (a := G.obj)
  bot_le G := bot_le (a := G.obj)

end CategoryTheory
