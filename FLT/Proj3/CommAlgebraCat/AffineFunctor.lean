/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/

import FLT.Proj3.CommAlgebraCat.Monoidal
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Yoneda
import FLT.Proj3.HopfMon


/-!
# The internal group object in the corepresentable functor from commutaive algebra

we prove that it is antiquivalent to hopf algebra.
-/

open CategoryTheory Opposite BigOperators

open scoped MonoidalCategory
open scoped TensorProduct

variable (k : Type v) [CommRing k]

local notation "⋆" => (coyoneda.obj <| op (CommAlgebraCat.of k k))

variable {k} in
@[ext]
structure CorepresentableFunctor (F : CommAlgebraCat k ⥤ Type v) :=
coreprX : CommAlgebraCat k
coreprW : coyoneda.obj (op coreprX) ≅ F

@[simps]
def CorepresentableFunctor.of_nat_iso {F G : CommAlgebraCat k ⥤ Type v} (ε : F ≅ G)
    (h : CorepresentableFunctor F) :
    CorepresentableFunctor G where
  coreprX := h.coreprX
  coreprW := h.coreprW ≪≫ ε


section setup

variable {k}
/--The binary product of two functors -/
@[simps]
def mul (F G : CommAlgebraCat k ⥤ Type v) :
    CommAlgebraCat k ⥤ Type v where
  obj A := (F.obj A) × (G.obj A)
  map f x := ⟨F.map f x.1, G.map f x.2⟩

/--
Taking binary product of two functors is functorial.
-/
@[simps]
def mulMap {a a' b b' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (g : b ⟶ b') :
    mul a b ⟶ mul a' b' where
  app X a := ⟨f.app X a.1, g.app X a.2⟩
  naturality X Y m := by
    ext ⟨c, d⟩
    simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq]
    have := congr_fun (f.naturality m) c
    rw [show f.app Y (a.map m c) = _ from congr_fun (f.naturality m) c,
      types_comp_apply, show g.app Y (b.map m d) = _ from
      congr_fun (g.naturality m) d, types_comp_apply]
    tauto

instance mulMap.isIso {a a' b b' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (g : b ⟶ b') [IsIso f] [IsIso g] :
    IsIso (mulMap f g) where
  out := by
    use mulMap (inv f) (inv g)
    constructor
    · ext X ⟨Y1, Y2⟩
      simp only [mul_obj, FunctorToTypes.comp, mulMap_app, NatIso.isIso_inv_app, NatTrans.id_app,
        types_id_apply, Prod.mk.injEq]
      constructor
      · rw [show inv (f.app X) = (inv f).app X by simp]
        change  (f ≫ inv f).app X Y1 = _
        simp only [IsIso.hom_inv_id, NatTrans.id_app, types_id_apply]
      · rw [show inv (g.app X) = (inv g).app X by simp]
        change  (g ≫ inv g).app X Y2 = _
        simp only [IsIso.hom_inv_id, NatTrans.id_app, types_id_apply]
    · ext X ⟨Y1, Y2⟩
      simp only [mul_obj, FunctorToTypes.comp, mulMap_app, NatIso.isIso_inv_app, NatTrans.id_app,
        types_id_apply, Prod.mk.injEq]
      constructor
      · rw [show inv (f.app X) = (inv f).app X by simp]
        change  (inv f ≫ f).app X Y1 = _
        simp only [IsIso.inv_hom_id, NatTrans.id_app, types_id_apply]
      · rw [show inv (g.app X) = (inv g).app X by simp]
        change  (inv g ≫ g).app X Y2 = _
        simp only [IsIso.inv_hom_id, NatTrans.id_app, types_id_apply]

@[reassoc]
lemma mulMap_comp {a a' a'' b b' b'' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (f' : a' ⟶ a'')
    (g : b ⟶ b') (g' : b' ⟶ b'') :
    mulMap (f ≫ f') (g ≫ g') =
    mulMap f g ≫ mulMap f' g' := by
  ext X ⟨Y1, Y2⟩
  simp only [mul_obj, mulMap_app, FunctorToTypes.comp]

@[reassoc]
lemma mulMap_id (a b : CommAlgebraCat k ⥤ Type v) :
    mulMap (𝟙 a) (𝟙 b) = 𝟙 (mul a b) := by aesop_cat

/--
The product of three functors is associative up to isomorphism.
-/
@[simps]
def mulAssoc (a b c : CommAlgebraCat k ⥤ Type v) :
    mul a (mul b c) ≅ mul (mul a b) c where
  hom := { app := fun x z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩ }
  inv := { app := fun x z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩ }

/--
shorthand for `mul F F`.
-/
@[simp]
def square (F : CommAlgebraCat k ⥤ Type v) : CommAlgebraCat k ⥤ Type v :=
  mul F F

/--
`Hom(k, -)` has the role of the unit up to isomorphism.
-/
@[simps]
def mulStar (a : CommAlgebraCat k ⥤ Type v) : mul a ⋆ ≅ a where
  hom := { app := fun x z ↦ z.1 }
  inv :=
  { app := fun x z ↦ ⟨z, Algebra.ofId k x⟩
    naturality := fun b c f ↦ types_ext _ _ fun x ↦ Prod.ext rfl <|
      AlgHom.ext fun x ↦ show algebraMap k c x = f (algebraMap k b x) from
      f.commutes _ |>.symm }
  hom_inv_id := by
    ext A ⟨x, (f : k →ₐ[k] A)⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app,
      types_id_apply, Prod.mk.injEq, true_and]
    refine AlgHom.ext fun x ↦ ?_
    change algebraMap k A x = _
    rw [Algebra.algebraMap_eq_smul_one, show x • 1 = x • f 1
      by rw [_root_.map_one], ← f.map_smul, Algebra.smul_def]
    simp
  inv_hom_id := by ext; simp

/--
`Hom(k, -)` has the role of the unit up to isomorphism.
-/
@[simps]
def starMul (a) : mul ⋆ a ≅ a where
  hom := { app := fun x z ↦ z.2 }
  inv :=
  { app := fun x z ↦ ⟨Algebra.ofId k x, z⟩
    naturality := fun b c f ↦ types_ext _ _ fun x ↦ Prod.ext
      (AlgHom.ext fun x ↦ show algebraMap k c x = f (algebraMap k b x) from
        f.commutes _ |>.symm) rfl }
  hom_inv_id := by
    ext A ⟨(f : k →ₐ[k] A), x⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app,
      types_id_apply, Prod.mk.injEq, and_true]
    refine AlgHom.ext fun x ↦ ?_
    change algebraMap k A x = _
    rw [Algebra.algebraMap_eq_smul_one, show x • 1 = x • f 1
      by rw [_root_.map_one], ← f.map_smul, Algebra.smul_def]
    simp
  inv_hom_id := by ext; simp

-- FIXME: **The formatting is not ideal**
/--
```
Hom(A, -) × Hom(B, -) ≅ Hom(A ⊗ B, -)
```
-/
@[simps]
noncomputable def coyonedaMulCoyoneda (A B : CommAlgebraCat k) :
    mul (coyoneda.obj <| op A) (coyoneda.obj <| op B) ≅
    (coyoneda.obj <| op <| A ⊗ B) where
  hom :=
  {
  app := fun X f ↦ Algebra.TensorProduct.lift f.1 f.2 fun a b ↦ show _ = _ by rw [mul_comm]
  naturality := by
    intro X Y f
    ext ⟨(x1 : A →ₐ[k] X), (x2 : B →ₐ[k] X)⟩
    simp only [coyoneda_obj_obj, unop_op, mul_obj, types_comp_apply, mul_map, coyoneda_obj_map]
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeft_apply]
      show f _ = f _
      simp only [RingHom.coe_coe]
      erw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    · ext b
      simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply,
        Algebra.TensorProduct.includeRight_apply]
      change f _ = f _
      simp only [RingHom.coe_coe]
      erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  }

  inv :=
  {
  app := fun X f ↦
    ⟨Algebra.TensorProduct.liftEquiv.symm f |>.1.1,
      Algebra.TensorProduct.liftEquiv.symm f |>.1.2⟩
  naturality := by
    intro X Y f
    change _ →ₐ[k] _ at f
    ext (T : _ →ₐ[k] _)
    simp only [unop_op] at T
    simp only [mul_obj, coyoneda_obj_obj, unop_op, Algebra.TensorProduct.liftEquiv_symm_apply_coe,
      types_comp_apply, coyoneda_obj_map, mul_map, Prod.mk.injEq]
    constructor <;> rfl
  }

  hom_inv_id := by
    dsimp only [mul_obj, coyoneda_obj_obj, unop_op, id_eq, eq_mpr_eq_cast, types_comp_apply,
      mul_map, coyoneda_obj_map, AlgHom.coe_comp, Function.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul, RingHom.coe_coe,
      cast_eq, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.liftEquiv_symm_apply_coe]
    ext X ⟨(f1 : A →ₐ[k] _), (f2 : B →ₐ[k] _)⟩
    simp only [mul_obj, coyoneda_obj_obj, unop_op, FunctorToTypes.comp,
      Algebra.TensorProduct.lift_comp_includeLeft, Algebra.TensorProduct.lift_comp_includeRight,
      NatTrans.id_app, types_id_apply]

  inv_hom_id := by
    dsimp only [coyoneda_obj_obj, unop_op, Algebra.TensorProduct.liftEquiv_symm_apply_coe, mul_obj,
      types_comp_apply, coyoneda_obj_map, mul_map, id_eq, eq_mpr_eq_cast, AlgHom.coe_comp,
      Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul,
      RingHom.coe_coe, cast_eq, AlgHom.coe_restrictScalars',
      Algebra.TensorProduct.includeRight_apply]
    ext X (f : A ⊗[k] B →ₐ[k] X)
    simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, NatTrans.id_app, types_id_apply]
    apply Algebra.TensorProduct.ext
    · ext a
      simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeft_apply]
    · ext b
      simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]


noncomputable def coyonedaMulCoyoneda'
    (F G : CommAlgebraCat k ⥤ Type v)
    (hF : CorepresentableFunctor F) (hG : CorepresentableFunctor G) :
    mul F G ≅ coyoneda.obj (op <| hF.coreprX ⊗ hG.coreprX) :=
  { hom := mulMap hF.coreprW.inv hG.coreprW.inv
    inv := mulMap hF.coreprW.hom hG.coreprW.hom } ≪≫ coyonedaMulCoyoneda _ _

@[simps]
noncomputable def coyonedaCorrespondence
    (F G : CommAlgebraCat k ⥤ Type v)
    (hF : CorepresentableFunctor F)
    (hG : CorepresentableFunctor G) :
    (F ⟶ G) ≃ (hG.coreprX ⟶ hF.coreprX) where
  toFun n := hG.coreprW.inv.app _ <| n.app hF.coreprX (hF.coreprW.hom.app hF.coreprX (𝟙 _))
  invFun f :=
    hF.coreprW.inv ≫
    coyoneda.map (X := op hF.coreprX) (Y := op hG.coreprX) (op f) ≫
    hG.coreprW.hom
  left_inv n := by
    simp only [unop_op]
    rw [Iso.inv_comp_eq]
    ext X a
    simp only [FunctorToTypes.comp, coyoneda_map_app, unop_op]
    change hG.coreprW.hom.app X (hG.coreprW.inv.app _ _ ≫ _) = _
    have := congr_fun (hG.coreprW.hom.naturality a) <|
      hG.coreprW.inv.app hF.coreprX (n.app hF.coreprX (hF.coreprW.hom.app hF.coreprX (𝟙 hF.coreprX)))
    dsimp at this
    rw [this]
    simp only [FunctorToTypes.inv_hom_id_app_apply]
    have := congr_fun (n.naturality a) <|
      (hF.coreprW.hom.app hF.coreprX (𝟙 hF.coreprX))
    dsimp at this
    rw [← this]
    congr!
    have := congr_fun (hF.coreprW.hom.naturality a) (𝟙 _)
    simp only [unop_op, coyoneda_obj_obj, types_comp_apply, coyoneda_obj_map,
      Category.id_comp] at this
    exact this.symm
  right_inv n := by
    simp only [unop_op, FunctorToTypes.comp, FunctorToTypes.hom_inv_id_app_apply, coyoneda_map_app,
      Category.comp_id]
    rfl

end setup

/--
An affine monoid functor is an internal monoid object in the category of corepresentable functors.
-/
structure AffineMonoid extends CommAlgebraCat k ⥤ Type v where
  /--the underlying functor is corepresentable-/
  corep : CorepresentableFunctor toFunctor  /--the multiplication map-/
  m : mul toFunctor toFunctor ⟶ toFunctor
  /--the unit map-/
  e : ⋆ ⟶ toFunctor
  mul_assoc' : mulMap (𝟙 toFunctor) m ≫ m =
    (mulAssoc toFunctor toFunctor toFunctor).hom ≫ mulMap m (𝟙 toFunctor) ≫ m
  mul_one' : mulMap (𝟙 _) e ≫ m = (mulStar toFunctor).hom
  one_mul' : mulMap e (𝟙 _) ≫ m = (starMul toFunctor).hom

attribute [instance] AffineMonoid.corep

/--
An affine group functor is the internal group object in the category of corepresentable functors.
-/
structure AffineGroup extends AffineMonoid k where
  /--the inverse map-/
  i : toFunctor ⟶ toFunctor
  /-**Check if this correct**-/
  mul_inv :
    ({
      app := fun _ x ↦ (i.app _ x, x)
      naturality := by
        intro X Y (f: X →ₐ[k] Y)
        ext x
        simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, and_true]
        have := i.naturality f
        change (i.app Y).comp _ = (toFunctor.map f).comp _ at this
        exact congr_fun this x
    } ≫ m : toFunctor ⟶ toFunctor) =
    corep.coreprW.inv ≫ coyoneda.map (op <| Algebra.ofId _ _) ≫ e
  inv_mul :
    ({
        app := fun _ x ↦ (x, i.app _ x)
        naturality := by
          intro X Y (f: X →ₐ[k] Y)
          ext x
          simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, true_and]
          have := i.naturality f
          change (i.app Y).comp _ = (toFunctor.map f).comp _ at this
          exact congr_fun this x
      } ≫ m : toFunctor ⟶ toFunctor) =
    corep.coreprW.inv ≫ coyoneda.map (op <| Algebra.ofId _ _) ≫ e

namespace AffineMonoid

variable {k}

/--morphism between two affine monoid functors-/
structure Hom (F G : AffineMonoid k) where
  /-- the underlying natural transformation-/
  hom : F.toFunctor ⟶ G.toFunctor
  one : F.e ≫ hom = G.e := by aesop_cat
  mul : F.m ≫ hom = mulMap hom hom ≫ G.m := by aesop_cat

attribute [reassoc, simp] Hom.one Hom.mul

instance : Category <| AffineMonoid k where
  Hom := Hom
  id F := { hom := 𝟙 _ }
  comp α β :=
  { hom := α.hom ≫ β.hom
    one := by rw [α.one_assoc, β.one]
    mul := by rw [α.mul_assoc, β.mul, mulMap_comp, Category.assoc] }

end AffineMonoid

namespace AffineGroup

variable {k}

/--Morphisms between two affine group functors. -/
structure Hom (F G : AffineGroup k) where
  /-- the underlying natural transformation. -/
  hom : F.toFunctor ⟶ G.toFunctor
  one : F.e ≫ hom = G.e := by aesop_cat
  mul : F.m ≫ hom = mulMap hom hom ≫ G.m := by aesop_cat

attribute [reassoc, simp] Hom.one Hom.mul

instance : Category <| AffineGroup k where
  Hom := Hom
  id F := { hom := 𝟙 _ }
  comp α β :=
  { hom := α.hom ≫ β.hom
    one := by rw [α.one_assoc, β.one]
    mul := by rw [α.mul_assoc, β.mul, mulMap_comp, Category.assoc] }


end AffineGroup

variable {k} in
/--A proposition stating that a corepresentable functor is an affine monoid with specified
multiplication and unit. -/
structure IsAffineMonoidWithChosenMulAndUnit
    (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) : Prop :=
  mul_assoc' : mulMap (𝟙 F) m ≫ m = (mulAssoc F F F).hom ≫ mulMap m (𝟙 F) ≫ m
  mul_one : mulMap (𝟙 F) e ≫ m = (mulStar F).hom
  one_mul : mulMap e (𝟙 F) ≫ m = (starMul F).hom

attribute [reassoc] IsAffineMonoidWithChosenMulAndUnit.mul_assoc'
  IsAffineMonoidWithChosenMulAndUnit.mul_one
  IsAffineMonoidWithChosenMulAndUnit.one_mul
namespace IsAffineMonoidWithChosenMulAndUnit

variable (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
variable (m : mul F F ⟶ F) (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F)
variable (G : CommAlgebraCat k ⥤ Type v) (ε : G ≅ F)

lemma of_iso (h : IsAffineMonoidWithChosenMulAndUnit F hF m e) :
    IsAffineMonoidWithChosenMulAndUnit
      G
      (hF.of_nat_iso k ε.symm)
      (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
      (e ≫ ε.inv) where
  mul_assoc' := by
    have eq0 : (mulAssoc G G G).hom =
      mulMap ε.hom (mulMap ε.hom ε.hom) ≫ (mulAssoc F F F).hom ≫
      mulMap (mulMap ε.inv ε.inv) ε.inv := by aesop_cat
    have eq1 : mulMap ε.hom (mulMap ε.hom ε.hom ≫ m) =
      mulMap ε.hom (mulMap ε.hom ε.hom) ≫ mulMap (𝟙 F) m := by aesop_cat
    rw [eq0, ← mulMap_comp_assoc, Category.id_comp, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, eq1, Category.assoc, h.mul_assoc'_assoc]
    aesop_cat
  mul_one := by
    have eq0 : (mulStar G).hom = mulMap ε.hom (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k k))))
      ≫ (mulStar F).hom ≫ ε.inv := by
      ext X ⟨f, g⟩
      change k →ₐ[k] _ at g
      simp only [coyoneda_obj_obj, unop_op, mulStar_hom_app, FunctorToTypes.comp, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.hom_inv_id_app_apply]
    have eq1 : mulMap ε.hom (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k k)))) =
      mulMap ε.hom (𝟙 _) ≫ mulMap (𝟙 F) (𝟙 _) := by
      rfl
    rw [eq0, eq1, ← mulMap_comp_assoc, Category.id_comp, ← h.mul_one]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp [← mulMap_comp_assoc]

  one_mul := by
    have eq0 : (starMul G).hom = mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k k)))) ε.hom ≫
      (starMul F).hom ≫ ε.inv := by
      ext X ⟨_, g⟩
      simp only [coyoneda_obj_obj, unop_op, starMul_hom_app, FunctorToTypes.comp, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.hom_inv_id_app_apply]
    have eq1 : mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k k)))) ε.hom =
      mulMap (𝟙 _) ε.hom ≫ mulMap (𝟙 _) (𝟙 F) := by rfl
    rw [eq0, eq1, ← mulMap_comp_assoc, Category.id_comp, ← h.one_mul]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← mulMap_comp_assoc, Category.id_comp]

lemma from_iso
    (h : IsAffineMonoidWithChosenMulAndUnit G
      (hF.of_nat_iso k ε.symm)
      (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
      (e ≫ ε.inv)) :
    IsAffineMonoidWithChosenMulAndUnit F hF m e := by
  have := of_iso k G (hF.of_nat_iso k ε.symm) (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
    (e ≫ ε.inv) F ε.symm h
  convert this <;> aesop

lemma iff_iso :
    IsAffineMonoidWithChosenMulAndUnit F hF m e ↔
    IsAffineMonoidWithChosenMulAndUnit
      G (hF.of_nat_iso k ε.symm)
      (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
      (e ≫ ε.inv) := by
  constructor
  · apply of_iso
  · apply from_iso

end IsAffineMonoidWithChosenMulAndUnit

variable {k} in
/--A proposition stating that a corepresentable functor is an affine group with specified
multiplication, unit and inverse -/
structure IsAffineGroupWithChosenMulAndUnitAndInverse
    (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F)
    extends IsAffineMonoidWithChosenMulAndUnit F hF m e : Prop :=
  mul_inv :
    ({
        app := fun _ x ↦ (i.app _ x, x)
        naturality := by
          intro X Y (f : X →ₐ[k] Y)
          ext x
          simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, and_true]
          have := i.naturality f
          change (i.app Y).comp _ = (F.map f).comp _ at this
          exact congr_fun this x
      } ≫ m : F ⟶ F) =
      hF.coreprW.inv ≫ coyoneda.map (op <| Algebra.ofId _ _) ≫ e
  inv_mul :
    ({ app := fun _ x ↦ (x, i.app _ x)
       naturality := by
          intro X Y (f : X →ₐ[k] Y)
          ext x
          simp only [mul_obj, types_comp_apply, mul_map, Prod.mk.injEq, true_and]
          have := i.naturality f
          change (i.app Y).comp _ = (F.map f).comp _ at this
          exact congr_fun this x
      } ≫ m : F ⟶ F) =
    hF.coreprW.inv ≫ coyoneda.map (op <| Algebra.ofId _ _) ≫ e

variable {k} in
open TensorProduct in
/-- A proposition stating that an algebra has a bialgebra structure with specified
  comultiplication and counit. -/
structure IsBialgebraWithChosenComulAndCounit
    (A : Type v) [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k) : Prop :=
  coassoc :
    (Algebra.TensorProduct.assoc k A A A |>.toAlgHom.comp <|
      Algebra.TensorProduct.map comul (AlgHom.id k A) |>.comp
        comul) =
    (Algebra.TensorProduct.map (AlgHom.id k A) comul).comp comul
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor A ∘ₗ comul = TensorProduct.mk k _ _ 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor A ∘ₗ comul = (TensorProduct.mk k _ _).flip 1
  mul_compr₂_counit :
    (LinearMap.mul k A).compr₂ counit =
    (LinearMap.mul k k).compl₁₂ counit counit
  mul_compr₂_comul :
    (LinearMap.mul k A).compr₂ comul =
    (LinearMap.mul k (A ⊗[k] A)).compl₁₂ comul comul

variable {k} in
/-- A proposition stating that an algebra has a Hopf algebra structure with specified
  comultiplication, counit and antipode map. -/
structure IsHopfAlgebraWithChosenComulAndCounitAndAntipode
    (A : Type v) [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A) extends
    IsBialgebraWithChosenComulAndCounit A comul counit : Prop :=
  mul_antipode_rTensor_comul :
      LinearMap.mul' k A ∘ₗ antipode.toLinearMap.rTensor A ∘ₗ comul =
        (Algebra.linearMap k A) ∘ₗ counit.toLinearMap
  mul_antipode_lTensor_comul :
    LinearMap.mul' k A ∘ₗ antipode.toLinearMap.lTensor A ∘ₗ comul =
      (Algebra.linearMap k A) ∘ₗ counit.toLinearMap

section setup

variable {k}
variable {A : Type v} [CommRing A] [Algebra k A]
open TensorProduct in
variable (comul : A →ₐ[k] A ⊗[k] A)
variable (counit : A →ₐ[k] k)
variable (antipode : A →ₐ[k] A)

open TensorProduct in
/--Any potential comultiplication can be reinterpreted as a multiplication in the functor
language.-/
@[simp]
noncomputable def comulToMul (comul : A →ₐ[k] A ⊗[k] A) :
    square (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  (coyonedaMulCoyoneda (.of k A) (.of k A)).hom ≫ coyoneda.map (CommAlgebraCat.ofHom comul).op

/-
coyonedaCorrespondence (coyoneda.obj (op <| CommAlgebraCat.of k A))
    (coyoneda.obj (op <| CommAlgebraCat.of k A)) _ _ (Iso.refl _) (Iso.refl _) |>.symm
-/
lemma comulToMul_eq (comul : A →ₐ[k] A ⊗[k] A)  :
  comulToMul comul =
  (coyonedaCorrespondence
    (mul (coyoneda.obj (op <| .of k A)) (coyoneda.obj (op <| .of k A)))
    (coyoneda.obj (op <| .of k A))
    { coreprX := (.of k A) ⊗ (.of k A)
      coreprW := (coyonedaMulCoyoneda (.of k A) (.of k A)).symm }
    { coreprX := _
      coreprW := Iso.refl _ }).symm comul := by
  simp only [square, comulToMul, coyonedaCorrespondence_symm_apply,
    unop_op, Iso.refl_inv, Iso.cancel_iso_hom_left]
  rfl


/--Any potential counit can be reinterpreted as a unit map in the functor language.-/
@[simp]
noncomputable def counitToUnit :
    ⋆ ⟶ coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  coyoneda.map <| op <| counit

lemma counitTounit_eq (counit : A →ₐ[k] k) :
    counitToUnit counit =
    (coyonedaCorrespondence
      (coyoneda.obj (op <| .of k k))
      (coyoneda.obj (op <| .of k A))
      ⟨_, Iso.refl _⟩ ⟨_, Iso.refl _⟩).symm counit := by
  simp only [counitToUnit, unop_op, coyonedaCorrespondence_symm_apply,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  rfl

/--Any potential antipodal map can be reinterpreted as an inverse map in the functor language.-/
@[simp]
noncomputable def antipodeToInverse :
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) :=
  coyoneda.map (op antipode)

variable {F : CommAlgebraCat k ⥤ Type v} (hF : CorepresentableFunctor F)
variable (m : mul F F ⟶ F)
variable (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F)
variable (i : F ⟶ F)

-- **I think this is how it works but I am not sure**
/-- Any potential multiplication can be reinterpreted as a comultiplication in the algebra
language.-/
noncomputable def mToComul : hF.coreprX →ₐ[k] hF.coreprX ⊗[k] hF.coreprX :=
  coyonedaCorrespondence
    (mul F F) F
    { coreprX := hF.coreprX ⊗ hF.coreprX
      coreprW := coyonedaMulCoyoneda' F F hF hF |>.symm } hF m

-- **I think this is how it works but I am not sure**
/-- Any potential unit can be reinterpreted as a counit in the algebra language. -/
noncomputable def eToCounit : hF.coreprX →ₐ[k] k :=
  coyonedaCorrespondence (coyoneda.obj (op (.of k k))) F ⟨_, Iso.refl _⟩ hF e

-- **I think this is how it works but I am not sure**
/-- Any potential inverse can be reinterpreted as an antipodal map in the algebra language. -/
noncomputable def iToAntipode : hF.coreprX →ₐ[k] hF.coreprX :=
    coyonedaCorrespondence F F hF hF i

lemma comulToMul_mToComul:
    comulToMul (mToComul hF m) =
    mulMap hF.coreprW.hom hF.coreprW.hom ≫ m ≫ hF.coreprW.inv := by
  rw [comulToMul_eq, mToComul]
  let e1 := coyonedaCorrespondence
    (mul (coyoneda.obj (op <| hF.coreprX)) (coyoneda.obj (op <| hF.coreprX)))
    (coyoneda.obj <| op hF.coreprX)
    { coreprX := hF.coreprX ⊗ hF.coreprX
      coreprW := coyonedaMulCoyoneda _ _ |>.symm }
    ⟨_, Iso.refl _⟩
  let e2 := coyonedaCorrespondence
    (mul F F) F
    ⟨hF.coreprX ⊗ hF.coreprX, coyonedaMulCoyoneda' F F hF hF |>.symm⟩ hF

  change e2.trans e1.symm m = _

  have eq0 : e2.trans e1.symm =
    { toFun := fun f ↦  mulMap hF.coreprW.hom hF.coreprW.hom ≫ f ≫ hF.coreprW.inv
      invFun := fun g ↦ mulMap hF.coreprW.inv hF.coreprW.inv ≫ g ≫ hF.coreprW.hom
      left_inv := by aesop_cat
      right_inv := by aesop_cat } := by
    ext g' A ⟨x, y⟩
    simp only [coyoneda_obj_obj, unop_op, Equiv.trans_apply,
      Equiv.coe_fn_mk, FunctorToTypes.comp, mulMap_app]
    change hF.coreprW.inv.app _ _ ≫ _ = _
    set f := _; set g := _
    change hF.coreprW.inv.app _ f ≫ g = _
    simp only [unop_op]
    have eq0 := congr_fun (hF.coreprW.inv.naturality g) f
    simp only [coyoneda_obj_obj, unop_op, types_comp_apply, coyoneda_obj_map] at eq0
    rw [← eq0]
    congr!
    have eq1 := congr_fun (@NatTrans.naturality (self := g') (hF.coreprX ⊗ hF.coreprX) A
      (Algebra.TensorProduct.lift x y (by intros; show _ * _ = _ * _; rw [mul_comm]))) <|
      (coyonedaMulCoyoneda' F F hF hF).inv.app (hF.coreprX ⊗ hF.coreprX)
        (𝟙 _)
    simp only [mul_obj, types_comp_apply, mul_map] at eq1
    dsimp [g, f]
    erw [← eq1]
    congr! 1
    simp only [mul_obj, coyonedaMulCoyoneda', Iso.trans_inv, unop_op, FunctorToTypes.comp,
      coyonedaMulCoyoneda_inv_app, coyoneda_obj_obj, Algebra.TensorProduct.liftEquiv_symm_apply_coe,
      mulMap_app, Prod.mk.injEq]
    constructor
    · have := hF.coreprW.hom.naturality
      have := congr_fun (@this (hF.coreprX ⊗ hF.coreprX) A
        (Algebra.TensorProduct.lift x y (by intros; show _ * _ = _ * _; rw [mul_comm])))
        (Algebra.TensorProduct.includeLeft)
      simp only [coyoneda_obj_obj, unop_op, types_comp_apply, coyoneda_obj_map] at this
      erw [← this]
      congr!
      change AlgHom.comp _ _ = _
      exact Algebra.TensorProduct.lift_comp_includeLeft x y _
    · have := hF.coreprW.hom.naturality
      have := congr_fun (@this (hF.coreprX ⊗ hF.coreprX) A
        (Algebra.TensorProduct.lift x y (by intros; show _ * _ = _ * _; rw [mul_comm])))
        (Algebra.TensorProduct.includeRight)
      simp only [coyoneda_obj_obj, unop_op, types_comp_apply, coyoneda_obj_map] at this
      erw [← this]
      congr!
      change AlgHom.comp _ _ = _
      exact Algebra.TensorProduct.lift_comp_includeRight x y
        (by intro (x1 : hF.coreprX) (x2 : hF.coreprX) ; rw [commute_iff_eq, mul_comm])

  simp [eq0]

lemma counitToUnit_eToCounit :
    counitToUnit (eToCounit hF e) = e ≫ hF.coreprW.inv := by
  rw [counitTounit_eq, eToCounit]
  let e1 := coyonedaCorrespondence (coyoneda.obj (op (CommAlgebraCat.of k k)))
        (coyoneda.obj (op hF.coreprX))
        ⟨_, Iso.refl _⟩ ⟨_, Iso.refl _⟩
  let e2 := (coyonedaCorrespondence
    (coyoneda.obj (op (CommAlgebraCat.of k k))) F
      ⟨_, Iso.refl _⟩ hF)
  change e2.trans e1.symm e = _
  have eq0 : e2.trans e1.symm =
    { toFun := fun f ↦ f ≫ hF.coreprW.inv
      invFun := fun g ↦ g ≫ hF.coreprW.hom
      left_inv := by aesop_cat
      right_inv := by aesop_cat } := by
    ext g' A ⟨x, y⟩
    simp only [coyoneda_obj_obj, unop_op, Equiv.trans_apply, CommAlgebraCat.coe_of,
      Equiv.coe_fn_mk, FunctorToTypes.comp]
    change hF.coreprW.inv.app _ _ ≫ _ = _
    set f := _; set g := _
    change hF.coreprW.inv.app _ f ≫ g = _
    have eq0 := congr_fun (hF.coreprW.inv.naturality g) f
    simp only [coyoneda_obj_obj, unop_op, types_comp_apply, coyoneda_obj_map] at eq0
    simp only [unop_op, CommAlgebraCat.coe_of]
    rw [← eq0]
    congr!
    simp only [Iso.refl_hom, unop_op, CommAlgebraCat.coe_of, NatTrans.id_app, coyoneda_obj_obj,
      types_id_apply, Iso.refl_inv, g, f]
    have := g'.naturality ⟨x, y⟩
    dsimp at this
    have := congr_fun this (𝟙 _)
    simp only [types_comp_apply, coyoneda_obj_map, unop_op, Category.id_comp] at this
    exact this.symm
  simp only [eq0, Equiv.coe_fn_mk]

lemma antipodeToInverse_iToAntipode :
    antipodeToInverse (iToAntipode hF i) = hF.coreprW.hom ≫ i ≫ hF.coreprW.inv := by
  simp only [antipodeToInverse, unop_op]
  apply_fun coyonedaCorrespondence (coyoneda.obj (op hF.coreprX)) (coyoneda.obj (op hF.coreprX))
    ⟨hF.coreprX, Iso.refl _⟩ ⟨hF.coreprX, Iso.refl _⟩
  simp only [coyonedaCorrespondence_apply, Iso.refl_inv, Iso.refl_hom, unop_op, NatTrans.id_app,
    coyoneda_obj_obj, types_id_apply, coyoneda_map_app, FunctorToTypes.comp]
  erw [Category.comp_id]
  rfl

lemma crazy_comul_repr (comul : A →ₐ[k] A ⊗[k] A) (x : A): ∃ (ι : Type v) (s : Finset ι) (a b : ι → A),
  comul x = ∑ i in s, a i ⊗ₜ[k] b i := by
    classical
    use A ⊗[k] A
    set aa := comul x
    have mem : aa ∈ (⊤ : Submodule k (A ⊗[k] A)) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
    obtain ⟨r, hr, (eq1 : ∑ i in r.support, (_ • _) = _)⟩ := mem
    choose a a' haa' using hr
    replace eq1 := calc _
      aa = ∑ i in r.support, r i • i := eq1.symm
      _ = ∑ i in r.support.attach, (r i : k) • (i : (A ⊗[k] A))
        := Finset.sum_attach _ _ |>.symm
      _ = ∑ i in r.support.attach, (r i • a i.2 ⊗ₜ[k] a' i.2) := by
        apply Finset.sum_congr rfl
        rintro i -
        rw [haa' i.2]
      _ = ∑ i in r.support.attach, ((r i • a i.2) ⊗ₜ[k] a' i.2) := by
        apply Finset.sum_congr rfl
        rintro i -
        rw [TensorProduct.smul_tmul']
    use r.support
    use fun i => if h : i ∈ r.support then r i • a h else 0
    use fun i => if h : i ∈ r.support then a' h else 0
    rw [eq1] ; conv_rhs => rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun _ _ ↦ (by split_ifs with h <;> aesop)

namespace auxlemma

lemma aux02 :
    (mulAssoc (coyoneda.obj (op (CommAlgebraCat.of k A))) (coyoneda.obj (op (CommAlgebraCat.of k A)))
        (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom ≫
    mulMap (comulToMul comul) (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) ≫
      comulToMul comul =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
      coyoneda.map (op <|
        (((CommAlgebraCat.ofHom comul :
            CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A) ▷ _) ≫
        (α_ _ _ _).hom)) ≫
    coyoneda.map (op <| CommAlgebraCat.ofHom comul) := by
  ext B ⟨f, g, h⟩
  change A →ₐ[k] B at f g h
  simp only [coyoneda_obj_obj, unop_op, comulToMul, square, mul_obj, FunctorToTypes.comp,
    mulAssoc_hom_app, mulMap_app, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op, NatTrans.id_app, types_id_apply]
  change _ = CommAlgebraCat.ofHom comul ≫ _
  congr 1
  change Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f g _).comp comul) _ _ =
    (Algebra.TensorProduct.lift _ _ _).comp ((Algebra.TensorProduct.assoc k A A A).toAlgHom.comp
    (Algebra.TensorProduct.map comul (AlgHom.id k A)))
  ext x <;> obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
  . simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
    eq0, map_sum, Algebra.TensorProduct.lift_tmul, CommAlgebraCat.coe_of, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.coe_coe, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
    map_one, TensorProduct.sum_tmul, Algebra.TensorProduct.assoc_tmul]
    simp_rw [Algebra.TensorProduct.lift_tmul g h
      (by intro x y; rw [commute_iff_eq, mul_comm]) (b _) (b := 1)]
    simp only [map_one, mul_one]

  · simp only [Algebra.TensorProduct.lift_comp_includeRight, CommAlgebraCat.coe_of,
    AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgHom.coe_coe,
    Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
    map_one, AlgHom.coe_id, id_eq]
    rw [show (1 : A ⊗[k] A) = (1 : A) ⊗ₜ[k] (1 : A) by rfl]
    simp only [CommAlgebraCat.coe_of,
      Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    erw [Algebra.TensorProduct.lift_tmul] ; simp only [CommAlgebraCat.coe_of, map_one, one_mul]

lemma aux01  :
    mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) (comulToMul comul)
      ≫ comulToMul comul =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
    coyoneda.map (op <| _ ◁ (CommAlgebraCat.ofHom comul :
      CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A)) ≫
    coyoneda.map (op <| CommAlgebraCat.ofHom comul) := by
  ext B ⟨f, ⟨g1, g2⟩⟩
  change A →ₐ[k] B at f g1 g2
  simp only [coyoneda_obj_obj, unop_op, square, comulToMul, mul_obj, FunctorToTypes.comp,
    mulMap_app, NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op]
  change _ = CommAlgebraCat.ofHom comul ≫ _
  congr 1
  change Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift g1 g2 _).comp comul) _ =
    (Algebra.TensorProduct.lift _ _ _).comp (Algebra.TensorProduct.map (AlgHom.id k A) comul)
  ext x
  · simp only [Algebra.TensorProduct.lift_comp_includeLeft, CommAlgebraCat.coe_of, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.coe_id, id_eq, map_one, Algebra.TensorProduct.lift_tmul, mul_one]

  · simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp, Function.comp_apply,
    CommAlgebraCat.coe_of, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.lift_tmul, one_mul]


end auxlemma

end setup

variable {k} in

def AffMon_to_Bialg {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (h : IsAffineMonoidWithChosenMulAndUnit
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      { coreprX := .of k A
        coreprW := Iso.refl _ }
      (comulToMul comul)
      (counitToUnit counit)) : IsBialgebraWithChosenComulAndCounit (k := k) A comul counit where

    coassoc := by
      obtain ⟨mul_assoc, mul_one, one_mul⟩ := h
      rw [auxlemma.aux01, auxlemma.aux02, ← IsIso.inv_comp_eq] at mul_assoc
      simp only [unop_op, CommAlgebraCat.coe_of, IsIso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
        ← coyoneda.map_comp] at mul_assoc
      apply Coyoneda.coyoneda_faithful.map_injective at mul_assoc
      apply_fun unop at mul_assoc
      symm at mul_assoc
      exact mul_assoc

    rTensor_counit_comp_comul := by
      have eq0 : mulMap (counitToUnit counit) (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) ≫
          comulToMul comul = (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map (op <|
          (Algebra.TensorProduct.map counit (AlgHom.id k A)).comp comul) := by
        simp only [counitToUnit, unop_op, comulToMul, square]
        ext B ⟨f, g⟩
        change k →ₐ[k] B at f ; change A →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, mulMap_app, coyoneda_map_app,
          NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
          Quiver.Hom.unop_op]
        change (Algebra.TensorProduct.lift (f.comp counit) g _).comp comul =
          (Algebra.TensorProduct.lift f g _).comp
          ((Algebra.TensorProduct.map counit (AlgHom.id k A)).comp comul)
        ext x
        obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
        simp only [AlgHom.coe_comp, Function.comp_apply, eq0, map_sum,
          Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

      have eq1 : (starMul (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom =
          (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map
          (op <| Algebra.TensorProduct.includeRight) := by
        simp only [unop_op, CommAlgebraCat.coe_of]
        ext B ⟨f, g⟩ ; change k →ₐ[k] B at f ; change A →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, starMul_hom_app, FunctorToTypes.comp,
          coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, coyoneda_map_app]
        change _ = (Algebra.TensorProduct.lift f g _).comp Algebra.TensorProduct.includeRight
        ext x
        simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul]

      obtain ⟨_, _, one_mul⟩ := h
      rw [eq0, eq1, ← IsIso.inv_comp_eq] at one_mul
      simp only [IsIso.Iso.inv_hom, unop_op, CommAlgebraCat.coe_of] at one_mul
      erw [Iso.inv_hom_id_assoc] at one_mul
      apply Coyoneda.coyoneda_faithful.map_injective at one_mul
      apply_fun unop at one_mul
      exact congr($(one_mul).toLinearMap)

    lTensor_counit_comp_comul := by
      have eq0 : mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) (counitToUnit counit) ≫
          comulToMul comul = (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map (op <|
          (Algebra.TensorProduct.map (AlgHom.id k A) counit).comp comul) := by
        simp only [counitToUnit, unop_op, comulToMul, square]
        ext B ⟨f, g⟩ ; change A →ₐ[k] B at f ; change k →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, mulMap_app, NatTrans.id_app,
          types_id_apply, coyoneda_map_app, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
          Quiver.Hom.unop_op]
        change (Algebra.TensorProduct.lift f (g.comp counit) _ ).comp comul =
          (Algebra.TensorProduct.lift f g _).comp
          ((Algebra.TensorProduct.map (AlgHom.id k A) counit).comp comul)
        ext x ; obtain ⟨ι, s, a, b, eq0⟩ := crazy_comul_repr comul x
        simp only [AlgHom.coe_comp, Function.comp_apply, eq0, map_sum,
          Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

      have eq1 : (mulStar (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom =
          (coyonedaMulCoyoneda _ _).hom ≫ coyoneda.map
          (op <| Algebra.TensorProduct.includeLeft) := by
        simp only [unop_op, CommAlgebraCat.coe_of]
        ext B ⟨f, g⟩ ; change A →ₐ[k] B at f ; change k →ₐ[k] B at g
        simp only [coyoneda_obj_obj, unop_op, mulStar_hom_app, FunctorToTypes.comp,
          coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, coyoneda_map_app]
        change _ = (Algebra.TensorProduct.lift f g _).comp Algebra.TensorProduct.includeLeft
        ext x
        simp only [Algebra.TensorProduct.lift_comp_includeLeft]

      obtain ⟨_, mul_one, one_mul⟩ := h
      rw [eq0, eq1, ← IsIso.inv_comp_eq] at mul_one
      simp only [IsIso.Iso.inv_hom, unop_op, CommAlgebraCat.coe_of] at mul_one
      erw [Iso.inv_hom_id_assoc] at mul_one
      apply Coyoneda.coyoneda_faithful.map_injective at mul_one
      apply_fun unop at mul_one
      change (Algebra.TensorProduct.map _ _).comp _ = Algebra.TensorProduct.includeLeft at mul_one
      apply_fun AlgHom.toLinearMap at mul_one
      exact mul_one

    mul_compr₂_counit := by
      ext x y ; simp

    mul_compr₂_comul := by
      ext x y ; simp

def Bialg_to_AffMon {A : Type v} [CommRing A] [Algebra k A] (comul : A →ₐ[k] A ⊗[k] A)
    (counit : A →ₐ[k] k)
    (h : IsBialgebraWithChosenComulAndCounit (k := k) A comul counit) :
    IsAffineMonoidWithChosenMulAndUnit
    (coyoneda.obj <| op <| CommAlgebraCat.of k A)
    { coreprX := .of k A
      coreprW := Iso.refl _ }
    (comulToMul comul)
    (counitToUnit counit) where
  mul_assoc' := by
    obtain ⟨coassoc, _, _, _, _⟩ := h
    rw [auxlemma.aux01, auxlemma.aux02, ← IsIso.inv_comp_eq]
    simp only [unop_op, CommAlgebraCat.coe_of, IsIso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
      ← coyoneda.map_comp]
    congr 1
    apply_fun unop using unop_injective
    exact coassoc.symm

  mul_one := by
    obtain ⟨coassoc, rTensor_counit_comp_comul,
      lTensor_counit_comp_comul, mul_compr₂_counit, mul_compr₂_comul⟩ := h
    let ba : Bialgebra k A :={
      comul := comul
      counit := counit
      coassoc := by
        apply_fun AlgHom.toLinearMap at coassoc
        simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toLinearMap,
          AlgEquiv.toAlgHom_toLinearMap] at coassoc
        exact coassoc
      rTensor_counit_comp_comul := rTensor_counit_comp_comul
      lTensor_counit_comp_comul := lTensor_counit_comp_comul
      counit_one := counit.map_one
      mul_compr₂_counit := mul_compr₂_counit
      comul_one := comul.map_one
      mul_compr₂_comul := mul_compr₂_comul
    }
    ext B ⟨f, g⟩
    change AlgHomPoint k A B at f ; change AlgHomPoint k k B at g
    simp only [coyoneda_obj_obj, unop_op, counitToUnit, CommAlgebraCat.coe_of, comulToMul, square,
        FunctorToTypes.comp, mulMap_app, NatTrans.id_app, types_id_apply,
        coyonedaMulCoyoneda_hom_app, coyoneda_map_app, Quiver.Hom.unop_op, mulStar_hom_app]
    symm
    change _ = (Algebra.TensorProduct.lift f (g.comp counit) _).comp comul
    ext (x : A)
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
    have eq0 (y : A) : g (counit y) = counit y • g 1 := by
      rw [← mul_one (counit y), ← smul_eq_mul, map_smul]
      simp only [_root_.map_one, smul_eq_mul, mul_one]
    simp_rw [eq0 _] ; rw [map_one g, ← map_one f]
    simp_rw [← map_smul f] ; simp_rw [← f.map_mul, ← map_sum, mul_smul_one]
    have : ∑ x in r, counit (x2 x) • x1 x = AlgHomPoint.mul (AlgHom.id k A) 1 x := by
      symm ; unfold AlgHomPoint.mul
      have codef : Coalgebra.comul (R := k) (A := A) = comul := rfl
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, codef,
          AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_coe, eq, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
          id_eq, Algebra.TensorProduct.lmul'_apply_tmul] ; rw [AlgHomPoint.one_def]
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply]
      calc _
          ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x)) =
            ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x) * 1) := by simp
          _ = ∑ x in r, x1 x * (Algebra.ofId k A) (Coalgebra.counit (x2 x) • 1) := by
            simp_rw [← smul_eq_mul k] ; rfl
          _ = ∑ x in r, x1 x * (Coalgebra.counit (x2 x) • 1) := by
            simp_rw [map_smul] ; rw [map_one (Algebra.ofId k A)]
          _ = ∑ x in r, counit (x2 x) • x1 x := by
            simp_rw [mul_smul_one] ; rfl
    rw [this]
    change f x = f (((AlgHom.id k A) * 1) x)
    rw [mul_one] ; rfl

  one_mul := by
    obtain ⟨coassoc, rTensor_counit_comp_comul,
      lTensor_counit_comp_comul, mul_compr₂_counit, mul_compr₂_comul⟩ := h
    let ba : Bialgebra k A :={
      comul := comul
      counit := counit
      coassoc := by
        apply_fun AlgHom.toLinearMap at coassoc
        simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toLinearMap,
          AlgEquiv.toAlgHom_toLinearMap] at coassoc
        exact coassoc
      rTensor_counit_comp_comul := rTensor_counit_comp_comul
      lTensor_counit_comp_comul := lTensor_counit_comp_comul
      counit_one := counit.map_one
      mul_compr₂_counit := mul_compr₂_counit
      comul_one := comul.map_one
      mul_compr₂_comul := mul_compr₂_comul
    }
    ext B ⟨f, g⟩
    change AlgHomPoint k k B at f ; change AlgHomPoint k A B at g
    simp only [coyoneda_obj_obj, unop_op, counitToUnit, comulToMul, square, FunctorToTypes.comp,
        mulMap_app, coyoneda_map_app, NatTrans.id_app, types_id_apply, coyonedaMulCoyoneda_hom_app,
        CommAlgebraCat.coe_of, Quiver.Hom.unop_op, starMul_hom_app] ; symm
    change _ = (Algebra.TensorProduct.lift (f.comp counit) g _).comp comul
    ext (x : A)
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
    have eq0 (y : A) : f (counit y) = counit y • f 1 := by
        rw [← mul_one (counit y), ← smul_eq_mul, map_smul]
        simp only [_root_.map_one, smul_eq_mul, mul_one]
    simp_rw [eq0 _] ; rw [map_one f, ← map_one g]
    simp_rw [← map_smul g] ; simp_rw [← g.map_mul, ← map_sum, smul_one_mul]
    have : ∑ x in r, counit (x1 x) • x2 x = AlgHomPoint.mul 1 (AlgHom.id k A) x := by
      symm ; unfold AlgHomPoint.mul
      have codef : Coalgebra.comul (R := k) (A := A) = comul := rfl
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, codef,
          AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
          DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
          NonUnitalAlgHom.coe_coe, eq, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
          id_eq, Algebra.TensorProduct.lmul'_apply_tmul] ; rw [AlgHomPoint.one_def]
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply]
      calc _
          ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x)) * x2 x =
            ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x) * 1) * x2 x := by simp
          _ = ∑ x in r, (Algebra.ofId k A) (Coalgebra.counit (x1 x) • 1) * x2 x := by
            simp_rw [← smul_eq_mul k] ; rfl
          _ = ∑ x in r, (Coalgebra.counit (x1 x) • 1) * x2 x := by
            simp_rw [map_smul] ; rw [map_one (Algebra.ofId k A)]
          _ = ∑ x in r, counit (x1 x) • x2 x := by
            simp_rw [smul_one_mul] ; rfl
    rw [this] ; change g x = g ((1 * (AlgHom.id k A)) x)
    rw [one_mul] ; rfl

theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit
    {A : Type v} [CommRing A] [Algebra k A] (comul : A →ₐ[k] A ⊗[k] A)
    (counit : A →ₐ[k] k) :
    IsBialgebraWithChosenComulAndCounit (k := k) A comul counit ↔
    IsAffineMonoidWithChosenMulAndUnit
    (coyoneda.obj <| op <| CommAlgebraCat.of k A)
    { coreprX := .of k A
      coreprW := Iso.refl _ }
    (comulToMul comul)
    (counitToUnit counit) :=
⟨Bialg_to_AffMon k comul counit, AffMon_to_Bialg comul counit⟩

theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit'
    {F : CommAlgebraCat k ⥤ Type v} (hF : CorepresentableFunctor F)
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) :
    IsAffineMonoidWithChosenMulAndUnit F hF m e ↔
    IsBialgebraWithChosenComulAndCounit hF.coreprX (mToComul hF m) (eToCounit hF e) := by
  rw [isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit,
    IsAffineMonoidWithChosenMulAndUnit.iff_iso k F hF m e
      (coyoneda.obj (op (CommAlgebraCat.of k hF.coreprX))) hF.coreprW]
  congr!
  · simp only [CorepresentableFunctor.of_nat_iso_coreprX,
    CorepresentableFunctor.of_nat_iso_coreprW, Iso.self_symm_id]
    rfl
  · symm; rw [comulToMul_mToComul]
  · symm; rw [counitToUnit_eToCounit]

variable {k} in
def AffGrp_to_HopfAlg
    {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A)
    (h : IsAffineGroupWithChosenMulAndUnitAndInverse
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      { coreprX := .of k A
        coreprW := Iso.refl _ }
      (comulToMul comul)
      (counitToUnit counit)
      (antipodeToInverse antipode) ) :
    IsHopfAlgebraWithChosenComulAndCounitAndAntipode A comul counit antipode := by
  obtain ⟨h1, mul_inv, inv_mul⟩ := h
  obtain ⟨coassoc, rTensor_counit_comp_comul, lTensor_counit_comp_comul,
    mul_compr₂_counit, mul_compr₂_comul⟩  := AffMon_to_Bialg comul counit h1
  have : Bialgebra k A := {
      comul := comul
      counit := counit
      coassoc := by
        apply_fun AlgHom.toLinearMap at coassoc
        exact coassoc
      rTensor_counit_comp_comul := rTensor_counit_comp_comul
      lTensor_counit_comp_comul := lTensor_counit_comp_comul
      counit_one := counit.map_one
      mul_compr₂_counit := mul_compr₂_counit
      comul_one := comul.map_one
      mul_compr₂_comul := mul_compr₂_comul
  }
  fconstructor
  · exact AffMon_to_Bialg comul counit h1
  · have eq0 := congr_fun (NatTrans.congr_app mul_inv (.of k A))
      (AlgHom.id k A)
    simp only [coyoneda_obj_obj, unop_op, antipodeToInverse, coyoneda_map_app, comulToMul, square,
      FunctorToTypes.comp, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, Quiver.Hom.unop_op,
      counitToUnit] at eq0
    change (Algebra.TensorProduct.lift ((AlgHom.id k A).comp antipode) _ _).comp comul = _ at eq0
    change _ = AlgHom.comp (AlgHom.comp _ (Algebra.ofId k _)) counit at eq0
    ext x
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    rw [DFunLike.ext_iff] at eq0 ; specialize eq0 x
    simp only [AlgHom.id_comp, AlgHom.coe_comp, Function.comp_apply, eq, map_sum,
      Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, CommAlgebraCat.coe_of, Iso.refl_inv,
      NatTrans.id_app, coyoneda_obj_obj, unop_op, types_id_apply] at eq0
    simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      LinearMap.coe_comp, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, Function.comp_apply, eq,
      map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.mul'_apply,
      Algebra.linearMap_apply]
    exact eq0
  · have eq0 := congr_fun (NatTrans.congr_app inv_mul (.of k A))
      (AlgHom.id k A)
    simp only [coyoneda_obj_obj, unop_op, antipodeToInverse, coyoneda_map_app, comulToMul, square,
      FunctorToTypes.comp, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of, Quiver.Hom.unop_op,
      Iso.refl_inv, counitToUnit, Category.id_comp] at eq0
    change (Algebra.TensorProduct.lift (AlgHom.id k A)
      ((AlgHom.id k A).comp antipode) _).comp comul = _ at eq0
    change _ = AlgHom.comp (AlgHom.comp _ (Algebra.ofId k A)) counit at eq0
    ext x
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    rw [DFunLike.ext_iff] at eq0 ; specialize eq0 x
    simp only [AlgHom.id_comp, AlgHom.coe_comp, Function.comp_apply, eq, map_sum,
      Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq] at eq0
    simpa only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      LinearMap.coe_comp, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, Function.comp_apply, eq,
      map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.mul'_apply,
      Algebra.linearMap_apply]

def HopfAlg_to_AffGrp {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A)
    (h : IsHopfAlgebraWithChosenComulAndCounitAndAntipode A comul counit antipode) :
    IsAffineGroupWithChosenMulAndUnitAndInverse
    (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      { coreprX := .of k A
        coreprW := Iso.refl _ }
      (comulToMul comul)
      (counitToUnit counit)
      (antipodeToInverse antipode) := by
  obtain ⟨h1 ,
    mul_antipode_rTensor_comul, mul_antipode_lTensor_comul⟩ := h
  let _ : HopfAlgebra k A :={
    comul := comul
    counit := counit
    coassoc := by
      have := h1.coassoc
      apply_fun AlgHom.toLinearMap at this
      exact this
    rTensor_counit_comp_comul := h1.rTensor_counit_comp_comul
    lTensor_counit_comp_comul := h1.lTensor_counit_comp_comul
    counit_one := counit.map_one
    mul_compr₂_counit := h1.mul_compr₂_counit
    comul_one := comul.map_one
    mul_compr₂_comul := h1.mul_compr₂_comul
    antipode := antipode
    mul_antipode_rTensor_comul := mul_antipode_rTensor_comul
    mul_antipode_lTensor_comul := mul_antipode_lTensor_comul
  }
  fconstructor
  · exact Bialg_to_AffMon k comul counit h1
  · dsimp only [coyoneda_obj_obj, unop_op, antipodeToInverse, coyoneda_map_app, mul_obj,
    types_comp_apply, coyoneda_obj_map, mul_map, id_eq, eq_mpr_eq_cast, comulToMul, square,
    Iso.refl_inv, CommAlgebraCat.coe_of, counitToUnit]
    simp only [Category.id_comp]
    ext B (f : A →ₐ[k] B)
    simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, coyonedaMulCoyoneda_hom_app,
      CommAlgebraCat.coe_of, coyoneda_map_app, Quiver.Hom.unop_op]
    change (Algebra.TensorProduct.lift (f.comp antipode) f
      (by intro x y ; rw [commute_iff_eq, mul_comm])).comp comul =
      (f.comp (Algebra.ofId k A)).comp counit
    ext x
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
    simp_rw [← f.map_mul, ← map_sum]
    rw [DFunLike.ext_iff] at mul_antipode_rTensor_comul ; specialize mul_antipode_rTensor_comul x
    simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      LinearMap.coe_comp, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, Function.comp_apply, eq,
      map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.mul'_apply,
      Algebra.linearMap_apply] at mul_antipode_rTensor_comul
    change _ = (Algebra.ofId k A) (counit x) at mul_antipode_rTensor_comul
    apply_fun f at mul_antipode_rTensor_comul
    exact mul_antipode_rTensor_comul

  · dsimp only [coyoneda_obj_obj, unop_op, antipodeToInverse, coyoneda_map_app, mul_obj,
    types_comp_apply, coyoneda_obj_map, mul_map, id_eq, eq_mpr_eq_cast, comulToMul, square,
    Iso.refl_inv, CommAlgebraCat.coe_of, counitToUnit]
    simp only [Category.id_comp]
    ext B (f : A →ₐ[k] B)
    simp only [coyoneda_obj_obj, unop_op, FunctorToTypes.comp, coyonedaMulCoyoneda_hom_app,
      CommAlgebraCat.coe_of, coyoneda_map_app, Quiver.Hom.unop_op]
    change (Algebra.TensorProduct.lift f (f.comp antipode) _).comp comul =
      (f.comp (Algebra.ofId k A)).comp counit
    ext x
    obtain ⟨I1, r, x1, x2, eq⟩ := crazy_comul_repr comul x
    simp only [AlgHom.coe_comp, Function.comp_apply, eq, map_sum, Algebra.TensorProduct.lift_tmul]
    simp_rw [← f.map_mul, ← map_sum]
    rw [DFunLike.ext_iff] at mul_antipode_lTensor_comul ; specialize mul_antipode_lTensor_comul x
    simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
      LinearMap.coe_comp, DistribMulActionHom.coe_toLinearMap,
      NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, Function.comp_apply, eq,
      map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.mul'_apply,
      Algebra.linearMap_apply] at mul_antipode_lTensor_comul
    change _ = (Algebra.ofId k A) (counit x) at mul_antipode_lTensor_comul
    apply_fun f at mul_antipode_lTensor_comul
    exact mul_antipode_lTensor_comul


variable {k} in

theorem isAffineGroup_iff_isHopfAlgebra
    {A : Type v} [CommRing A] [Algebra k A] (comul : A →ₐ[k] A ⊗[k] A)
    (counit : A →ₐ[k] k) (antipode : A →ₐ[k] A) :
    IsHopfAlgebraWithChosenComulAndCounitAndAntipode A comul counit antipode ↔
    IsAffineGroupWithChosenMulAndUnitAndInverse
    (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      { coreprX := .of k A
        coreprW := Iso.refl _ }
      (comulToMul comul)
      (counitToUnit counit)
      (antipodeToInverse antipode) :=
  ⟨HopfAlg_to_AffGrp k comul counit antipode, AffGrp_to_HopfAlg comul counit antipode⟩

variable (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
variable (m : mul F F ⟶ F) (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F)
variable (G : CommAlgebraCat k ⥤ Type v) (ε : G ≅ F)

lemma hopf_of_iso (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
  (m : mul F F ⟶ F) (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F) (i : F ⟶ F)
  (G : CommAlgebraCat k ⥤ Type v) (ε : G ≅ F)
  (h : IsAffineGroupWithChosenMulAndUnitAndInverse F hF m e i) :
    IsAffineGroupWithChosenMulAndUnitAndInverse
      G
      (hF.of_nat_iso k ε.symm)
      (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
      (e ≫ ε.inv)
      (ε.hom ≫ i ≫ ε.inv):= by
  fconstructor
  · rw [← IsAffineMonoidWithChosenMulAndUnit.iff_iso k F hF m e G ε]
    exact h.1
  · simp only [FunctorToTypes.comp, CorepresentableFunctor.of_nat_iso_coreprX,
      CorepresentableFunctor.of_nat_iso_coreprW, Iso.trans_inv, Iso.symm_inv, unop_op,
      Category.assoc]
    rw [← Iso.inv_comp_eq]
    ext B f
    simp only [FunctorToTypes.comp, FunctorToTypes.inv_hom_id_app_apply, mulMap_app,
      coyoneda_map_app, unop_op]
    have := congr_fun (NatTrans.congr_app h.2 B) f
    simp only [FunctorToTypes.comp, unop_op, coyoneda_map_app] at this
    rw [this]

  · simp only [FunctorToTypes.comp, CorepresentableFunctor.of_nat_iso_coreprX,
    CorepresentableFunctor.of_nat_iso_coreprW, Iso.trans_inv, Iso.symm_inv, unop_op, Category.assoc]
    rw [← Iso.inv_comp_eq]
    ext B f
    simp only [FunctorToTypes.comp, FunctorToTypes.inv_hom_id_app_apply, mulMap_app,
      coyoneda_map_app, unop_op]
    have := congr_fun (NatTrans.congr_app h.3 B) f
    simp only [FunctorToTypes.comp, unop_op, coyoneda_map_app] at this
    rw [this]

lemma hopf_iff_iso (F : CommAlgebraCat k ⥤ Type v) (hF : CorepresentableFunctor F)
    (m : mul F F ⟶ F) (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F) (i : F ⟶ F)
    (G : CommAlgebraCat k ⥤ Type v) (ε : G ≅ F):
    IsAffineGroupWithChosenMulAndUnitAndInverse F hF m e i ↔
    IsAffineGroupWithChosenMulAndUnitAndInverse
      G
      (hF.of_nat_iso k ε.symm)
      (mulMap ε.hom ε.hom ≫ m ≫ ε.inv)
      (e ≫ ε.inv)
      (ε.hom ≫ i ≫ ε.inv) := by
  constructor
  · apply hopf_of_iso
  · intro h
    apply hopf_of_iso (ε := ε.symm) at h
    simp only [Iso.symm_symm_eq, Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, ← mulMap_comp_assoc, mulMap_id, Category.id_comp,
      Iso.inv_hom_id_assoc] at h
    convert h
    ext <;> simp

variable {k} in
theorem
  isAffineGroup_iff_isHopfAlgebra'
    {F : CommAlgebraCat k ⥤ Type v} (hF : CorepresentableFunctor F)
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F) :
    IsAffineGroupWithChosenMulAndUnitAndInverse F hF m e i ↔
    IsHopfAlgebraWithChosenComulAndCounitAndAntipode
      hF.coreprX (mToComul hF m) (eToCounit hF e) (iToAntipode hF i) := by
  rw [isAffineGroup_iff_isHopfAlgebra, hopf_iff_iso k F hF m e i
    (coyoneda.obj (op (CommAlgebraCat.of k hF.coreprX))) hF.coreprW]
  congr!
  · simp only [CorepresentableFunctor.of_nat_iso_coreprX,
    CorepresentableFunctor.of_nat_iso_coreprW, Iso.self_symm_id]
    rfl
  · symm ; rw [comulToMul_mToComul]
  · symm ; rw [counitToUnit_eToCounit]
  · symm ; rw [antipodeToInverse_iToAntipode]

noncomputable instance (F : AffineGroup k) : HopfAlgebra k (F.corep.coreprX) :=
  let i :=
  isAffineGroup_iff_isHopfAlgebra'
    F.corep F.m F.e F.i |>.mp
    { mul_assoc' := F.mul_assoc'
      mul_one := F.mul_one'
      one_mul := F.one_mul'
      mul_inv := F.mul_inv
      inv_mul := F.inv_mul }
  { comul := mToComul F.corep F.m
    counit := eToCounit F.corep F.e
    coassoc := by ext x; exact congr($i.coassoc x)
    rTensor_counit_comp_comul := i.1.2
    lTensor_counit_comp_comul := i.1.3
    counit_one := AlgHom.map_one _
    mul_compr₂_counit := i.1.4
    comul_one := AlgHom.map_one _
    mul_compr₂_comul := i.1.5
    antipode := iToAntipode F.corep F.i
    mul_antipode_rTensor_comul := i.2
    mul_antipode_lTensor_comul := i.3 }


/--
The antiequivalence from affine group functor to category of hopf algebra.
-/
noncomputable def affineGroupAntiToHopfAlgCat :
    (AffineGroup k)ᵒᵖ ⥤ HopfAlgCat k where
  obj F :=
  { carrier := F.unop.corep.coreprX }
  map {F G} n :=
    ({ coyonedaCorrespondence G.unop.toFunctor F.unop.toFunctor G.unop.corep F.unop.corep
              n.unop.hom with
      map_smul' := fun r  x =>
        (coyonedaCorrespondence G.unop.toFunctor F.unop.toFunctor G.unop.corep F.unop.corep
          n.unop.hom).map_smul r x
      comul_comp' := by
        let equiv :
          _ ≃ AlgHom k F.unop.corep.coreprX (G.unop.corep.coreprX ⊗[k] G.unop.corep.coreprX) :=
          coyonedaCorrespondence (mul G.unop.toFunctor G.unop.toFunctor)
          F.unop.toFunctor ⟨G.unop.corep.coreprX ⊗ G.unop.corep.coreprX,
            coyonedaMulCoyoneda' _ _ ⟨G.unop.corep.coreprX, G.unop.corep.coreprW⟩
              ⟨G.unop.corep.coreprX, G.unop.corep.coreprW⟩ |>.symm⟩
            F.unop.corep
        let f := F.unop.corep.coreprW.inv.app G.unop.corep.coreprX
                    (n.unop.hom.app G.unop.corep.coreprX
                      (G.unop.corep.coreprW.hom.app G.unop.corep.coreprX
                        (𝟙 G.unop.corep.coreprX)))
        change
          TensorProduct.map f.toLinearMap f.toLinearMap ∘ₗ
            (Bialgebra.comulAlgHom k F.unop.corep.coreprX).toLinearMap =
          Bialgebra.comulAlgHom k G.unop.corep.coreprX ∘ₗ f.toLinearMap
        suffices AlgHom.comp (Algebra.TensorProduct.map f f)
          (mToComul _ F.unop.m) = (mToComul _ G.unop.m).comp f from congr($(this).toLinearMap)
        apply_fun equiv.symm 
        dsimp only [equiv, coyonedaCorrespondence]
        simp only [Iso.symm_hom, unop_op, Iso.symm_inv, Equiv.coe_fn_symm_mk,
          Iso.cancel_iso_hom_right_assoc, Iso.cancel_iso_hom_left]
        erw [coyoneda.map_comp]
        -- change coyoneda.map ((CommAlgebraCat.ofHom (mToComul F.unop.corep F.unop.m)) ≫ 
        --   (CommAlgebraCat.ofHom (Algebra.TensorProduct.map f f))) = _
        -- change coyoneda.map (_ ≫ _) = _
        sorry
      comul_counit' := sorry
    } : F.unop.corep.coreprX →bi[k] G.unop.corep.coreprX)

  map_id X := by 
    dsimp only [coyonedaCorrespondence_apply, unop_op, AlgHom.toRingHom_eq_coe,
      RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
      RingHom.coe_coe, coyoneda_obj_obj, AlgHom.toNonUnitalAlgHom_eq_coe,
      NonUnitalAlgHom.toDistribMulActionHom_eq_coe, AlgHom.comp_toLinearMap, id_eq, unop_id]
    let f :=  (X.unop.corep.coreprW.inv.app X.unop.corep.coreprX
                ((𝟙 X.unop).hom.app X.unop.corep.coreprX
                (X.unop.corep.coreprW.hom.app X.unop.corep.coreprX (𝟙 X.unop.corep.coreprX))))
    sorry
  map_comp := sorry

#exit
noncomputable def HopfAlgebraCatToAffineGroup :
    HopfAlgCat k ⥤ (AffineGroup k)ᵒᵖ  where
  obj A := op
    { toFunctor := coyoneda.obj (op <| .of k A)
      corep :=
      { coreprX := .of k A
        coreprW := Iso.refl _ }
      m := comulToMul (Bialgebra.comulAlgHom k A)
      e := counitToUnit (Bialgebra.counitAlgHom k A)
      mul_assoc' := sorry
      mul_one' := sorry
      one_mul' := sorry
      i := antipodeToInverse HopfAlgebra.antipodeAlgHom
      mul_inv := sorry
      inv_mul := sorry }
  map {X Y} f := op <|
    { hom :=
      { app := fun A g ↦ AlgHom.comp g f.toAlgHom }
      one := sorry
      mul := sorry }
  map_id := sorry
  map_comp := sorry


noncomputable def antiequiv : (AffineGroup k)ᵒᵖ ≌ HopfAlgCat k where
  functor := affineGroupAntiToHopfAlgCat k
  inverse := HopfAlgebraCatToAffineGroup k
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry
