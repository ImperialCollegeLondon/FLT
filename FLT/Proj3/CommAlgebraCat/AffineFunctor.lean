import FLT.Proj3.CommAlgebraCat.Monoidal
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Yoneda
import FLT.Proj3.HopfMon

open CategoryTheory Opposite BigOperators

open scoped MonoidalCategory
open scoped TensorProduct

variable (k : Type v) [CommRing k]

local notation "⋆" => (coyoneda.obj <| op (CommAlgebraCat.of k k))

section setup

variable {k}


@[simps]
def mul (F G : CommAlgebraCat k ⥤ Type v) :
    CommAlgebraCat k ⥤ Type v where
  obj A := (F.obj A) × (G.obj A)
  map f x := ⟨F.map f x.1, G.map f x.2⟩

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
    IsIso (mulMap f g) := sorry

lemma mulMap_comp {a a' a'' b b' b'' : CommAlgebraCat k ⥤ Type v}
    (f : a ⟶ a') (f' : a' ⟶ a'')
    (g : b ⟶ b') (g' : b' ⟶ b'') :
    mulMap (f ≫ f') (g ≫ g') =
    mulMap f g ≫ mulMap f' g' := sorry

@[simps]
def mulAssoc (a b c : CommAlgebraCat k ⥤ Type v) :
    mul a (mul b c) ≅ mul (mul a b) c where
  hom := { app := fun x z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩ }
  inv := { app := fun x z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩ }

@[simp]
def square (F : CommAlgebraCat k ⥤ Type v) : CommAlgebraCat k ⥤ Type v :=
  mul F F

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

-- The formatting is not ideal
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

end setup

structure AffineMonoid extends CommAlgebraCat k ⥤ Type v where
  corep : toFunctor.Corepresentable
  /--
  F × (F × F) -mul-> F × F -mul-> F
    |                             |
  mulAssoc                       𝟙 F
    v                             v
  (F × F) × F -mul> F × F -mul-> F
  -/
  m : mul toFunctor toFunctor ⟶ toFunctor
  e : ⋆ ⟶ toFunctor
  mul_assoc' : mulMap (𝟙 toFunctor) m ≫ m =
    (mulAssoc toFunctor toFunctor toFunctor).hom ≫ mulMap m (𝟙 toFunctor) ≫ m
  mul_one' : mulMap (𝟙 _) e ≫ m = (mulStar toFunctor).hom
  one_mul' : mulMap e (𝟙 _) ≫ m = (starMul toFunctor).hom

attribute [instance] AffineMonoid.corep


structure AffineGroup extends AffineMonoid k where
  i : toFunctor ⟶ toFunctor
  /--
  **Check if this correct**
  -/
  mul_inv :
  ({
    app := fun _ x ↦ (i.app _ x, x)
    naturality := by sorry
  } ≫ m : toFunctor ⟶ toFunctor) = 𝟙 toFunctor
  inv_mul :
  ({
      app := fun _ x ↦ (x, i.app _ x)
      naturality := by sorry
    } ≫ m : toFunctor ⟶ toFunctor)= 𝟙 toFunctor

namespace AffineMonoid

variable {k}

structure Hom (F G : AffineMonoid k) where
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

structure Hom (F G : AffineGroup k) where
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
structure IsAffineMonoidWithChosenMulAndUnit
    (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) : Prop :=
  /--
  F × (F × F) -mul-> F × F -mul-> F
    |                             |
  mulAssoc                       𝟙 F
    v                             v
  (F × F) × F -mul> F × F -mul-> F
  -/
  mul_assoc' : mulMap (𝟙 F) m ≫ m = (mulAssoc F F F).hom ≫ mulMap m (𝟙 F) ≫ m
  mul_one : mulMap (𝟙 F) e ≫ m = (mulStar F).hom
  one_mul : mulMap e (𝟙 F) ≫ m = (starMul F).hom


variable {k} in
structure IsAffineGroupWithChosenMulAndUnitAndInverse
    (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F)
    extends IsAffineMonoidWithChosenMulAndUnit F m e: Prop :=
  mul_inv :
    ({
      app := fun _ x ↦ (i.app _ x, x)
      naturality := by sorry
    } ≫ m : F ⟶ F) = 𝟙 F
  inv_mul :
    ({
        app := fun _ x ↦ (x, i.app _ x)
        naturality := by sorry
      } ≫ m : F ⟶ F)= 𝟙 F

variable {k} in
open TensorProduct in
class IsBialgebraWithChosenComulAndCounit
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
@[simp]
noncomputable def comulToMul (comul : A →ₐ[k] A ⊗[k] A) :
    square (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  (coyonedaMulCoyoneda (.of k A) (.of k A)).hom ≫ coyoneda.map (CommAlgebraCat.ofHom comul).op

@[simp]
noncomputable def counitToUnit :
    ⋆ ⟶ coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  coyoneda.map <| op <| counit

@[simp]
noncomputable def antipodeToInverse :
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    (coyoneda.obj <| op <| CommAlgebraCat.of k A) :=
  coyoneda.map (op antipode)

variable {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
variable (m : mul F F ⟶ F)
variable (e : (coyoneda.obj <| op (CommAlgebraCat.of k k)) ⟶ F)
variable (i : F ⟶ F)

-- **I think this is how it works but I am not sure**
noncomputable def mToComul : F.coreprX →ₐ[k] F.coreprX ⊗[k] F.coreprX :=
  (coyonedaMulCoyoneda _ _).inv ≫ mulMap F.coreprW.hom F.coreprW.hom ≫ m ≫ F.coreprW.inv |>.app
    (F.coreprX ⊗ F.coreprX) (𝟙 _)

-- **I think this is how it works but I am not sure**
noncomputable def eToCounit : F.coreprX →ₐ[k] k :=
  e ≫ F.coreprW.inv |>.app (CommAlgebraCat.of k k) (𝟙 _)

-- **I think this is how it works but I am not sure**
noncomputable def iToAntipode : F.coreprX →ₐ[k] F.coreprX :=
  F.coreprW.hom ≫ i ≫ F.coreprW.inv |>.app (F.coreprX) (𝟙 _)
end setup

variable {k} in
theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit
    {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k) :
    IsAffineMonoidWithChosenMulAndUnit
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      (comulToMul comul)
      (counitToUnit counit) ↔
    IsBialgebraWithChosenComulAndCounit A comul counit := sorry

variable {k} in
theorem isAffineMonoidWithChosenMulAndUnit_iff_isBialgebraWithChosenComulAndCounit'
    {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) :
    IsAffineMonoidWithChosenMulAndUnit F m e ↔
    IsBialgebraWithChosenComulAndCounit F.coreprX (mToComul m) (eToCounit e) := sorry

variable {k} in
theorem
  isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode
    {A : Type v} [CommRing A] [Algebra k A]
    (comul : A →ₐ[k] A ⊗[k] A) (counit : A →ₐ[k] k)
    (antipode : A →ₐ[k] A) :
    IsAffineGroupWithChosenMulAndUnitAndInverse
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      (comulToMul comul)
      (counitToUnit counit)
      (antipodeToInverse antipode) ↔
    IsBialgebraWithChosenComulAndCounit A comul counit := sorry

variable {k} in
theorem
  isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode'
    {F : CommAlgebraCat k ⥤ Type v} [F.Corepresentable]
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) (i : F ⟶ F) :
    IsAffineGroupWithChosenMulAndUnitAndInverse F m e i ↔
    IsHopfAlgebraWithChosenComulAndCounitAndAntipode
      F.coreprX (mToComul m) (eToCounit e) (iToAntipode i) := sorry

def affineGroupAntiEquivCommAlgCat :
    (AffineGroup k)ᵒᵖ ≌ HopfAlgCat.{v} k where
  functor :=
    { obj := fun F ↦
        { carrier := F.unop.coreprX
          isCommRing := inferInstance
          isHopfAlgebra :=
            let i := isAffineGroupWithChosenMulAndUnitAndInverse_iff_isBialgebraWithChosenComulAndCounitAndAntipode'
              F.unop.m F.unop.e F.unop.i |>.mp
                ⟨⟨F.unop.mul_assoc', F.unop.mul_one', F.unop.one_mul'⟩,
                  F.unop.mul_inv, F.unop.inv_mul⟩
            { comul := mToComul F.unop.m
              counit := eToCounit F.unop.e
              coassoc := by ext x; exact congr($(i.1.coassoc) x)
              rTensor_counit_comp_comul := i.1.2
              lTensor_counit_comp_comul := i.1.3
              counit_one := (eToCounit F.unop.e).map_one
              mul_compr₂_counit := i.1.4
              comul_one := (mToComul F.unop.m).map_one
              mul_compr₂_comul := i.1.5
              antipode := iToAntipode F.unop.i
              mul_antipode_rTensor_comul := i.2
              mul_antipode_lTensor_comul := i.mul_antipode_lTensor_comul } }
      map := sorry
      map_id := sorry
      map_comp := sorry }
  inverse := sorry
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry
