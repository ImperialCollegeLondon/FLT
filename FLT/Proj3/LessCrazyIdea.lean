import FLT.Proj3.CommAlgebraCat.Monoidal
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Yoneda

open CategoryTheory Opposite BigOperators

open scoped MonoidalCategory

universe v

variable (k : Type v) [CommRing k]

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

@[simps]
def mulAssoc (a b c : CommAlgebraCat k ⥤ Type v) :
    mul a (mul b c) ≅ mul (mul a b) c where
  hom := { app := fun x z ↦ ⟨⟨z.1, z.2.1⟩, z.2.2⟩ }
  inv := { app := fun x z ↦ ⟨z.1.1, ⟨z.1.2, z.2⟩⟩ }

@[simp]
def square (F : CommAlgebraCat k ⥤ Type v) : CommAlgebraCat k ⥤ Type v :=
  mul F F

local notation "⋆" => (coyoneda.obj <| op (CommAlgebraCat.of k k))

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

@[simps]
noncomputable def coyonedaMulCoyoneda (A B : CommAlgebraCat k) :
    mul (coyoneda.obj <| op A) (coyoneda.obj <| op B) ≅
    (coyoneda.obj <| op <| A ⊗ B) where
  hom :=
  { app := fun X f ↦ Algebra.TensorProduct.lift f.1 f.2 fun a b ↦ show _ = _ by rw [mul_comm]
    naturality := fun X Y f ↦ by
      ext ⟨x, y⟩
      simp only [coyoneda_obj_obj, unop_op, mul_obj, types_comp_apply, mul_map, coyoneda_obj_map]
      apply Algebra.TensorProduct.ext
      · ext a
        simp only [Algebra.TensorProduct.lift_comp_includeLeft, AlgHom.coe_comp, Function.comp_apply,
          Algebra.TensorProduct.includeLeft_apply]
        change f _ = f _
        simp only [RingHom.coe_coe]
        erw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      · ext b
        simp only [Algebra.TensorProduct.lift_comp_includeRight, AlgHom.coe_comp,
          AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply]
        change f _ = f _
        simp only [RingHom.coe_coe]
        erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul] }
  inv :=
  { app := fun X f ↦
      ⟨Algebra.TensorProduct.liftEquiv.symm f |>.1.1,
        Algebra.TensorProduct.liftEquiv.symm f |>.1.2⟩
    naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

class AffineMonoid (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable] where
  m : mul F F ⟶ F
  e : ⋆ ⟶ F
  mul_assoc' : mulMap (𝟙 F) m = (mulAssoc F F F).hom ≫ mulMap m (𝟙 F)
  mul_one' : mulMap (𝟙 F) e ≫ m = (mulStar F).hom
  one_mul' : mulMap e (𝟙 F) ≫ m = (starMul F).hom

namespace AffineMonoid

variable (F : CommAlgebraCat k ⥤ Type v) [F.Corepresentable] [amF : AffineMonoid F]

lemma mul_assoc_elementwise {A : CommAlgebraCat k} (a b c : F.obj A) :
    m.app A ⟨a, (m.app A) ⟨b, c⟩⟩ =
    m.app A ⟨m.app A ⟨a, b⟩, c⟩ := by
  have eq0 := congr_fun (NatTrans.congr_app amF.mul_assoc' A) ⟨a, ⟨b, c⟩⟩
  simp only [mul_obj, mulMap_app, NatTrans.id_app, types_id_apply, FunctorToTypes.comp,
    mulAssoc_hom_app, Prod.mk.injEq] at eq0
  rw [eq0.2, ← eq0.1]

lemma mul_one_elementwise {A : CommAlgebraCat k} (a : F.obj A) :
    m.app A ⟨a, e.app A (Algebra.ofId k A)⟩ = a := by
  simpa using congr_fun (NatTrans.congr_app amF.mul_one' A) ⟨a, Algebra.ofId k A⟩

lemma one_mul_elementwise {A : CommAlgebraCat k} (a : F.obj A) :
    m.app A ⟨e.app A (Algebra.ofId k A), a⟩ = a := by
  simpa using congr_fun (NatTrans.congr_app amF.one_mul' A) ⟨Algebra.ofId k A, a⟩

end AffineMonoid

class IsAffineMonoidWithChosenMulAndUnit
    (F : CommAlgebraCat k ⥤ Type v)
    (m : mul F F ⟶ F) (e : ⋆ ⟶ F) : Prop :=
  corepresentable : F.Corepresentable
  mul_assoc' : mulMap (𝟙 F) m = (mulAssoc F F F).hom ≫ mulMap m (𝟙 F)
  mul_one : mulMap (𝟙 F) e ≫ m = (mulStar F).hom
  one_mul : mulMap e (𝟙 F) ≫ m = (starMul F).hom

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

variable {A : Type v} [CommRing A] [Algebra k A]
open TensorProduct in
variable (comul : A →ₐ[k] A ⊗[k] A)

variable (counit : A →ₐ[k] k)

open TensorProduct in
@[simp]
noncomputable def comulToMul (comul : A →ₐ[k] A ⊗[k] A) :
    square (coyoneda.obj <| op <| CommAlgebraCat.of k A) ⟶
    coyoneda.obj <| op <| CommAlgebraCat.of k A :=
  (coyonedaMulCoyoneda (.of k A) (.of k A)).hom ≫ coyoneda.map (CommAlgebraCat.ofHom comul).op

@[simp]
noncomputable def counitToUnit :
    ⋆ ⟶ coyoneda.obj <| op <| CommAlgebraCat.of k A where
  app := fun X x => x.comp <| counit
  naturality := by
    intro X Y f
    ext
    rfl

namespace auxilary_lemmas_for_affine_monoid_implies_bialgebra.coassoc

lemma aux02 :
    (mulAssoc (coyoneda.obj (op (CommAlgebraCat.of k A))) (coyoneda.obj (op (CommAlgebraCat.of k A)))
        (coyoneda.obj (op (CommAlgebraCat.of k A)))).hom ≫
    mulMap (comulToMul comul) (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
      coyoneda.map (op <|
        (((CommAlgebraCat.ofHom comul :
            CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A) ▷ _) ≫
        (α_ _ _ _).hom)) ≫ (coyonedaMulCoyoneda _ _).inv := by
  ext B ⟨f, ⟨g1, g2⟩⟩
  simp only [mul_obj, coyoneda_obj_obj, unop_op, comulToMul, square, FunctorToTypes.comp,
    mulAssoc_hom_app, mulMap_app, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op, NatTrans.id_app, types_id_apply,
    coyonedaMulCoyoneda_inv_app, Prod.mk.eta]
  ext (x : A)
  · simp only [CommAlgebraCat.coe_of, comp_apply, Algebra.TensorProduct.liftEquiv,
      Equiv.coe_fn_symm_mk]
    erw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply]
    simp only [CommAlgebraCat.coe_of]
    change _ = Algebra.TensorProduct.lift f _ _
      ((Algebra.TensorProduct.assoc k A A A).toAlgHom.comp (Algebra.TensorProduct.map _ _) _)
    simp only [CommAlgebraCat.coe_of, unop_op, AlgHom.coe_comp, Function.comp_apply]
    simp only [CommAlgebraCat.coe_of, unop_op, AlgEquiv.toAlgHom_eq_coe,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_coe]
    obtain ⟨ι, s, a, b, eq0⟩ : ∃ (ι : Type v) (s : Finset ι) (a b : ι → A),
      comul x = ∑ i in s, a i ⊗ₜ[k] b i := sorry
    erw [eq0]
    simp only [CommAlgebraCat.coe_of, map_sum, unop_op, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    erw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul]
    simp only [CommAlgebraCat.coe_of, unop_op, map_one, mul_one]
  · sorry

lemma aux01  :
    mulMap (𝟙 (coyoneda.obj (op (CommAlgebraCat.of k A)))) (comulToMul comul) =
    mulMap (𝟙 _) (coyonedaMulCoyoneda _ _).hom ≫
    (coyonedaMulCoyoneda _ _).hom ≫
    coyoneda.map (op <| _ ◁ (CommAlgebraCat.ofHom comul :
      CommAlgebraCat.of k A ⟶ CommAlgebraCat.of k A ⊗ CommAlgebraCat.of k A)) ≫
    (coyonedaMulCoyoneda _ _).inv := by
  ext B ⟨f, g⟩
  simp only [mul_obj, coyoneda_obj_obj, unop_op, square, mulMap, NatTrans.id_app, types_id_apply,
    comulToMul, FunctorToTypes.comp, coyonedaMulCoyoneda_hom_app, CommAlgebraCat.coe_of,
    coyoneda_map_app, Quiver.Hom.unop_op, MonoidalCategory.id_tensorHom,
    coyonedaMulCoyoneda_inv_app, Prod.mk.eta]
  ext (x : A)
  · simp only [CommAlgebraCat.coe_of]
    simp only [Algebra.TensorProduct.liftEquiv, CommAlgebraCat.coe_of, Equiv.coe_fn_symm_mk]
    erw [AlgHom.comp_apply, AlgHom.comp_apply]
    change _ = Algebra.TensorProduct.lift f _ _ (Algebra.TensorProduct.map (AlgHom.id _ _) _
      (x ⊗ₜ[k] 1))
    simp only [unop_op, CommAlgebraCat.coe_of]
    simp only [unop_op, CommAlgebraCat.coe_of, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      _root_.map_one]
    erw [Algebra.TensorProduct.lift_tmul]
    simp
    rfl
  · simp only [CommAlgebraCat.coe_of, comp_apply]
    simp only [CommAlgebraCat.coe_of, Algebra.TensorProduct.liftEquiv, Equiv.coe_fn_symm_mk]
    erw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply]
    simp only [CommAlgebraCat.coe_of, AlgHom.coe_restrictScalars']
    erw [Algebra.TensorProduct.lift_tmul]
    simp only [CommAlgebraCat.coe_of, AlgHom.toLinearMap_apply, _root_.map_one, one_mul]
    intros
    change _ * _ = _ * _
    rw [mul_comm]

end  auxilary_lemmas_for_affine_monoid_implies_bialgebra.coassoc

open TensorProduct in
open auxilary_lemmas_for_affine_monoid_implies_bialgebra.coassoc in
theorem five_point_one  :
    IsAffineMonoidWithChosenMulAndUnit
      (coyoneda.obj <| op <| CommAlgebraCat.of k A)
      (comulToMul comul)
      (counitToUnit counit) ↔
    IsBialgebraWithChosenComulAndCounit A comul counit := by
  constructor
  · rintro ⟨corepresentable, mul_assoc, mul_one, one_mul⟩
    let am : AffineMonoid (coyoneda.obj (op (.of k A))) :=
    { m := comulToMul comul
      e := counitToUnit counit
      mul_assoc' := mul_assoc
      mul_one' := mul_one
      one_mul' := one_mul }
    fconstructor
    · rw [aux01, aux02] at mul_assoc
      have eq0 :
        coyoneda.map (op (CommAlgebraCat.of k A ◁ CommAlgebraCat.ofHom comul)) =
        coyoneda.map (op
          (CommAlgebraCat.ofHom comul ▷ CommAlgebraCat.of k A ≫
            (α_ (CommAlgebraCat.of k A) (CommAlgebraCat.of k A) (CommAlgebraCat.of k A)).hom)) :=
        sorry -- this is the middle part of `mul_assoc`, other terms are all isomorphisms
      apply Coyoneda.coyoneda_faithful.map_injective at eq0
      apply_fun unop at eq0
      simp only [unop_op] at eq0
      ext x
      exact (DFunLike.congr_fun (F := AlgHom k (A ⊗[k] A) (A ⊗[k] (A ⊗[k] A))) eq0 (comul x)).symm
    · sorry
    · sorry
    · have eq0 := congr_fun (NatTrans.congr_app mul_assoc (.of k A))
        ⟨AlgHom.id _ _, ⟨Algebra.TensorProduct.lmul' k (S := A) |>.comp comul, AlgHom.id _ _⟩⟩
      simp only [mul_obj, coyoneda_obj_obj, unop_op, CommAlgebraCat.coe_of, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.comp, mulAssoc_hom_app,
        Prod.mk.injEq] at eq0
      obtain ⟨eq0, eq1⟩ := eq0
      apply_fun AlgHom.toLinearMap at eq0 eq1
      simp only [AlgHom.toLinearMap_id, AlgHom.comp_toLinearMap,
        Algebra.TensorProduct.lmul'_toLinearMap] at eq0 eq1 ⊢
      ext
      simp
    · have eq0 := congr_fun (NatTrans.congr_app mul_assoc (.of k A))
        ⟨AlgHom.id _ _, ⟨Algebra.TensorProduct.lmul' k (S := A) |>.comp comul, AlgHom.id _ _⟩⟩
      simp only [mul_obj, coyoneda_obj_obj, unop_op, CommAlgebraCat.coe_of, mulMap_app,
        NatTrans.id_app, types_id_apply, FunctorToTypes.comp, mulAssoc_hom_app,
        Prod.mk.injEq] at eq0
      obtain ⟨eq0, eq1⟩ := eq0
      apply_fun AlgHom.toLinearMap at eq0 eq1
      simp only [AlgHom.toLinearMap_id, AlgHom.comp_toLinearMap,
        Algebra.TensorProduct.lmul'_toLinearMap] at eq0 eq1 ⊢
      ext a b
      simp
  · sorry
