import FLT.for_mathlib.Coalgebra.Monoid
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.Algebra.Category.AlgebraCat.Monoidal

variable (R : Type*)[CommRing R]

open CategoryTheory Opposite
open BigOperators

section Coalgebra

variable (A B : Type*) [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddCommMonoid B]
  [Module R B] [Coalgebra R B]

structure CoalgHom extends A →ₗ[R] B where
  comul_comp' :
    (TensorProduct.map toLinearMap toLinearMap).comp (Coalgebra.comul (R := R) (A := A)) =
    (Coalgebra.comul (R := R) (A := B)).comp toLinearMap
  comul_counit' :
    (Coalgebra.counit (R := R) (A := B)).comp toLinearMap = (Coalgebra.counit (R := R) (A := A))

notation:25 M " →co[" R:25 "] " M₂:0 => CoalgHom R M M₂

instance : FunLike (A →co[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; dsimp at h; congr; ext; exact congr_fun h _

instance : LinearMapClass (A →co[R] B) R A B where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

end Coalgebra

section Bialgebra


variable (A B C : Type*) [Ring A] [Ring B] [Ring C] [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]


structure BialgHom extends A →co[R] B, A →ₐ[R] B

notation:25 M " →bi[" R:25 "] " M₂:0 => BialgHom R M M₂

namespace BialgHom

instance : FunLike (A →bi[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; dsimp at h; congr;
    refine DFunLike.ext _ _ fun _ ↦ ?_
    exact congr_fun h _

instance : AlgHomClass (A →bi[R] B) R A B where
  map_mul f := map_mul f.toAlgHom
  map_one f := map_one f.toAlgHom
  map_add f := f.map_add
  map_zero f := f.map_zero
  commutes f := f.toAlgHom.commutes

@[simps!]
def id : A →bi[R] A where
  __ := LinearMap.id (R := R) (M := A)
  __ := AlgHom.id R A
  toFun x := x
  comul_comp' := by
    ext x ; simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R:= R) (x:A)
    rw [hx, map_sum] ; simp
  comul_counit' := rfl

variable {R A B C} in
def comp (g : B →bi[R] C) (f : A →bi[R] B)  : A →bi[R] C :=
  {
    __ := g.toLinearMap.comp f.toLinearMap
    __ := g.toAlgHom.comp f.toAlgHom
    comul_comp' := by
      ext x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp, AlgHom.coe_mk,
        AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
      obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) (x : A)
      rw [hx, map_sum]
      simp only [TensorProduct.map_tmul, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
      have : ∑ x in I1, g.toLinearMap (f.toLinearMap (x1 x)) ⊗ₜ[R]
          g.toLinearMap (f.toLinearMap (x2 x)) =
          (TensorProduct.map g.toLinearMap g.toLinearMap).comp
          (TensorProduct.map f.toLinearMap f.toLinearMap) (∑ x in I1, (x1 x ⊗ₜ[R] x2 x)) := by
        simp only [map_sum, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul]
      simp only [LinearMap.coe_toAddHom, LinearMap.coe_comp, Function.comp_apply]
      rw [this, ← hx]
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← g.comul_comp']
      rw [← LinearMap.comp_apply, LinearMap.comp_assoc f.toLinearMap Coalgebra.comul
         (TensorProduct.map g.toLinearMap g.toLinearMap)]
      rw [← f.comul_comp']
      simp
    map_smul' := by simp
    comul_counit' := by
      ext x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp, AlgHom.coe_mk,
        AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.coe_mk, MonoidHom.coe_mk,
        OneHom.coe_mk, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
      rw [← LinearMap.comp_apply]
      rw [LinearMap.ext_iff.1 g.toCoalgHom.comul_counit' (f.toLinearMap x)]
      rw [← LinearMap.comp_apply]
      apply LinearMap.ext_iff.1 f.toCoalgHom.comul_counit' x
  }

lemma comp_id (f : A →bi[R] B) : comp f (id R A) = f := rfl

lemma id_comp (f : A →bi[R] B) : (id R (A:=B)).comp f = f := rfl

end BialgHom


structure BialgEquiv (R A B : Type*) [CommRing R] [Ring A] [Ring B]
  [Bialgebra R A] [Bialgebra R B] extends A →bi[R] B, A ≃ₐ[R] B

notation:50 A " ≃bi[" R "] " A' => BialgEquiv R A A'

namespace BialgEquiv
instance : EquivLike (A ≃bi[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨⟨⟨f,_⟩,_⟩,_,_⟩,_⟩,_⟩ := f
    obtain ⟨⟨⟨⟨⟨g,_⟩,_⟩,_,_⟩,_⟩,_⟩ := g
    congr

instance : AlgEquivClass (BialgEquiv R A B) R A B where
  map_mul := fun f => f.toAlgEquiv.map_mul
  map_add := fun f => f.toAlgEquiv.map_add
  commutes := fun f => f.toAlgEquiv.commutes

def Simps.apply (e : A ≃bi[R] B) : A → B :=
  e

def Simps.toEquiv (e : A ≃ₐ[R] B) : A ≃ B :=
  e

instance : FunLike (A ≃ₐ[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

@[ext]
theorem ext {f g : A ≃bi[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : A ≃bi[R] A :=
{ AlgEquiv.refl,
  BialgHom.id  R A with }

lemma apply_symm_apply (e : A ≃ₐ[R] B) : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
  LinearMap.ext fun x => by simp

lemma comul_eq_invinv_comul_e (e : A ≃bi[R] B) : Coalgebra.comul =
    (TensorProduct.map e.toAlgEquiv.symm.toLinearMap e.toAlgEquiv.symm.toLinearMap) ∘ₗ
    Coalgebra.comul ∘ₗ e.toLinearMap := by
    calc
      Coalgebra.comul = (TensorProduct.map LinearMap.id LinearMap.id) ∘ₗ Coalgebra.comul := by
          ext x ; simp
      _ = (TensorProduct.map (e.toAlgEquiv.symm.toLinearMap ∘ₗ e.toAlgEquiv.toLinearMap)
            (e.toAlgEquiv.symm.toLinearMap ∘ₗ e.toAlgEquiv.toLinearMap)) ∘ₗ Coalgebra.comul:= by
          rw [apply_symm_apply]
      _ = (TensorProduct.map e.toAlgEquiv.symm.toLinearMap e.toAlgEquiv.symm.toLinearMap) ∘ₗ
            (TensorProduct.map e.toAlgEquiv.toLinearMap e.toAlgEquiv.toLinearMap) ∘ₗ
            Coalgebra.comul := by
          rw [TensorProduct.map_comp]; rfl
      _ = (TensorProduct.map e.toAlgEquiv.symm.toLinearMap e.toAlgEquiv.symm.toLinearMap) ∘ₗ
            Coalgebra.comul ∘ₗ e.toLinearMap := by
          rw [← CoalgHom.comul_comp']; rfl

@[symm]
def symm (e : A ≃bi[R] B) : B ≃bi[R] A :=
  {
    e.toAlgEquiv.symm with
  map_smul' := by simp
  comul_comp' := by
    have eq0 : Coalgebra.comul ∘ₗ e.toAlgEquiv.symm.toLinearMap =
        (TensorProduct.map e.toAlgEquiv.symm.toLinearMap e.toAlgEquiv.symm.toLinearMap) ∘ₗ
        Coalgebra.comul ∘ₗ e.toLinearMap ∘ₗ e.toAlgEquiv.symm.toLinearMap := by
      rw [comul_eq_invinv_comul_e (e := e)]
      rfl
    ext x
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AlgEquiv.coe_mk,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    change TensorProduct.map e.toAlgEquiv.symm.toLinearMap e.toAlgEquiv.symm.toLinearMap _ = _
    replace eq0 := congr($eq0 x)
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_mk] at eq0
    rw [eq0]
    congr
    exact e.4 x |>.symm
  comul_counit' := by
    have eq0 : (Coalgebra.counit ∘ₗ e.toLinearMap) ∘ₗ e.toAlgEquiv.symm.toLinearMap =
        Coalgebra.counit ∘ₗ e.toAlgEquiv.symm.toLinearMap := by rw [e.comul_counit']
    ext x
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AlgEquiv.coe_mk,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    replace eq0 := congr($eq0 x)
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_mk] at eq0
    rw [eq0.symm]
    congr
    exact e.4 x
  map_one' := by simp
  map_zero' := by simp
  }

@[trans]
def trans (e₁ : A ≃bi[R] B) (e₂ : B ≃bi[R] C) : A ≃bi[R] C :=
  {
    e₁.toAlgEquiv.trans e₂.toAlgEquiv with
  map_smul' := by simp
  comul_comp' := (e₂.toBialgHom.comp e₁.toBialgHom).comul_comp'
  comul_counit' := (e₂.toBialgHom.comp e₁.toBialgHom).comul_counit'
  map_zero' := by simp
  map_one' := by simp
  }

end BialgEquiv
end Bialgebra


section Hopf

variable (H : Type*)[CommRing H][HopfAlgebra R H]
variable (H1 H2 : Type*)[CommRing H1][CommRing H2][HopfAlgebra R H1][HopfAlgebra R H2]

noncomputable section HopfEquivScheme

open Opposite
open CategoryTheory
open scoped TensorProduct
open HopfAlgebra
open Coalgebra

structure HopfAlgCat where
  carrier : Type*
  [isCommRing : CommRing carrier]
  [isHopfAlgebra : HopfAlgebra R carrier]

attribute [instance]  HopfAlgCat.isHopfAlgebra HopfAlgCat.isCommRing

namespace HopfAlgCat

instance : CoeSort (HopfAlgCat R) Type* := ⟨HopfAlgCat.carrier⟩

attribute [coe] HopfAlgCat.carrier

abbrev ten_anti := TensorProduct.map (antipode (R := R) (A := H1)) (antipode (R := R) (A := H2))

lemma antipode_decomp (I1: Finset (H1 ⊗[R] H1)) (h11 h12 : H1 ⊗[R] H1 → H1) (h1 : H1)
  (h01: Coalgebra.comul h1 = ∑ i in I1, h11 i ⊗ₜ[R] h12 i) :
  ∑ a in I1, antipode (R := R) (h11 a) * h12 a =  (1 : LinearPoint R H1 H1) h1 := by
  symm ; rw [← antipode_mul_id (R:= R) (A:= H1), LinearPoint.mul_repr antipode LinearMap.id h1 I1 _ _ h01]
  simp only [LinearMap.comp_apply, h01, map_sum, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.mul'_apply]
--another way to decomp
lemma antipode_decomp' (I1: Finset (H1 ⊗[R] H1)) (h11 h12 : H1 ⊗[R] H1 → H1) (h1 : H1)
  (h01: Coalgebra.comul h1 = ∑ i in I1, h11 i ⊗ₜ[R] h12 i) :
  ∑ a in I1, h11 a * antipode (R := R) (h12 a) = (1 : LinearPoint R H1 H1) h1 := by
  symm ; rw [← id_mul_antipode (R:= R) (A:= H1), LinearPoint.mul_repr LinearMap.id antipode h1 I1 _ _ h01]
  simp only [LinearMap.comp_apply, h01, map_sum, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.mul'_apply]

instance : AddMonoidHomClass ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2 →ₗ[R] (H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2)
  ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2) ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2) where
      map_add f := f.map_add
      map_zero := fun f ↦ LinearMap.map_zero f

open TensorProduct BigOperators
lemma anti_rTensor : LinearMap.mul' R (H1 ⊗[R] H2) ∘ₗ
    LinearMap.rTensor (H1 ⊗[R] H2) (TensorProduct.map antipode antipode) ∘ₗ Coalgebra.comul =
  Algebra.linearMap R (H1 ⊗[R] H2) ∘ₗ Coalgebra.counit := by
  ext h1 h2 ; simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨I1, h11, h12, h01⟩ := Coalgebra.exists_repr (R := R) (h1 : H1)
  obtain ⟨I2, h21, h22, h02⟩ := Coalgebra.exists_repr (R := R) (h2 : H2)
  --have : Coalgebra.comul (R := R) (A := H1 ⊗[R] H2) = (TensorProduct.tensorTensorTensorComm (R := R) (M := H1) (N := H1) (P:= H2) (Q:= H2)) ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by exact Coalgebra.TensorProduct.comul_def R H1 H2
  rw [TensorProduct.comul_apply_repr h1 h2 I1 I2 h11 h12 h01 h21 h22 h02]
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Algebra.TensorProduct.tmul_mul_tmul] ; rw [Finset.sum_comm]
  simp_rw [← TensorProduct.sum_tmul] ; rw [antipode_decomp R H1 I1 h11 h12 h1 h01]
  simp_rw [← TensorProduct.tmul_sum] ; rw [antipode_decomp R H2 I2 h21 h22 h2 h02]
  --have cou : Coalgebra.counit (R := R) (A := H1 ⊗[R] H2) = ten_counit R H1 H2 := rfl
  simp only [TensorProduct.counit_def, AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
    NonUnitalAlgHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
    Bialgebra.counitAlgHom_apply, Algebra.TensorProduct.lmul'_apply_tmul, _root_.map_mul]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_tmul, lid_tmul,
    smul_eq_mul]
  rw [← mul_one (Coalgebra.counit h2), mul_comm,
    ← smul_eq_mul (a := Coalgebra.counit h2) (a' := 1), ← Algebra.ofId_apply,
    Algebra.smul_mul_assoc, AlgHom.map_smul (Algebra.ofId R H1), one_mul, TensorProduct.smul_tmul,
    Algebra.smul_def (R := R) (A := H2) (Coalgebra.counit h2) (1 : H2), mul_one,
    ← Bialgebra.counitAlgHom_apply, ← Bialgebra.counitAlgHom_apply, ← AlgHom.comp_apply]
  rw [← AlgHomPoint.one_def (R := R) (A := H1) (L := H1), ← Algebra.ofId_apply, ← AlgHom.comp_apply,
    ← AlgHomPoint.one_def (R := R) (A := H2) (L := H2)] ; rfl

lemma anti_lTensor : LinearMap.mul' R (H1 ⊗[R] H2) ∘ₗ
    LinearMap.lTensor (H1 ⊗[R] H2) (TensorProduct.map antipode antipode) ∘ₗ Coalgebra.comul =
  Algebra.linearMap R (H1 ⊗[R] H2) ∘ₗ Coalgebra.counit := by
  ext h1 h2 ; simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨I1, h11, h12, h01⟩ := Coalgebra.exists_repr (R := R) (h1 : H1)
  obtain ⟨I2, h21, h22, h02⟩ := Coalgebra.exists_repr (R := R) (h2 : H2)
  --have : Coalgebra.comul (R := R) (A := H1 ⊗[R] H2) = HopfPoints.tcomul R H1 H2 := rfl
  rw [TensorProduct.comul_apply_repr h1 h2 I1 I2 h11 h12 h01 h21 h22 h02]
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Algebra.TensorProduct.tmul_mul_tmul] ; rw [Finset.sum_comm]
  simp_rw [← TensorProduct.sum_tmul] ; rw [antipode_decomp' R H1 I1 h11 h12 h1 h01]
  simp_rw [← TensorProduct.tmul_sum] ; rw [antipode_decomp' R H2 I2 h21 h22 h2 h02]
  --have cou : Coalgebra.counit (R := R) (A := H1 ⊗[R] H2) = ten_counit R H1 H2 := rfl
  simp only [TensorProduct.counit_def, AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
    NonUnitalAlgHom.coe_coe, AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul,
    Bialgebra.counitAlgHom_apply, Algebra.TensorProduct.lmul'_apply_tmul, _root_.map_mul]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_tmul, lid_tmul,
    smul_eq_mul]
  rw [← mul_one (Coalgebra.counit h2), mul_comm,
    ← smul_eq_mul (a := Coalgebra.counit h2) (a' := 1), ← Algebra.ofId_apply,
    Algebra.smul_mul_assoc, AlgHom.map_smul (Algebra.ofId R H1), one_mul, TensorProduct.smul_tmul,
    Algebra.smul_def (R := R) (A := H2) (Coalgebra.counit h2) (1 : H2), mul_one,
    ← Bialgebra.counitAlgHom_apply, ← Bialgebra.counitAlgHom_apply, ← AlgHom.comp_apply]
  rw [← AlgHomPoint.one_def (R := R) (A := H1) (L := H1), ← Algebra.ofId_apply, ← AlgHom.comp_apply,
    ← AlgHomPoint.one_def (R := R) (A := H2) (L := H2)] ; rfl

instance _root_.HopfAlgebra.tensorProduct : HopfAlgebra R (H1 ⊗[R] H2) where
  __ := (inferInstance : Bialgebra R (H1 ⊗[R] H2))
  antipode := TensorProduct.map (antipode (R := R) (A := H1)) (antipode (R := R) (A := H2))
  mul_antipode_rTensor_comul := anti_rTensor R H1 H2
  mul_antipode_lTensor_comul := anti_lTensor R H1 H2

instance : Category (HopfAlgCat R) where
  Hom A B := A →bi[R] B
  id A := BialgHom.id R A
  comp f g := BialgHom.comp g f
  comp_id f := by simp; exact BialgHom.comp_id R _ _ f
  id_comp f := by simp; exact BialgHom.id_comp R _ _ f
  assoc f g h := by simp only; exact rfl

end HopfAlgCat

end HopfEquivScheme

end Hopf
