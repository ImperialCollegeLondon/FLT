import FLT.for_mathlib.Coalgebra.Monoid
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.for_mathlib.HopfAlgebra.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Algebra.Basic
variable (R :Type)[CommRing R]

open CategoryTheory AlgebraicGeometry Opposite
open BigOperators

-- local notation "AScheme/" R => Over (AffineScheme.Spec.obj (op <| CommRingCat.of R))

-- noncomputable instance : MonoidalCategory (AScheme/R) where
--   tensorObj := sorry
--   whiskerLeft := sorry
--   whiskerRight := sorry
--   tensorUnit := sorry
--   associator := sorry
--   leftUnitor := sorry
--   rightUnitor := sorry

section Coalgebra

namespace CoalgHom

variable (A B C D : Type) [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddCommMonoid B]
  [Module R B] [Coalgebra R B] [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid D] [Module R D] [Coalgebra R D]

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

instance : FunLike (A →co[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; dsimp at h; congr;
    refine DFunLike.ext _ _ fun _ ↦ ?_
    exact congr_fun h _

instance funLike : FunLike (A →co[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

@[simps!]
def id : A →co[R] A where
  __ := LinearMap.id (R := R) (M := A)
  toFun x := x
  comul_comp' := by
    ext x ; simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R:= R) (x:A)
    rw [hx, map_sum] ; simp
  comul_counit' := rfl

variable {R A B C} in
def comp (g : B →co[R] C) (f : A →co[R] B)  : A →co[R] C :=
  {
    __ := g.toLinearMap.comp f.toLinearMap
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
      rw [LinearMap.ext_iff.1 g.comul_counit' (f.toLinearMap x)]
      rw [← LinearMap.comp_apply]
      apply LinearMap.ext_iff.1 f.comul_counit' x
  }

lemma comp_id (f : A →co[R] B) : comp f (id R A) = f := rfl

lemma id_comp (f : A →co[R] B) : comp (id R B) f = f := rfl

end CoalgHom

section Bialgebra

variable (A B C : Type) [Ring A] [Ring B] [Ring C] [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

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

instance funLike : FunLike (A →bi[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

instance algHomClass : AlgHomClass (A →bi[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

@[simps!]
def id : A →bi[R] A where
  __ := CoalgHom.id R A
  __ := AlgHom.id R A
  toFun x := x

variable {R A B C} in
def comp (g : B →bi[R] C) (f : A →bi[R] B)  : A →bi[R] C :=
  {
    __ := g.toAlgHom.comp f.toAlgHom
    __ := CoalgHom.comp g.toCoalgHom f.toCoalgHom
  }

lemma comp_id (f : A →bi[R] B) : comp f (id R A) = f := rfl

lemma id_comp (f : A →bi[R] B) : (id R B).comp f = f := rfl

end BialgHom

structure CoalgEquiv (R : Type) (C : Type) (D : Type) [CommRing R] [Ring C] [Ring D]
  [Module R C] [Module R D] [Coalgebra R C] [Coalgebra R D] extends C →co[R] D, C ≃ₗ[R] D

notation:50 A " ≃co[" R "] " A' => CoalgEquiv R A A'

namespace CoalgEquiv

instance : EquivLike (A ≃co[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨⟨f,_⟩,_⟩,_,_⟩,_⟩ := f
    obtain ⟨⟨⟨⟨g,_⟩,_⟩,_,_⟩,_⟩ := g
    congr

def Simps.apply (e : A ≃co[R] B) : A → B :=
  e

instance : FunLike (A ≃co[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

@[ext]
theorem ext {f g : A ≃co[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : A ≃co[R] A :=
{ LinearEquiv.refl R A,
  CoalgHom.id  R A with }

lemma apply_symm_apply (e : A ≃ₗ[R] B) : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
  LinearMap.ext fun x => by simp

lemma comul_eq_invinv_comul_e (e : A ≃co[R] B) : Coalgebra.comul =
    (TensorProduct.map e.toLinearEquiv.symm e.toLinearEquiv.symm.toLinearMap) ∘ₗ
    Coalgebra.comul ∘ₗ e.toLinearMap := by
    calc
      Coalgebra.comul = (TensorProduct.map LinearMap.id LinearMap.id) ∘ₗ Coalgebra.comul := by
          ext x ; simp
      _ = (TensorProduct.map (e.toLinearEquiv.symm.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
            (e.toLinearEquiv.symm.toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)) ∘ₗ Coalgebra.comul:= by
          rw [apply_symm_apply]
      _ = (TensorProduct.map e.toLinearEquiv.symm.toLinearMap e.toLinearEquiv.symm.toLinearMap) ∘ₗ
            (TensorProduct.map e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap) ∘ₗ
            Coalgebra.comul := by
          rw [TensorProduct.map_comp]; rfl
      _ = (TensorProduct.map e.toLinearEquiv.symm.toLinearMap e.toLinearEquiv.symm.toLinearMap) ∘ₗ
            Coalgebra.comul ∘ₗ e.toLinearMap := by
          rw [← CoalgHom.CoalgHom.comul_comp']

@[symm]
def symm (e : A ≃co[R] B) : B ≃co[R] A :=
  {
    e.toLinearEquiv.symm with
  map_smul' := by simp
  comul_comp' := by
    have eq0 : Coalgebra.comul ∘ₗ e.toLinearEquiv.symm.toLinearMap =
        (TensorProduct.map e.toLinearEquiv.symm.toLinearMap e.toLinearEquiv.symm.toLinearMap) ∘ₗ
        Coalgebra.comul ∘ₗ e.toLinearMap ∘ₗ e.toLinearEquiv.symm.toLinearMap := by
      rw [comul_eq_invinv_comul_e (e := e)]
      rfl
    ext x
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AlgEquiv.coe_mk,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    change TensorProduct.map e.toLinearEquiv.symm.toLinearMap e.toLinearEquiv.symm.toLinearMap _ = _
    replace eq0 := congr($eq0 x)
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_mk] at eq0
    rw [eq0]
    congr
    exact e.4 x |>.symm
  comul_counit' := by
    have eq0 : (Coalgebra.counit ∘ₗ e.toLinearMap) ∘ₗ e.toLinearEquiv.symm.toLinearMap =
        Coalgebra.counit ∘ₗ e.toLinearEquiv.symm.toLinearMap := by rw [e.comul_counit']
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
  }

@[trans]
def trans (e₁ : A ≃co[R] B) (e₂ : B ≃co[R] C) : A ≃co[R] C :=
  {
    e₁.toLinearEquiv.trans e₂.toLinearEquiv with
  map_smul' := by simp
  comul_comp' := (CoalgHom.comp e₂.toCoalgHom e₁.toCoalgHom).comul_comp'
  comul_counit' := (CoalgHom.comp e₂.toCoalgHom e₁.toCoalgHom).comul_counit'
  }

end CoalgEquiv

structure BialgEquiv (R : Type) (A : Type) (B : Type) [CommRing R] [Ring A] [Ring B]
  [Bialgebra R A] [Bialgebra R B] extends A ≃co[R] B, A ≃ₐ[R] B

notation:50 A " ≃bi[" R "] " A' => BialgEquiv R A A'

namespace BialgEquiv
instance : EquivLike (A ≃bi[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    obtain ⟨⟨⟨⟨⟨f,_⟩,_⟩,_,_⟩,_⟩,_⟩:= f
    obtain ⟨⟨⟨⟨g,_⟩,_⟩,_,_⟩,_⟩ := g
    congr

instance : AlgEquivClass (BialgEquiv R A B) R A B where
  map_mul := fun f => f.toAlgEquiv.map_mul
  map_add := fun f => f.toAlgEquiv.map_add
  commutes := fun f => f.toAlgEquiv.commutes

def Simps.apply (e : A ≃bi[R] B) : A → B :=
  e

def Simps.toEquiv (e : A ≃ₐ[R] B) : A ≃ B :=
  e

instance : FunLike (A ≃bi[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

@[ext]
theorem ext {f g : A ≃bi[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : A ≃bi[R] A :=
{
    AlgEquiv.refl,
    BialgHom.id  R A with
}

@[symm]
def symm (e : A ≃bi[R] B) : B ≃bi[R] A :=
{
    e.toAlgEquiv.symm,
    e.toCoalgEquiv.symm with
}

@[trans]
def trans (e₁ : A ≃bi[R] B) (e₂ : B ≃bi[R] C) : A ≃bi[R] C :=
  {
    e₁.toAlgEquiv.trans e₂.toAlgEquiv,
    CoalgEquiv.trans (e₁ := e₁.toCoalgEquiv) (e₂ := e₂.toCoalgEquiv) with
  }

end BialgEquiv

end Bialgebra


section Hopf

variable (H : Type)[CommRing H][HopfAlgebra R H]
variable (H1 H2 : Type)[CommRing H1][CommRing H2][HopfAlgebra R H1][HopfAlgebra R H2]

noncomputable section HopfEquivScheme

open AlgebraicGeometry Opposite
open CategoryTheory
open scoped TensorProduct
open HopfAlgebra
open Coalgebra
def spec := AffineScheme.Spec.obj (op (CommRingCat.of R))

structure HopfAlgCat where
  carrier : Type 0
  [isCommRing : CommRing carrier]
  [isHopfAlgebra : HopfAlgebra R carrier]

attribute [instance]  HopfAlgCat.isHopfAlgebra HopfAlgCat.isCommRing

namespace HopfAlgCat

instance : CoeSort (HopfAlgCat R) Type := ⟨HopfAlgCat.carrier⟩

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
      map_add := by simp only [map_add, forall_const]
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

def of (H : Type) [CommRing H] [HopfAlgebra R H] : HopfAlgCat R where
   carrier := H

@[simps!]
noncomputable abbrev tensorObj (A B : HopfAlgCat R) : HopfAlgCat R := of R (A ⊗[R] B)

variable {X₁ X₂ : Type}

@[simps!]
def toHopfAlgebraIso {g₁ : CommRing X₁} {g₂ : CommRing X₂} {m₁ : HopfAlgebra R X₁} {m₂ : HopfAlgebra R X₂}
    (e : X₁ ≃bi[R] X₂) : HopfAlgCat.of R X₁ ≅ HopfAlgCat.of R X₂ where
  hom := sorry--(e : X₁ →hopf[R] X₂)
  inv := sorry--(e.symm : X₂ →ₐ[R] X₁)
  hom_inv_id := sorry--by ext x; exact e.left_inv x
  inv_hom_id := sorry --by ext x; exact e.right_inv x

variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing D] [HopfAlgebra R A] 
    [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R D] 

--我们差HopfAlgebra.TensorProduct.assoc，我们还要证明tensor of hopf是hopf， 回到了coalg
def map (f : A →bi[R] B) (g : C →bi[R] D) : A ⊗[R] C →bi[R] B ⊗[R] D := sorry --TensorProduct.map (R:=R) (M:=A) (N:=C) (P:=B) (Q:= D) f.toLinearMap g.toLinearMap
noncomputable abbrev tensorHom {W X Y Z : HopfAlgCat R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj R W Y ⟶ tensorObj R X Z :=
  HopfAlgCat.map R W X Y Z f g
  
instance : MonoidalCategoryStruct (HopfAlgCat R) where
  tensorObj := tensorObj R
  whiskerLeft X _ _ f :=  tensorHom R (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom R f (𝟙 Y)
  tensorHom := tensorHom R
  tensorUnit := of R R
  associator X Y Z := sorry--(HopfAlgebra.TensorProduct.assoc R X Y Z).toHopfAlgebraIso
  leftUnitor := sorry--(HopfAlgebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor := sorry--(HopfAlgebra.TensorProduct.rid R R X).toAlgebraIso

--下面这里在尝试用algebra推hopf
@[ext]
theorem ext {f g : H1 →bi[R] H2} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h
instance: ConcreteCategory (HopfAlgCat R) where
  forget :=
    { obj := fun M => M
      map := fun f => f.toFun }
  forget_faithful := ⟨fun h => HopfAlgCat.ext _ _ _ (by intros x; dsimp at h; exact congrFun h x)⟩

instance{S : HopfAlgCat R}: Semiring ((forget (HopfAlgCat R)).obj S) := by sorry
instance {S : HopfAlgCat R} : HopfAlgebra R ((forget (HopfAlgCat R)).obj S) := by sorry
instance HasForgettoAlg : HasForget₂ (HopfAlgCat R) (AlgebraCat R) where
  forget₂ := { obj := sorry --fun A => AlgebraCat.of R A --by exact fun (A : HopfAlgCat R) => AlgebraCat.of R A.carrier
               map := sorry --fun A => A.toLinearMap
              }
  -- forget₂ := { obj := sorry --fun A => AlgebraCat.of R A --by exact fun (A : HopfAlgCat R) => AlgebraCat.of R A.carrier
  --              map := sorry --fun A => A.toLinearMap
  --             }
noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlgCat R) :=
  Monoidal.induced
  (forget₂ (HopfAlgCat R) (AlgebraCat R))
    { μIso := fun X Y => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_module_obj, forget₂_map_associator_hom]
        simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, MonoidalCategory.tensor_id]
        erw [Category.id_comp, Category.comp_id, MonoidalCategory.tensor_id, Category.id_comp]
      leftUnitor_eq := fun X => by
        dsimp only [forget₂_module_obj, forget₂_module_map, Iso.refl_symm, Iso.trans_hom,
          Iso.refl_hom, tensorIso_hom]
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        rfl
      rightUnitor_eq := fun X => by
        dsimp
        erw [Category.id_comp, MonoidalCategory.tensor_id, Category.id_comp]
        exact congr_arg LinearEquiv.toLinearMap <|
          TensorProduct.AlgebraTensorModule.rid_eq_rid R X }

--这下面是原版
instance : MonoidalCategory (HopfAlgCat R) where
  tensorHom_def := sorry
  tensor_id := sorry
  tensor_comp := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry
-- abbrev HopfMon := sorry
-- structure Grp_ extends Mon_

  -- (inferInstance : Algebra R S.carrier)

-- instance : MonoidalCategoryStruct (HopfAlgCat R) := {
--   tensorObj := λ A B, of R (A ⊗[R] B),
--   whiskerLeft := λ A B C f, HopfAlgCat.map R f (𝟙 C),
--   whiskerRight := λ A B C f, HopfAlgCat.map R (𝟙 A) f,
--   tensorUnit := of R R,
--   associator := λ A B C, HopfAlgCat.map R (tensor_assoc_hom R A B C),
--   leftUnitor := λ A, HopfAlgCat.map R (tensor_unit_left_hom R A),
--   rightUnitor := λ A, HopfAlgCat.map R (tensor_unit_right_hom R A)

-- }
end HopfAlgCat

end HopfEquivScheme

end Hopf
