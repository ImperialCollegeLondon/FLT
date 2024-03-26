import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Coalgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.Proj3.HopfAlgCat.BialgHom
import FLT.Proj3.HopfAlgCat.CoalgEquiv

open TensorProduct BigOperators
universe u
variable {R :Type u}[CommRing R]

structure BialgEquiv (R : Type u) (A : Type u) (B : Type u)
  [CommRing R] [Ring A] [Ring B]
  [Bialgebra R A] [Bialgebra R B] extends A ≃co[R] B, A ≃ₐ[R] B where

notation:50 A " ≃bi[" R "] " A' => BialgEquiv R A A'

namespace BialgEquiv
variable (A : Type u) (B : Type u) (C : Type u)
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

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

def toBialgHom (e : A ≃bi[R] B) : A →bi[R] B :=
  {
      e.toAlgEquiv.toAlgHom,
      e.toCoalgEquiv.toCoalgHom with
  }

instance : FunLike (A ≃bi[R] B) A B where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective'

@[ext]
theorem ext {f g : A ≃bi[R] B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : A ≃bi[R] A :=
{
  __ := AlgEquiv.refl
  __ := CoalgEquiv.refl
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


def toBiAlgHom (e : A ≃bi[R] B) : A →bi[R] B := e.toBialgHom
def toBialgEquiv (e : A ≃bi[R] B) : B ≃bi[R] A := symm A B e

end BialgEquiv

namespace Bialgebra.TensorProduct

variable (A : Type u) (B : Type u) (C : Type u)
  [CommRing R] [Ring A] [Ring B] [Ring C]
  [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

open Coalgebra in
noncomputable def comm : A ⊗[R] B ≃bi[R] B ⊗[R] A where
  __ := Algebra.TensorProduct.comm R A B
  __ := _root_.TensorProduct.comm R A B
  comul_comp' := by
    ext x y
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Algebra.TensorProduct.comm_tmul]
    obtain ⟨Ix, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) x
    obtain ⟨Iy, y1, y2, hy⟩ := Coalgebra.exists_repr (R := R) y
    have comul_xy' : comul (x ⊗ₜ y) = ∑ i in Ix, ∑ j in Iy, (x1 i ⊗ₜ y1 j) ⊗ₜ[R] (x2 i ⊗ₜ y2 j) :=
      TensorProduct.comul_apply_repr (a := x) (b := y) (repr_a := hx) (repr_b := hy)
    have comul_yx' : comul (y ⊗ₜ x) = ∑ j in Iy, ∑ i in Ix, (y1 j ⊗ₜ x1 i) ⊗ₜ[R] (y2 j ⊗ₜ x2 i) :=
      TensorProduct.comul_apply_repr (a := y) (b := x) (repr_a := hy) (repr_b := hx)
    simpa only [comul_xy', map_sum, map_tmul, LinearMap.coe_mk, AddHom.coe_mk,
      Algebra.TensorProduct.comm_tmul, comul_yx'] using Finset.sum_comm
  counit_comp' := by
    ext x y
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
      Function.comp_apply, Algebra.TensorProduct.comm_tmul]
    rw[Coalgebra.TensorProduct.counit_def, Coalgebra.TensorProduct.counit_def]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lid_tmul, smul_eq_mul]
    rw [mul_comm]
end Bialgebra.TensorProduct
