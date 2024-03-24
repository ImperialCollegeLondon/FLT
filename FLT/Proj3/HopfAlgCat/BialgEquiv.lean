import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Coalgebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.Proj3.HopfAlgCat.CoalgHom
import FLT.Proj3.HopfAlgCat.BialgHom
import FLT.Proj3.HopfAlgCat.CoalgEquiv

open TensorProduct BigOperators
universe u
variable {R :Type u}[CommRing R]

structure BialgEquiv (R : Type u) (A : Type u) (B : Type u) [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Bialgebra R A] [Bialgebra R B] extends A ≃co[R] B, A ≃ₐ[R] B where

notation:50 A " ≃bi[" R "] " A' => BialgEquiv R A A'

namespace BialgEquiv
variable (A : Type u) (B : Type u) (C : Type u) [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Coalgebra R A] [Coalgebra R B] [Coalgebra R C]
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
def toBialgEquiv (e : A ≃bi[R] B) : B ≃bi[R] A := by exact symm A B e

end BialgEquiv
