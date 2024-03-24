import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Bialgebra
-- import Mathlib.RingTheory.Coalgebra
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.Proj3.CoalgHom

open TensorProduct BigOperators
universe u
set_option quotPrecheck false

section Bialgebra


namespace BialgHom
-- variable {A B C: Type u} [Ring A] [Ring B] [Ring C] [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

structure BialgHom (R : Type u) (A : Type u) (B : Type u) [CommRing R] [Ring A] [Ring B] [Module R A] [Module R B]
[Algebra R A] [Algebra R B] [Coalgebra R A] [Coalgebra R B] [Bialgebra R A] [Bialgebra R B] extends A →co[R] B, A →ₐ[R] B where

notation:25 M " →bi[" R:25 "] " M₂:0 => BialgHom R M M₂

variable {R :Type u}[CommRing R]
variable {A B C : Type u} [Ring A] [Ring B] [Ring C] [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

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
  __ := CoalgHom.id
  __ := AlgHom.id R A
  toFun x := x

def comp (g : B →bi[R] C) (f : A →bi[R] B)  : A →bi[R] C :=
  {
    __ := g.toAlgHom.comp f.toAlgHom
    __ := CoalgHom.comp g.toCoalgHom f.toCoalgHom
  }

lemma comp_id (f : A →bi[R] B) : comp f id = f := rfl

lemma id_comp (f : A →bi[R] B) : comp id f = f := rfl

end BialgHom
namespace Bialgebra.TensorProduct
variable {R :Type u}[CommRing R]
variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D] [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
noncomputable def map (f: A →bi[R] B) (g: C →bi[R] D): A ⊗[R] C →bi[R] B ⊗[R] D :=
{
  __ := Coalgebra.TensorProduct.map f.toCoalgHom g.toCoalgHom
  __ := Algebra.TensorProduct.map f.toAlgHom g.toAlgHom

}

end Bialgebra.TensorProduct
end Bialgebra
