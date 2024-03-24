import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Coalgebra
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.Proj3.HopfAlgCat.CoalgHom

open TensorProduct BigOperators
universe u
variable {R :Type u}[CommRing R]

structure CoalgEquiv (R : Type u) (A : Type u) (B : Type u) [CommRing R] [Ring A] [Ring B]
  [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B] extends A →co[R] B, A ≃ₗ[R] B

notation:50 A " ≃co[" R "] " A' => CoalgEquiv R A A'


namespace CoalgEquiv
variable {A B C: Type u} [Ring A] [Ring B] [Ring C] [Module R A] [Module R B] [Module R C]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra R C]

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
{
  LinearEquiv.refl R A,
  CoalgHom.id  with
}

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
          rw [← CoalgHom.comul_comp']

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
    symm
    exact e.right_inv x
  counit_comp' := by
    have eq0 : (Coalgebra.counit ∘ₗ e.toLinearMap) ∘ₗ e.toLinearEquiv.symm.toLinearMap =
        Coalgebra.counit ∘ₗ e.toLinearEquiv.symm.toLinearMap := by rw [e.counit_comp']
    ext x
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, AlgEquiv.coe_mk,
      LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    replace eq0 := congr($eq0 x)
    simp only [AlgEquiv.symm_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_mk] at eq0
    rw [eq0.symm]
    congr
    exact e.right_inv x
  }

@[trans]
def trans (e₁ : A ≃co[R] B) (e₂ : B ≃co[R] C) : A ≃co[R] C :=
  {
    e₁.toLinearEquiv.trans e₂.toLinearEquiv with
  map_smul' := by simp
  comul_comp' := (CoalgHom.comp e₂.toCoalgHom e₁.toCoalgHom).comul_comp'
  counit_comp' := (CoalgHom.comp e₂.toCoalgHom e₁.toCoalgHom).counit_comp'
  }

end CoalgEquiv
