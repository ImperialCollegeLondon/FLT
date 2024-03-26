import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Coalgebra
import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct

open TensorProduct BigOperators
universe u

variable {R :Type u}[CommRing R]

structure CoalgHom (R : Type u) (A : Type u) (B : Type u) [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B] [Coalgebra R A]
 [Coalgebra R B] extends LinearMap (RingHom.id R) A B  where
  comul_comp' :
    ((TensorProduct.map toLinearMap toLinearMap).comp (Coalgebra.comul (R := R) (A := A))) =
    ((Coalgebra.comul (R := R) (A := B)).comp (toLinearMap))
  counit_comp' :
    (Coalgebra.counit (A := B)) ∘ₗ toLinearMap = Coalgebra.counit (A:=A)

notation:25 M " →co[" R:25 "] " M₂ => CoalgHom R M M₂

namespace CoalgHom
variable {R :Type u}[CommRing R]
variable {A B C: Type u} [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddCommMonoid B][Module R B] [Coalgebra R B] [AddCommMonoid C][Module R C] [Coalgebra R C]


instance : FunLike (A →co[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f; cases g; dsimp at h; congr; ext; exact congr_fun h _

instance : LinearMapClass (A →co[R] B) R A B where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

instance funLike : FunLike (A →co[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

noncomputable instance : Coalgebra R (A ⊗[R] B) := by infer_instance

@[simps!]
def id : A →co[R] A :=
{
    LinearMap.id (R := R) (M := A) with
  toFun := fun x => x
  map_add' := by simp
  map_smul' := by simp
  comul_comp' := by
    ext x ; simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨I1, x1, x2, hax⟩ := Coalgebra.exists_repr (R := R) (A:= A) (x : A)
    rw [hax, map_sum] ; simp
  counit_comp' := by rfl
}

@[simps!]
def comp (g : B →co[R] C) (f : A →co[R] B): A →co[R] C:=
{
    g.toLinearMap.comp f.toLinearMap with
  map_add' := by simp
  map_smul' := by simp
  comul_comp' := by
    ext x ; simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨I1, x1, x2, hx⟩ := Coalgebra.exists_repr (R := R) (x : A)
    rw [hx, map_sum]
    simp only [map_tmul, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    have : ∑ x in I1, g.toLinearMap (f.toLinearMap (x1 x)) ⊗ₜ[R]
          g.toLinearMap (f.toLinearMap (x2 x)) =
          (TensorProduct.map g.toLinearMap g.toLinearMap).comp
          (TensorProduct.map f.toLinearMap f.toLinearMap) (∑ x in I1, (x1 x ⊗ₜ[R] x2 x)) := by
      simp only [map_sum, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul]
    rw [this, ← hx]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← g.comul_comp']
    rw [← LinearMap.comp_apply, LinearMap.comp_assoc f.toLinearMap Coalgebra.comul
        (TensorProduct.map g.toLinearMap g.toLinearMap)]
    rw [← f.comul_comp']
    simp
  counit_comp' := by
    ext x ; simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    rw [← LinearMap.comp_apply]
    rw [LinearMap.ext_iff.1 g.counit_comp' (f.toLinearMap x)]
    rw [← LinearMap.comp_apply]
    apply LinearMap.ext_iff.1 f.counit_comp' x
}

lemma comp_id (f : A →co[R] B) : comp f id = f := by rfl

lemma id_comp (f : A →co[R] B) : comp id f = f := by rfl

end CoalgHom

namespace Coalgebra.TensorProduct


variable {A B C D: Type u} [AddCommMonoid A] [Module R A] [Coalgebra R A] [AddCommMonoid B][Module R B] [Coalgebra R B]
[AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid D][Module R D] [Coalgebra R D]

lemma apply_repr (f : A →co[R] B) (a : A) {ιA : Type u}
    (sA : Finset ιA) (xA yA : ιA → A) (repr_a : comul a = ∑ i in sA, xA i ⊗ₜ[R] yA i) :
    comul (f a) = ∑ i in sA, f.toLinearMap (xA i) ⊗ₜ[R] f.toLinearMap (yA i) := by
  simpa [repr_a] using congr($(f.comul_comp') a).symm

lemma comul_apply_coalgeHom_tensor (f : A →co[R] B) (g : C →co[R] D)
    (a : A) (c : C) {ιA ιC: Type u}
    (sA : Finset ιA) (sC : Finset ιC) (xA yA : ιA → A) (repr_a : comul a = ∑ i in sA, xA i ⊗ₜ[R] yA i)
    (xC yC : ιC → C) (repr_c : comul c = ∑ i in sC, xC i ⊗ₜ[R] yC i) :
  comul (f a ⊗ₜ[R] g c) =
  ∑ i in sA, ∑ j in sC,
    (f (xA i) ⊗ₜ[R] g (xC j)) ⊗ₜ[R]
    (f (yA i) ⊗ₜ[R] g (yC j)) := by
  have eq0 := apply_repr f a sA xA yA repr_a
  have eq1 := apply_repr g c sC xC yC repr_c
  exact TensorProduct.comul_apply_repr (repr_a := eq0) (repr_b := eq1)

noncomputable def map (f: A →co[R] B) (g: C →co[R] D): A ⊗[R] C →co[R] B ⊗[R] D :=
{
    _root_.TensorProduct.map f.toLinearMap g.toLinearMap with
  comul_comp' := by
    ext a c
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, Function.comp_apply, map_tmul]
    obtain ⟨I1, a1, a2, ha⟩ := Coalgebra.exists_repr (R := R) (a : A)
    obtain ⟨I2, c1, c2, hc⟩ := Coalgebra.exists_repr (R := R) (c : C)
    have eq0 : comul _ = ∑ i in I1, ∑ j in I2, _ :=
      comul_apply_coalgeHom_tensor (f := f) (g := g) (repr_a := ha) (repr_c := hc)
    have eq1 : comul _ = ∑ i in I1, _ :=
      TensorProduct.comul_apply_repr (repr_a := ha) (repr_b := hc)
    rw [eq1, show f.toLinearMap a = f a from rfl, show g.toLinearMap c = g c from rfl, eq0]
    simp only [map_sum]
    rfl
  counit_comp' := by
    ext x y
    rw[counit_def, counit_def]
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_tmul, lid_tmul, smul_eq_mul]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
    rw [LinearMap.ext_iff.1 f.counit_comp', LinearMap.ext_iff.1 g.counit_comp']
}

end Coalgebra.TensorProduct
