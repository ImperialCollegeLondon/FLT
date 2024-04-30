import FLT.for_mathlib.Coalgebra.Sweedler
import FLT.for_mathlib.Coalgebra.TensorProduct
import FLT.for_mathlib.HopfAlgebra.Basic
import FLT.Proj3.HopfAlgCat.CoalgEquiv
import FLT.Proj3.HopfAlgCat.BialgEquiv
universe u
variable (R :Type u)[CommRing R]

open CategoryTheory AlgebraicGeometry Opposite
open BigOperators

noncomputable section HopfEquivScheme

open AlgebraicGeometry Opposite
open CategoryTheory
open scoped TensorProduct
open HopfAlgebra
open Coalgebra
-- def spec := AffineScheme.Spec.obj (op (CommRingCat.of R))

structure HopfAlgCat where
  carrier : (Type u)
  [isCommRing : CommRing carrier]
  [isHopfAlgebra : HopfAlgebra R carrier]

attribute [instance]  HopfAlgCat.isHopfAlgebra HopfAlgCat.isCommRing

namespace HopfAlgCat

variable (H : Type u)[CommRing H][HopfAlgebra R H]
variable (H1 H2 : Type u)[CommRing H1][CommRing H2][HopfAlgebra R H1][HopfAlgebra R H2]

instance : CoeSort (HopfAlgCat R) (Type u) := ⟨HopfAlgCat.carrier⟩

attribute [coe] HopfAlgCat.carrier
--The antipode of a tensor product of Hopf algebras is the tensor product of the antipodes
abbrev ten_anti := TensorProduct.map (antipode (R := R) (A := H1)) (antipode (R := R) (A := H2))

-- Here we define the expansion of comul in H1 in sweedler notation as the sum of pure
-- tensor products of two elements in H1, where each of them got from mapping H1 ⊗[R] H1
-- elements to H1.
-- That is, comul h1 = ∑ h11 i ⊗ₜ h12 i, i ∈ H1 ⊗[R] H1, h11 h12 : H1 ⊗[R] H1 → H1
-- With this, we can use the property "S ⋆ id = id ⋆ S = η ∘ₗ ε", to get the decomposition
-- given below
-- S ⋆ id (h1) = m ∘ₗ (antipode ⊗[R] id) ∘ₗ Δ (h1)
-- = m ∘ₗ (antipode ⊗[R] id) ∘ₗ ∑ h11 i ⊗ₜ h12 i
-- = ∑ m ∘ₗ (antipode (h11 i) ⊗ₜ h12 i) = ∑ antipode (h11 i) * h12 i = η ∘ₗ ε (h1) = h1
lemma antipode_decomp (I1: Finset (H1 ⊗[R] H1)) (h11 h12 : H1 ⊗[R] H1 → H1) (h1 : H1)
  (h01: Coalgebra.comul h1 = ∑ i in I1, h11 i ⊗ₜ[R] h12 i) :
  ∑ a in I1, antipode (R := R) (h11 a) * h12 a =  (1 : LinearPoint R H1 H1) h1 := by
  symm
  rw [← antipode_mul_id (R:= R) (A:= H1), LinearPoint.mul_repr antipode LinearMap.id h1 I1 _ _ h01]
  simp only [LinearMap.comp_apply, h01, map_sum, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.mul'_apply]

--another way to decomp, as you know that "S ⋆ id = id ⋆ S = η ∘ₗ ε"
lemma antipode_decomp' (I1: Finset (H1 ⊗[R] H1)) (h11 h12 : H1 ⊗[R] H1 → H1) (h1 : H1)
  (h01: Coalgebra.comul h1 = ∑ i in I1, h11 i ⊗ₜ[R] h12 i) :
  ∑ a in I1, h11 a * antipode (R := R) (h12 a) = (1 : LinearPoint R H1 H1) h1 := by
  symm
  rw [← id_mul_antipode (R:= R) (A:= H1), LinearPoint.mul_repr LinearMap.id antipode h1 I1 _ _ h01]
  simp only [LinearMap.comp_apply, h01, map_sum, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.mul'_apply]

-- We aim to prove that the tensor product of two Hopf algebras is a Hopf algebra.
-- First we need to prove "mul_antipode_rTensor_comul", an antipode axiom of Hopf Algebra
-- Here it needs to an AddMonoidHom, for later using "map_sum" to simplify the sum of tensor products
instance : AddMonoidHomClass ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2 →ₗ[R] (H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2)
  ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2) ((H1 ⊗[R] H2) ⊗[R] H1 ⊗[R] H2) where
      map_add := by simp only [map_add, forall_const]
      map_zero := fun f ↦ LinearMap.map_zero f

--Proving "mul_antipode_rTensor_comul"
lemma anti_rTensor : LinearMap.mul' R (H1 ⊗[R] H2) ∘ₗ
    LinearMap.rTensor (H1 ⊗[R] H2) (TensorProduct.map antipode antipode) ∘ₗ Coalgebra.comul =
  Algebra.linearMap R (H1 ⊗[R] H2) ∘ₗ Coalgebra.counit := by
  ext h1 h2 ; simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
  -- exist representation of expansion of comul in H1 and H2
  obtain ⟨I1, h11, h12, h01⟩ := Coalgebra.exists_repr (R := R) (h1 : H1)
  obtain ⟨I2, h21, h22, h02⟩ := Coalgebra.exists_repr (R := R) (h2 : H2)
  rw [TensorProduct.comul_apply_repr h1 h2 I1 I2 h11 h12 h01 h21 h22 h02]
  -- got by simp
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Algebra.TensorProduct.tmul_mul_tmul] ; rw [Finset.sum_comm]
  simp_rw [← TensorProduct.sum_tmul] ; rw [antipode_decomp R H1 I1 h11 h12 h1 h01]
  simp_rw [← TensorProduct.tmul_sum] ; rw [antipode_decomp R H2 I2 h21 h22 h2 h02]
  simp only [TensorProduct.counit_def, AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul, _root_.map_mul]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]
  rw [← mul_one (Coalgebra.counit h2), mul_comm,
    ← smul_eq_mul (a := Coalgebra.counit h2) (a' := 1), ← Algebra.ofId_apply,
    Algebra.smul_mul_assoc, AlgHom.map_smul (Algebra.ofId R H1), one_mul, TensorProduct.smul_tmul,
    Algebra.smul_def (R := R) (A := H2) (Coalgebra.counit h2) (1 : H2), mul_one,
    ← Bialgebra.counitAlgHom_apply, ← Bialgebra.counitAlgHom_apply, ← AlgHom.comp_apply]
  rw [← AlgHomPoint.one_def (R := R) (A := H1) (L := H1), ← Algebra.ofId_apply, ← AlgHom.comp_apply,
    ← AlgHomPoint.one_def (R := R) (A := H2) (L := H2)] ; rfl

--Proving "mul_antipode_lTensor_comul"
lemma anti_lTensor : LinearMap.mul' R (H1 ⊗[R] H2) ∘ₗ
    LinearMap.lTensor (H1 ⊗[R] H2) (TensorProduct.map antipode antipode) ∘ₗ Coalgebra.comul =
  Algebra.linearMap R (H1 ⊗[R] H2) ∘ₗ Coalgebra.counit := by
  ext h1 h2 ; simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
    Algebra.linearMap_apply, Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨I1, h11, h12, h01⟩ := Coalgebra.exists_repr (R := R) (h1 : H1)
  obtain ⟨I2, h21, h22, h02⟩ := Coalgebra.exists_repr (R := R) (h2 : H2)
  rw [TensorProduct.comul_apply_repr h1 h2 I1 I2 h11 h12 h01 h21 h22 h02]
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Algebra.TensorProduct.tmul_mul_tmul] ; rw [Finset.sum_comm]
  simp_rw [← TensorProduct.sum_tmul] ; rw [antipode_decomp' R H1 I1 h11 h12 h1 h01]
  simp_rw [← TensorProduct.tmul_sum] ; rw [antipode_decomp' R H2 I2 h21 h22 h2 h02]
  simp only [TensorProduct.counit_def, AlgHom.toNonUnitalAlgHom_eq_coe,
    NonUnitalAlgHom.toDistribMulActionHom_eq_coe, DistribMulActionHom.coe_toLinearMap,
    NonUnitalAlgHom.coe_to_distribMulActionHom, NonUnitalAlgHom.coe_coe, AlgHom.coe_comp,
    Function.comp_apply, Algebra.TensorProduct.map_tmul, Bialgebra.counitAlgHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul, _root_.map_mul]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul]
  rw [← mul_one (Coalgebra.counit h2), mul_comm,
    ← smul_eq_mul (a := Coalgebra.counit h2) (a' := 1), ← Algebra.ofId_apply,
    Algebra.smul_mul_assoc, AlgHom.map_smul (Algebra.ofId R H1), one_mul, TensorProduct.smul_tmul,
    Algebra.smul_def (R := R) (A := H2) (Coalgebra.counit h2) (1 : H2), mul_one,
    ← Bialgebra.counitAlgHom_apply, ← Bialgebra.counitAlgHom_apply, ← AlgHom.comp_apply]
  rw [← AlgHomPoint.one_def (R := R) (A := H1) (L := H1), ← Algebra.ofId_apply, ← AlgHom.comp_apply,
    ← AlgHomPoint.one_def (R := R) (A := H2) (L := H2)] ; rfl

--Claim that the tensor product of two Hopf algebras is a Hopf algebra
instance _root_.HopfAlgebra.tensorProduct : HopfAlgebra R (H1 ⊗[R] H2) where
  __ := (inferInstance : Bialgebra R (H1 ⊗[R] H2))
  antipode := TensorProduct.map (antipode (R := R) (A := H1)) (antipode (R := R) (A := H2))
  mul_antipode_rTensor_comul := anti_rTensor R H1 H2
  mul_antipode_lTensor_comul := anti_lTensor R H1 H2

--Hopf Algebra forms a category.
--The morphisms are the bialgebra homomorphisms, which are the linear maps that preserve
--the comul, counit, and product, that introduced before
instance : Category (HopfAlgCat R) where
  Hom A B := A →bi[R] B
  id A := BialgHom.id
  comp f g := BialgHom.comp g f
  comp_id f := by simp; exact BialgHom.comp_id f
  id_comp f := by simp; exact BialgHom.id_comp f
  assoc f g h := by simp only; exact rfl

--define basic structure of HopfAlgCat
def of (H : Type u) [CommRing H] [HopfAlgebra R H] : HopfAlgCat R where
   carrier := H

end HopfAlgCat
