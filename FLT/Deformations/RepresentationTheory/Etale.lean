/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import FLT.Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Equivalence between continuous `G`-finite sets and `k`-etale algebras

The bulk of this development has been moved to `FLT.Mathlib.*` (see
`FLT.Mathlib.FieldTheory.Galois.Infinite` and the files it imports). This file keeps only the
convolution monoid structure on `A →ₐ[K] L` for a bialgebra `A`, which is not yet destined for
Mathlib.
-/

@[expose] public section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

open TensorProduct

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass in
noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] : Monoid (A →ₐ[K] L) where
  mul f g := .comp (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)) (Bialgebra.comulAlgHom K A)
  mul_assoc a b c := by
    ext x
    convert congr(Algebra.TensorProduct.lift a (Algebra.TensorProduct.lift b c (fun _ _ ↦ .all _ _))
      (fun _ _ ↦ .all _ _) $(Coalgebra.coassoc_apply (R := K) x))
    · change Algebra.TensorProduct.lift _ c (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
      induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        change (Algebra.TensorProduct.lift a b (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) * _ = _
        dsimp
        induction Coalgebra.comul (R := K) x with
        | zero => simp only [map_zero, zero_mul, TensorProduct.zero_tmul]
        | add x y _ _ => simp only [map_add, add_mul, TensorProduct.add_tmul, *]
        | tmul x z => exact mul_assoc _ _ _
    · change Algebra.TensorProduct.lift a _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
      induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y => rfl
  one := (Algebra.ofId K L).comp (Bialgebra.counitAlgHom K A)
  one_mul f := by
    ext x
    change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
    convert congr(Algebra.TensorProduct.lift (Algebra.ofId K L)
      f (fun _ _ ↦ .all _ _) $(Coalgebra.rTensor_counit_comul (R := K) x))
    · induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        simp only [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul]
        rfl
    · simp
  mul_one f := by
    ext x
    change Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x) = _
    convert congr(Algebra.TensorProduct.lift f (Algebra.ofId K L) (fun _ _ ↦ .all _ _)
      $(Coalgebra.lTensor_counit_comul (R := K) x))
    · induction Coalgebra.comul (R := K) x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul x y =>
        simp only [Algebra.TensorProduct.lift_tmul]
        rfl
    · simp

noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] :
    MulDistribMulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul_mul r f g := by
    ext x
    change r (Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)) =
      Algebra.TensorProduct.lift _ _ (fun _ _ ↦ .all _ _) (Coalgebra.comul x)
    induction Coalgebra.comul (R := K) x with
    | zero => simp only [map_zero]
    | add x y _ _ => simp only [map_add, *]
    | tmul x y => simp; rfl
  smul_one r := by
    ext x
    change r (algebraMap _ _ _) = _
    simp
    rfl
