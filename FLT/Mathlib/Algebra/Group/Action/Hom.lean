/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Action.Hom

/-!
# Algebra structures on equivariant homs
-/

@[expose] public section

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [MulAction G Y]
    [SMul H Y] [SMulCommClass G H Y] :
    SMul H (X →[G] Y) where
  smul h f := ⟨h • f, by simp [smul_comm _ h]⟩

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring H] [Algebra H Y] [SMulCommClass G H Y] :
    Algebra H (X →[G] Y) where
  algebraMap :=
  { toFun h := ⟨fun _ ↦ algebraMap H Y h, by simp⟩
    map_one' := by ext; simp; rfl
    map_mul' _ _ := by ext; simp; rfl
    map_zero' := by ext; simp; rfl
    map_add' _ _ := by ext; simp; rfl }
  commutes' _ _ := MulActionHom.ext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := MulActionHom.ext fun _ ↦ Algebra.smul_def _ _

/-- Composing `MulActionHom` on the left as an `AlgHom`. -/
def MulActionHom.compLeftAlgHom (G R Y : Type*) {X X' : Type*}
    [Monoid G] [MulAction G X] [MulAction G X'] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring R] [Algebra R Y] [SMulCommClass G R Y] (f : X →[G] X') :
    (X' →[G] Y) →ₐ[R] (X →[G] Y) where
  toFun := (·.comp f)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The coercion from `MulActionHom` to functions as an `AlgHom`. -/
def MulActionHom.toFunAlgHom
    {G H X Y : Type*} [Monoid G] [MulAction G X] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring H] [Algebra H Y] [SMulCommClass G H Y] :
    (X →[G] Y) →ₐ[H] (X → Y) where
  toFun f := f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

instance {R S T G : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Monoid G] [MulSemiringAction G T] [SMulCommClass G R T] : MulAction G (S →ₐ[R] T) where
  smul g := (MulSemiringAction.toAlgHom _ _ g).comp
  one_smul f := by ext x; exact one_smul G (f x)
  mul_smul g g' f := by ext x; exact mul_smul g g' (f x)

/-- Evaluating a `MulActionHom` is an `AlgHom`, bundled as a `MulActionHom`. -/
def MulActionHom.evalAlgHom (G R X Y : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [MulAction G X] [MulSemiringAction G Y] [SMulCommClass G R Y] :
    X →[G] ((X →[G] Y) →ₐ[R] Y) where
  toFun x := (Pi.evalAlgHom _ _ x).comp MulActionHom.toFunAlgHom
  map_smul' σ x := by ext f; exact f.map_smul σ x

@[simp]
lemma MulActionHom.evalAlgHom_apply {G R X Y : Type*} [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [MulAction G X] [MulSemiringAction G Y] [SMulCommClass G R Y] (x f) :
    evalAlgHom G R X Y x f = f x := rfl

/-- Evaluating a `AlgHom` is an `MulActionHom`, bundled as a `AlgHom`. -/
def AlgHom.evalMulActionHom (G R A Y : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [Semiring A] [Algebra R A] [MulSemiringAction G Y] [SMulCommClass G R Y] :
    A →ₐ[R] ((A →ₐ[R] Y) →[G] Y) where
  toFun a := ⟨fun f ↦ f a, fun g f ↦ rfl⟩
  map_one' := by ext f; exact map_one f
  map_mul' a b := by ext f; exact map_mul f a b
  map_zero' := by ext f; exact map_zero f
  map_add' a b := by ext f; exact map_add f a b
  commutes' r := by ext f; exact f.commutes r
