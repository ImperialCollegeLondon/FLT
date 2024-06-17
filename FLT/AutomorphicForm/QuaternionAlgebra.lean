/-
Copyright (c) 2024 Kevin Buzzaed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib

/-

# Definiteion of automorphic forms on a totally definite quaternion algebra
-/

suppress_compilation

variable (F : Type*) [Field F] [NumberField F]

variable (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D]

#check DedekindDomain.FiniteAdeleRing

open DedekindDomain

open scoped NumberField

#check FiniteAdeleRing (𝓞 F) F

-- my work (two PRs)
instance : TopologicalSpace (FiniteAdeleRing (𝓞 F) F) := sorry
instance : TopologicalRing (FiniteAdeleRing (𝓞 F) F) := sorry

open scoped TensorProduct

#check D ⊗[F] (FiniteAdeleRing (𝓞 F) F)

-- your work
instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := sorry
instance : TopologicalRing (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := sorry

namespace TotallyDefiniteQuaternionAlgebra

-- #synth Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F)

noncomputable example : D →+* (D ⊗[F] FiniteAdeleRing (𝓞 F) F) := by exact
  Algebra.TensorProduct.includeLeftRingHom

abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ
noncomputable abbrev incl : Dˣ →* Dfx F D := Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

structure AutomorphicForm (M : Type*) [AddCommGroup M] where
  toFun : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ → M
  left_invt : ∀ (d : Dˣ) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    toFun (Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom d * x) = toFun x
  loc_cst : ∃ U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ,
    IsOpen (U : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) ∧
    ∀ (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    ∀ u ∈ U, toFun (x * u) = toFun x

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M]

variable {F D}

instance : CoeFun (AutomorphicForm F D M) (fun _ ↦ Dfx F D → M) where
  coe := toFun

attribute [coe] AutomorphicForm.toFun

@[ext]
lemma ext (φ ψ : AutomorphicForm F D M) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

def zero : (AutomorphicForm F D M) where
  toFun := 0
  left_invt := sorry
  loc_cst := sorry

instance : Zero (AutomorphicForm F D M) where
  zero := zero

@[simp]
lemma zero_apply (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (0 : AutomorphicForm F D M) x = 0 := rfl

def neg (φ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := - φ x
  left_invt := sorry
  loc_cst := sorry

instance : Neg (AutomorphicForm F D M) where
  neg := neg

@[simp, norm_cast]
lemma neg_apply (φ : AutomorphicForm F D M) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (-φ : AutomorphicForm F D M) x = -(φ x) := rfl

def add (φ ψ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := φ x + ψ x
  left_invt := sorry
  loc_cst := sorry

instance : Add (AutomorphicForm F D M) where
  add := add

@[simp, norm_cast]
lemma add_apply (φ ψ : AutomorphicForm F D M) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (φ + ψ) x = (φ x) + (ψ x) := rfl

instance addCommGroup : AddCommGroup (AutomorphicForm F D M) where
  add := (· + ·)
  add_assoc := by intros; ext; simp [add_assoc];
  zero := 0
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul := nsmulRec
  neg := (-·)
  zsmul := zsmulRec
  add_left_neg := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]

instance : MulAction (Dfx F D) (AutomorphicForm F D M) where
  smul g f := {
    toFun := fun x ↦ f (x * g)
    left_invt := sorry
    loc_cst := sorry
  }
  one_smul := sorry
  mul_smul := sorry
