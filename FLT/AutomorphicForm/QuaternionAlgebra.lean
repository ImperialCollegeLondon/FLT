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

#check Units.map

#synth Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F)

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

variable (M : Type*) [AddCommGroup M]

instance : CoeFun (AutomorphicForm F D M) (fun _ ↦ Dfx F D → M) where
  coe := toFun

instance zero : (AutomorphicForm F D M) where
  toFun := 0
  left_invt := sorry
  loc_cst := sorry


instance  neg (φ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := - φ x
  left_invt := sorry
  loc_cst := sorry

-- instance add

-- instance : AddCommGroup

instance : MulAction (Dfx F D) (AutomorphicForm F D M) where
  smul := sorry -- (g • f) (x) := f(xg) -- x(gf)=(xg)f
  one_smul := sorry
  mul_smul := sorry

-- if M is an R-module (e.g. if M = R!), then Automorphic forms are also an R-module
-- with the action being 0on the coefficients.
