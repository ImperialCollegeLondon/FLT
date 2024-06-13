/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.HIMExperiments.module_topology
--import Mathlib

/-

# Definition of automorphic forms on a totally definite quaternion algebra
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

section missing_instances

variable {R D A : Type*} [CommRing R] [Ring D] [CommRing A] [Algebra R D] [Algebra R A]

--TODO:
instance : Algebra A (D ⊗[R] A) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra' (by
    sorry
    )

instance [Module.Finite R D]  : Module.Finite A (D ⊗[R] A) := sorry

instance [Module.Free R D]  : Module.Free A (D ⊗[R] A) := sorry

#check Group


end missing_instances
-- your work
instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := Module.topology (FiniteAdeleRing (𝓞 F) F)
instance : TopologicalRing (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := moobar (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))

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
  left_invt := by simp
  loc_cst := by use ⊤; simp

instance  neg (φ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := - φ x
  left_invt := by
    intro d x
    simp only [RingHom.toMonoidHom_eq_coe, neg_inj]
    exact φ.left_invt d x
  loc_cst := by
    rcases φ.loc_cst with ⟨U, openU, hU⟩
    use U
    exact ⟨openU, fun x u umem ↦ by rw [neg_inj]; exact hU x u umem⟩

instance add (φ ψ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := φ x + ψ x
  left_invt := by
    intro d x
    simp only [← φ.left_invt d x, ← ψ.left_invt d x]
  loc_cst := by
    rcases φ.loc_cst with ⟨U, openU, hU⟩
    rcases ψ.loc_cst with ⟨V, openV, hV⟩
    use U ⊓ V
    constructor
    · unfold Subgroup.instInf Submonoid.instInf
      simp only [Subgroup.coe_toSubmonoid, Subgroup.coe_set_mk]
      exact IsOpen.inter openU openV
    · intro x u ⟨umemU, umemV⟩
      simp only
      rw [hU x u umemU, hV x u umemV]


-- instance : AddCommGroup

instance : MulAction (Dfx F D) (AutomorphicForm F D M) where
  smul := sorry -- (g • f) (x) := f(xg) -- x(gf)=(xg)f
  one_smul := sorry
  mul_smul := sorry

-- if M is an R-module (e.g. if M = R!), then Automorphic forms are also an R-module
-- with the action being 0on the coefficients.
