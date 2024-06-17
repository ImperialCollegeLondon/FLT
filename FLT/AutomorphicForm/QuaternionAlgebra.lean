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
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    intro a b
    apply TensorProduct.induction_on (motive := fun b ↦ 1 ⊗ₜ[R] a * b = b * 1 ⊗ₜ[R] a)
    . simp only [mul_zero, zero_mul]
    . intro d a'
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [NonUnitalCommSemiring.mul_comm]
    . intro x y hx hy
      rw [left_distrib, hx, hy, right_distrib]
    )



instance [Module.Finite R D] : Module.Finite A (D ⊗[R] A) := sorry

instance [Module.Free R D]  : Module.Free A (D ⊗[R] A) := sorry

-- #synth Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F)

end missing_instances
-- your work
instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := Module.topology (FiniteAdeleRing (𝓞 F) F)
instance : TopologicalRing (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := moobar (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))

namespace TotallyDefiniteQuaternionAlgebra

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
  left_invt := by simp
  loc_cst := by use ⊤; simp

instance : Zero (AutomorphicForm F D M) where
  zero := zero

@[simp]
lemma zero_apply (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (0 : AutomorphicForm F D M) x = 0 := rfl

def neg (φ : AutomorphicForm F D M) : AutomorphicForm F D M where
  toFun x := - φ x
  left_invt := by
    intro d x
    simp only [RingHom.toMonoidHom_eq_coe, neg_inj]
    exact φ.left_invt d x
  loc_cst := by
    rcases φ.loc_cst with ⟨U, openU, hU⟩
    use U
    exact ⟨openU, fun x u umem ↦ by rw [neg_inj]; exact hU x u umem⟩

instance : Neg (AutomorphicForm F D M) where
  neg := neg

@[simp, norm_cast]
lemma neg_apply (φ : AutomorphicForm F D M) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (-φ : AutomorphicForm F D M) x = -(φ x) := rfl

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
  smul g φ :=   {
    toFun := fun x => φ (x * g)
    left_invt := by
      intros d x
      simp only [← φ.left_invt d x, mul_assoc]
      exact φ.left_invt d (x * g)
    loc_cst := by
      rcases φ.loc_cst with ⟨U, openU, hU⟩
      use U
      constructor
      · exact openU
      · intros x u umem
        simp only
        sorry
  } -- (g • f) (x) := f(xg) -- x(gf)=(xg)f
  one_smul := by intros; simp only [instHSMul, mul_one]
  mul_smul := by intros; ext; simp only [instHSMul, mk.injEq, mul_assoc]
-- if M is an R-module (e.g. if M = R!), then Automorphic forms are also an R-module
-- with the action being 0on the coefficients.

example(a b c :ℝ ): a * b * c = (a * b) * c := rfl
