/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ludwig Monnerjahn, Hannah Scholz
-/
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Algebra.Group.Subgroup.Pointwise
import FLT.ForMathlib.ActionTopology

/-

# Definition of automorphic forms on a totally definite quaternion algebra

-/

suppress_compilation

variable (F : Type*) [Field F] [NumberField F]

variable (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D]

open DedekindDomain

open scoped NumberField

open scoped TensorProduct

section missing_instances

variable {R D A : Type*} [CommRing R] [Ring D] [CommRing A] [Algebra R D] [Algebra R A]

#synth Algebra A (A ⊗[R] D)
-- does this make a diamond?
instance : Algebra A (D ⊗[R] A) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra' (by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    intro a b
    apply TensorProduct.induction_on (motive := fun b ↦ 1 ⊗ₜ[R] a * b = b * 1 ⊗ₜ[R] a)
    · simp only [mul_zero, zero_mul]
    · intro d a'
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [NonUnitalCommSemiring.mul_comm]
    · intro x y hx hy
      rw [left_distrib, hx, hy, right_distrib]
    )

instance [Module.Finite R D] : Module.Finite A (D ⊗[R] A) := sorry
instance [Module.Free R D]  : Module.Free A (D ⊗[R] A) := sorry

-- #synth Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F)

end missing_instances

instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := actionTopology (FiniteAdeleRing (𝓞 F) F) _
instance : IsActionTopology (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := ⟨rfl⟩
instance : TopologicalRing (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :=
  -- this def would be a dangerous instance
  -- (it can't guess R) but it's just a Prop so we can easily add it here
  ActionTopology.Module.topologicalRing (FiniteAdeleRing (𝓞 F) F) _

namespace TotallyDefiniteQuaternionAlgebra

noncomputable example : D →+* (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
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
theorem ext (φ ψ : AutomorphicForm F D M) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

def zero : (AutomorphicForm F D M) where
  toFun := 0
  left_invt := by simp
  loc_cst := by use ⊤; simp

instance : Zero (AutomorphicForm F D M) where
  zero := zero

@[simp]
theorem zero_apply (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
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
theorem neg_apply (φ : AutomorphicForm F D M) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
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
theorem add_apply (φ ψ : AutomorphicForm F D M) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
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
  neg_add_cancel := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]

open ConjAct
open scoped Pointwise

theorem conjAct_mem {G: Type*}  [Group G] (U: Subgroup G) (g: G) (x : G):
  x ∈ toConjAct g • U ↔ ∃ u ∈ U, g * u * g⁻¹ = x := by rfl

theorem toConjAct_open {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (g : G) : IsOpen (toConjAct g • U : Set G) := by
  have this1 := continuous_mul_left g⁻¹
  have this2 := continuous_mul_right g
  rw [continuous_def] at this1 this2
  specialize this2 U hU
  specialize this1 _ this2
  convert this1 using 1
  ext x
  convert conjAct_mem _ _ _ using 1
  simp only [Set.mem_preimage, SetLike.mem_coe]
  refine ⟨?_, ?_⟩ <;> intro h
  · use g⁻¹ * x * g -- duh
    simp [h]
    group
  · rcases h with ⟨u, hu, rfl⟩
    group
    exact hu

instance : SMul (Dfx F D) (AutomorphicForm F D M) where
  smul g φ :=   { -- (g • f) (x) := f(xg) -- x(gf)=(xg)f
    toFun := fun x => φ (x * g)
    left_invt := by
      intros d x
      simp only [← φ.left_invt d x, mul_assoc]
      exact φ.left_invt d (x * g)
    loc_cst := by
      rcases φ.loc_cst with ⟨U, openU, hU⟩
      use toConjAct g • U
      constructor
      · apply toConjAct_open _ openU
      · intros x u umem
        simp only
        rw[conjAct_mem] at umem
        obtain ⟨ugu, hugu, eq⟩ := umem
        rw[←eq, ←mul_assoc, ←mul_assoc, inv_mul_cancel_right, hU (x*g) ugu hugu]
  }

@[simp]
theorem sMul_eval (g : Dfx F D) (f : AutomorphicForm F D M) (x : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) :
  (g • f) x = f (x * g) := rfl

instance : MulAction (Dfx F D) (AutomorphicForm F D M) where
  smul := (· • ·)
  one_smul := by intros; ext; simp only [sMul_eval, mul_one]
  mul_smul := by intros; ext; simp only [sMul_eval, mul_assoc]
