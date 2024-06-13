/-
Copyright (c) 2024 Kevin Buzzaed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer, Mario Carneiro
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.FdRep
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Matrix
import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.BaseChange

suppress_compilation

/-!

# The Global Langlands Conjectures for GL(n) over the rationals.

## First sub-goal: definition of an automorphic form.

I've made the design decision of working with the functor
`Matrix.GeneralLinearGroup (Fin n)` as our implementation
of the `GL_n` functor. There's notation `GL (Fin n)` for this.

-/

open scoped Manifold

namespace DedekindDomain

open scoped algebraMap

section PRs

open IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

local notation "K_hat" => ProdAdicCompletions
local notation "R_hat" => FiniteIntegralAdeles

section PR13705

namespace ProdAdicCompletions.IsFiniteAdele

open IsDedekindDomain.HeightOneSpectrum

@[simp]
lemma mem_FiniteAdeleRing (x : K_hat R K) : x ∈ (
    { carrier := {x : K_hat R K | x.IsFiniteAdele}
      mul_mem' := mul
      one_mem' := one
      add_mem' := add
      zero_mem' := zero
      algebraMap_mem' := algebraMap'
    } : Subalgebra K (K_hat R K)) ↔ {v | x v ∉ adicCompletionIntegers K v}.Finite := Iff.rfl

open Set

/-- The finite adele ring is an algebra over the finite integral adeles. -/
noncomputable instance : Algebra (R_hat R K) (FiniteAdeleRing R K) where
  smul rhat fadele := ⟨fun v ↦ rhat v * fadele.1 v, by
    have this := fadele.2
    rw [mem_FiniteAdeleRing] at this ⊢
    apply Finite.subset this (fun v hv ↦ ?_)
    rw [mem_setOf_eq, mem_adicCompletionIntegers] at hv ⊢
    contrapose! hv
    sorry -- works in the PR, don't worry about this
    ⟩
  toFun r := ⟨r, by sorry⟩ -- works in the PR!
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ _ := mul_comm _ _
  smul_def' r x := rfl

end ProdAdicCompletions.IsFiniteAdele -- namespace

end PR13705 -- section

section PR13703

open scoped nonZeroDivisors

noncomputable instance : Algebra R (FiniteAdeleRing R K) :=
  RingHom.toAlgebra ((algebraMap K (FiniteAdeleRing R K)).comp (algebraMap R K))

lemma FiniteAdeleRing.clear_denominator (a : FiniteAdeleRing R K) :
    ∃ (b : R⁰) (c : R_hat R K), a * (b : R) = c := by
  sorry -- there's a nearly-done mathlib PR which proves this

#check Classical.choose (v.valuation_exists_uniformizer K)

-- These instances are sorry-free in the PR.
instance : TopologicalSpace (FiniteAdeleRing ℤ ℚ) := sorry


instance instTopologicalRingFiniteAdeleRing : TopologicalRing (FiniteAdeleRing ℤ ℚ) := sorry

end PR13703

end PRs  -- section

end DedekindDomain

namespace AutomorphicForm

open DedekindDomain
namespace GLn

open Manifold

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- this makes

-- variable (n : ℕ) in
-- #synth LieGroup 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ)

--work

open Matrix

variable (n : ℕ)
variable (G : Type) [TopologicalSpace G] [Group G]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H]
  [ChartedSpace H G]
  (I : ModelWithCorners ℝ E H)
  [LieGroup I G]

def action :
    LeftInvariantDerivation I G →ₗ⁅ℝ⁆ (Module.End ℝ C^∞⟮I, G; ℝ⟯) where
  toFun l := Derivation.toLinearMap l
  map_add' := by simp
  map_smul' := by simp
  map_lie' {x y} := rfl

open scoped TensorProduct

def LieModuleHom.baseChange
    (A : Type*) {R L M N : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (f : M →ₗ⁅R, L⁆ N) : A ⊗[R] M →ₗ⁅A, A ⊗[R] L⁆ A ⊗[R] N where
      __ := (LinearMap.baseChange A f : A ⊗[R] M →ₗ[A] A ⊗[R] N)
      map_lie' := by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
        intro x m
        induction x using TensorProduct.induction_on
        · simp only [zero_lie, map_zero]
        · induction m using TensorProduct.induction_on <;> simp_all
        · simp_all only [add_lie, map_add]

def LieHom.baseChange
    (A : Type*) {R L L' : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L' := by
  sorry

def actionTensorC :
    ℂ ⊗[ℝ] LeftInvariantDerivation I G →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] (Module.End ℝ C^∞⟮I, G; ℝ⟯)) :=
  LieHom.baseChange _ (action _ _)

section
variable (R : Type*) (L : Type*)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable {A : Type*} [Ring A] [Algebra R A] (f : L →ₗ⁅R⁆ A)
variable {A' : Type*} [LieRing A'] [LieAlgebra R A']

def lift' (e : A' ≃ₗ[R] A) (h : ∀ x y, e ⁅x, y⁆ = e x * e y - e y * e x) :
    (L →ₗ⁅R⁆ A') ≃ (UniversalEnvelopingAlgebra R L →ₐ[R] A) := by
  refine Equiv.trans ?_ (UniversalEnvelopingAlgebra.lift _)
  sorry
end

def actionTensorCAlg :
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation I G) →ₐ[ℂ]
    ℂ ⊗[ℝ] (Module.End ℝ C^∞⟮I, G; 𝓘(ℝ, ℝ), ℝ⟯) :=
  have := lift' ℂ
    (ℂ ⊗[ℝ] LeftInvariantDerivation I G)
    (A' := ℂ ⊗[ℝ] (C^∞⟮I, G; ℝ⟯ →ₗ[ℝ] C^∞⟮I, G; ℝ⟯))
    (A := ℂ ⊗[ℝ] (C^∞⟮I, G; ℝ⟯ →ₗ[ℝ] C^∞⟮I, G; ℝ⟯))
    (.refl _ _)
    (fun x y => sorry)
  this (actionTensorC G I)

def actionTensorCAlg' :
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation I G) →ₐ[ℂ]
    Module.End ℂ (ℂ ⊗[ℝ] C^∞⟮I, G; 𝓘(ℝ, ℝ), ℝ⟯) :=
  (LinearMap.tensorProductEnd ..).comp (actionTensorCAlg G I)

def actionTensorCAlg'2 :
  Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation I G)) →ₐ[ℂ]
    Module.End ℂ (ℂ ⊗[ℝ] C^∞⟮I, G; 𝓘(ℝ, ℝ), ℝ⟯) :=
  (actionTensorCAlg' G I).comp (SubalgebraClass.val _)

instance : Module ℝ C^∞⟮I, G; 𝓘(ℝ, ℝ), ℝ⟯ := inferInstance
instance : Module ℂ C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯ := sorry

def actionTensorCAlg'3 :
  Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation I G)) →ₐ[ℂ]
    Module.End ℂ (C^∞⟮I, G; 𝓘(ℝ, ℂ), ℂ⟯) := sorry


-- algebra needs to be done
-- Step 1: tensor up to ℂ
-- Step 2: induced action of univ env alg
-- Step 3: induced action of centre

variable {n : ℕ}
structure IsSmooth (f :
    (GL (Fin n) (FiniteAdeleRing ℤ ℚ)) ×
    (GL (Fin n) ℝ)
    → ℂ) : Prop where
  continuous : Continuous f
  loc_cst (y : GL (Fin n) ℝ) :
    IsLocallyConstant (fun x ↦ f (x, y))
  smooth (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    Smooth 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) 𝓘(ℝ, ℂ) (fun y ↦ f (x, y))

variable {n : ℕ}

open Matrix

noncomputable abbrev s (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (M * M.transpose).trace + (M⁻¹ * M⁻¹.transpose).trace

structure IsSlowlyIncreasing (f : GeneralLinearGroup (Fin n) ℝ → ℂ) : Prop where
  bounded_by : ∃ (C : ℝ) (N : ℕ),
    ∀ (M : GeneralLinearGroup (Fin n) ℝ),
    ‖f M‖ ≤ C * (s (M : Matrix (Fin n) (Fin n) ℝ)) ^ N

--
#check Matrix.orthogonalGroup (Fin n) ℝ

structure preweight (n : ℕ) where
  d : ℕ -- dimension
  rho : orthogonalGroup (Fin n) ℝ →* GeneralLinearGroup (Fin d) ℂ
  rho_continuous: Continuous rho

open CategoryTheory

noncomputable def preweight.fdRep (n : ℕ) (w : preweight n) :
    FdRep ℂ (orthogonalGroup (Fin n) ℝ) where
  V := FGModuleCat.of ℂ (Fin w.d → ℂ)
  ρ := {
    toFun := fun A ↦ {
      toFun := fun x ↦ (w.rho A).1 *ᵥ x
      map_add' := fun _ _ ↦ Matrix.mulVec_add _ _ _
      map_smul' := fun _ _ ↦ by simpa using Matrix.mulVec_smul _ _ _ }
    map_one' := by aesop
    map_mul' := fun _ _ ↦ by
      simp only [obj_carrier, MonCat.mul_of, _root_.map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
  }

structure Weight (n : ℕ) where
  w : preweight n
  isSimple : Simple w.fdRep

-- This will be useful
def _root_.RingHom.GL {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
  (m : Type*) [Fintype m] [DecidableEq m] :
  GL m A →* GL m B := Units.map <| (RingHom.mapMatrix φ).toMonoidHom

structure IsConstantOn (U : Subgroup (GL (Fin n) (FiniteAdeleRing ℤ ℚ)))
  (f : (GL (Fin n) (FiniteAdeleRing ℤ ℚ)) × (GL (Fin n) ℝ) → ℂ) : Prop where
  is_open : IsOpen U.carrier
  is_compact : IsCompact U.carrier
  finite_level (u : U.carrier) (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) (y : GL (Fin n) ℝ) :
    f (x * u, y) = f (x, y)

def annihilator {R} [CommSemiring R]
  {M} [AddCommMonoid M] [Module R M]
  {N} [AddCommMonoid N] [Module R N]
  {P} [AddCommMonoid P] [Module R P]
  (action : M →ₗ[R] (N →ₗ[R] P)) (a : N) : Submodule R M :=
  { carrier := { x | action x a = 0 }
    add_mem' := sorry
    zero_mem' := sorry
    smul_mem' := sorry }

/-- Automorphic forms for GL_n/Q with weight ρ. -/
structure AutomorphicFormForGLnOverQ (n : ℕ) (ρ : Weight n) where
  toFun : (GL (Fin n) (FiniteAdeleRing ℤ ℚ)) ×
      (GL (Fin n) ℝ) → ℂ
  is_smooth : IsSmooth toFun
  is_periodic : ∀ (g : GL (Fin n) ℚ) (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) (y : GL (Fin n) ℝ),
    toFun (RingHom.GL (algebraMap _ _) _ g * x, RingHom.GL (algebraMap _ _) _ g * y) = toFun (x, y)
  is_slowly_increasing (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    IsSlowlyIncreasing (fun y ↦ toFun (x, y))
  has_finite_level: ∃ U, IsConstantOn U toFun
  is_finite_cod (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    FiniteDimensional ℂ (_ ⧸ annihilator
      (actionTensorCAlg'3 (GL (Fin n) ℝ) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)).toLinearMap
      ⟨fun y ↦ toFun (x, y), is_smooth.smooth x⟩)
  -- missing: infinite part has a weight

namespace AutomorphicFormForGLnOverQ

-- not entirely sure what I'm doing here. Is it as simple as this?
-- attribute [coe] toFun
variable (n : ℕ) (ρ : Weight n) in
instance : CoeFun (AutomorphicFormForGLnOverQ n ρ) (fun _ ↦ (GL (Fin n) (FiniteAdeleRing ℤ ℚ)) ×
      (GL (Fin n) ℝ) → ℂ) :=
  ⟨toFun⟩

end AutomorphicFormForGLnOverQ

end GLn

end AutomorphicForm
