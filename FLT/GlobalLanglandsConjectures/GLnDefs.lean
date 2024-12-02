/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer, Mario Carneiro
-/
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.FDRep
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.LocallyConstant.Basic

suppress_compilation

/-!

# The Global Langlands Conjectures for GL(n) over the rationals.

## First sub-goal: definition of an automorphic form.

I've made the design decision of working with the functor
`Matrix.GeneralLinearGroup (Fin n)` as our implementation
of the `GL_n` functor. There's notation `GL (Fin n)` for this.

-/

open scoped Manifold
/- Next line is necessary while the manifold smoothness class is not extended to `ω`.
Later, replace with `open scoped ContDiff`. -/
local notation "∞" => (⊤ : ℕ∞)

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
noncomputable instance : Algebra (R_hat R K) (FiniteAdeleRing R K) := inferInstance

end ProdAdicCompletions.IsFiniteAdele -- namespace

end PR13705 -- section

section PR13703

open scoped nonZeroDivisors

noncomputable instance foobar37 : Algebra R (FiniteAdeleRing R K) :=
  RingHom.toAlgebra ((algebraMap K (FiniteAdeleRing R K)).comp (algebraMap R K))

@[deprecated mul_nonZeroDivisor_mem_finiteIntegralAdeles (since := "2024-08-11")]
lemma FiniteAdeleRing.clear_denominator (a : FiniteAdeleRing R K) :
    ∃ (b : R⁰) (c : R_hat R K), a * (b : R) = c := by
  exact mul_nonZeroDivisor_mem_finiteIntegralAdeles a

#check Classical.choose (v.valuation_exists_uniformizer K)

-- These instances are sorry-free in the PR.
instance : TopologicalSpace (FiniteAdeleRing ℤ ℚ) := sorry


instance instTopologicalRingFiniteAdeleRing : TopologicalRing (FiniteAdeleRing ℤ ℚ) := sorry

end PR13703

end PRs  -- section

section

@[simps!]
def bracketBilin (R L M) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] :
    L →ₗ[R] M →ₗ[R] M :=
  LinearMap.mk₂ _ (Bracket.bracket)
    add_lie smul_lie lie_add lie_smul

attribute [ext] Bracket

open scoped TensorProduct

noncomputable instance instLieAlgebra'
  (S R A L : Type*) [CommRing S] [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
    [Algebra S A] [SMulCommClass R S A] :
    LieAlgebra S (A ⊗[R] L) where
  lie_smul a x y := by
    induction x using TensorProduct.induction_on generalizing y
    · simp
    · induction y using TensorProduct.induction_on
      · simp
      · simp [TensorProduct.smul_tmul']
      · simp_all
    · simp_all [add_lie]

variable (R A L M B : Type*)
variable [CommRing R] [CommRing A] [Ring B] [Algebra R A] [Algebra R B]

theorem diamond_fix :
    LieAlgebra.ExtendScalars.instBracketTensorProduct R A B B = Ring.instBracket := by
  ext x y
  conv_lhs => rw [← @bracketBilin_apply_apply R _ _ _ _]
  rw [← @bracketBilin_apply_apply R _ _ _ (_) (.ofAssociativeAlgebra) _ _ (_) (_) x y]
  rotate_left
  exact @lieAlgebraSelfModule ..
  refine LinearMap.congr_fun₂ ?_ x y
  ext xa xb ya yb
  change @Bracket.bracket _ _ _ (xa ⊗ₜ[R] xb) (ya ⊗ₜ[R] yb) = _
  dsimp [Ring.lie_def]
  rw [TensorProduct.tmul_sub, mul_comm]

end

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
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) G]

def action :
    LeftInvariantDerivation 𝓘(ℝ, E) G →ₗ⁅ℝ⁆ (Module.End ℝ C^∞⟮𝓘(ℝ, E), G; ℝ⟯) where
  toFun l := Derivation.toLinearMap l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

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
    (f : L →ₗ⁅R⁆ L') : A ⊗[R] L →ₗ⁅A⁆ A ⊗[R] L' where
  __ := (LinearMap.baseChange A f : A ⊗[R] L →ₗ[A] A ⊗[R] L')
  map_lie' := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    intro x m
    induction x using TensorProduct.induction_on
    · simp only [zero_lie, map_zero]
    · induction m using TensorProduct.induction_on <;> simp_all
    · simp_all only [add_lie, map_add]

def actionTensorC :
    ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] (Module.End ℝ C^∞⟮𝓘(ℝ, E), G; ℝ⟯)) :=
  LieHom.baseChange _ (action _ _)

def actionTensorCAlg :
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G) →ₐ[ℂ]
    ℂ ⊗[ℝ] (Module.End ℝ C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℝ), ℝ⟯) := by
  have := actionTensorC G E; revert this
  convert ⇑(UniversalEnvelopingAlgebra.lift ℂ
    (L := ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G)
    (A := ℂ ⊗[ℝ] (Module.End ℝ C^∞⟮𝓘(ℝ, E), G; ℝ⟯))) using 0
  congr!
  · dsimp [LieAlgebra.ExtendScalars.instLieRing, LieRing.ofAssociativeRing]; congr
    apply diamond_fix
  · change HEq ({..} : LieAlgebra ..) (@LieAlgebra.mk _ _ _ (_) _ _); congr!

def actionTensorCAlg' :
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G) →ₐ[ℂ]
    Module.End ℂ (ℂ ⊗[ℝ] C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℝ), ℝ⟯) :=
  (LinearMap.tensorProductEnd ..).comp (actionTensorCAlg G E)

def actionTensorCAlg'2 :
  Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G)) →ₐ[ℂ]
    Module.End ℂ (ℂ ⊗[ℝ] C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℝ), ℝ⟯) :=
  (actionTensorCAlg' G E).comp (SubalgebraClass.val _)

instance : Module ℝ C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℝ), ℝ⟯ := inferInstance
instance : Module ℂ C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℂ), ℂ⟯ := sorry

def Alg := UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] LeftInvariantDerivation 𝓘(ℝ, E) G)
instance : Semiring (Alg G E) := inferInstanceAs (Semiring (UniversalEnvelopingAlgebra ..))
instance : Algebra ℂ (Alg G E) := inferInstanceAs (Algebra ℂ (UniversalEnvelopingAlgebra ..))

def Z := Subalgebra.center ℂ (Alg G E)
instance : CommSemiring (Z G E) := inferInstanceAs (CommSemiring (Subalgebra.center ..))
instance : AddCommMonoid (Z G E) := inferInstanceAs (AddCommMonoid (Subalgebra.center ..))

def actionTensorCAlg'3 : Z G E →ₐ[ℂ] Module.End ℂ C^∞⟮𝓘(ℝ, E), G; 𝓘(ℝ, ℂ), ℂ⟯ := sorry


-- algebra needs to be done
-- Step 1: tensor up to ℂ
-- Step 2: induced action of univ env alg
-- Step 3: induced action of centre

variable {n : ℕ}
structure IsSmooth (f : GL (Fin n) (FiniteAdeleRing ℤ ℚ) × GL (Fin n) ℝ → ℂ) : Prop where
  continuous : Continuous f
  loc_cst (y : GL (Fin n) ℝ) :
    IsLocallyConstant (fun x ↦ f (x, y))
  smooth (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) 𝓘(ℝ, ℂ) ∞ (fun y ↦ f (x, y))

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
    FDRep ℂ (orthogonalGroup (Fin n) ℝ) where
  V := FGModuleCat.of ℂ (Fin w.d → ℂ)
  ρ := {
    toFun := fun A ↦ {
      toFun := fun x ↦ (w.rho A).1 *ᵥ x
      map_add' := fun _ _ ↦ Matrix.mulVec_add ..
      map_smul' := fun _ _ ↦ by simpa using Matrix.mulVec_smul .. }
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
    (a : M) : Submodule R (M →ₗ[R] N) :=
  Submodule.compatibleMaps (Submodule.span R {a}) ⊥

set_option synthInstance.maxHeartbeats 40000 in
/-- Automorphic forms for GL_n/Q with weight ρ. -/
structure AutomorphicFormForGLnOverQ (n : ℕ) (ρ : Weight n) where
  toFun : GL (Fin n) (FiniteAdeleRing ℤ ℚ) × GL (Fin n) ℝ → ℂ
  is_smooth : IsSmooth toFun
  is_periodic : ∀ (g : GL (Fin n) ℚ) (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) (y : GL (Fin n) ℝ),
    toFun (RingHom.GL (algebraMap _ _) _ g * x, RingHom.GL (algebraMap _ _) _ g * y) = toFun (x, y)
  is_slowly_increasing (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    IsSlowlyIncreasing (fun y ↦ toFun (x, y))
  has_finite_level : ∃ U, IsConstantOn U toFun
  is_finite_cod (x : GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :
    haveI f : C^∞⟮𝓘(ℝ, _), _; 𝓘(ℝ, ℂ), ℂ⟯ := ⟨fun y ↦ toFun (x, y), is_smooth.smooth x⟩
    letI m := (actionTensorCAlg'3 (GL (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)).toLinearMap
    FiniteDimensional ℂ (Z (GL (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ) ⧸ (annihilator f).comap m)
  -- missing: invariance under compact open subgroup
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
