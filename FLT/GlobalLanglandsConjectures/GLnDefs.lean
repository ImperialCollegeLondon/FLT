/-
Copyright (c) 2024 Kevin Buzzaed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib
/-

# The Global Langlands Conjectures for GL(n) over a number field.

## First sub-goal: definition of an automorphic form.

-/

--open Matrix

--#check GeneralLinearGroup

open scoped Manifold

-- GL_n, basis-free version, is already a Lie group: this works:
--variable (n : ℕ) in
--#synth LieGroup 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))ˣ

-- Invertible matrix group version I don't know how to state yet:
--variable (n : ℕ) in
--#synth LieGroup sorry (Matrix.GeneralLinearGroup (Fin n) ℝ) -- don't know how to fill in the sorry

namespace DedekindDomain

--#check FiniteAdeleRing ℤ ℚ -- type
--#synth CommRing (FiniteAdeleRing ℤ ℚ) -- works
-- #synth TopologicalSpace (FiniteAdeleRing ℤ ℚ) -- fails right now

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
  sorry -- this needs doing

-- These instances are sorry-free in the PR.
instance : TopologicalSpace (FiniteAdeleRing ℤ ℚ) := sorry


instance instTopologicalRingFiniteAdeleRing : TopologicalRing (FiniteAdeleRing ℤ ℚ) := sorry

end PR13703

end PRs  -- section

-- This would be helpful for getting 13703 over the line.
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] in
@[elab_as_elim]
lemma FiniteAdeleRing.mul_induction_on {P : FiniteAdeleRing R K → Prop}
    (h0 : ∀ (a : FiniteIntegralAdeles R K), P a)
    (h1 : ∀ x y, P x → P y → P (x * y))
    (h2 : ∀ (a : FiniteAdeleRing R K) (v :IsDedekindDomain.HeightOneSpectrum R),
      ∀ w ≠ v, (a : ProdAdicCompletions R K) v ∈ v.adicCompletionIntegers K): ∀ x, P x := sorry

end DedekindDomain

namespace AutomorphicForm.GLn

open DedekindDomain

variable (n : ℕ)

structure IsSmooth (f :
    (Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing ℤ ℚ)) ×
    (Matrix.GeneralLinearGroup (Fin n) ℝ)
    → ℂ) : Prop where
  continuous : Continuous f
  loc_cst (y : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    IsLocallyConstant (fun x ↦ f (x, y))
-- I need some help to formalise the statement that it's smooth at the infinite places.
--  smooth (x : Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing ℤ ℚ)) :
--    Smooth sorry sorry (fun y ↦ f (x, y))

end AutomorphicForm.GLn
