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
import FLT.NumberField.IsTotallyReal
import Mathlib.GroupTheory.DoubleCoset

/-

# Fujisaki's lemma

We prove a lemma which Voight (in his quaternion algebra book) attributes to Fujisaki:
if `D` is a finite-dimensional division algebra over a number field `K`
and if `U ⊆ (D ⊗[K] 𝔸_K^infty)ˣ` is a compact open subgroup then the double coset
space `Dˣ \ (D ⊗ 𝔸_F^infty)ˣ / U` is finite.

-/

suppress_compilation

open DedekindDomain

open scoped NumberField TensorProduct

section missing_instances

variable {R D A : Type*} [CommSemiring R] [Semiring D] [CommSemiring A] [Algebra R D] [Algebra R A]

-- Algebra.TensorProduct.rightAlgebra has unnecessary commutativity assumptions
-- This should be fixed in mathlib; ideally it should be an exact mirror of leftAlgebra but
-- I ignore S as I don't need it.
def Algebra.TensorProduct.rightAlgebra' : Algebra A (D ⊗[R] A) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra' (by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    intro a b
    apply TensorProduct.induction_on (motive := fun b ↦ 1 ⊗ₜ[R] a * b = b * 1 ⊗ₜ[R] a)
    · simp only [mul_zero, zero_mul]
    · intro d a'
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        NonUnitalCommSemiring.mul_comm]
    · intro x y hx hy
      rw [left_distrib, hx, hy, right_distrib]
    )

-- this makes a diamond for Algebra A (A ⊗[R] A) which will never happen here
attribute [local instance] Algebra.TensorProduct.rightAlgebra'

-- These seem to be missing
instance [Module.Finite R D] : Module.Finite A (D ⊗[R] A) := sorry
instance [Module.Free R D]  : Module.Free A (D ⊗[R] A) := sorry

end missing_instances

attribute [local instance] Algebra.TensorProduct.rightAlgebra'

variable (K : Type*) [Field K] [NumberField K]
variable (D : Type*) [DivisionRing D] [Algebra K D]

local instance : TopologicalSpace (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  actionTopology (FiniteAdeleRing (𝓞 K) K) _
local instance : IsActionTopology (FiniteAdeleRing (𝓞 K) K) (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  ⟨rfl⟩

variable [FiniteDimensional K D]

instance : TopologicalRing (D ⊗[K] (FiniteAdeleRing (𝓞 K) K)) :=
  ActionTopology.Module.topologicalRing (FiniteAdeleRing (𝓞 K) K) _

variable [Algebra.IsCentral K D]

abbrev Dfx := (D ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ

noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.rightAlgebra'.toMonoidHom

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If `D` is a finite-dimensional division algebra over a number field `K`
then the double coset space `Dˣ \ (D ⊗ 𝔸_K^infty)ˣ / U` is finite for any compact open subgroup `U`
of `(D ⊗ 𝔸_F^infty)ˣ`.
-/
theorem DivisionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx K D)} (hU : IsOpen (U : Set (Dfx K D))) :
    Finite (Doset.Quotient (Set.range (incl₁ K D)) U) :=
  sorry
