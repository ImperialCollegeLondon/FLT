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
if `D` is a totally definite quaternion algebra over a totally real number field `F`
and if U ⊆ (D ⊗ 𝔸_F^infty)ˣ is a compact open subgroup then the double coset
space Dˣ \ (D ⊗ 𝔸_F^infty)ˣ / U is finite.

-/

suppress_compilation

variable (F : Type*) [Field F] [NumberField F]

-- should be a quaternion algebra but all the definitions below make sense (and are
-- meaningless, but we're stuck with this cultural choice) in far more generality
variable (D : Type*) [Ring D] [Algebra F D]

open DedekindDomain

open scoped NumberField

open scoped TensorProduct

section missing_instances

variable {R D A : Type*} [CommRing R] [Ring D] [CommRing A] [Algebra R D] [Algebra R A]

-- #synth Algebra A (A ⊗[R] D) -- Algebra.TensorProduct.leftAlgebra

-- Algebra.TensorProduct.rightAlgebra has unnecessary commutativity assumptions
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
instance [Module.Finite R D] : Module.Finite A (D ⊗[R] A) := sorry
instance [Module.Free R D]  : Module.Free A (D ⊗[R] A) := sorry

end missing_instances

attribute [local instance] Algebra.TensorProduct.rightAlgebra'

instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := actionTopology (FiniteAdeleRing (𝓞 F) F) _
instance : IsActionTopology (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) := ⟨rfl⟩

  -- the below def would be a dangerous instance in general I would imagine
  -- (it can't guess which topological ring this is a module over) but it's just a Prop
  -- so we can easily add it here
variable [FiniteDimensional F D]

instance : TopologicalRing (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :=
  ActionTopology.Module.topologicalRing (FiniteAdeleRing (𝓞 F) F) _

-- this should be elsewhere (and in mathlib!)
class IsCentralSimple
    (K : Type*) [Field K] (D : Type*) [Ring D] [Algebra K D] : Prop where
  is_central : Subalgebra.center K D ≤ ⊥
  [is_simple : IsSimpleOrder (TwoSidedIdeal D)]

open NumberField in
variable [IsTotallyReal F] [IsCentralSimple F D]

abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ
noncomputable abbrev incl₁ : Dˣ →* Dfx F D := Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom
noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 F) F)ˣ →* Dfx F D :=
  Units.map Algebra.TensorProduct.rightAlgebra'.toMonoidHom

-- Voight "Main theorem 27.6.14(b) (Fujisaki's lemma)"
/-!
If D is a finite-dimensional totally definite central simple algebra over a totally real number field F
then the double coset space Dˣ \ (D ⊗ 𝔸_F^infty)ˣ / U is finite for any compact open subgroup U
of (D ⊗ 𝔸_F^infty)ˣ.
-/
theorem TotallyDefiniteQuaternionAlgebra.finiteDoubleCoset
    {U : Subgroup (Dfx F D)} (hU : IsOpen (U : Set (Dfx F D))) :
    Finite (Doset.Quotient (Set.range (incl₁ F D)) U) :=
  sorry
  -- not even true in this generality, need to add the hypothesis that D is totally definite.
