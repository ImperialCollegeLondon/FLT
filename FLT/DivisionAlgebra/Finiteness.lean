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
import FLT.NumberField.AdeleRing
import Mathlib.GroupTheory.DoubleCoset

/-

# Fujisaki's lemma

We prove a lemma which Voight (in his quaternion algebra book) attributes to Fujisaki:
if `D` is a finite-dimensional division algebra over a number field `K`
and if `U ⊆ (𝔸_K^infty ⊗[K] D)ˣ` is a compact open subgroup then the double coset
space `Dˣ \ (𝔸_F^infty ⊗[K] D)ˣ / U` is finite.

-/

suppress_compilation

open DedekindDomain

open scoped NumberField TensorProduct

variable (K : Type*) [Field K] [NumberField K]
variable (D : Type*) [DivisionRing D] [Algebra K D]

local instance : TopologicalSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] D) :=
  actionTopology (FiniteAdeleRing (𝓞 K) K) _
local instance : IsActionTopology (FiniteAdeleRing (𝓞 K) K) ((FiniteAdeleRing (𝓞 K) K) ⊗[K] D) :=
  ⟨rfl⟩

variable [FiniteDimensional K D]

instance : TopologicalRing ((FiniteAdeleRing (𝓞 K) K) ⊗[K] D) :=
  ActionTopology.Module.topologicalRing (FiniteAdeleRing (𝓞 K) K) _

variable [Algebra.IsCentral K D]

abbrev Dfx := ((FiniteAdeleRing (𝓞 K) K) ⊗[K] D)ˣ

noncomputable abbrev incl₁ : Dˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeRight.toMonoidHom

noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Dfx K D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

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
