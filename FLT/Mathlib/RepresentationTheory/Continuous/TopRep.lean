/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RepresentationTheory.Rep.Basic
public import FLT.Mathlib.RepresentationTheory.Continuous.Basic

/-!
# The internal hom of topological representations

Material destined for `Mathlib.RepresentationTheory.Continuous.TopRep`.
-/

@[expose] public section

universe u v

open ContinuousLinearMap.CompactOpen

namespace TopRep

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

/-- The internal hom of two topological representations: the topological representation on the
space of continuous linear maps `A →L[k] B`, with `G` acting by conjugation. -/
abbrev iHom (A B : TopRep k G) : TopRep k G := TopRep.of (ContRepresentation.linHom A.ρ B.ρ)

/-- A `G`-module over a discrete base ring, endowed with the discrete topology, is a continuous
`G`-module: every linear endomorphism is automatically continuous. -/
def mkDiscrete [DiscreteTopology k] (A : Rep k G) : TopRep k G :=
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
    of (X := A) <| .ofMonoidHom
      { toFun g := ⟨A.ρ g, continuous_of_discreteTopology⟩
        map_one' := by ext x; simp
        map_mul' g h := by ext x; simp }

@[simp]
lemma mkDiscrete_ρ_apply [DiscreteTopology k] (A : Rep k G) (g : G) (x : A) :
    (mkDiscrete A).ρ g x = A.ρ g x := rfl

end TopRep
