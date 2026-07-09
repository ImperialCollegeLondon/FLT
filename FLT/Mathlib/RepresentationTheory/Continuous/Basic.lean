/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import FLT.Mathlib.Topology.Algebra.Module.CompactOpen
public import FLT.Mathlib.Topology.Constructions

/-!
# The internal hom of continuous representations

This file constructs `ContRepresentation.linHom ρ2 ρ3`, the continuous representation of `G` on
`M2 →L[k] M3` by conjugation, `g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the
topology induced from the compact-open topology on `C(M2, M3)`.

Material destined for `Mathlib.RepresentationTheory.Continuous.Basic`.
-/

@[expose] public section

universe u v w

open ContinuousLinearMap.CompactOpen

namespace ContRepresentation

variable {k : Type u} {G : Type v} [CommRing k] [TopologicalSpace k] [Group G]

section LinHom

variable {M2 M3 : Type w}
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3] (ρ2 : ContRepresentation k G M2) (ρ3 : ContRepresentation k G M3)

/-- The continuous representation of `G` on `M2 →L[k] M3` by conjugation,
`g • φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹`, where `M2 →L[k] M3` carries the topology induced from the
compact-open topology on `C(M2, M3)`. -/
def linHom : ContRepresentation k G (M2 →L[k] M3) where
  toMonoidHom.toFun g := {
    toFun f := ρ3 g ∘L f ∘L ρ2 g⁻¹
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := by
      refine continuous_induced_rng.2 ?_
      change Continuous fun f : M2 →L[k] M3 ↦
        (ρ3 g : C(M3, M3)).comp ((⟨f.toFun, f.cont⟩ : C(M2, M3)).comp (ρ2 g⁻¹ : C(M2, M2)))
      exact ((ρ3 g : C(M3, M3)).continuous_postcomp).comp
        (((ρ2 g⁻¹ : C(M2, M2)).continuous_precomp).comp continuous_induced_dom) }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' g₁ g₂ := by ext; simp

@[simp]
lemma linHom_apply (g : G) (φ : M2 →L[k] M3) :
    linHom ρ2 ρ3 g φ = ρ3 g ∘L φ ∘L ρ2 g⁻¹ := rfl

end LinHom

section DiscretePairing

variable {M1 M2 M3 : Type w}
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]
  [AddCommGroup M3] [Module k M3] [TopologicalSpace M3] [IsTopologicalAddGroup M3]
  [ContinuousSMul k M3]
  {ρ1 : ContRepresentation k G M1} {ρ2 : ContRepresentation k G M2}
  {ρ3 : ContRepresentation k G M3}

/-- When the source module of an intertwining map into an internal hom is discrete, its
uncurried pairing is automatically jointly continuous. -/
lemma continuous_pair_of_discrete [DiscreteTopology M1] (f : ρ1 →ⁱL linHom ρ2 ρ3) :
    Continuous fun p : M2 × M1 ↦ f p.2 p.1 :=
  continuous_of_discreteTopology_snd fun v ↦ (f v).continuous

end DiscretePairing

end ContRepresentation
