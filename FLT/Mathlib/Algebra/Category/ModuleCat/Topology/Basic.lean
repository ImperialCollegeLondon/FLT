/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import FLT.Mathlib.Topology.Algebra.Module.CompactOpen

/-!
# The internal hom of topological modules

This file equips the category of topological modules with an internal hom `TopModuleCat.linHom`,
the space of continuous linear maps carrying the topology induced from the compact-open topology,
together with its functoriality (`TopModuleCat.linHomMap`) and a constructor
(`TopModuleCat.homOfBilinear`) bundling a bilinear pairing with jointly continuous uncurried form
into a morphism to the internal hom.

Material destined for `Mathlib.Algebra.Category.ModuleCat.Topology.Basic`.
-/

@[expose] public section

universe u

open ContinuousLinearMap.CompactOpen

namespace TopModuleCat

variable {k : Type u} [CommRing k] [TopologicalSpace k]

/-- The internal hom of two topological modules: the space of continuous linear maps `A →L[k] B`
carrying the topology induced from the compact-open topology on `C(A, B)`. -/
abbrev linHom (M1 M2 : TopModuleCat k) : TopModuleCat k := .of k (M1 →L[k] M2)

/-- Pre- and post-composition induce a morphism between the internal homs of topological
modules. -/
def linHomMap {A A' B B' : TopModuleCat k} (a : A' ⟶ A) (b : B ⟶ B') :
    linHom A B ⟶ linHom A' B' :=
  ofHom
    { toFun φ := b.hom ∘L φ ∘L a.hom
      map_add' φ ψ := by ext x; simp
      map_smul' c φ := by ext x; simp
      cont := by
        refine continuous_induced_rng.2 ?_
        change Continuous fun φ : ↥A →L[k] ↥B ↦
          (b.hom : C(↥B, ↥B')).comp ((⟨φ, φ.cont⟩ : C(↥A, ↥B)).comp (a.hom : C(↥A', ↥A)))
        exact ((b.hom : C(↥B, ↥B')).continuous_postcomp).comp
          (((a.hom : C(↥A', ↥A)).continuous_precomp).comp continuous_induced_dom) }

@[simp]
lemma linHomMap_apply {A A' B B' : TopModuleCat k} (a : A' ⟶ A) (b : B ⟶ B')
    (φ : ↥(linHom A B)) (x : ↥A') :
    linHomMap a b φ x = b.hom (φ (a.hom x)) := rfl

/-- Bundle a bilinear pairing with jointly continuous uncurried form into a morphism to the
internal hom. Stating this for abstract topological modules keeps all instance searches on
abstract carriers. -/
def homOfBilinear {A B C : TopModuleCat k} (F : ↥A → (↥B →L[k] ↥C))
    (hadd : ∀ a a' b, F (a + a') b = F a b + F a' b)
    (hsmul : ∀ (c : k) a b, F (c • a) b = c • F a b)
    (hF : Continuous fun p : ↥A × ↥B ↦ F p.1 p.2) :
    A ⟶ linHom B C :=
  ofHom
    { toFun := F
      map_add' a a' := ContinuousLinearMap.ext fun b ↦ hadd a a' b
      map_smul' c a := ContinuousLinearMap.ext fun b ↦ hsmul c a b
      cont := continuous_induced_rng.2 (ContinuousMap.continuous_of_continuous_uncurry _ hF)
    }

@[simp]
lemma homOfBilinear_apply {A B C : TopModuleCat k} (F : ↥A → (↥B →L[k] ↥C))
    (hadd : ∀ a a' b, F (a + a') b = F a b + F a' b)
    (hsmul : ∀ (c : k) a b, F (c • a) b = c • F a b)
    (hF : Continuous fun p : ↥A × ↥B ↦ F p.1 p.2) (a : ↥A) :
    homOfBilinear F hadd hsmul hF a = F a := rfl

end TopModuleCat
