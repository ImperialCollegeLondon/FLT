/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Algebra.Group.Basic

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

/--
`ContinuousSMulDiscrete G M` means that the action `G × M → M` is continuous
when `M` is given the discrete topology (See `continuousSMulDiscrete_iff`).

This class is especially useful when `M` already has another topology and we cannot easily put the
discrete topology on it.
-/
class ContinuousSMulDiscrete (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isOpen_smul_eq (G) (x y : M) : IsOpen { g : G | g • x = y }

lemma continuousSMulDiscrete_iff [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMulDiscrete G M ↔ ContinuousSMul G M := by
  refine ⟨fun H ↦ ⟨continuous_discrete_rng.mpr fun y ↦ ?_⟩, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  · convert_to IsOpen (⋃ x, { g : G | g • x = y } ×ˢ {x})
    · ext; simp
    · exact isOpen_iUnion fun _ ↦
        .prod (ContinuousSMulDiscrete.isOpen_smul_eq _ _ _) (isOpen_discrete _)
  · exact ((isOpen_discrete {y}).preimage continuous_smul).preimage (Continuous.prodMk_left x)

instance (priority := low) [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMulDiscrete G M] : ContinuousSMul G M := by
  rwa [← continuousSMulDiscrete_iff]

lemma ContinuousSMulDiscrete.of_continuousSMul [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul G M] : ContinuousSMulDiscrete G M := by
  rwa [continuousSMulDiscrete_iff]

lemma continuousSMulDiscrete_iff_isOpen_stabilizer {G M : Type*} [TopologicalSpace G]
    [Group G] [ContinuousMul G] [MulAction G M] :
    ContinuousSMulDiscrete G M ↔ ∀ x : M, IsOpen (MulAction.stabilizer G x : Set G) := by
  refine ⟨fun H x ↦ ContinuousSMulDiscrete.isOpen_smul_eq _ _ _, fun H ↦ ⟨fun x y ↦ ?_⟩⟩
  obtain h | ⟨g, rfl⟩ := Set.eq_empty_or_nonempty {g : G | g • x = y}
  · exact h ▸ isOpen_empty
  · convert (H x).preimage (Homeomorph.mulLeft g⁻¹).continuous using 1
    ext g'
    simp [mul_smul, inv_smul_eq_iff]

lemma ContinuousSMulDiscrete.isOpen_stabilizer (G : Type*) {M : Type*} [TopologicalSpace G]
    [Group G] [MulAction G M] [ContinuousSMulDiscrete G M] (x : M) :
      IsOpen (MulAction.stabilizer G x : Set G) := ContinuousSMulDiscrete.isOpen_smul_eq _ _ _
