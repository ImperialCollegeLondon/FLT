import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Monoid

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [ContinuousMul G]
-- TODO: `ContinuousMulConst` would be enough but it doesn't exist, and `ContinuousConstSMul Gᵐᵒᵖ G`
-- should work but doesn't

section induced

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

open Topology

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
@[to_additive]
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

@[to_additive]
theorem induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _ := by
  convert (IsInducing.induced h).continuousMul h

end induced
