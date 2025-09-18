import Mathlib

-- scrath file where I work on iso₁_cont_extracted in max(?) generality

variable (R S : Type*) [Ring R] [Ring S] [TopologicalSpace R] [TopologicalSpace S]
variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]

instance : TopologicalSpace M :=
  moduleTopology R M

instance : TopologicalSpace N :=
  moduleTopology S N

instance : TopologicalSpace (Prod M N) :=
  instTopologicalSpaceProd

instance : Module (Prod R S) (Prod M N) := by

  sorry

lemma add_cont : ContinuousAdd (Prod M N) := by
  refine { continuous_add := ?_ }
  refine { isOpen_preimage := ?_}

  sorry

lemma smul_cont : ContinuousSMul (Prod R S) (Prod M N) := by

  sorry

--- this will be the final goal
lemma hmm : IsModuleTopology (Prod R S) (Prod M N) := by
  have := add_cont M N
  have := smul_cont R S M N
  refine IsModuleTopology.of_continuous_id ?_

  sorry
