import Mathlib.Algebra.Group.Prod

import Mathlib.Topology.Algebra.Constructions -- min_imports for this addition
import Mathlib.Topology.Algebra.Monoid.Defs

--- Believe this should go under embedProduct (lines 616)

variable (L : Type*) [Monoid L]

/-- Auxillary map used in `embedProduct_preimageOf`. -/
def p : Prod L Lᵐᵒᵖ → L :=
  fun p => p.1 * MulOpposite.unop p.2

/-- Auxillary map used in `embedProduct_preimageOf`. -/
def q : Prod L Lᵐᵒᵖ → L :=
  fun p => MulOpposite.unop p.2 * p.1

lemma p_cont [TopologicalSpace L] [ContinuousMul L] : Continuous (p L) :=
    Continuous.mul (continuous_fst) (Continuous.comp (MulOpposite.continuous_unop) continuous_snd)

lemma q_cont [TopologicalSpace L] [ContinuousMul L] : Continuous (q L) :=
    Continuous.mul (Continuous.comp (MulOpposite.continuous_unop) continuous_snd) (continuous_fst)

lemma embedProduct_preimageOf : (Set.range ⇑(Units.embedProduct L)) =
    Set.preimage (p L) {1} ∩ Set.preimage (q L) {1} := by
  ext x
  simp only [Set.mem_range, Units.embedProduct_apply, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, ⟨x1, x2⟩⟩
    exact ⟨by simp only [p , MulOpposite.unop_op, Units.mul_inv],
      by simp only [q, MulOpposite.unop_op, Units.inv_mul]⟩
  · rintro ⟨hp, hq⟩
    use ⟨x.1, MulOpposite.unop x.2, hp, hq⟩
    rfl

lemma embedProduct_closed [TopologicalSpace L] [ContinuousMul L] [T1Space L] :
    IsClosed (Set.range ⇑(Units.embedProduct L))
    := by
  rw [embedProduct_preimageOf]
  exact IsClosed.inter (IsClosed.preimage (p_cont L) (isClosed_singleton))
    (IsClosed.preimage (q_cont L) (isClosed_singleton))
