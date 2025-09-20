import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Monoid.Defs

open MulOpposite Set Units in
lemma embedProduct_preimageOf (L : Type*) [Monoid L] : (range ⇑(embedProduct L)) =
    {x : L × Lᵐᵒᵖ | x.1 * unop x.2 = 1 ∧ unop x.2 * x.1 = 1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · rintro h
    exact ⟨⟨x.1, unop x.2, h.1, h.2⟩, rfl⟩

lemma embedProduct_closed (L : Type*) [Monoid L] [TopologicalSpace L] [ContinuousMul L] [T1Space L]
    : IsClosed (Set.range ⇑(Units.embedProduct L)) := by
  rw [embedProduct_preimageOf]
  exact .inter (.preimage (by fun_prop) isClosed_singleton)
    (.preimage (by fun_prop) isClosed_singleton)
