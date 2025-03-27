import Mathlib.Topology.Homeomorph.Defs

-- elsewhere
theorem Homeomorph.coinducing {A B : Type*} [τA : TopologicalSpace A]
    [τB : TopologicalSpace B] (e : A ≃ₜ B) : τB = τA.coinduced e := by
  ext U
  nth_rw 2 [isOpen_coinduced]
  exact e.isOpen_preimage.symm

theorem Homeomorph.symm_apply_eq {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] (e : M ≃ₜ N) {x : N} {y : M} :
  e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _
