import Mathlib.Topology.Constructions.SumProd

variable (R S M N : Type*) [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace M]
  [TopologicalSpace N]

@[fun_prop]
lemma continuous_prodProdProdComm : Continuous (Equiv.prodProdProdComm R S M N) := by
  unfold Equiv.prodProdProdComm
  simp only [Equiv.coe_fn_mk]
  fun_prop
