import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas

lemma TopologicalSpace.secondCountableTopology_of_countable_cover' {α : Type*}
    [TopologicalSpace α] {ι : Sort*} [Countable ι] {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
    [∀ (i : ι), SecondCountableTopology (U i)]
    (f : ∀ i, U i → α) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hc : ∀ a, ∃ (i : ι) (u : U i), f i u = a) : SecondCountableTopology α :=
  let V i := Set.range (f i)
  have (i : ι) : SecondCountableTopology (V i) :=
    (hf i).toHomeomorph.symm.secondCountableTopology
  have Vo (i : ι) : IsOpen (V i) := (hf i).isOpen_range
  have hV : ⋃ i, V i = Set.univ := Set.eq_univ_of_forall fun a =>
    (hc a).elim fun i hi => Set.mem_iUnion_of_mem i (Set.mem_range.2 hi)
  secondCountableTopology_of_countable_cover Vo hV
