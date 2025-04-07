import Mathlib.Topology.Order

open TopologicalSpace

lemma isOpenMap_induced {X Y : Type*} [TopologicalSpace Y]
    {f : X → Y} (hf : Function.Surjective f) :
    @IsOpenMap _ _ (.induced f ‹_›) _ f  := by
  intro U
  simp only [isOpen_induced_iff, forall_exists_index, and_imp]
  rintro V hV rfl
  rwa [Set.image_preimage_eq _ hf]
