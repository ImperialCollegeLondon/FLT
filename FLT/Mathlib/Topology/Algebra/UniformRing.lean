import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological rings
-/

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [TopologicalRing α] [UniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [UniformAddGroup β] [TopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

theorem mapRingHom_apply {x : UniformSpace.Completion α} :
    UniformSpace.Completion.mapRingHom f hf x = UniformSpace.Completion.map f x := rfl

variable {f}

theorem mapRingHom_coe (hf : UniformContinuous f) (a : α) :
    mapRingHom f hf.continuous a = f a := by
  rw [mapRingHom_apply, map_coe hf]

end UniformSpace.Completion
