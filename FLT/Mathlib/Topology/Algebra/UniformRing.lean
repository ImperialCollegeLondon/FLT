import Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Algebra.Algebra.Hom

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

noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α]
    [TopologicalRing α] [UniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [UniformAddGroup β] [TopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    Completion α →ₛₐ[f] Completion β where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m x := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr
    exact extensionHom_coe _ _ m

end UniformSpace.Completion
