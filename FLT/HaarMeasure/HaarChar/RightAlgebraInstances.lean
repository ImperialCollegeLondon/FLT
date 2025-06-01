import FLT.HaarMeasure.HaarChar.Ring
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.RingTheory.TensorProduct.Finite
import FLT.Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [Ring B] [Algebra R B]

scoped[RightAlgebra] attribute [instance] Algebra.TensorProduct.rightAlgebra

open scoped TensorProduct

namespace RightAlgebra

scoped instance [h : Module.Finite R B] : Module.Finite A (B ⊗[R] A) := by
  classical
    obtain ⟨s, hs⟩ := h.fg_top
    refine ⟨⟨s.image ((TensorProduct.mk R B A).flip 1), eq_top_iff.mpr ?_⟩⟩
    rintro x -
    induction x with
    | zero => exact zero_mem _
    | tmul x y =>
      have : x ⊗ₜ[R] y = y • x ⊗ₜ[R] 1 := by simp [RingHom.smul_toAlgebra']
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.range_coe, this]
      exact Submodule.smul_mem _ y (Submodule.subset_span <| Set.mem_range_self x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy



scoped instance [Module.Free R B] : Module.Free A (B ⊗[R] A) :=
  sorry -- copy the proof in the commented-out code and make it work for right tensors?

noncomputable scoped instance [TopologicalSpace A] : TopologicalSpace (B ⊗[R] A) :=
  moduleTopology A (B ⊗[R] A)

scoped instance [TopologicalSpace A] : IsModuleTopology A (B ⊗[R] A) := ⟨rfl⟩

-- AdeleRing is locally compact, B/R is finite, so this is just homeo to a finite
-- product of locally compact spaces
scoped instance [TopologicalSpace A] [LocallyCompactSpace A] [Module.Finite R B] :
    LocallyCompactSpace (B ⊗[R] A) := sorry

scoped instance [TopologicalSpace A] [IsTopologicalRing A]
    [Module.Finite R B] : IsTopologicalRing (B ⊗[R] A) :=
  haveI : IsModuleTopology A (B ⊗[R] A) := ⟨rfl⟩
  IsModuleTopology.Module.topologicalRing A _
