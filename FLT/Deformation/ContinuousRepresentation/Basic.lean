import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Module.LinearMap

structure ContinuousRepresentation
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    extends (Representation R G M) where
  continuous := Continuous (X := G × M) (Y := M) fun ⟨g, m⟩ ↦ toFun g m

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]

instance : CoeOut (ContinuousRepresentation R G M) (Representation R G M) where
  coe ρ := ρ.1

instance : FunLike (ContinuousRepresentation R G M) G (M →L[R] M) where
  coe ρ g := {
    toFun := ρ.toFun g
    map_add' := by aesop
    map_smul' := by aesop
    cont := by sorry
  }
  coe_injective' ρ ρ' h := by
    sorry
