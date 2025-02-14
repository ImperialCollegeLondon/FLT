import Mathlib
import FLT.Deformation.ContinuousRepresentation.TopologicalModule

structure ContinuousRepresentation
    (R : Type*) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
    (G : Type*) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M] [TopologicalModule R M]
    extends (Representation R G M) where
  continuous := Continuous (X := G × M) (Y := M) fun ⟨g, m⟩ ↦ toFun g m

variable {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]
  {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [TopologicalModule R M]

instance : CoeOut (ContinuousRepresentation R G M) (Representation R G M) where
  coe ρ := ρ.1

instance : FunLike (ContinuousRepresentation R G M) G (M →L[R] M) where
  coe ρ g := {
    toFun := ρ.toFun g
    map_add' := by aesop
    map_smul' := by aesop
    cont := sorry
  }
  coe_injective' ρ ρ' h := by
    sorry
