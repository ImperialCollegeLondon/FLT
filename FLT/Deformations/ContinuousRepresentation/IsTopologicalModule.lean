import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Topology.Algebra.Module.LinearMap

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]

/--
`IsTopologicalModule R M` states that the topology in `M` makes scalar multiplication and addition
into continuous maps.
-/
class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M

variable [IsTopologicalModule R M]

protected theorem Topology.IsInducing.topologicalModule {F : Type*}
    (R : Type*) [Ring R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    {H : Type*} [AddCommGroup H] [Module R H] [TopologicalSpace H]
    [FunLike F H M] [LinearMapClass F R H M] (f : F) (hf : IsInducing ⇑f) :
    IsTopologicalModule R H where
  continuous_smul := (hf.continuousSMul (by continuity) (by aesop)).continuous_smul
  continuous_add := (hf.continuousAdd ..).continuous_add

instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := IsInducing.subtypeVal.topologicalModule R S.subtypeL

instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) where
  continuous_smul := by apply continuous_smul
  continuous_add := by apply continuous_add
