import Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.TensorProduct.FiniteFree
import Mathlib.Topology.Algebra.Module.ModuleTopology

open scoped TensorProduct

/-- The canonical continuous R-linear isomorphism `M ⊗[R] V ≃ (ι → M)`
where V is a finite free R-module with basis indexed by `ι`, `M` is a commutative
`R`-algebra, and `M ⊗[R] V` has the `M`-module topology. -/
noncomputable def ContinuousLinearEquiv.chooseBasis_piScalarRight (R M V : Type*)
    [CommRing M] [CommRing R] [Algebra R M]
    [TopologicalSpace M] [IsTopologicalRing M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)]
    [IsModuleTopology M (M ⊗[R] V)] :
    (M ⊗[R] V) ≃L[R] (Module.Free.ChooseBasisIndex R V → M) := {
  __ := (LinearEquiv.chooseBasis_piScalarRight R M V).restrictScalars _
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (LinearEquiv.chooseBasis_piScalarRight R M V).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (LinearEquiv.chooseBasis_piScalarRight R M V).symm.toLinearMap
  }


namespace ContinuousLinearMap

/-- The continuous `R`-linear map `M ⊗[R] V → N ⊗[R] V` induced
by a continuous `R`-linear map `M → N`.
-/
def rTensor {R : Type*} {M N : Type*} (V : Type*)
    [CommRing M] [CommRing N] [CommRing R] [Algebra R M] [Algebra R N]
    [TopologicalSpace M] [TopologicalSpace N] [IsTopologicalRing M] [IsTopologicalRing N]
    (φ : M →L[R] N)
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)] [IsModuleTopology M (M ⊗[R] V)]
    [TopologicalSpace (N ⊗[R] V)] [IsTopologicalAddGroup (N ⊗[R] V)]
    [IsModuleTopology N (N ⊗[R] V)] :
    (M ⊗[R] V) →L[R] (N ⊗[R] V) := {
  __ := LinearMap.rTensor V φ.toLinearMap
  cont := by
    -- f1 : M ⊗[R] V ≃L[R] (ι → M)
    let f1 := ContinuousLinearEquiv.chooseBasis_piScalarRight R M V
    -- f2 : (ι → M) →L[R] (ι → N)
    let f2 : (Module.Free.ChooseBasisIndex R V → M) →L[R]
      (Module.Free.ChooseBasisIndex R V → N) := {
      __ := φ.toLinearMap.compLeft (Module.Free.ChooseBasisIndex R V)
      }
    -- f3 : (N ⊗[R] V) ≃[L]R (ι → N)
    let f3 := (ContinuousLinearEquiv.chooseBasis_piScalarRight R N V)
    -- f = f3.symm ∘ f2 ∘ f1
    let f := f3.symm.toContinuousLinearMap.comp (f2.comp f1.toContinuousLinearMap)
    -- it suffices to show that the map we want to be continuous is f,
    -- because f is obviously continuous.
    suffices LinearMap.rTensor V ↑φ = f.toLinearMap by
      rw [this]
      exact f.cont
    -- The question is no longer a topological one, it's just algebraic.
    -- We now want to change goal from g = f3.symm ∘ f2 ∘ f1 to f3 ∘ g = f2 ∘ f1
    -- and this is annoyingly painful
    simp only [f]
    push_cast
    suffices f3.toLinearMap ∘ₗ (LinearMap.rTensor V φ) =
        (f2 ∘ₗ f1.toContinuousLinearMap.toLinearMap) by
      rw [← this]
      ext
      simp
    -- but now that's done, it's easy
    ext m v j
    exact (map_smul φ _ m).symm
  }

lemma rTensor_id_apply {R : Type*} {M : Type*} (V : Type*)
    [CommRing M] [CommRing R] [Algebra R M]
    [TopologicalSpace M] [IsTopologicalRing M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)]
    [IsModuleTopology M (M ⊗[R] V)] (x : M ⊗[R] V) :
    rTensor V (.id R M) x = x := by
  simp [rTensor]

lemma rTensor_id {R : Type*} {M : Type*} (V : Type*)
    [CommRing M] [CommRing R] [Algebra R M]
    [TopologicalSpace M] [IsTopologicalRing M]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)]
    [IsModuleTopology M (M ⊗[R] V)] :
    rTensor V (.id R M) = .id R (M ⊗[R] V) := by
  ext x
  apply rTensor_id_apply

lemma rTensor_comp_apply {R : Type*} {M N P : Type*} (V : Type*)
    [CommRing M] [CommRing N] [CommRing P] [CommRing R] [Algebra R M] [Algebra R N] [Algebra R P]
    [TopologicalSpace M] [IsTopologicalRing M]
    [TopologicalSpace N] [IsTopologicalRing N]
    [TopologicalSpace P] [IsTopologicalRing P]
    (φ : M →L[R] N)
    (ψ : N →L[R] P) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)] [IsModuleTopology M (M ⊗[R] V)]
    [TopologicalSpace (N ⊗[R] V)] [IsTopologicalAddGroup (N ⊗[R] V)] [IsModuleTopology N (N ⊗[R] V)]
    [TopologicalSpace (P ⊗[R] V)] [IsTopologicalAddGroup (P ⊗[R] V)] [IsModuleTopology P (P ⊗[R] V)]
    (x : M ⊗[R] V) :
    rTensor V (ψ.comp φ) x = rTensor V ψ (rTensor V φ x) := by
  simp [rTensor, LinearMap.rTensor, TensorProduct.map_map]

lemma rTensor_comp {R : Type*} {M N P : Type*} (V : Type*)
    [CommRing M] [CommRing N] [CommRing P] [CommRing R] [Algebra R M] [Algebra R N] [Algebra R P]
    [TopologicalSpace M] [IsTopologicalRing M]
    [TopologicalSpace N] [IsTopologicalRing N]
    [TopologicalSpace P] [IsTopologicalRing P]
    (φ : M →L[R] N)
    (ψ : N →L[R] P) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [TopologicalSpace (M ⊗[R] V)] [IsTopologicalAddGroup (M ⊗[R] V)] [IsModuleTopology M (M ⊗[R] V)]
    [TopologicalSpace (N ⊗[R] V)] [IsTopologicalAddGroup (N ⊗[R] V)] [IsModuleTopology N (N ⊗[R] V)]
    [TopologicalSpace (P ⊗[R] V)] [IsTopologicalAddGroup (P ⊗[R] V)]
    [IsModuleTopology P (P ⊗[R] V)] :
    rTensor V (ψ.comp φ) = (rTensor V ψ).comp (rTensor V φ) := by
  ext
  apply rTensor_comp_apply

end ContinuousLinearMap
