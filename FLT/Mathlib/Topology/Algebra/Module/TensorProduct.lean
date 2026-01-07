import Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.TensorProduct.FiniteFree
import Mathlib.Topology.Algebra.Module.ModuleTopology

open scoped TensorProduct

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

-- must let φ be linear rather than algebra map because single : K_p -> 𝔸_K isn't a ring hom
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
    let f1 := ContinuousLinearEquiv.chooseBasis_piScalarRight R M V
    let f3 := (ContinuousLinearEquiv.chooseBasis_piScalarRight R N V).symm
    let f2 : (Module.Free.ChooseBasisIndex R V → M) →L[R]
      (Module.Free.ChooseBasisIndex R V → N) := {
      __ := φ.toLinearMap.compLeft (Module.Free.ChooseBasisIndex R V)
      }
    let moo := f3.toContinuousLinearMap.comp (f2.comp f1.toContinuousLinearMap)
    suffices LinearMap.rTensor V ↑φ = moo.toLinearMap by
      rw [this]
      exact moo.cont
    simp only [moo, f3]
    suffices (ContinuousLinearEquiv.chooseBasis_piScalarRight R N V).toLinearMap.comp
        (LinearMap.rTensor V φ.toLinearMap) =
        (f2.comp f1.toContinuousLinearMap) by
      push_cast at this ⊢
      rw [← this]
      ext
      simp
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
