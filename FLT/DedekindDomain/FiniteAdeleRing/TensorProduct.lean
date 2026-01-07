import FLT.Mathlib.LinearAlgebra.TensorProduct.Algebra
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.Mathlib.LinearAlgebra.TensorProduct.FiniteFree
import FLT.Mathlib.Topology.Algebra.Module.TensorProduct
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

open scoped TensorProduct

namespace IsDedekindDomain.FiniteAdeleRing

open scoped RestrictedProduct

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [DecidableEq (HeightOneSpectrum R)]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

open TensorProduct

variable (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable
    [TopologicalSpace (FiniteAdeleRing R K ⊗[K] V)]
    [IsTopologicalAddGroup (FiniteAdeleRing R K ⊗[K] V)]
    [IsModuleTopology (FiniteAdeleRing R K) (FiniteAdeleRing R K ⊗[K] V)]
    [∀ (p : HeightOneSpectrum R), TopologicalSpace (p.adicCompletion K ⊗[K] V)]
    [∀ (p : HeightOneSpectrum R), IsTopologicalAddGroup (p.adicCompletion K ⊗[K] V)]
    [∀ (p : HeightOneSpectrum R), IsModuleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] V)]

open IsDedekindDomain NumberField

/--
If `φ : 𝔸_K^f ⊗[K] V → 𝔸_K^f ⊗[K] V` is `𝔸_K^f`-linear and `p : HeightOneSpectrum (𝓞 K)`
then `localcomponent R K V p φ : Kₚ ⊗[K] V →[K] Kₚ ⊗[K] V` is the associated
map `φₚ` satisfying `φ = Πₚ φₚ`.
-/
noncomputable def TensorProduct.localcomponent (p : HeightOneSpectrum R)
    (φ : FiniteAdeleRing R K ⊗[K] V →L[FiniteAdeleRing R K]
      FiniteAdeleRing R K ⊗[K] V) :
    p.adicCompletion K ⊗[K] V →L[K] p.adicCompletion K ⊗[K] V := by
  -- bar1 : `𝔸_K^f ⊗[K] V →L[K] Kₚ ⊗[K] V` is evalₚ ⊗ id_V
  let bar1 := (ContinuousLinearMap.rTensor V
    (evalContinuousAlgebraMap R K p).toContinuousLinearMap)
  -- bar2 : `𝔸_K^f ⊗[K] V →L[K] 𝔸_K^f ⊗[K] V` is φ
  let bar2 : FiniteAdeleRing R K ⊗[K] V →L[K] FiniteAdeleRing R K ⊗[K] V := {
    __ := φ.toLinearMap.restrictScalars K
    cont := φ.cont
  }
  -- bar3 : `Kₚ ⊗[K] V →L[K] 𝔸_K^f ⊗[K] V` is singleₚ ⊗ id_V
  let bar3 := (ContinuousLinearMap.rTensor V (singleContinuousLinearMap R K p))
  -- bar1 ∘ bar2 ∘ bar3
  refine bar1.comp (bar2.comp bar3)

/--
`localIdempotent R K p` is the finite adele which is 1 at p and 0 elsewhere.
-/
noncomputable def localIdempotent (p : HeightOneSpectrum R) : FiniteAdeleRing R K :=
  ⟨Pi.single p 1, by
    filter_upwards
    intro q
    obtain rfl | h := eq_or_ne p q
    · rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne' h]
      exact zero_mem _⟩

lemma eval_localIdempotent (p : HeightOneSpectrum R) :
    (evalContinuousAlgebraMap R K p) (localIdempotent R K p) = 1 :=
  Pi.single_eq_same _ _

lemma singleContinuousAlgebraMap_comp_evalContinuousLinearMap (j : HeightOneSpectrum R) :
    ((singleContinuousLinearMap R K j).comp
    (evalContinuousAlgebraMap R K j).toContinuousLinearMap).toLinearMap =
    LinearMap.lsmul (FiniteAdeleRing R K) (FiniteAdeleRing R K) (localIdempotent R K j) := by
  ext x q
  change Pi.single _ (x j) _ = Pi.single j _ q * _
  obtain rfl | h := eq_or_ne j q
  · simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne' h]

lemma TensorProduct.localcomponent_apply
    (φ : FiniteAdeleRing R K ⊗[K] V →L[FiniteAdeleRing R K] FiniteAdeleRing R K ⊗[K] V)
    (x : FiniteAdeleRing R K ⊗[K] V) (p : HeightOneSpectrum R) :
    (ContinuousLinearMap.rTensor V
      (evalContinuousAlgebraMap R K p).toContinuousLinearMap) (φ x) =
    TensorProduct.localcomponent R K V p φ ((ContinuousLinearMap.rTensor V
      (evalContinuousAlgebraMap R K p).toContinuousLinearMap) x) := by
  unfold localcomponent
  dsimp
  rw [← ContinuousLinearMap.rTensor_comp_apply]
  change (LinearMap.rTensor V _) (φ x) = (LinearMap.rTensor V _)
    (φ ((LinearMap.rTensor V _) x))
  rw [singleContinuousAlgebraMap_comp_evalContinuousLinearMap]
  let moo := (LinearMap.lsmul
    (FiniteAdeleRing R K) (FiniteAdeleRing R K) (localIdempotent R K p)).restrictScalars K
  have foo : LinearMap.rTensor V moo x = (localIdempotent R K p) • x := by
    induction x with
    | zero => simp
    | tmul x y =>
      rw [LinearMap.rTensor_tmul]
      rfl
    | add x y _ _ => simp_all
  rw [foo]
  rw [ContinuousLinearMap.map_smul]
  change (AlgHom.rTensor V ((evalContinuousAlgebraMap R K p).toAlgHom)) (φ x) =
    (AlgHom.rTensor V ((evalContinuousAlgebraMap R K p).toAlgHom)) (localIdempotent R K p • φ x)
  rw [map_smulₛₗ]
  change _ = (evalContinuousAlgebraMap R K p) (localIdempotent R K p) • _
  simp [eval_localIdempotent]

-- plan; 𝔸_K ⊗ V = (Fin n) → 𝔸_K topologically, which is Πʳ (Fin n -> K_v)
-- topologically, and the claim is that the induced top iso A_K ⊗ V = Πʳ (Fin n -> K_v)
-- sends φ to ∏_v φ_v

end FiniteAdeleRing

end IsDedekindDomain
