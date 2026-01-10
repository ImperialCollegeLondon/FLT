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
map `φₚ` defined as `Kₚ ⊗[K] V --(single)--> 𝔸_K^f ⊗ V --(φ)--> 𝔸_K^f ⊗ V --(eval)--> Kₚ ⊗ V`.
This map morally satisfies `φ = Πₚ φₚ` but because source of φ isn't literally a restricted
product we cannot make this assertion.
-/
noncomputable def TensorProduct.localcomponent (p : HeightOneSpectrum R)
    (φ : FiniteAdeleRing R K ⊗[K] V →L[FiniteAdeleRing R K]
      FiniteAdeleRing R K ⊗[K] V) :
    p.adicCompletion K ⊗[K] V →L[K] p.adicCompletion K ⊗[K] V :=
  -- f1 : `𝔸_K^f ⊗[K] V →L[K] Kₚ ⊗[K] V` is evalₚ ⊗ id_V
  letI f1 := (ContinuousLinearMap.rTensor V
    (evalContinuousAlgebraMap R K p).toContinuousLinearMap)
  -- f2 : `𝔸_K^f ⊗[K] V →L[K] 𝔸_K^f ⊗[K] V` is φ
  letI f2 : FiniteAdeleRing R K ⊗[K] V →L[K] FiniteAdeleRing R K ⊗[K] V := {
    __ := φ.toLinearMap.restrictScalars K
    cont := φ.cont
  }
  -- f3 : `Kₚ ⊗[K] V →L[K] 𝔸_K^f ⊗[K] V` is singleₚ ⊗ id_V
  letI f3 := (ContinuousLinearMap.rTensor V (singleContinuousLinearMap R K p))
  -- f1 ∘ f2 ∘ f3
  f1.comp (f2.comp f3)

/--
If `φ : 𝔸_K^f ⊗ V → 𝔸_K^f ⊗ V` is `𝔸_K^f`-linear and `φₚ` is its local component at a place `p`
then for all `x : 𝔸_K^f ⊗ V` we have
`(evalₚ ⊗ id_V) (φ x) = φₚ ((evalₚ ⊗ id_V) x)`, or, more colloquiually,
`(φ x)ₚ = φₚ (xₚ)`.
-/
lemma TensorProduct.localcomponent_apply
    (φ : FiniteAdeleRing R K ⊗[K] V →L[FiniteAdeleRing R K] FiniteAdeleRing R K ⊗[K] V)
    (x : FiniteAdeleRing R K ⊗[K] V) (p : HeightOneSpectrum R) :
    (ContinuousLinearMap.rTensor V
      (evalContinuousAlgebraMap R K p).toContinuousLinearMap) (φ x) =
    TensorProduct.localcomponent R K V p φ ((ContinuousLinearMap.rTensor V
      (evalContinuousAlgebraMap R K p).toContinuousLinearMap) x) := by
  dsimp [localcomponent]
  rw [← ContinuousLinearMap.rTensor_comp_apply]
  change (LinearMap.rTensor V _) (φ x) = (LinearMap.rTensor V _) (φ ((LinearMap.rTensor V _) x))
  rw [singleContinuousAlgebraMap_comp_evalContinuousLinearMap]
  let f := (LinearMap.lsmul
    (FiniteAdeleRing R K) (FiniteAdeleRing R K) (localIdempotent R K p)).restrictScalars K
  have hf : LinearMap.rTensor V f x = (localIdempotent R K p) • x := by
    induction x with
    | zero => simp
    | tmul x y => exact LinearMap.rTensor_tmul _ _ _ _
    | add x y _ _ => simp_all
  rw [hf, ContinuousLinearMap.map_smul]
  change (AlgHom.rTensor V ((evalContinuousAlgebraMap R K p).toAlgHom)) (φ x) =
    (AlgHom.rTensor V ((evalContinuousAlgebraMap R K p).toAlgHom)) (localIdempotent R K p • φ x)
  simp [eval_localIdempotent]

/--
If `φ : 𝔸_K^f ⊗[K] V → 𝔸_K^f ⊗[K] V` is `𝔸_K^f`-linear and `p : HeightOneSpectrum (𝓞 K)`
then `localcomponent R K V p φ : Kₚ ⊗[K] V →[K] Kₚ ⊗[K] V` is the associated
map `φₚ` defined as `Kₚ ⊗[K] V --(single)--> 𝔸_K^f ⊗ V --(φ)--> 𝔸_K^f ⊗ V --(eval)--> Kₚ ⊗ V`.
This map morally satisfies `φ = Πₚ φₚ` but because source of φ isn't literally a restricted
product we cannot make this assertion.
-/
noncomputable def TensorProduct.localcomponentEquiv (p : HeightOneSpectrum R)
    (φ : FiniteAdeleRing R K ⊗[K] V ≃L[FiniteAdeleRing R K]
      FiniteAdeleRing R K ⊗[K] V) :
    p.adicCompletion K ⊗[K] V ≃L[K] p.adicCompletion K ⊗[K] V where
  __ := TensorProduct.localcomponent R K V p φ
  invFun := TensorProduct.localcomponent R K V p φ.symm
  left_inv := sorry -- these might be annoying. Best way is I think
  -- to prove localcomponent_id and localcomponent_comp
  right_inv := sorry

/-

Plan.

Need to use `MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight`

Problem: this is a statement about maps `G i ≃ₜ+ G i` and a map (their "restricted product")
`Πʳ (i : ι), [G i, ↑(C i)] ≃ₜ+ Πʳ (i : ι), [G i, ↑(C i)]`

and we have a map B ⊗ 𝔸_K^f → B ⊗ 𝔸_K^f

Step 0: symm to reduce to a statement about 𝔸_K^f ⊗ B → 𝔸_K^f ⊗ B

Step 1:

𝔸_K^f ⊗ B = ι → 𝔸_K^f = Πʳ [ι → Kᵥ, ι → 𝓞ᵥ] topologically and algebraically

Step 2:

Given 𝔸_K^f-linear φ : 𝔸_K^f ⊗ B → 𝔸_K^f ⊗ B, we have local components φᵥ : Kᵥ ⊗ B → Kᵥ ⊗ B.
The step 1 iso gives us ψ : Πʳ [ι → Kᵥ, ι → 𝓞ᵥ] from φ and the first half of it gives
ψᵥ : (ι → Kᵥ) → (ι → Kᵥ) from the local components φᵥ

Check that the lemma we proved already gives us ψ = Πᶠᵥ ψᵥ

Step 3 : `MeasureTheory.addEquivAddHaarChar_restrictedProductCongrRight` to ψ and ψᵥ

Step 4: hope that this is enough

-/

end FiniteAdeleRing

end IsDedekindDomain
