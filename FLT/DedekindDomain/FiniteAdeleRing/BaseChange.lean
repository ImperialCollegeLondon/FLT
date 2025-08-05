/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.NumberTheory.RamificationInertia.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.Finiteness.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod
/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeAlgEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

## Main theorems

* `BaseChange.isModuleTopology` : `FiniteAdeleRing B L` has the
  `FiniteAdeleRing A K`-module topology.

-/

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]


namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum

open scoped TensorProduct RestrictedProduct -- ⊗ notation for tensor product

#exit
variable {M : Type u_1} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
variable (S : Finset (HeightOneSpectrum A))

noncomputable def tensor_iso :
  (M ⊗[A]((Π v : S, v.1.adicCompletion K) ×
  (Π v : (Set.compl (Finset.toSet S)), (adicCompletionIntegers K v.1))))
  ≃ₗ[A] ((Π v : S, M ⊗[A] v.1.adicCompletion K) ×
  (Π v : (Set.compl (Finset.toSet S)), M ⊗[A] (adicCompletionIntegers K v.1))) :=
  TensorProduct.prodRight _ _ M
    (Π v : S, v.1.adicCompletion K) (Π v : (Set.compl (Finset.toSet S)),
    (adicCompletionIntegers K v.1)) ≪≫ₗ LinearEquiv.prodCongr
    (tensorPi_equiv_piTensor' A M _) (tensorPi_equiv_piTensor' A M _)

lemma tensor_iso_apply (m : M) (k : (Π v : S, v.1.adicCompletion K))
  (a :  (Π v : (Set.compl (Finset.toSet S)), (adicCompletionIntegers K v.1))) :
  tensor_iso  A K S (m ⊗ₜ (k, a)) = (fun v ↦ (m ⊗ₜ k v), fun v ↦ (m ⊗ₜ a v)) := rfl



noncomputable def forward : M ⊗[A] (Πʳ i, [K i, A i]) →ₗ[A]
    (Πʳ i, [M ⊗[R] (C i), LinearMap.range (LinearMap.lTensor M (D i).subtype)]) :=
    TensorProduct.lift <| by
    refine LinearMap.mk₂ R (fun m x ↦ ?_) ?_ ?_ ?_ ?_
    · refine RestrictedProduct.mk (tensorPi_equiv_piTensor' R M C (m ⊗ₜ[R] x.val)) ?_
      filter_upwards [x.property] with i hi
      simp only [SetLike.mem_coe, LinearMap.mem_range]
      let ai : D i := ⟨x.val i, hi⟩
      use m ⊗ₜ[R] ai
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      rfl
    · -- Linearity in first argument
      intro m₁ m₂ x
      ext i
      simp [TensorProduct.add_tmul]
    · intro m x₁ x₂
      ext i
      simp [TensorProduct.tmul_add]
      rfl
    · intro r m x
      ext i
      simp only [RestrictedProduct.mk_apply, RestrictedProduct.add_apply]
      apply TensorProduct.tmul_add
    · intro r m x
      ext i
      simp only [RestrictedProduct.mk_apply, RestrictedProduct.smul_apply]
      apply TensorProduct.tmul_smul


-- noncomputable def tensor_restrictedProduct_iso :
--   M ⊗[R] (Πʳ i, [C i, D i]) ≃ₗ[R]
--   (Πʳ i, [M ⊗[R] (C i), LinearMap.range (LinearMap.lTensor M (D i).subtype)]) := by
--   refine LinearEquiv.ofBijective forward ⟨?_, ?_⟩
--   · dsimp [forward]
--     intro a b hab
--     sorry
--   · sorry


/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields. -/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L := RestrictedProduct.mapAlongRingHom
  (fun (v : HeightOneSpectrum A) ↦ v.adicCompletion K)
  (fun (w : HeightOneSpectrum B) ↦ w.adicCompletion L)
  (HeightOneSpectrum.comap A)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <| Extension.finite A K L B)
  (fun w ↦ adicCompletionComapSemialgHom A K L B (w.comap A) w rfl)
  (by
    apply Filter.Eventually.of_forall
    intro w
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    have := adicCompletionComapSemialgHom.mapadicCompletionIntegers A K L B (comap A w) w rfl
    exact Set.image_subset_iff.1 this)

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields,
as a morphism lying over the canonical map `K → L`. -/
noncomputable def FiniteAdeleRing.mapSemialgHom :
    FiniteAdeleRing A K →ₛₐ[algebraMap K L] FiniteAdeleRing B L where
      __ := FiniteAdeleRing.mapRingHom A K L B
      map_smul' k a := by
        ext w
        simpa only [Algebra.smul_def'] using
          (adicCompletionComapSemialgHom A K L B (comap A w) w rfl).map_smul' k (a (comap A w))

open scoped TensorProduct.RightActions

noncomputable
instance BaseChange.algebra : Algebra (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  RingHom.toAlgebra (FiniteAdeleRing.mapRingHom A K L B)

lemma FiniteAdeleRing.mapSemialgHom_continuous : Continuous (mapSemialgHom A K L B) :=
  sorry

attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass
-- otherwise
-- #synth SMul (FiniteAdeleRing A K) (FiniteAdeleRing B L)
-- spends 2 seconds failing to find `SMul (FiniteAdeleRing A K) (adicCompletion L w)

lemma BaseChange.isModuleTopology : IsModuleTopology (FiniteAdeleRing A K) (FiniteAdeleRing B L) :=
  sorry -- this should follow from the fact that L_w has the K_v-module topology? Hopefully
  -- **TODO** this needs an issue number.

noncomputable instance : TopologicalSpace (L ⊗[K] FiniteAdeleRing A K) :=
  moduleTopology (FiniteAdeleRing A K) (L ⊗[K] FiniteAdeleRing A K)

/-- The `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞`. -/
noncomputable def FiniteAdeleRing.baseChangeAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L where
  __ := AlgEquiv.ofBijective
    (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    -- ⊢ Function.Bijective ⇑(mapSemialgHom A K L B).baseChange_of_algebraWMap
    sorry -- #243

/-- The continuous `L`-algebra isomorphism `L ⊗_K 𝔸_K^∞ ≅ 𝔸_L^∞` -/
noncomputable def FiniteAdeleRing.baseChangeContinuousAlgEquiv :
    L ⊗[K] FiniteAdeleRing A K ≃A[L] FiniteAdeleRing B L where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  continuous_toFun := sorry
  continuous_invFun := sorry
  -- TODO needs issue number

noncomputable instance baseChangeAlgebra : Algebra K (FiniteAdeleRing B L) :=
  RingHom.toAlgebra <| (algebraMap L _).comp (algebraMap K L)

noncomputable instance baseChangeScalarTower :
    IsScalarTower K (FiniteAdeleRing A K) (FiniteAdeleRing B L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  nth_rw 2 [RingHom.algebraMap_toAlgebra]
  symm
  exact SemialgHom.commutes (FiniteAdeleRing.mapSemialgHom A K L B) x

end IsDedekindDomain
