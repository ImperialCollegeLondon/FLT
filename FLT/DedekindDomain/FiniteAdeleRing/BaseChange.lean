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

/-!

# Base change of adele rings.

If `A` is a Dedekind domain with field of fractions `K`, if `L/K` is a finite separable
extension and if `B` is the integral closure of `A` in `L`, then `B` is also a Dedekind
domain. Hence the rings of finite adeles `𝔸_K^∞` and `𝔸_L^∞` (defined using `A` and `B`)
are defined. In this file we define the natural `K`-algebra map `𝔸_K^∞ → 𝔸_L^∞` and
the natural `L`-algebra map `𝔸_K^∞ ⊗[K] L → 𝔸_L^∞`, and show that the latter map
is an isomorphism.

## Main definitions

* `FiniteAdeleRing.baseChangeEquiv : L ⊗[K] FiniteAdeleRing A K ≃ₐ[L] FiniteAdeleRing B L`

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

open scoped TensorProduct -- ⊗ notation for tensor product


section
universe u
variable {R : Type*} [CommRing R]
variable {ι : Type*} {M : Type*} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]Add commentMore actions
variable {K : ι → Type*} [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
variable {A : ∀ i, Submodule R (K i)} [∀ i, TopologicalSpace (K i)]
variable {X Y: Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable {S : Set ι}

noncomputable def tensor_restrictedProduct_iso :
  M ⊗[R] (Πʳ i, [K i, A i]) ≃ₗ[R]
  (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := by
  letI := RestrictedProduct.topologicalSpace K (fun i ↦ (A i : Set (K i))) Filter.cofinite
  haveI := @RestrictedProduct.topologicalSpace_eq_iSup _ K (fun i ↦ (A i : Set (K i))) Filter.cofinite _

  --rw [TopologicalSpace.Opens.iSup_def] at this
  have forward : M ⊗[R] (Πʳ i, [K i, A i]) →ₗ[R]
    (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := by
    apply LinearMap.codRestrict
    (LinearMap.comp
      (LinearMap.pi fun i => LinearMap.rangeRestrict (LinearMap.lTensor M (A i).subtype))
      (LinearMap.comp tensorPi_equiv_piTensor'.toLinearMap
        (LinearMap.lTensor M (LinearMap.pi fun i => (A i).subtype))))
    _
    (fun x => by
      -- Show that the result satisfies the restricted product condition
      sorry
    )

    let embed_source : (Πʳ i, [K i, A i]) →ₗ[R] (Π i, K i) :=
     {toFun := (↑), map_add' x y := rfl, map_smul' k x := rfl}
    let embed_source' : (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)])
       →ₗ[R] (Π i, M ⊗[R] (K i)) :=
      {toFun := (↑), map_add' x y := rfl, map_smul' k x := rfl}
    -- def K_restricted : Submodule R (Π i, K i) := (Πʳ i, [K i, A i])
    -- let q := LinearMap.range embed_source'
    -- have hf : ∀ x ∈ p, (tensorPi_equiv_piTensor' R M K) x ∈ q  := sorry
    -- have p' : p =  M ⊗[R] (Πʳ i, [K i, A i]) := sorry
    -- have q' : q = (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := sorry

    -- let a := LinearMap.restrict (tensorPi_equiv_piTensor' R M K).toLinearMap hf/
    apply TensorProduct.lift
    refine LinearMap.mk₂ R ?_ ?_ ?_ ?_ ?_
    · -- The bilinear map m × x ↦ restricted product
      intro m x
      use tensorPi_equiv_piTensor' R M K (m ⊗ₜ[R] x.val)
      filter_upwards [x.property] with i hi
      simp only [SetLike.mem_coe, LinearMap.mem_range]
      let ai : A i := ⟨x.val i, hi⟩
      use m ⊗ₜ[R] ai
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      rfl
    · -- Linearity in first argument
      intro m₁ m₂ x; ext i; simp [TensorProduct.add_tmul]
    · intro m x₁ x₂; ext i; simp [TensorProduct.tmul_add]; rfl
    · intro r m x; ext i; simp [TensorProduct.smul_tmul]; rfl
    · intro r m x; ext i; simp [TensorProduct.tmul_smul]; rfl



  -- First, we need embeddings of restricted products into full products
  let embed_source : (Πʳ i, [K i, A i]) →ₗ[R] (Π i, K i) := by
    -- This should be the natural inclusion
    exact {toFun := (↑), map_add' x y := rfl, map_smul' k x := rfl}

  let embed_target : (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) →ₗ[R] (Π i, M ⊗[R] (K i)) := by
    -- Natural inclusion of restricted product into full product
    exact {toFun := fun y => y.val, map_add' := by sorry, map_smul' := by sorry}

  let f1 := (tensorPi_equiv_piTensor' R M K).toLinearMap
  let f2 := (LinearMap.lTensor M embed_source)
  let f₃ := f1.comp f2


  -- The key lemma: tensorPi_equiv_piTensor' maps the source submodule to target submodule
  have maps_correctly : ∀ (t : M ⊗[R] (Πʳ i, [K i, A i])),
    (tensorPi_equiv_piTensor' R M K) (LinearMap.lTensor M embed_source t) ∈
    LinearMap.range embed_target := by
    intro t
    sorry
    -- -- We need to show the image lands in the restricted product
    -- -- Use the fact that tensor products preserve the restricted product structure
    -- apply TensorProduct.induction_on t
    -- · -- Base case: 0
    --   simp [LinearMap.map_zero]
    --   use 0
    --   simp
    -- · -- Pure tensor case: m ⊗ₜ x
    --   intro m x
    --   -- Key insight: tensorPi_equiv_piTensor'_apply gives us the formula
    --   have h_formula : (tensorPi_equiv_piTensor' R M K) (LinearMap.lTensor M embed_source (m ⊗ₜ x)) =
    --     fun i => m ⊗ₜ[R] x.val i := by
    --     simp [LinearMap.lTensor_tmul, tensorPi_equiv_piTensor'_apply, embed_source]

    --   -- Now show this function is in the restricted product
    --   use ⟨fun i => m ⊗ₜ[R] x.val i, ?_⟩
    --   · -- Show it equals the formula
    --     ext i
    --     rw [h_formula]
    --     rfl
    --   · -- Show the support condition
    --     filter_upwards [x.property] with i hi
    --     -- x.val i ∈ A i, so m ⊗ₜ x.val i is in the range
    --     use m ⊗ₜ[R] ⟨x.val i, hi⟩
    --     simp [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    -- · -- Additivity
    --   intro t₁ t₂ h₁ h₂
    --   simp [LinearMap.map_add]
    --   obtain ⟨y₁, hy₁⟩ := h₁
    --   obtain ⟨y₂, hy₂⟩ := h₂
    --   use y₁ + y₂
    --   simp [← hy₁, ← hy₂]

  -- Similarly for the reverse direction
  have maps_back : ∀ (s : Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]),
    (tensorPi_equiv_piTensor' R M K).symm (embed_target s) ∈
    LinearMap.range (LinearMap.lTensor M embed_source) := by
    intro s
    -- This uses finite presentation of M and the structure of the ranges
    sorry

  -- Construct the isomorphism using these embeddings
  have forward : M ⊗[R] (Πʳ i, [K i, A i]) →ₗ[R]
    (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := by

      -- have' := (embed_target.comp (tensorPi_equiv_piTensor' R M K).toLinearMap).comp (LinearMap.lTensor M embed_source)
      sorry
--  have backward := sorry -- Construct using maps_back

  sorry
--  use forward, backward





#exit

-- The key insight: we can view this as a restriction of the full product case
  -- M ⊗[R] (Π i, K i) ≃ₗ[R] Π i, (M ⊗[R] K i)

  -- Forward direction: M ⊗[R] (Πʳ i, [K i, A i]) → target
  have forward : M ⊗[R] (Πʳ i, [K i, A i]) →ₗ[R]
    (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := by
    -- have := RestrictedProduct.mk


    -- #exit
    --apply TensorProduct.lift

    apply LinearMap.mk

    #exit
    refine LinearMap.mk₂ R ?_ ?_ ?_ ?_ ?_
    · -- The bilinear map m × x ↦ restricted product
      intro m x
      use tensorPi_equiv_piTensor' R M K (m ⊗ₜ[R] x.val)
      filter_upwards [x.property] with i hi
      simp only [SetLike.mem_coe, LinearMap.mem_range]
      let ai : A i := ⟨x.val i, hi⟩
      use m ⊗ₜ[R] ai
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      rfl
    · -- Linearity in first argument
      intro m₁ m₂ x; ext i; simp [TensorProduct.add_tmul]
    · -- Linearity in second argument
      intro m x₁ x₂; ext i; simp [TensorProduct.tmul_add]
    · -- Scalar action in first argument
      intro r m x; ext i; simp [TensorProduct.smul_tmul]
    · -- Scalar action in second argument
      intro r m x; ext i; simp [TensorProduct.tmul_smul]


#exit
-- Forward map: M ⊗[R] (Πʳ i, [K i, A i]) → (Πʳ i, [M ⊗[R] (K i), ...])
  let forward : M ⊗[R] (Πʳ i, [K i, A i]) →ₗ[R]
    (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) := by
    -- Use TensorProduct.lift to define the map
    apply TensorProduct.lift
    -- Define the bilinear map M × (Πʳ i, [K i, A i]) → target
    exact {
      toFun := fun m => {
        toFun := fun x => by
          -- For each component i, we need (M ⊗[R] K i) in the range of lTensor M (A i).subtype
          refine RestrictedProduct.mk (fun i => m ⊗ₜ[R] x.val i) ?_
          -- Use filter_upwards from x's restricted product property
          filter_upwards [x.property] with i hi
          simp?
          sorry
          -- Need to show this is eventually in the submodule
          -- apply Filter.eventually_of_forall
          -- intro i
          -- -- Show m ⊗ₜ[R] x.val i is in LinearMap.range (LinearMap.lTensor M (A i).subtype)
          -- use m ⊗ₜ[R] ⟨x.val i, x.property i⟩
          -- simp [LinearMap.lTensor_tmul]
        map_add' := by
          intro x y
          ext i
          --simp [RestrictedProduct.mk_val, TensorProduct.tmul_add]
          sorry
        map_smul' := by
          intro r x
          ext i
          --simp [RestrictedProduct.mk_val, TensorProduct.tmul_smul]
          sorry
      }
      map_add' := by
        intro m₁ m₂
        ext x i
        --simp [RestrictedProduct.mk_val, TensorProduct.add_tmul]
        sorry
      map_smul' := by
        intro r m
        ext x i
        --simp [RestrictedProduct.mk_val, TensorProduct.smul_tmul]
        sorry
    }

  -- Backward map: construct the inverse
  let backward : (Πʳ i, [M ⊗[R] (K i), LinearMap.range (LinearMap.lTensor M (A i).subtype)]) →ₗ[R]
    M ⊗[R] (Πʳ i, [K i, A i]) := by
    -- This is more complex - we need to use the finite support property
    -- and the fact that elements in the range come from tensor products
    sorry -- This direction requires more careful construction

  -- Show these are inverses
  use forward, backward
  · -- forward ∘ backward = id
    intro x
    sorry
  · -- backward ∘ forward = id
    intro m
    sorry

end

/-- The ring homomorphism `𝔸_K^∞ → 𝔸_L^∞` for `L/K` an extension of number fields.-/
noncomputable def FiniteAdeleRing.mapRingHom :
    FiniteAdeleRing A K →+* FiniteAdeleRing B L := RestrictedProduct.mapRingHom
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
