import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.HaarMeasure.HaarChar.FiniteDimensional
import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.AdicCompletion
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import Mathlib.Algebra.Central.Basic
/-!

# Haar character of the finite adele ring of a number field

We prove the crucial result that left and right multiplication by an element of `D ⊗[K] 𝔸_K^f`
scale Haar measure by the same factor, if D is a finite-dimensional central simple `K`-alegbra.

-/

open NumberField

open scoped TensorProduct

variable (K : Type*) [Field K] [NumberField K]

variable (B : Type*) [Ring B] [Algebra K B] [FiniteDimensional K B]

open scoped TensorProduct

open NumberField MeasureTheory

-- in FLT#823
instance (k A B : Type*) [Field k] [CommRing A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] :
    Algebra.IsCentral A (A ⊗[k] B) := sorry


-- in FLT#823
instance (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := sorry

-- in FLT#823
instance (k A B : Type*) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (B ⊗[k] A) :=
  IsSimpleRing.of_ringEquiv
    (Algebra.TensorProduct.comm k A B).toRingEquiv inferInstance

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


open IsDedekindDomain HeightOneSpectrum RestrictedProduct

attribute [-instance] instIsScalarTowerFiniteAdeleRing_fLT_1

variable
  [TopologicalSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] B)]
  [IsTopologicalRing (FiniteAdeleRing (𝓞 K) K ⊗[K] B)]
  [LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K ⊗[K] B)]
  [IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 K) K ⊗[K] B)]
  [MeasurableSpace ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)]
  [BorelSpace ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)] in
lemma NumberField.FiniteAdeleRing.tensor_isCentralSimple_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : ((FiniteAdeleRing (𝓞 K) K) ⊗[K] B)ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  sorry

-- in FLT#823
open scoped TensorProduct.RightActions in
instance (k A B : Type*) [Field k] [Field A] [Ring B]
    [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] :
    Algebra.IsCentral A (B ⊗[k] A) :=
  Algebra.IsCentral.of_algEquiv _ _ _ {
    __ := (Algebra.TensorProduct.comm k A B)
    commutes' := by simp }

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
open scoped TensorProduct.RightActions in
variable
  [MeasurableSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))]
  [BorelSpace (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))] in
lemma NumberField.AdeleRing.isCentralSimple_finite_addHaarScalarFactor_left_mul_eq_right_mul
    [IsSimpleRing B] [Algebra.IsCentral K B] (u : (B ⊗[K] (FiniteAdeleRing (𝓞 K) K))ˣ) :
    addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) =
    addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  -- finite places
  -- the code here is just testing whether `ringHaarChar_eq_addEquivAddHaarChar_mulRight`
  -- works for each finite place `v`
  -- feel free to modify this code
  have : Module.FinitePresentation K B := Module.finitePresentation_of_finite ..
  let v : HeightOneSpectrum (𝓞 K) := sorry
  let u' : (B ⊗[K] (v.adicCompletion K))ˣ := sorry
  let : MeasurableSpace (B ⊗[K] v.adicCompletion K) := borel _
  have : BorelSpace (B ⊗[K] v.adicCompletion K) := ⟨rfl⟩
  have hf := IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (F := v.adicCompletion K) u'
  sorry
