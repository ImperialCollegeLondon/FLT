/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- if I can get all imports as FLT.Mathlib then I can upstream
module

public import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.LinearAlgebra.Countable
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
import FLT.NumberField.Completion.Finite
import FLT.NumberField.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite Adele Ring

Material destined for Mathlib.
-/

@[expose] public section

/-

# The finite adele ring of a number field is locally compact.

-/
open scoped TensorProduct

universe u

open NumberField IsDedekindDomain RestrictedProduct Adele

section Instances

variable (K : Type*) [Field K] [NumberField K]

open HeightOneSpectrum

/-- `𝔸ᶠ[K]` is notation for `FiniteAdeleRing (𝓞 K) K`. -/
scoped[Adele] notation:max "𝔸ᶠ[" K "]" => 𝔸ᶠ[𝓞 K, K]
namespace IsDedekindDomain.FiniteAdeleRing

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
instance : LocallyCompactSpace 𝔸ᶠ[K] :=
  haveI : Fact (∀ (i : HeightOneSpectrum (𝓞 K)),
      IsOpen (adicCompletionIntegers K i : Set (adicCompletion K i))) :=
    ⟨isOpenAdicCompletionIntegers K⟩
  inferInstanceAs <| LocallyCompactSpace (Πʳ _, [_, _])

instance : CompactSpace (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.1 <|
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

lemma isCompact_integralAdeles : IsCompact (X := 𝔸ᶠ[K]) (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (integralAdeles (𝓞 K) K)))

instance : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (Πʳ _, [_, _])

instance : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.secondCountableTopology (isOpenAdicCompletionIntegers K)

lemma HeightOneSpectrum.nonempty {R : Type*} [CommRing R] (hR : ¬ IsField R) [Nontrivial R] :
    Nonempty (HeightOneSpectrum R) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  exact ⟨⟨I, inferInstance, by rintro rfl; exact hR (Ring.isField_iff_maximal_bot.mpr hI)⟩⟩

instance {R : Type*} [CommRing R] [Algebra.IsIntegral ℤ R] [FaithfulSMul ℤ R] :
    Nonempty (HeightOneSpectrum R) :=
  have := (FaithfulSMul.algebraMap_injective ℤ R).nontrivial
  HeightOneSpectrum.nonempty fun h ↦
    Int.not_isField
      (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R) h)

instance : Nontrivial (FiniteAdeleRing (𝓞 K) K) :=
  RingHom.domain_nontrivial (FiniteAdeleRing.evalAlgebraMap _ _
    (Nonempty.some inferInstance)).toRingHom

end IsDedekindDomain.FiniteAdeleRing

end Instances
