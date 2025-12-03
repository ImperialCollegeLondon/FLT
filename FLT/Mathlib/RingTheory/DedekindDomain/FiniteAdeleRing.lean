import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The integral adele subring inside the finite adele ring. -/
abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _

section for_mathlib

variable {R K}

@[simp] lemma one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

@[simp] lemma mul_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : FiniteAdeleRing R K :=
  ⟨f, h⟩

@[simp]
lemma mk_apply (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) (v : HeightOneSpectrum R) :
    mk f h v = f v := rfl

end for_mathlib

end IsDedekindDomain.FiniteAdeleRing
