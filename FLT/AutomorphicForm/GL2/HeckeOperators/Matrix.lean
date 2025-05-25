import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
/-

# Matrix-related stuff for Hecke operators for adelic GL_2

-/

-- should be elsewhere
namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

def diagonal (d : n → Rˣ) : GL n R :=
  ⟨.diagonal <| fun i ↦ d i, .diagonal <| fun i ↦ ((d i)⁻¹ : Rˣ),
    by simp, by simp⟩

end Matrix.GeneralLinearGroup

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K]

noncomputable def adicCompletionIntegersUniformizer (v : HeightOneSpectrum A) :
    v.adicCompletionIntegers K :=
  algebraMap A (v.adicCompletionIntegers K) v.intValuation_exists_uniformizer.choose

noncomputable def adicCompletionUniformizer (v : HeightOneSpectrum A) :
    v.adicCompletion K :=
  algebraMap K (v.adicCompletion K) (v.valuation_exists_uniformizer K).choose

lemma adicCompletionUniformizer_spec (v : HeightOneSpectrum A) :
    Valued.v (v.adicCompletionUniformizer K) = (Multiplicative.ofAdd (-1 : ℤ)) := by
  let u := (v.valuation_exists_uniformizer K).choose
  have h : (valuation K v) u = (Multiplicative.ofAdd (-1 : ℤ)) :=
    (v.valuation_exists_uniformizer K).choose_spec
  rwa [← valuedAdicCompletion_eq_valuation' v u] at h

lemma adicCompletionUniformizer_ne_zero (v : HeightOneSpectrum A) :
    v.adicCompletionUniformizer K ≠ 0 := by
  intro h
  apply_fun Valued.v at h
  rw [adicCompletionUniformizer_spec] at h
  simp at h

/--
The diagonal matrix `(ϖ 0; 0 1)` as a 2x2 matrix in `M_2(𝓞ᵥ)`. Do we even want this?
-/
noncomputable def pi_zero_zero_one_int (v : HeightOneSpectrum A) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) :=
  .diagonal
  ![algebraMap A (v.adicCompletionIntegers K) v.intValuation_exists_uniformizer.choose, 1]

noncomputable def pi_zero_zero_one (v : HeightOneSpectrum A) :
    GL (Fin 2) (v.adicCompletion K) :=
  .diagonal
  ![.mk0 (v.adicCompletionUniformizer K) <| v.adicCompletionUniformizer_ne_zero K, 1]
