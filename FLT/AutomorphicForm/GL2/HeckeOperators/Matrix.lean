import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
/-

# Matrix-related stuff for Hecke operators for adelic GL_2

-/

-- should be elsewhere
namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- The invertible diagonal matrix associated to a vector of units (the diagonal entries).
-/
def diagonal (d : n → Rˣ) : GL n R :=
  ⟨.diagonal <| fun i ↦ d i, .diagonal <| fun i ↦ ((d i)⁻¹ : Rˣ),
    by simp, by simp⟩

end Matrix.GeneralLinearGroup

namespace IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K]

namespace HeightOneSpectrum

/-- A uniformiser associated to `v` in the integers of the completion `Kᵥ`. -/
noncomputable def adicCompletionIntegersUniformizer (v : HeightOneSpectrum A) :
    v.adicCompletionIntegers K :=
  algebraMap A (v.adicCompletionIntegers K) v.intValuation_exists_uniformizer.choose

/-- A uniformiser associated to `v` in the completion `Kᵥ`. -/
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

/-- A uniformiser associated to `v` in the units of the completion `Kᵥ`. -/
noncomputable def adicCompletionUniformizerUnit (v : HeightOneSpectrum A) :
    (v.adicCompletion K)ˣ :=
  .mk0 (v.adicCompletionUniformizer K) <| v.adicCompletionUniformizer_ne_zero K

-- /--
-- The diagonal matrix `(ϖ 0; 0 1)` as a 2x2 matrix in `M_2(𝓞ᵥ)`. Do we even want this?
-- -/
-- noncomputable def pi_zero_zero_one_int (v : HeightOneSpectrum A) :
--     Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) :=
--   .diagonal
--   ![algebraMap A (v.adicCompletionIntegers K) v.intValuation_exists_uniformizer.choose, 1]

-- noncomputable def pi_zero_zero_one (v : HeightOneSpectrum A) :
--     GL (Fin 2) (v.adicCompletion K) :=
--   .diagonal
--   ![.mk0 (v.adicCompletionUniformizer K) <| v.adicCompletionUniformizer_ne_zero K, 1]

end HeightOneSpectrum

namespace FiniteAdeleRing

/-- `localUniformiser v` is an adele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiser (v : HeightOneSpectrum A) [DecidableEq (HeightOneSpectrum A)] :
    FiniteAdeleRing A K :=
  ⟨fun i ↦ if i = v then i.adicCompletionUniformizer K else 1, sorry⟩

/-- `localUniformiser v` is an idele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiserUnit (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨localUniformiser K v,
    ⟨fun i ↦ if i = v then (i.adicCompletionUniformizer K)⁻¹ else 1, sorry⟩,
    sorry,
    sorry⟩

-- these should not be in a file called Matrix
noncomputable def localUnit {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨⟨fun i ↦ if h : i = v then h ▸ α else 1, sorry⟩,
  ⟨fun i ↦ if h : i = v then h ▸ α⁻¹ else 1, sorry⟩,
  sorry,
  sorry⟩

lemma localUnit_eval_of_eq {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (localUnit K α).1 v = α := by
  simp [localUnit]

lemma localUnit_eval_of_ne {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) (hw : w ≠ v) :
    (localUnit K α).1 w = 1 := by
  simp [localUnit, hw]
