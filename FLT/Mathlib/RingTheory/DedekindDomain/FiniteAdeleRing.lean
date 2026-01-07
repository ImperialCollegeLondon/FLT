import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The integral adele subring inside the finite adele ring. -/
abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _

variable {R K}

@[simp] lemma one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

@[simp] lemma mul_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl

/-- Constructor for `FiniteAdeleRing R K`. An `abbrev`. -/
abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : FiniteAdeleRing R K :=
  ⟨f, h⟩

@[simp]
lemma mk_apply (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) (v : HeightOneSpectrum R) :
    mk f h v = f v := rfl

variable (R K)
def evalContinuousAlgebraMap (j : HeightOneSpectrum R) :
    FiniteAdeleRing R K →A[K] j.adicCompletion K := {
  __ := RestrictedProduct.evalContinuousAddMonoidHom _ j
  map_one' := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  cont := RestrictedProduct.continuous_eval j -- this should be automatic -- why is this
                                              -- field not called continuous_toFun??
    }

variable [DecidableEq (HeightOneSpectrum R)] in
noncomputable def singleContinuousLinearMap (j : HeightOneSpectrum R) :
    j.adicCompletion K →L[K] FiniteAdeleRing R K := {
  __ := RestrictedProduct.singleContinuousAddMonoidHom _ j
  map_smul' k x := by
    open RestrictedProduct in
    ext i; by_cases! h : i = j <;> conv_lhs => change singleContinuousAddMonoidHom _ j (k • x) i
    · rw [h, singleContinuousAddMonoidHom_apply_same]
      simp [-mul_eq_mul_right_iff, FiniteAdeleRing, Algebra.smul_def,
        singleContinuousAddMonoidHom_apply_same]
      rfl -- this can probably be avoided but it works for now..
    · rw [singleContinuousAddMonoidHom_apply_of_ne _ h _]
      simp [FiniteAdeleRing, Algebra.smul_def, singleContinuousAddMonoidHom_apply_of_ne _ h _]
    }

variable [DecidableEq (HeightOneSpectrum R)] in
lemma evalContinuousAlgebraMap_singleContinuousLinearMap (j : HeightOneSpectrum R)
    (xj : j.adicCompletion K) :
    (evalContinuousAlgebraMap R K j) (singleContinuousLinearMap R K j xj) = xj :=
  Pi.single_eq_same j xj
end IsDedekindDomain.FiniteAdeleRing
