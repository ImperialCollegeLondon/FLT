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
/--
The continuous K-algebra map `𝔸_K^f → Kᵥ` from the finite adele ring of K to a completion.
-/
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
/--
The continuous K-linear inclusion Kᵥ → 𝔸_K^f from a completion to the finite K-adeles.
-/
noncomputable def singleContinuousLinearMap (j : HeightOneSpectrum R) :
    j.adicCompletion K →L[K] FiniteAdeleRing R K := {
  __ := RestrictedProduct.singleContinuousAddMonoidHom _ j
  map_smul' k x := by
    open RestrictedProduct in
    ext i
    change Pi.single j (k • x) i = _
    obtain rfl | h := eq_or_ne i j
    · simp [Pi.single_eq_same, -mul_eq_mul_right_iff, FiniteAdeleRing, Algebra.smul_def,
        singleContinuousAddMonoidHom_apply_same]
      rfl -- (annoying)
    · simp [Pi.single_eq_of_ne h, FiniteAdeleRing, Algebra.smul_def,
        singleContinuousAddMonoidHom_apply_of_ne _ h _]
    }

variable [DecidableEq (HeightOneSpectrum R)] in
lemma evalContinuousAlgebraMap_singleContinuousLinearMap (j : HeightOneSpectrum R)
    (xj : j.adicCompletion K) :
    (evalContinuousAlgebraMap R K j) (singleContinuousLinearMap R K j xj) = xj :=
  Pi.single_eq_same j xj

variable [DecidableEq (HeightOneSpectrum R)] in
/--
`localIdempotent R K p` is the finite adele which is 1 at p and 0 elsewhere.
-/
noncomputable def localIdempotent (p : HeightOneSpectrum R) : FiniteAdeleRing R K :=
  ⟨Pi.single p 1, by
    apply Set.Finite.subset (Set.finite_singleton p)
    rw [Set.compl_subset_comm]
    intro q hq
    simp [Pi.single_eq_of_ne hq]⟩

variable [DecidableEq (HeightOneSpectrum R)] in
lemma eval_localIdempotent (p : HeightOneSpectrum R) :
    (evalContinuousAlgebraMap R K p) (localIdempotent R K p) = 1 :=
  Pi.single_eq_same _ _

end IsDedekindDomain.FiniteAdeleRing
