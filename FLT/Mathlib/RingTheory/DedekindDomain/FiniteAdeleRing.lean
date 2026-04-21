module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The integral adele subring inside the finite adele ring. -/
noncomputable abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
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
The K-algebra map `𝔸_K^f → Kᵥ` from the finite adele ring of K to a completion.
-/
noncomputable def evalAlgebraMap (j : HeightOneSpectrum R) :
    FiniteAdeleRing R K →ₐ[K] j.adicCompletion K := {
  __ := RestrictedProduct.evalContinuousAddMonoidHom _ j
  map_one' := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
    }

/--
The continuous K-algebra map `𝔸_K^f → Kᵥ` from the finite adele ring of K to a completion.
-/
noncomputable def evalContinuousAlgebraMap (j : HeightOneSpectrum R) :
    FiniteAdeleRing R K →A[K] j.adicCompletion K := {
  __ := RestrictedProduct.evalContinuousAddMonoidHom _ j
  __ := IsDedekindDomain.FiniteAdeleRing.evalAlgebraMap R K j
  cont := RestrictedProduct.continuous_eval j -- this should be automatic -- why is this
                                              -- field not called continuous_toFun??
    }

set_option backward.isDefEq.respectTransparency false in
variable [DecidableEq (HeightOneSpectrum R)] in
/--
The continuous K-linear inclusion Kᵥ → 𝔸_K^f from a completion to the finite K-adeles.
-/
noncomputable def singleLinearMap (j : HeightOneSpectrum R) :
    j.adicCompletion K →ₗ[K] FiniteAdeleRing R K := {
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
/--
The continuous K-linear inclusion Kᵥ → 𝔸_K^f from a completion to the finite K-adeles.
-/
noncomputable def singleMulHom (j : HeightOneSpectrum R) :
    j.adicCompletion K →ₙ* FiniteAdeleRing R K := {
  __ := RestrictedProduct.singleContinuousAddMonoidHom _ j
  map_mul' a b := by
    ext v
    change Pi.single j (a * b) v = Pi.single j a v * Pi.single j b v
    obtain rfl | h := eq_or_ne j v
    · simp
    · simp [Pi.single_eq_of_ne' h]
    }

set_option backward.isDefEq.respectTransparency false in
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
  -- this would not be necessary if this field were called `continuous_toFun` as it should be
  cont := (RestrictedProduct.singleContinuousAddMonoidHom _ j).continuous_toFun
  }

variable [DecidableEq (HeightOneSpectrum R)] in
lemma evalContinuousAlgebraMap_singleContinuousLinearMap (j : HeightOneSpectrum R)
    (xj : j.adicCompletion K) :
    (evalContinuousAlgebraMap R K j) (singleContinuousLinearMap R K j xj) = xj :=
  Pi.single_eq_same j xj

variable [DecidableEq (HeightOneSpectrum R)] in
lemma evalAlgebraMap_singleLinearMap (j : HeightOneSpectrum R)
    (xj : j.adicCompletion K) :
    (evalAlgebraMap R K j) (singleLinearMap R K j xj) = xj :=
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

set_option backward.isDefEq.respectTransparency false in
variable [DecidableEq (HeightOneSpectrum R)] in
/--
The composite `𝔸_K^f --(eval)--> Kᵥ --(single)--> 𝔸_K^f` is multiplication by
the local idempotent at v.
-/
lemma singleContinuousAlgebraMap_comp_evalContinuousLinearMap (j : HeightOneSpectrum R) :
    ((singleContinuousLinearMap R K j).comp
    (evalContinuousAlgebraMap R K j).toContinuousLinearMap).toLinearMap =
    LinearMap.lsmul (FiniteAdeleRing R K) (FiniteAdeleRing R K) (localIdempotent R K j) := by
  ext x q
  change Pi.single _ (x j) _ = Pi.single j _ q * _
  obtain rfl | h := eq_or_ne j q
  · simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne' h]

end IsDedekindDomain.FiniteAdeleRing
