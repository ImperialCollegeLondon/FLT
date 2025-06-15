/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.Topology.Algebra.RestrictedProduct -- needed for RestrictedProduct.mk
/-

# Constructions of various "local" elements of adelic groups

For example ideles which are uniformisers at one finite place.

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

end HeightOneSpectrum

namespace FiniteAdeleRing

/-- `localUniformiser v` is an adele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiser (v : HeightOneSpectrum A) [DecidableEq (HeightOneSpectrum A)] :
    FiniteAdeleRing A K :=
  ⟨fun i ↦ if i = v then i.adicCompletionUniformizer K else 1, by
    apply Set.Finite.subset (Set.finite_singleton v)
    simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    intro w hw
    contrapose! hw
    rw [if_neg hw]
    exact ValuationSubring.one_mem (HeightOneSpectrum.adicCompletionIntegers K w)⟩

@[simp] lemma localUniformiser_eval (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) :
    localUniformiser K v w = if w = v then w.adicCompletionUniformizer K else 1 := rfl

/-- `localUniformiser v` is an idele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiserUnit (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨localUniformiser K v,
    ⟨fun i ↦ if i = v then (i.adicCompletionUniformizer K)⁻¹ else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro w hw
      contrapose! hw
      rw [if_neg hw]
      exact ValuationSubring.one_mem (HeightOneSpectrum.adicCompletionIntegers K w)⟩,
    by
      ext w
      by_cases hw : w = v
      · simp only [RestrictedProduct.mul_apply, localUniformiser_eval, hw, ↓reduceIte,
        RestrictedProduct.mk_apply, RestrictedProduct.one_apply]
        apply mul_inv_cancel₀
        exact HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w
      · simp [hw],
    by
      ext w
      by_cases hw : w = v
      · simp only [RestrictedProduct.mul_apply, localUniformiser_eval, hw, ↓reduceIte,
        RestrictedProduct.mk_apply, RestrictedProduct.one_apply]
        apply inv_mul_cancel₀
        exact HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w
      · simp [hw]⟩

-- these should not be in a file called Matrix
/-- `localUnit K α` for `α : (v.adicCompletion K)ˣ`, is the finite idele which is `α` at
`v` and `1` elsewhere. -/
noncomputable def localUnit {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨⟨fun i ↦ if h : i = v then h ▸ α else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro w hw
      contrapose! hw
      rw [dif_neg hw]
      exact ValuationSubring.one_mem (HeightOneSpectrum.adicCompletionIntegers K w)⟩,
  ⟨fun i ↦ if h : i = v then h ▸ α⁻¹ else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      simp only [SetLike.mem_coe, Set.subset_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
      intro w hw
      contrapose! hw
      rw [dif_neg hw]
      exact ValuationSubring.one_mem (HeightOneSpectrum.adicCompletionIntegers K w)⟩,
    by
      ext w
      by_cases hw : w = v
      · subst hw
        simp
      · simp [hw],
    by
      ext w
      by_cases hw : w = v
      · subst hw
        simp
      · simp [hw]⟩

lemma localUnit_eval_of_eq {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (localUnit K α).1 v = α := by
  simp [localUnit]

lemma localUnit_eval_of_ne {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) (hw : w ≠ v) :
    (localUnit K α).1 w = 1 := by
  simp [localUnit, hw]

end FiniteAdeleRing

end IsDedekindDomain
