/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
/-

# Constructions of various "local" elements of adelic groups

For example ideles which are uniformisers at one finite place.

-/

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
  ⟨Pi.mulSingle v (v.adicCompletionUniformizer K), by
    apply Set.Finite.subset (Set.finite_singleton v)
    rw [Set.compl_subset_comm]
    intro p hp
    simp [Pi.mulSingle_eq_of_ne hp]⟩

@[simp] lemma localUniformiser_eval (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] (w : HeightOneSpectrum A) :
    localUniformiser K v w = Pi.mulSingle v (v.adicCompletionUniformizer K) w := rfl

/-- `localUniformiser v` is an idele which is 1 at all finite places except `v`, where
it is a uniformiser. -/
noncomputable def localUniformiserUnit (v : HeightOneSpectrum A)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨localUniformiser K v,
    ⟨fun i ↦ if i = v then (i.adicCompletionUniformizer K)⁻¹ else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w (hw : w ≠ v)
      simp [if_neg hw]⟩,
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp [mul_inv_cancel₀ <| HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w]
      · simp [hw],
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp [inv_mul_cancel₀ <| HeightOneSpectrum.adicCompletionUniformizer_ne_zero K w]
      · simp [hw]⟩

/-- `localUnit K α` for `α : (v.adicCompletion K)ˣ`, is the finite idele which is `α` at
`v` and `1` elsewhere. -/
noncomputable def localUnit {v : HeightOneSpectrum A} (α : (v.adicCompletion K)ˣ)
    [DecidableEq (HeightOneSpectrum A)] :
    (FiniteAdeleRing A K)ˣ :=
  ⟨⟨fun i ↦ if h : i = v then h ▸ α else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w (hw : w ≠ v)
      simp [dif_neg hw]⟩,
  ⟨fun i ↦ if h : i = v then h ▸ α⁻¹ else 1, by
      apply Set.Finite.subset (Set.finite_singleton v)
      rw [Set.compl_subset_comm]
      intro w (hw : w ≠ v)
      simp [dif_neg hw]⟩,
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp
      · simp [hw],
    by
      ext w
      obtain rfl | hw := eq_or_ne w v
      · simp
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
