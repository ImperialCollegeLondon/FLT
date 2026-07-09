/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Elements of a quadratic field extension

Proposed new Mathlib file `Mathlib.LinearAlgebra.Dimension.IsQuadraticExtension`: basic
lemmas about elements of a quadratic extension lying outside the base field.
-/

@[expose] public section

section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- `1` and any element lying outside the base field are linearly independent over the base
field. -/
theorem linearIndependent_one_of_notMem_range_algebraMap {θ : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] :=
  (LinearIndependent.pair_iff' one_ne_zero).mpr fun a ha ↦
    hθ ⟨a, by rwa [Algebra.algebraMap_eq_smul_one]⟩

variable [Algebra.IsQuadraticExtension K L]

/-- A quadratic extension contains an element not in the base field. (Used to choose a
generator of `L/K` in the definition of the quadratic twist below.) -/
theorem Algebra.IsQuadraticExtension.exists_notMem_range_algebraMap :
    ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
  by_contra! h
  have hbot : (⊥ : Subalgebra K L) = ⊤ :=
    Algebra.eq_top_iff.mpr fun x ↦ Algebra.mem_bot.mpr (h x)
  have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
  have h2 := finrank_eq_two K L
  lia

/-- Any element of a quadratic extension `L/K` is a `K`-linear combination of `1` and a given
generator `θ`, and the `θ`-coefficient is nonzero if the element also lies outside `K`. -/
theorem Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul {θ θ' : L}
    (hθ : θ ∉ Set.range (algebraMap K L)) (hθ' : θ' ∉ Set.range (algebraMap K L)) :
    ∃ a b : K, a ≠ 0 ∧ θ' = algebraMap K L b + algebraMap K L a * θ := by
  have hli := linearIndependent_one_of_notMem_range_algebraMap K L hθ
  have hmem : θ' ∈ Submodule.span K (Set.range ![(1 : L), θ]) := by
    rw [hli.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin]; exact (finrank_eq_two K L).symm)]
    trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hmem
  obtain ⟨c, d, hcd⟩ := hmem
  refine ⟨d, c, fun hd ↦ hθ' ⟨c, ?_⟩, ?_⟩
  · rw [← hcd, hd, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]
  · rw [← hcd, Algebra.smul_def, Algebra.smul_def, mul_one]

end

section

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

/-- An element whose square is (the image of) a nonsquare of `K` lies outside `K`. -/
lemma notMem_range_algebraMap_of_not_isSquare {d : K} (hd : ¬IsSquare d) {α : L}
    (hα : α ^ 2 = algebraMap K L d) : α ∉ Set.range (algebraMap K L) := by
  rintro ⟨c, rfl⟩
  refine hd ⟨c, FaithfulSMul.algebraMap_injective K L ?_⟩
  rw [map_mul, ← sq]
  exact hα.symm

end

end
