import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Pi

@[to_additive]
lemma finprod_option {ι : Type*} {B : Type*} [Finite ι] [CommMonoid B] (φ : Option ι → B) :
    (∏ᶠ oi, φ oi) = φ none * ∏ᶠ (j : ι),  φ (some j) := by
  rw [← finprod_mem_univ]
  convert finprod_mem_insert φ (show none ∉ Set.range Option.some by aesop)
    (Set.finite_range some)
  · exact (Set.insert_none_range_some ι).symm
  · rw [finprod_mem_range]
    exact Option.some_injective ι

@[to_additive]
lemma finprod_apply {α ι N : Type*} [CommMonoid N] [Finite ι] (f : ι → α → N) (a : α) :
    (∏ᶠ i, f i) a = ∏ᶠ i, (f i) a := by
  classical
  simp only [finprod_def, dif_pos (Set.toFinite _), Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop
