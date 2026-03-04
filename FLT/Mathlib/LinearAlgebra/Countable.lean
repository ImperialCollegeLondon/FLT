import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Rat.Encodable

-- TODO upstream
lemma Countable.of_module_finite (R M : Type*) [Semiring R] [Countable R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  Countable.of_module_finite ℚ K
