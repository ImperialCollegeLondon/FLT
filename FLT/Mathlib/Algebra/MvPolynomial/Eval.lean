import Mathlib.Algebra.MvPolynomial.Eval

@[simp]
lemma MvPolynomial.eval₂_of_smul_algebraMap {σ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  (g : σ → S) (F : MvPolynomial σ R) (x : R) :
    (x • F).eval₂ (algebraMap R S) g = x • (F.eval₂ (algebraMap R S) g) := by
  sorry
