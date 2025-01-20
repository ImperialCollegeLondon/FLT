import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Fintype.Option

theorem LinearMap.finsum_apply {R : Type*} [Semiring R] {A B : Type*} [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] {ι : Type*} [Finite ι] (φ : ∀ _ : ι, A →ₗ[R] B) (a : A) :
    (∑ᶠ i, φ i) a = ∑ᶠ i, φ i a := by
  induction ι using Finite.induction_empty_option
  · case of_equiv X Y e hx =>
    convert hx (φ ∘ e)
    · exact (finsum_comp_equiv e).symm
    · exact (finsum_comp_equiv e).symm
  · simp [finsum_of_isEmpty]
  · case h_option X _ hX =>
    rw [finsum_option (Set.toFinite _), finsum_option (Set.toFinite _)]
    simp [hX]
