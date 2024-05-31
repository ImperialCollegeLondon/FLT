import Mathlib.Tactic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Algebraic

def div_contain_root_is_field (D : Type*) [Ring D] [DivisionRing D]
    (p : ℕ) [CharP D p](h : ∀ (a : D), ∃ (m : ℕ), (a ^ p ^ m) ∈ Subring.center D) :
    IsField D where
  exists_pair_ne := sorry
  mul_comm := sorry
  mul_inv_cancel := sorry

abbrev p_radical_extension (K E: Type*) [Field K] [DivisionRing E] [Algebra K E] (p : ℕ) [CharP K p]
    (_ : p.Prime) := ∀(x : E), ∃(m : ℕ), x ^ p ^ m ∈ (Algebra.ofId K E).range


lemma findim_divring_over_sep_closed (K : Type*) (D : Type*) [Field K]
    [IsSepClosed K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (p : ℕ) (hp : p.Prime) [CharP K p]:
    ∀(x y : D), x * y = y * x := by
  have alg_ext: ∀(d : D), IsAlgebraic K d := sorry
  have p_rad : p_radical_extension K D p hp := by
    intro d ; let f := minpoly K d

    sorry
  sorry
