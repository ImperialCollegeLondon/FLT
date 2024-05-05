import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
/-

# Example of a space of automorphic forms

-/

/-- We define the profinite completion of ℤ explicitly as compatible elements of ℤ/Nℤ for
all positive integers `N`. We declare it as a subring of `∏_{N ≥ 1} (ℤ/Nℤ)`, and then promote it
to a type. -/
abbrev ZHat : Type :=
({
  carrier := { f : Π M : ℕ+, ZMod M | ∀ (D N : ℕ+) (h : (D : ℕ) ∣ N),
    ZMod.castHom h (ZMod D) (f N) = f D },
  zero_mem' := sorry
  neg_mem' := sorry
  add_mem' := sorry
  one_mem' := sorry
  mul_mem' := sorry
} : Subring (Π n : ℕ+, ZMod n))

-- #synth CommRing ZHat -- works fine

instance : DFunLike ZHat ℕ+ (fun (N : ℕ+) ↦ ZMod N) where
  coe z := z.1
  coe_injective' M N := by simp_all

namespace ZHat

open BigOperators Nat Finset in
/-- A nonarchimedean analogue $0! + 1! + 2! + \cdots$ of $e=1/0! + 1/1! + 1/2! + \cdots$. -/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i in range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  sorry
⟩

/-- Nonarchimedean $e$ is not an integer. -/
lemma e_not_in_Int : ∀ a : ℤ, e ≠ a := sorry
-- This isn't necessary but looks true. I assume it's known?
-- I believe that in general `e` is conjectured to be transcendental, i.e. satisfies no
-- nontrivial polynomial with coefficients in `ℤ`.

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := sorry

-- LaTeX proof in the notes.
lemma multiples (N : ℕ+) (z : ZHat) : N * z = 0 ↔ z N = 0 := sorry

end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

namespace QHat

lemma canonicalForm : ∀ z : QHat, ∃ q : ℚ, ∃ z' : ZHat, z = q ⊗ₜ z' := sorry

/-
open scoped TensorProduct in
example (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
 A →+* A ⊗[R] B := by exact? -- fails
-/

-- lemma injective_Rat : Function.Injective (fun q : ℚ ↦ q ⊗ₜ 1) := sorry

-- lemma injective_ZHat : Function.Injective (fun z : ZHat ↦ 1 ⊗ₜ z) := sorry

-- Now need to gives names to these subrings and go from there.

--\begin{lemma}\label{Qhat.rat_meet_zHat} The intersection of $\Q$ and $\Zhat$ in $\Qhat$ is $\Z$.
--\end{lemma}
--\begin{proof}
--    Shouldn't be hard.
--\end{proof}

--\begin{lemma}\label{Qhat.rat_join_zHat} The sum of $\Q$ and $\Zhat$ in $\Qhat$ is $\Qhat$.
--    More precisely, every elemenet of $\Qhat$ can be written as $q+z$ with $q\in\Q$ and $z\in\Zhat$,
--    or more precisely as $$q\otimes_t 1+1\otimes_t z$.
--\end{lemma}
--\begin{proof}
--    Shouldn't be hard.
--\end{proof}

end QHat
