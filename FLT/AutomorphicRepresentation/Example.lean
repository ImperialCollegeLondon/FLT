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

namespace ZHat

instance : DFunLike ZHat ℕ+ (fun (N : ℕ+) ↦ ZMod N) where
  coe z := z.1
  coe_injective' M N := by simp_all

@[simp] lemma zero_val : (0 : ZHat) n = 0 := rfl
@[simp] lemma one_val : (1 : ZHat) n = 1 := rfl

instance commRing : CommRing ZHat := inferInstance

--wooah, `import Mathlib` breaks this. TODO test this again after bump to Lean v4.8
lemma zeroNeOne : (0 : ZHat) ≠ 1 := by
  intro h
  have h2 : (0 : ZHat) 2 = (1 : ZHat) 2 := by simp [h]
  rw [zero_val, one_val] at h2
  revert h2 ; decide

instance nontrivial : Nontrivial ZHat := ⟨0, 1, zeroNeOne⟩

instance charZero : CharZero ZHat := ⟨ fun a b h ↦ by
  sorry
  ⟩
--lemma NonAssocSemiring.Nontrivial_iff (R : Type) [NonAssocSemiring R] :
--    Nontrivial R ↔ (0 : R) ≠ 1 :=
--  ⟨fun _ ↦ zero_ne_one' R, fun a ↦ ⟨0, 1, a⟩⟩

open BigOperators Nat Finset in
/-- A nonarchimedean analogue $0! + 1! + 2! + \cdots$ of $e=1/0! + 1/1! + 1/2! + \cdots$. -/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i in range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  sorry
⟩

open BigOperators Nat Finset in
lemma e_def (n : ℕ+) : e n = ∑ i in range (n : ℕ), (i ! : ZMod n) := rfl

/-- Nonarchimedean $e$ is not an integer. -/
lemma e_not_in_Int : ∀ a : ℤ, e ≠ a := sorry
-- This isn't necessary but looks true. I assume it's known?
-- I believe that in general `e` is conjectured to be transcendental, i.e. satisfies no
-- nontrivial polynomial with coefficients in `ℤ`.

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := sorry

-- LaTeX proof in the notes.
lemma multiples (N : ℕ+) (z : ZHat) : (∃ (y : ZHat), N * y = z) ↔ z N = 0 := by
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    change N * (y N) = 0
    simp [ZMod.natCast_self]
  · intro h
    let y : ZHat := {
      val := fun j ↦ (by
        let yj_preimage := z (N * j)
        have hh := z.2 N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
        have : z.val N = 0 := h
        rw [this] at hh
        -- use `hh` to conclude that `yj_preimage/N` makes sense as an element of `ZMod j`.
        -- This is the `y j` we want.
        sorry)
      property := sorry
        -- `y` is compatible
    }
    refine ⟨y, ?_⟩
    ext j
    have hh := z.2 j (N * j) (by simp only [PNat.mul_coe, dvd_mul_left])
    rw [← hh]
    sorry -- This should be easy once `y` is defined.

end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

noncomputable example : QHat := (22 / 7) ⊗ₜ ZHat.e

namespace QHat

lemma canonicalForm : ∀ z : QHat, ∃ q : ℚ, ∃ z' : ZHat, z = q ⊗ₜ z' := sorry

open scoped TensorProduct in
noncomputable example (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] :
 A →+* A ⊗[R] B := by exact Algebra.TensorProduct.includeLeftRingHom -- fails

lemma injective_rat :
    Function.Injective (Algebra.TensorProduct.includeLeft : ℚ →ₐ[ℤ] QHat) := sorry

lemma injective_zHat :
    Function.Injective (Algebra.TensorProduct.includeRight : ZHat →ₐ[ℤ] QHat) := sorry

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
