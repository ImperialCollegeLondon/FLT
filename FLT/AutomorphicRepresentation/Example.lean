import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Data.Complex.Basic -- debugging
/-

# Example of a space of automorphic forms

-/

/-- We define the profinite completion of ℤ explicitly as compatible elements of ℤ/Nℤ for
all positive integers `N`. We declare it as a subring of `∏_{N ≥ 1} (ℤ/Nℤ)`, and then promote it
to a type. -/
def ZHat : Type := {
  carrier := { f : Π M : ℕ+, ZMod M | ∀ (D N : ℕ+) (h : (D : ℕ) ∣ N),
    ZMod.castHom h (ZMod D) (f N) = f D },
  zero_mem' := sorry
  neg_mem' := sorry
  add_mem' := sorry
  one_mem' := sorry
  mul_mem' := sorry
  : Subring (Π n : ℕ+, ZMod n)}
deriving CommRing

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
lemma multiples (N : ℕ+) (z : ZHat) : N * z = 0 ↔ z N = 0 := sorry

end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

noncomputable example : QHat := (22 / 7) ⊗ₜ ZHat.e

namespace QHat

lemma canonicalForm : ∀ z : QHat, ∃ N : ℕ+, ∃ z' : ZHat, z = (1 / N : ℚ) ⊗ₜ z' := sorry

def IsCoprime (N : ℕ+) (z : ZHat) : Prop := IsUnit (z N)

lemma lowestTerms (x : QHat) : (∃ N z, IsCoprime N z ∧ x = (1 / N : ℚ) ⊗ₜ z) ∧
    (∀ N₁ N₂ z₁ z₂,
    IsCoprime N₁ z₁ ∧ IsCoprime N₂ z₂ ∧ (1 / N₁ : ℚ) ⊗ₜ z₁ = (1 / N₂ : ℚ) ⊗ₜ[ℤ] z₂ →
      N₁ = N₂ ∧ z₁ = z₂) := sorry

noncomputable abbrev i₁ : ℚ →ₐ[ℤ] QHat := Algebra.TensorProduct.includeLeft
lemma injective_rat :
    Function.Injective i₁ := sorry -- flatness

noncomputable abbrev i₂ : ZHat →ₐ[ℤ] QHat := Algebra.TensorProduct.includeRight
lemma injective_zHat :
    Function.Injective i₂ := sorry -- flatness

section additive_structure_of_QHat

noncomputable abbrev ratsub : AddSubgroup QHat :=
    (i₁ : ℚ →+ QHat).range

noncomputable abbrev zHatsub : AddSubgroup QHat :=
    (i₂ : ZHat →+ QHat).range

noncomputable abbrev zsub : AddSubgroup QHat :=
  (Int.castRingHom QHat : ℤ →+ QHat).range

lemma rat_meet_zHat : ratsub ⊓ zHatsub = zsub := sorry

lemma rat_join_zHat : ratsub ⊔ Zhatsub = ⊤ := sorry

end additive_structure_of_QHat

end QHat
