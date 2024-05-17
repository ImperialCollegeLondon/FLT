import Mathlib.RingTheory.Congruence
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic.Abel

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)
variable {R : Type*} [Ring R] (t : RingCon R)

open BigOperators

namespace AddCon

variable {r s}

lemma sum {f g : ι → M} (h : ∀ i ∈ s, r (f i) (g i)) :
    r (∑ i in s, f i) (∑ i in s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r.refl 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact r.add (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)

end AddCon

namespace RingCon

variable {t s}

lemma sum {f g : ι → R} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (∑ i in s, f i) (∑ i in s, g i) :=
  t.toAddCon.sum h

variable (t)

lemma sub {a b c d : R} (h : t a b) (h' : t c d) : t (a - c) (b - d) :=
  t.toAddCon.sub h h'

lemma neg {a b} (h : t a b) : t (-a) (-b) := t.toAddCon.neg h

instance : SetLike (RingCon R) R where
  coe t := {r | t r 0}
  coe_injective' t₁ t₂ (h : {x | _} = {x | _}) := by
    refine RingCon.ext fun a b ↦ ⟨fun H ↦ ?_, fun H ↦ ?_⟩
    · have H' : a - b ∈ {x | t₁ x 0} := sub_self b ▸  t₁.sub H (t₁.refl b)
      rw [h] at H'
      convert t₂.add H' (t₂.refl b) using 1 <;> abel
    · have H' : a - b ∈ {x | t₂ x 0} := sub_self b ▸  t₂.sub H (t₂.refl b)
      rw [← h] at H'
      convert t₁.add H' (t₁.refl b) using 1 <;> abel

variable (I : RingCon R)

lemma zero_mem : 0 ∈ I := I.refl 0

lemma add_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := by
  simpa using I.add hx hy

lemma neg_mem {x} (hx : x ∈ I) : -x ∈ I := by
  simpa using I.neg hx

lemma sub_mem {x y} (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I := by
  convert I.add_mem hx (I.neg_mem hy) using 1; abel

lemma mul_mem_left (x y) (hy : y ∈ I) : x * y ∈ I := by
  simpa using I.mul (I.refl x) hy

lemma mul_mem_right (x y) (hx : x ∈ I) : x * y ∈ I := by
  simpa using I.mul hx (I.refl y)

instance : AddCommGroup I where
  add x y := ⟨x.1 + y.1, I.add_mem x.2 y.2⟩
  add_assoc x y z := by
    ext; show x.1 + y.1 + z.1 = x.1 + (y.1 + z.1); abel
  zero := ⟨0, I.zero_mem⟩
  zero_add x := by
    ext; show 0 + x.1 = x.1; abel
  add_zero x := by
    ext; show x.1 + 0 = x.1; abel
  nsmul n x := ⟨n • x.1, n.rec (by simpa using I.zero_mem) fun n hn ↦ by
    simpa only [Nat.succ_eq_add_one, add_smul, one_smul] using I.add_mem hn x.2⟩
  nsmul_zero x := by
    ext; show 0 • x.1 = 0; simp
  nsmul_succ n x := by
    ext; show (n + 1) • x.1 = n • x.1 + x.1; simp [add_mul]
  neg x := ⟨-x.1, I.neg_mem x.2⟩
  sub x y := ⟨x.1 - y.1, I.sub_mem x.2 y.2⟩
  sub_eq_add_neg x y := by
    ext; show x.1 - y.1 = x.1 + -y.1; abel
  zsmul n x := ⟨n • x.1, n.rec (fun a ↦ a.rec (by simpa using I.zero_mem)
    (fun a ha ↦ by
      simp only [Nat.succ_eq_add_one, Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one,
        Int.cast_add, Int.cast_natCast, Int.cast_one, add_smul, one_smul]
      exact I.add_mem ha x.2))
    (fun a ↦ a.rec (by simpa using I.neg_mem x.2)
    (fun a ha ↦ by
      simp only [Nat.succ_eq_add_one, negSucc_zsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, neg_add_rev] at ha ⊢
      exact I.add_mem (I.neg_mem x.2) ha))⟩
  zsmul_zero' x := by
    ext; show 0 • x.1 = 0; simp
  zsmul_succ' n x := by
    ext; show ((n : ℤ) + 1) • x.1 = (n : ℤ) • x.1 + x; simp [add_mul]
  zsmul_neg' n x := by
    ext; show _ • x.1 = - (_ • x.1); simp [add_mul]
  add_left_neg x := by
    ext; show (-x.1) + x = 0; abel
  add_comm x y := by
    ext; show x.1 + y.1 = y.1 + x.1; abel

instance : Module R I where
  smul r x := ⟨r * x.1, I.mul_mem_left _ _ x.2⟩
  one_smul x := by ext; show 1 * x.1 = x.1; simp
  mul_smul x y z := by
    ext; show (x * y) * z.1 = x * (y * z.1); simp [mul_assoc]
  smul_zero x := by
    ext; show x * 0 = 0; simp
  smul_add x y z := by
    ext; show x • (y.1 + z.1) = x • y.1 + x • z.1; simp [mul_add]
  add_smul x y z := by
    ext; show (x + y) • z.1 = x • z.1 + y • z.1; simp [add_mul]
  zero_smul x := by
    ext; show 0 * x.1 = 0; simp

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; show x.1 * 1 = x.1; simp
  mul_smul x y z := by
    ext; show z.1 * (y.unop * x.unop) = (z.1 * y.unop) * x.unop; simp [mul_assoc]
  smul_zero x := by sorry
  smul_add x y z := by sorry
  add_smul x y z := by sorry
  zero_smul x := by sorry

end RingCon
