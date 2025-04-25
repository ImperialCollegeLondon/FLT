/-
Copyright (c) 2025 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.DirectedInverseSystem
import Mathlib.Tactic.SuppressCompilation

/-!
# Inverse limit of algebraic structures

We introduce all kinds of algebraic instances on `InverseLimit`, and specialize to the cases
of modules and rings, showing that they are indeed limits in the respective categories.
-/

suppress_compilation

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G j) (G i)] [InverseSystem (f · · ·)]
variable [IsDirected ι (· ≤ ·)]

variable (G f) in
def InverseLimit : Type _ := {x : (i : ι) → G i // ∀ i j h, f i j h (x j) = (x i)}

namespace InverseLimit

variable (i : ι) (x y z : InverseLimit G f)

instance : CoeOut (InverseLimit G f) ((i : ι) → G i) where
  coe x := x.val

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[simp]
lemma prop : ∀ (i j : _) (h : i ≤ j), f i j h (x.1 j) = x.1 i := x.2

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[ext]
lemma ext_lemma (h : ∀ i, x.1 i = y.1 i) : x = y := by
  unfold InverseLimit at *
  ext i
  exact h i

section ZeroOne

variable [Nonempty ι] [∀ i, One (G i)]

variable [∀ i j h, OneHomClass (T h) (G j) (G i)]

@[to_additive] instance instOne : One (InverseLimit G f) where
  one := ⟨fun _ ↦ 1, by simp⟩

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[to_additive (attr := simp)] theorem one_def : (1 : InverseLimit G f).1 = 1 := rfl

end ZeroOne
section AddMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)]

@[to_additive] instance : Mul (InverseLimit G f) where
  mul x y := ⟨fun (i : ι) ↦ (x.1 i) * (y.1 i), by simp⟩

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[to_additive (attr := simp)] theorem mul_def :
    (x * y).1 = (x.1 * y.1) := rfl

end AddMul

@[to_additive] instance [∀ i, CommMagma (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)] :
    CommMagma (InverseLimit G f) where
  mul_comm a b := by ext i; simp [mul_comm]

@[to_additive] instance [∀ i, Semigroup (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)] :
    Semigroup (InverseLimit G f) where
  mul_assoc a b c := by ext i; simp [mul_assoc]

@[to_additive] instance [∀ i, CommSemigroup (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)] :
    CommSemigroup (InverseLimit G f) where
  mul_comm := mul_comm

section SMul
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G j) (G i)]

@[to_additive] instance : SMul R (InverseLimit G f) where
  smul r x := ⟨fun (i : ι) ↦ (r • (x.1 i)), by simp⟩

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] in
@[to_additive (attr := simp)] theorem smul_def (r : R) : (r • x).1 = (r • x.1) := rfl

end SMul

@[to_additive] instance [Monoid R] [∀ i, MulAction R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G j) (G i)] :
    MulAction R (InverseLimit G f) where
  one_smul x := by ext i; simp
  mul_smul r x y := by ext i; simp [mul_smul]

variable [Nonempty ι]

@[to_additive] instance [∀ i, MulOneClass (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)] :
    MulOneClass (InverseLimit G f) where
  one_mul x := by ext i; simp
  mul_one x := by ext i; simp

section Monoid
variable [instMonoidG : ∀ i, Monoid (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]

@[to_additive] instance : Monoid (InverseLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  npow n x := ⟨x.1 ^ n, by simp⟩
  npow_zero x := by ext i; simp
  npow_succ n x := by ext i; simp only [Pi.pow_apply, mul_def]; exact pow_succ (x.1 i) n

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[to_additive (attr := simp)] theorem npow_def (n : ℕ) : (x ^ n).1 = (x.1 ^ n) := rfl

end Monoid

@[to_additive] instance [∀ i, CommMonoid (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)] :
    CommMonoid (InverseLimit G f) where
  mul_comm := mul_comm

section Group
variable [instGroupG : ∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]

@[to_additive] instance : Group (InverseLimit G f) where
  inv x := ⟨x⁻¹, by simp⟩
  div a b := ⟨a.1 / b.1, by simp⟩
  zpow n x := ⟨x^n, by simp⟩
  div_eq_mul_inv a b := by
    ext i
    simp only [mul_def, Pi.inv_apply]
    change (a.1 i) / (b.1 i) = _
    exact div_eq_mul_inv ..
  zpow_zero' x := by ext i; simp
  zpow_succ' n x := by
    ext i
    rw [mul_def]
    exact (instGroupG i).zpow_succ' n (x.1 i)
  zpow_neg' n x := by
    ext i
    change ((x.1 i) ^ (Int.negSucc n)) = ((x.1 i) ^ (n.succ : ℤ))⁻¹
    exact (instGroupG i).zpow_neg' n (x.1 i)
  inv_mul_cancel a := by ext i; simp

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[to_additive (attr := simp)] theorem inv_def : x⁻¹.1 = x.1⁻¹ := rfl

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[to_additive (attr := simp)] theorem div_def : (x / y).1 = (x.1 / y.1) := rfl

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[to_additive (attr := simp)] theorem zpow_def (n : ℤ) : (x ^ n).1 = (x.1 ^ n) := rfl

end Group

@[to_additive] instance [∀ i, CommGroup (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)] :
    CommGroup (InverseLimit G f) where
  mul_comm := mul_comm

instance [∀ i, MulZeroClass (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)]
    [∀ i j h, ZeroHomClass (T h) (G j) (G i)] :
    MulZeroClass (InverseLimit G f) where
  zero_mul x := by ext i; simp
  mul_zero x := by ext i; simp

section MulZeroOneClass

variable [∀ i, MulZeroOneClass (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G j) (G i)]

instance : MulZeroOneClass (InverseLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, Nontrivial (G i)] : Nontrivial (InverseLimit G f) where
  exists_pair_ne := ⟨0, 1, by
    intro h
    have hh (i) : (0 : InverseLimit G f).1 i = (1 : InverseLimit G f).1 i := by rw [h]
    simp at hh
  ⟩

end MulZeroOneClass

instance [∀ i, SemigroupWithZero (G i)] [∀ i j h, MulHomClass (T h) (G j) (G i)]
    [∀ i j h, ZeroHomClass (T h) (G j) (G i)] :
    SemigroupWithZero (InverseLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, MonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G j) (G i)] :
    MonoidWithZero (InverseLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, CommMonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G j) (G i)] :
    CommMonoidWithZero (InverseLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

section GroupWithZero

variable [instGroupWithZeroG : ∀ i, GroupWithZero (G i)]
  [∀ i j h, MonoidWithZeroHomClass (T h) (G j) (G i)]

instance : DivInvMonoid (InverseLimit G f) where
  inv x := ⟨x.1⁻¹, by simp⟩
  div x y := ⟨x.1 / y.1, by simp⟩
  zpow n x := ⟨x.1 ^ n, by simp⟩
  div_eq_mul_inv x y := by
    ext i
    change (x.1 i) / (y.1 i) = (x.1 i) * (y.1 i)⁻¹
    exact div_eq_mul_inv ..
  zpow_zero' x := by simp; rfl
  zpow_succ' n x := by
    ext i
    change (x.1 i) ^ (n.succ : ℤ) = ((x.1 i) ^ (n : ℤ)) * (x.1 i)
    exact (instGroupWithZeroG i).zpow_succ' n (x.1 i)
  zpow_neg' n x := by
    ext i
    change (x.1 i) ^ Int.negSucc n = ((x.1 i) ^ (n.succ : ℤ))⁻¹
    exact (instGroupWithZeroG i).zpow_neg' n (x.1 i)

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[simp] theorem inv₀_def : x⁻¹.1 = x.1⁻¹ := rfl

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[simp] theorem div₀_def : (x / y).1 = (x.1 / y.1) := rfl

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[simp] theorem zpow₀_def (n : ℤ) : (x ^ n).1 = (x.1 ^ n) := rfl

end GroupWithZero

instance [∀ i, CommMonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G j) (G i)] :
    CommMonoidWithZero (InverseLimit G f) where
  __ : MonoidWithZero _ := inferInstance
  mul_comm := mul_comm

section AddMonoidWithOne

variable [∀ i, AddMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G j) (G i)]
  [∀ i j h, OneHomClass (T h) (G j) (G i)]

instance : AddMonoidWithOne (InverseLimit G f) where
  natCast n := ⟨n, by
    intro i j h
    change f i j h n = n
    exact map_natCast' (f i j h) (map_one (f i j h)) n
  ⟩
  natCast_zero := by ext i; simp
  natCast_succ n := by ext i; simp
  one := ⟨1, by intros; simp⟩

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
@[simp] theorem natCast_def (n : ℕ) :
    (n : InverseLimit G f).1 = n := rfl

end AddMonoidWithOne

section AddGroupWithOne

variable [∀ i, AddGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G j) (G i)]
  [∀ i j h, OneHomClass (T h) (G j) (G i)]

instance : AddGroupWithOne (InverseLimit G f) where
  __ : AddGroup _ := inferInstance
  intCast n := ⟨fun i ↦ n, by
    intro i j h
    simp only
    exact map_intCast' (f i j h) (map_one (f i j h)) n
  ⟩
  intCast_ofNat n := by ext i; simp
  intCast_negSucc n := by ext i; simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

omit [InverseSystem fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
theorem intCast_def (n : ℤ) :
    (n : InverseLimit G f).1 i = n := rfl

end AddGroupWithOne

instance [∀ i, AddCommMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G j) (G i)]
    [∀ i j h, OneHomClass (T h) (G j) (G i)] :
    AddCommMonoidWithOne (InverseLimit G f) where
  add_comm := add_comm

instance [∀ i, AddCommGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G j) (G i)]
    [∀ i j h, OneHomClass (T h) (G j) (G i)] :
    AddCommGroupWithOne (InverseLimit G f) where
  __ : AddGroupWithOne _ := inferInstance
  add_comm := add_comm

instance [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G j) (G i)] :
    NonUnitalNonAssocSemiring (InverseLimit G f) where
  left_distrib x y z := by ext i; simp [left_distrib]
  right_distrib x y z := by ext i; simp [right_distrib]
  zero_mul := zero_mul
  mul_zero := mul_zero

instance [∀ i, NonUnitalNonAssocCommSemiring (G i)]
    [∀ i j h, NonUnitalRingHomClass (T h) (G j) (G i)] :
    NonUnitalNonAssocCommSemiring (InverseLimit G f) where
  mul_comm := mul_comm

instance [∀ i, NonUnitalSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G j) (G i)] :
    NonUnitalSemiring (InverseLimit G f) where
  mul_assoc := mul_assoc

instance [∀ i, NonUnitalCommSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G j) (G i)] :
    NonUnitalCommSemiring (InverseLimit G f) where
  mul_comm := mul_comm

instance [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] :
    NonAssocSemiring (InverseLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

-- There is no NonAssocCommSemiring

instance [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] :
    Semiring (InverseLimit G f) where
  __ : NonAssocSemiring _ := inferInstance
  __ : Monoid _ := inferInstance

instance [∀ i, CommSemiring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] :
    CommSemiring (InverseLimit G f) where
  mul_comm := mul_comm

instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] : Ring (InverseLimit G f) where
  __ : Semiring _ := inferInstance
  __ : AddCommGroupWithOne _ := inferInstance

instance [∀ i, CommRing (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] :
    CommRing (InverseLimit G f) where
  mul_comm := mul_comm

section Action

instance [∀ i, Zero (G i)] [∀ i, SMulZeroClass R (G i)]
    [∀ i j h, ZeroHomClass (T h) (G j) (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G j) (G i)] :
    SMulZeroClass R (InverseLimit G f) where
  smul_zero r := by
    ext i
    simp

instance [Zero R] [∀ i, Zero (G i)] [∀ i, SMulWithZero R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G j) (G i)]
    [∀ i j h, ZeroHomClass (T h) (G j) (G i)] :
    SMulWithZero R (InverseLimit G f) where
  zero_smul x := by
    ext i
    simp

instance [∀ i, AddZeroClass (G i)] [∀ i, DistribSMul R (G i)]
    [∀ i j h, AddMonoidHomClass (T h) (G j) (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G j) (G i)] :
    DistribSMul R (InverseLimit G f) where
  smul_add r x y := by
    ext i
    simp

instance [Monoid R] [∀ i, AddMonoid (G i)] [∀ i, DistribMulAction R (G i)]
    [∀ i j h, DistribMulActionHomClass (T h) R (G j) (G i)] :
    DistribMulAction R (InverseLimit G f) :=
  letI _ i j h : MulActionHomClass (T h) R (G j) (G i) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }

instance [Monoid R] [∀ i, Monoid (G i)] [∀ i, MulDistribMulAction R (G i)]
    [∀ i j h, MonoidHomClass (T h) (G j) (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G j) (G i)] :
    MulDistribMulAction R (InverseLimit G f) where
  smul_mul r x y := by
    ext i; simp
  smul_one r := by
    ext i; simp

instance [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G j) (G i)] :
    Module R (InverseLimit G f) :=
  letI _ i j h : DistribMulActionHomClass (T h) R (G j) (G i) := inferInstance
  {
    add_smul r s x := by ext i; simp [add_smul],
    zero_smul x := by ext i; simp
  }

end Action

section ToComponent

variable (G f) in
def toComponent (i : ι) : InverseLimit G f → G i := fun (z : InverseLimit G f) ↦ z.1 i

variable (G f) in
def toComponentₘ (i : ι) [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)] :
    InverseLimit G f →* G i where
  toFun := toComponent G f i
  map_one' := by aesop
  map_mul' := by aesop

variable (G f) in
def toComponentᵣ (i : ι) [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)] :
    InverseLimit G f →+* G i where
  toFun := toComponent G f i
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop

variable (G f) in
def toComponentₗ (i : ι) {R : Type*} [Ring R]
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)] [∀ i j h, LinearMapClass (T h) R (G j) (G i)] :
    InverseLimit G f →ₗ[R] G i where
  toFun := toComponent G f i
  map_add' := by aesop
  map_smul' := by aesop

end ToComponent

section Maps

variable {W : Type*} {M : ι → Type*} (maps : ∀ i, M i) [∀ i, FunLike (M i) W (G i)]

variable (G f) in
def InverseSystemHom := ∀ i j (h : i ≤ j) w, (f i j h) (maps j w) = maps i w

variable (inverseSystemHom : InverseSystemHom G f maps)

variable (G f) in
abbrev lift : W → InverseLimit G f :=
  fun w ↦ ⟨fun i ↦ maps i w, by
    intro i j h
    simp only
    exact inverseSystemHom i j h w
  ⟩

variable (G f) in
def liftₘ [∀ i, Group (G i)] [∀ i j h, MonoidHomClass (T h) (G j) (G i)]
    [Group W] [∀ i, MonoidHomClass (M i) W (G i)] :
    W →* InverseLimit G f where
  toFun := lift G f maps inverseSystemHom
  map_one' := by ext i; simp
  map_mul' x y := by ext i; simp

variable (G f) in
def liftᵣ [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G j) (G i)]
    [Ring W] [∀ i, RingHomClass (M i) W (G i)] :
    W →+* InverseLimit G f where
  toFun := lift G f maps inverseSystemHom
  map_one' := by ext i; simp
  map_mul' x y := by ext i; simp
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

variable (G f) in
def liftₗ {R : Type*} [Ring R]
    [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)] [∀ i j h, LinearMapClass (T h) R (G j) (G i)]
    [AddCommGroup W] [Module R W] [∀ i, LinearMapClass (M i) R W (G i)] :
    W →ₗ[R] InverseLimit G f where
  toFun := lift G f maps inverseSystemHom
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

end Maps

end InverseLimit
