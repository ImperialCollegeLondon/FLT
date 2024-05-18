import Mathlib.RingTheory.Congruence
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

variable {M : Type*} [AddCommMonoid M] (r : AddCon M) {ι : Type*} (s : Finset ι)
variable {R : Type*} [Ring R] (t : RingCon R)

open BigOperators MulOpposite

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

/--
An alternative constructor for `RingCon`, making it obvious that we are view it as a
two-sided-ideal.
-/
@[simps]
def fromIdeal
    (carrier : Set R)
    (zero : 0 ∈ carrier)
    (add : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
    (neg : ∀ a, a ∈ carrier → -a ∈ carrier)
    (left_absorb : ∀ a b, b ∈ carrier → a * b ∈ carrier)
    (right_absorb : ∀ a b, a ∈ carrier → a * b ∈ carrier) : RingCon R where
  r a b := a - b ∈ carrier
  iseqv :=
  { refl := fun a ↦ by simpa
    symm := fun {x y} h ↦ by
      simpa only [show y - x = -(x - y) by abel] using neg _ h
    trans := fun {a b c } h1 h2 ↦ by
      simpa only [show a - c = (a - b) + (b - c) by abel] using add _ _ h1 h2 }
  mul' {a b c d} h1 h2 := show _ - _ ∈ _ by
    change a * c - b * d ∈ carrier
    rw [show a * c - b * d = (a - b) * c + b * (c - d) by
      rw [sub_mul, mul_sub]; aesop]
    exact add _ _ (right_absorb _ _ h1) (left_absorb _ _ h2)
  add' {a b c d} h1 h2 := by
    change (a + c) - (b + d) ∈ carrier
    rw [show (a + c) - (b + d) = (a - b) + (c - d) by abel]
    exact add _ _ h1 h2

@[simp] lemma mem_fromIdeal
    (carrier : Set R)
    (zero : 0 ∈ carrier)
    (add : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
    (neg : ∀ a, a ∈ carrier → -a ∈ carrier)
    (left_absorb : ∀ a b, b ∈ carrier → a * b ∈ carrier)
    (right_absorb : ∀ a b, a ∈ carrier → a * b ∈ carrier)
    (x) :
    x ∈ fromIdeal carrier zero add neg left_absorb right_absorb ↔ x ∈ carrier := by
  simp only [fromIdeal]
  change _ ∈ carrier ↔ _
  rw [sub_zero]

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

lemma sum_mem (f : ι → R) (h : ∀ i ∈ s, f i ∈ I) : ∑ i in s, f i ∈ I := by
  simpa using I.sum h

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

/--
For any `RingCon R`, when we view it as an ideal, `subtype` is the injective linear map.
-/
@[simps]
def subtype : I →ₗ[R] R where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
For any `RingCon R`, when we view it as an ideal in `Rᵒᵖ`, `subtype` is the injective linear map.
-/
@[simps]
def subtypeMop : I →ₗ[R] Rᵐᵒᵖ where
  toFun x := MulOpposite.op x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
Any two-sided-ideal in `A` corresponds to a two-sided-ideal in `Aᵒᵖ`.
-/
@[simps]
def toMop (rel : RingCon R) : (RingCon Rᵐᵒᵖ) :=
{ r := fun a b ↦ rel b.unop a.unop
  iseqv :=
  { refl := fun a ↦ rel.refl a.unop
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

/--
Any two-sided-ideal in `Aᵒᵖ` corresponds to a two-sided-ideal in `A`.
-/
@[simps]
def fromMop (rel : RingCon Rᵐᵒᵖ) : (RingCon R) :=
{ r := fun a b ↦ rel (op b) (op a)
  iseqv :=
  { refl := fun a ↦ rel.refl (op a)
    symm := rel.symm
    trans := fun h1 h2 ↦ rel.trans h2 h1 }
  mul' := fun h1 h2 ↦ rel.mul h2 h1
  add' := rel.add }

/--
Two-sided-ideals of `A` and that of `Aᵒᵖ` corresponds bijectively to each other.
-/
@[simps]
def toMopOrderIso : (RingCon R) ≃o (RingCon Rᵐᵒᵖ) where
  toFun := toMop
  invFun := fromMop
  left_inv := unop_op
  right_inv := unop_op
  map_rel_iff' {a b} := by
    constructor <;>
    · intro h _ _ H
      exact h H

variable {R' : Type*} [Ring R']

/--
Pulling back a RingCon across a ring hom.
-/
@[simps!]
def comap {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (J : RingCon R') (f : F) :
    RingCon R where
  __ := J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

@[simp] lemma mem_comap {F : Type*} [FunLike F R R'] [RingHomClass F R R'] (J : RingCon R') (f : F) (x) :
    x ∈ J.comap f ↔ f x ∈ J := by
  change J (f x) (f 0) ↔ J (f x) 0
  simp

instance : Module Rᵐᵒᵖ I where
  smul r x := ⟨x.1 * r.unop, I.mul_mem_right _ _ x.2⟩
  one_smul x := by ext; show x.1 * 1 = x.1; simp
  mul_smul x y z := by
    ext; show z.1 * (y.unop * x.unop) = (z.1 * y.unop) * x.unop; simp only [mul_assoc]
  smul_zero x := by
    ext ; show 0 * _ = 0; simp only [zero_mul]
  smul_add x y z := by
    ext ; show (y.1 + z.1) * _ = (y * _) + (z * _); simp only [right_distrib]
  add_smul x y z := by
    ext; show _ * (_ + _) = _ * _ + _ * _; simp only [left_distrib]
  zero_smul x := by
    ext ; show _ * 0 = 0; simp only [mul_zero]

lemma le_iff (I J : RingCon R) : I ≤ J ↔ (I : Set R) ⊆ (J : Set R) := by
  constructor
  · intro h x hx
    exact h hx
  · intro h x y hxy
    have h' : J _ _ := h <| sub_self y ▸ I.sub hxy (I.refl y)
    convert J.add h' (J.refl y) <;>
    abel

end RingCon
