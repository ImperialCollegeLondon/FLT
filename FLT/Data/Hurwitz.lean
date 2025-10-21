import Mathlib.Data.PNat.Prime
import Mathlib.Tactic.Peel
import Mathlib.Analysis.Quaternion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree

@[ext]
structure Hurwitz : Type where
  re : ℤ -- 1
  im_o : ℤ -- ω
  im_i : ℤ -- i
  im_oi : ℤ -- ωi -- note iω + ωi + 1 + i = 0

notation "𝓞" => Hurwitz -- 𝓞 = \MCO
namespace Hurwitz

open Quaternion in
noncomputable def toQuaternion (z : 𝓞) : ℍ where
  re := z.re - 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi
  imI := z.im_i + 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi
  imJ := 2⁻¹ * z.im_o + 2⁻¹ * z.im_oi
  imK := 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi

open Quaternion in
noncomputable def fromQuaternion (z : ℍ) : 𝓞 where
  re := Int.floor <| z.re + z.imJ
  im_o := Int.floor <| z.imJ + z.imK
  im_i := Int.floor <| z.imI - z.imK
  im_oi := Int.floor <| z.imJ - z.imK

lemma leftInverse_fromQuaternion_toQuaternion :
    Function.LeftInverse fromQuaternion toQuaternion := by
  intro z
  simp only [fromQuaternion, toQuaternion, sub_add_add_cancel, sub_add_cancel, Int.floor_intCast,
    add_add_sub_cancel, ← two_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_inv_cancel_left₀, sub_sub_sub_cancel_right, add_sub_cancel_right, add_sub_sub_cancel]

lemma toQuaternion_injective : Function.Injective toQuaternion :=
  leftInverse_fromQuaternion_toQuaternion.injective

open Quaternion in
lemma leftInvOn_toQuaternion_fromQuaternion :
    Set.LeftInvOn toQuaternion fromQuaternion
      { q : ℍ | ∃ a b c d : ℤ, q = ⟨a, b, c, d⟩ ∨ q = ⟨a + 2⁻¹, b + 2⁻¹, c + 2⁻¹, d + 2⁻¹⟩ } := by
  have h₀ (x y : ℤ) : (x + 2 ⁻¹ : ℝ) + (y + 2⁻¹) = ↑(x + y + 1) := by
    field_simp; norm_cast; ring
  intro q hq
  simp only [Set.mem_setOf] at hq
  simp only [toQuaternion, fromQuaternion]
  obtain ⟨a, b, c, d, rfl|rfl⟩ := hq <;>
  ext <;>
  simp only [h₀, add_sub_add_right_eq_sub, Int.floor_sub_intCast, Int.floor_intCast, Int.cast_sub,
    Int.cast_add, Int.cast_one, Int.floor_add_one, Int.floor_sub_intCast] <;>
  simp only [Int.floor_add_intCast, Int.floor_intCast, Int.cast_add] <;>
  field_simp <;>
  norm_cast <;>
  ring

open Quaternion in
lemma fromQuaternion_injOn :
    Set.InjOn fromQuaternion
      { q : ℍ | ∃ a b c d : ℤ, q = ⟨a, b, c, d⟩ ∨ q = ⟨a + 2⁻¹, b + 2⁻¹, c + 2⁻¹, d + 2⁻¹⟩ } :=
  leftInvOn_toQuaternion_fromQuaternion.injOn

/-! ## zero (0) -/

/-- The Hurwitz number 0 -/
def zero : 𝓞 := ⟨0, 0, 0, 0⟩

/-- notation `0` for `zero` -/
instance : Zero 𝓞 := ⟨zero⟩

@[simp] lemma zero_re : re (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_o : im_o (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_i : im_i (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_oi : im_oi (0 : 𝓞) = 0 := rfl

lemma toQuaternion_zero : toQuaternion 0 = 0 := by
  ext <;> (simp [toQuaternion])

@[simp]
lemma toQuaternion_eq_zero_iff {z} : toQuaternion z = 0 ↔ z = 0 :=
  toQuaternion_injective.eq_iff' toQuaternion_zero

lemma toQuaternion_ne_zero_iff {z} : toQuaternion z ≠ 0 ↔ z ≠ 0 :=
  toQuaternion_injective.ne_iff' toQuaternion_zero

/-! ## one (1) -/

def one : 𝓞 := ⟨1, 0, 0, 0⟩

/-- Notation `1` for `one` -/
instance : One 𝓞 := ⟨one⟩

@[simp] lemma one_re : re (1 : 𝓞) = 1 := rfl
@[simp] lemma one_im_o : im_o (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_i : im_i (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_oi : im_oi (1 : 𝓞) = 0 := rfl

lemma toQuaternion_one : toQuaternion 1 = 1 := by
  ext <;> (simp [toQuaternion])

/-! ## Neg (-) -/

-- negation

/-- The negation `-z` of a Hurwitz number -/
def neg (z : 𝓞) : 𝓞 := ⟨-re z, -im_o z, -im_i z, -im_oi z⟩

/-- Notation `-` for negation -/
instance : Neg 𝓞 := ⟨neg⟩

-- how neg interacts with re and im_*
@[simp] lemma neg_re (z : 𝓞) : re (-z) = -re z  := rfl
@[simp] lemma neg_im_o (z : 𝓞) : im_o (-z) = -im_o z  := rfl
@[simp] lemma neg_im_i (z : 𝓞) : im_i (-z) = -im_i z  := rfl
@[simp] lemma neg_im_oi (z : 𝓞) : im_oi (-z) = -im_oi z  := rfl

lemma toQuaternion_neg (z : 𝓞) :
    toQuaternion (-z) = - toQuaternion z := by
  ext <;> simp [toQuaternion] <;> ring

/-! ## add (+) -/

-- Now let's define addition

/-- addition `z+w` of complex numbers -/
def add (z w : 𝓞) : 𝓞 := ⟨z.re + w.re, z.im_o + w.im_o, z.im_i + w.im_i, z.im_oi + w.im_oi⟩

/-- Notation `+` for addition -/
instance : Add 𝓞 := ⟨add⟩

-- basic properties
@[simp] lemma add_re (z w : 𝓞) : re (z + w) = re z  + re w  := rfl
@[simp] lemma add_im_o (z w : 𝓞) : im_o (z + w) = im_o z  + im_o w  := rfl
@[simp] lemma add_im_i (z w : 𝓞) : im_i (z + w) = im_i z  + im_i w  := rfl
@[simp] lemma add_im_oi (z w : 𝓞) : im_oi (z + w) = im_oi z  + im_oi w  := rfl

lemma toQuaternion_add (z w : 𝓞) :
    toQuaternion (z + w) = toQuaternion z + toQuaternion w := by
  ext <;> simp [toQuaternion] <;> ring

/-- Notation `+` for addition -/
instance : Sub 𝓞 := ⟨fun a b => a + -b⟩

lemma toQuaternion_sub (z w : 𝓞) :
    toQuaternion (z - w) = toQuaternion z - toQuaternion w := by
  convert toQuaternion_add z (-w) using 1
  rw [sub_eq_add_neg, toQuaternion_neg]


-- instance : AddCommGroup 𝓞 where
--   add_assoc := by intros; ext <;> simp [add_assoc]
--   zero_add := by intros; ext <;> simp
--   add_zero := by intros; ext <;> simp
--   nsmul := nsmulRec
--   zsmul := zsmulRec
--   add_left_neg := by intros; ext <;> simp
--   add_comm := by intros; ext <;> simp [add_comm]

instance : SMul ℕ 𝓞 where
  smul := nsmulRec

lemma preserves_nsmulRec {M N : Type*} [Zero M] [Add M] [AddMonoid N]
    (f : M → N) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (n : ℕ) (x : M) :
    f (nsmulRec n x) = n • f x := by
  induction n with
  | zero => rw [nsmulRec, zero, zero_smul]
  | succ n ih => rw [nsmulRec, add, add_nsmul, one_nsmul, ih]

lemma toQuaternion_nsmul (z : 𝓞) (n : ℕ) :
    toQuaternion (n • z) = n • toQuaternion z :=
  preserves_nsmulRec _ toQuaternion_zero toQuaternion_add _ _

instance : SMul ℤ 𝓞 where
  smul := zsmulRec

lemma preserves_zsmul {G H : Type*} [Zero G] [Add G] [Neg G] [SMul ℕ G] [SubNegMonoid H]
    (f : G → H) (nsmul : ∀ (g : G) (n : ℕ), f (n • g) = n • f g)
    (neg : ∀ x, f (-x) = -f x)
    (z : ℤ) (g : G) :
    f (zsmulRec (· • ·) z g) = z • f g := by
  cases z with
  | ofNat n =>
    rw [zsmulRec, nsmul, Int.ofNat_eq_coe, natCast_zsmul]
  | negSucc n =>
    rw [zsmulRec, neg, nsmul, negSucc_zsmul]

lemma toQuaternion_zsmul (z : 𝓞) (n : ℤ) :
    toQuaternion (n • z) = n • toQuaternion z :=
  preserves_zsmul _
    toQuaternion_nsmul
    toQuaternion_neg
    n z

-- noncomputable instance : AddCommGroup 𝓞 :=
--   toQuaternion_injective.addCommGroup
--     _
--     toQuaternion_zero
--     toQuaternion_add
--     toQuaternion_neg
--     toQuaternion_sub
--     toQuaternion_nsmul
--     toQuaternion_zsmul

/-! ## mul (*) -/

-- multiplication

/-- Multiplication `z*w` of two Hurwitz numbers -/
def mul (z w : 𝓞) : 𝓞 where
  re := z.re * w.re - z.im_o * w.im_o - z.im_i * w.im_o -
    z.im_i * w.im_i + z.im_i * w.im_oi - z.im_oi * w.im_oi
  im_o := z.im_o * w.re + z.re * w.im_o - z.im_o * w.im_o -
    z.im_oi * w.im_o - z.im_oi * w.im_i + z.im_i * w.im_oi
  im_i := z.im_i * w.re - z.im_i * w.im_o + z.im_oi * w.im_o +
    z.re * w.im_i - z.im_o * w.im_oi - z.im_i * w.im_oi
  im_oi := z.im_oi * w.re - z.im_i * w.im_o + z.im_o * w.im_i +
    z.re * w.im_oi - z.im_o * w.im_oi - z.im_oi * w.im_oi

/-- Notation `*` for multiplication -/
instance : Mul 𝓞 := ⟨mul⟩

-- how `mul` reacts with `re` and `im`
@[simp] lemma mul_re (z w : 𝓞) :
    re (z * w) = z.re * w.re - z.im_o * w.im_o - z.im_i * w.im_o -
      z.im_i * w.im_i + z.im_i * w.im_oi - z.im_oi * w.im_oi := rfl

@[simp] lemma mul_im_o (z w : 𝓞) :
    im_o (z * w) = z.im_o * w.re + z.re * w.im_o - z.im_o * w.im_o -
      z.im_oi * w.im_o - z.im_oi * w.im_i + z.im_i * w.im_oi := rfl

@[simp] lemma mul_im_i (z w : 𝓞) :
    im_i (z * w) = z.im_i * w.re - z.im_i * w.im_o + z.im_oi * w.im_o +
      z.re * w.im_i - z.im_o * w.im_oi - z.im_i * w.im_oi := rfl

@[simp] lemma mul_im_oi (z w : 𝓞) :
    im_oi (z * w) = z.im_oi * w.re - z.im_i * w.im_o + z.im_o * w.im_i +
      z.re * w.im_oi - z.im_o * w.im_oi - z.im_oi * w.im_oi := rfl

lemma toQuaternion_mul (z w : 𝓞) :
    toQuaternion (z * w) = toQuaternion z * toQuaternion w := by
  ext <;> simp [toQuaternion] <;> ring

lemma o_mul_i :
    { re := 0, im_o := 1, im_i := 0, im_oi := 0 } * { re := 0, im_o := 0, im_i := 1, im_oi := 0 }
      = ({ re := 0, im_o := 0, im_i := 0, im_oi := 1 } : 𝓞) := by
  ext <;> simp

instance : Pow 𝓞 ℕ := ⟨fun z n => npowRec n z⟩

lemma preserves_npowRec {M N : Type*} [One M] [Mul M] [Monoid N]
    (f : M → N) (one : f 1 = 1) (mul : ∀ x y : M, f (x * y) = f x * f y) (z : M) (n : ℕ) :
    f (npowRec n z) = (f z) ^ n := by
  induction n with
  | zero => rw [npowRec, one, pow_zero]
  | succ n ih => rw [npowRec, pow_succ, mul, ih]

lemma toQuaternion_npow (z : 𝓞) (n : ℕ) : toQuaternion (z ^ n) = (toQuaternion z) ^ n :=
  preserves_npowRec toQuaternion toQuaternion_one toQuaternion_mul z n

instance : NatCast 𝓞 := ⟨Nat.unaryCast⟩

lemma preserves_unaryCast {R S : Type*} [One R] [Zero R] [Add R] [AddMonoidWithOne S]
    (f : R → S) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (n : ℕ) :
    f (Nat.unaryCast n) = n := by
  induction n with
  | zero => rw [Nat.unaryCast, zero, Nat.cast_zero]
  | succ n ih => rw [Nat.unaryCast, add, one, Nat.cast_add, Nat.cast_one, ih]

lemma toQuaternion_natCast (n : ℕ) : toQuaternion n = n :=
  preserves_unaryCast _ toQuaternion_zero toQuaternion_one toQuaternion_add n

instance : IntCast 𝓞 := ⟨Int.castDef⟩

lemma Int.castDef_ofNat {R : Type*} [NatCast R] [Neg R] (n : ℕ) :
    (Int.castDef (Int.ofNat n) : R) = n := rfl

lemma Int.castDef_negSucc {R : Type*} [NatCast R] [Neg R] (n : ℕ) :
    (Int.castDef (Int.negSucc n) : R) = -(n + 1 : ℕ) := rfl

lemma preserves_castDef
    {R S : Type*} [NatCast R] [Neg R] [AddGroupWithOne S]
    (f : R → S) (natCast : ∀ n : ℕ, f n = n) (neg : ∀ x, f (-x) = - f x) (n : ℤ) :
    f (Int.castDef n) = n := by
  cases n with
  | ofNat n => rw [Int.castDef_ofNat, natCast, Int.ofNat_eq_coe, Int.cast_natCast]
  | negSucc _ => rw [Int.castDef_negSucc, neg, natCast, Int.cast_negSucc]

lemma toQuaternion_intCast (n : ℤ) : toQuaternion n = n :=
  preserves_castDef _ toQuaternion_natCast toQuaternion_neg n

noncomputable instance ring : Ring 𝓞 :=
  toQuaternion_injective.ring
    _
    toQuaternion_zero
    toQuaternion_one
    toQuaternion_add
    toQuaternion_mul
    toQuaternion_neg
    toQuaternion_sub
    (fun _ _ => toQuaternion_nsmul _ _) -- TODO for Yaël: these are inconsistent with addCommGroup
    (fun _ _ => toQuaternion_zsmul _ _) -- TODO for Yaël: these are inconsistent with addCommGroup
    toQuaternion_npow
    toQuaternion_natCast
    toQuaternion_intCast

@[simp] lemma natCast_re (n : ℕ) : (n : 𝓞).re = n := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_o (n : ℕ) : (n : 𝓞).im_o = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_i (n : ℕ) : (n : 𝓞).im_i = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa
@[simp] lemma natCast_im_oi (n : ℕ) : (n : 𝓞).im_oi = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa

@[simp] lemma intCast_re (n : ℤ) : (n : 𝓞).re = n := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_o (n : ℤ) : (n : 𝓞).im_o = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_i (n : ℤ) : (n : 𝓞).im_i = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]
@[simp] lemma intCast_im_oi (n : ℤ) : (n : 𝓞).im_oi = 0 := by
  cases n with
  | ofNat _ => simp
  | negSucc _ => simp [← Int.neg_ofNat_succ]


/-- Conjugate; sends $a+bi+cj+dk$ to $a-bi-cj-dk$. -/
instance starRing : StarRing 𝓞 where
  star z := ⟨z.re - z.im_o - z.im_oi, -z.im_o, -z.im_i, -z.im_oi⟩
  star_involutive x := by ext <;> simp only <;> ring
  star_mul x y := by ext <;> simp <;> ring
  star_add x y := by ext <;> simp <;> ring

@[simp] lemma star_re (z : 𝓞) : (star z).re = z.re - z.im_o - z.im_oi := rfl
@[simp] lemma star_im_o (z : 𝓞) : (star z).im_o = -z.im_o := rfl
@[simp] lemma star_im_i (z : 𝓞) : (star z).im_i = -z.im_i := rfl
@[simp] lemma star_im_oi (z : 𝓞) : (star z).im_oi = -z.im_oi := rfl

lemma toQuaternion_star (z : 𝓞) : toQuaternion (star z) = star (toQuaternion z) := by
  ext <;>
  simp only [star_re, star_im_o, star_im_i, star_im_oi, toQuaternion,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;>
  field_simp <;>
  norm_cast <;>
  ring

lemma star_eq (z : 𝓞) : star z = (fromQuaternion ∘ star ∘ toQuaternion) z := by
  simp only [Function.comp_apply, ← toQuaternion_star]
  rw [leftInverse_fromQuaternion_toQuaternion]

instance : CharZero 𝓞 where
  cast_injective x y hxy := by simpa [Hurwitz.ext_iff] using hxy

def norm (z : 𝓞) : ℤ :=
  z.re * z.re + z.im_o * z.im_o + z.im_i * z.im_i + z.im_oi * z.im_oi
  - z.re * (z.im_o + z.im_oi) + z.im_i * (z.im_o - z.im_oi)

lemma norm_eq_mul_conj (z : 𝓞) : (norm z : 𝓞) = z * star z := by
  ext <;> simp only [norm, intCast_re, intCast_im_o, intCast_im_i, intCast_im_oi,
    mul_re, mul_im_o, mul_im_i, mul_im_oi, star_re, star_im_o, star_im_i, star_im_oi] <;> ring

lemma coe_norm (z : 𝓞) :
    (norm z : ℝ) =
      (z.re - 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 +
      (z.im_i + 2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 +
      (2⁻¹ * z.im_o + 2⁻¹ * z.im_oi) ^ 2 +
      (2⁻¹ * z.im_o - 2⁻¹ * z.im_oi) ^ 2 := by
  rw [norm]
  field_simp
  norm_cast
  ring

lemma norm_zero : norm 0 = 0 := by simp [norm]

lemma norm_one : norm 1 = 1 := by simp [norm]

lemma norm_mul (x y : 𝓞) : norm (x * y) = norm x * norm y := by
  rw [← Int.cast_inj (α := 𝓞)]
  simp_rw [norm_eq_mul_conj, star_mul]
  rw [mul_assoc, ← mul_assoc y, ← norm_eq_mul_conj]
  rw [Int.cast_comm, ← mul_assoc, ← norm_eq_mul_conj, Int.cast_mul]

lemma norm_nonneg (x : 𝓞) : 0 ≤ norm x := by
  rw [← Int.cast_nonneg (R := ℝ), coe_norm]
  positivity

lemma norm_eq_zero (x : 𝓞) : norm x = 0 ↔ x = 0 := by
  constructor
  swap
  · rintro rfl; exact norm_zero
  intro h
  rw [← Int.cast_eq_zero (α := ℝ), coe_norm] at h
  field_simp at h
  norm_cast at h
  have h4 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h.le
  rw [sq_eq_zero_iff, sub_eq_zero] at h4
  have h1 := eq_zero_of_add_nonpos_left (by positivity) (by positivity) h.le
  have h3 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h1.le
  rw [h4] at h3
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, add_self_eq_zero] at h3
  rw [h3] at h4
  simp only [h4, sub_zero, h3, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    at h1
  have h2 := eq_zero_of_add_nonpos_right (by positivity) (by positivity) h1.le
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, mul_eq_zero,
    false_or] at h2
  simp only [h2, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    pow_eq_zero_iff, mul_eq_zero, or_false] at h1
  ext <;> assumption

open Quaternion in
lemma normSq_toQuaternion (z : 𝓞) : normSq (toQuaternion z) = norm z := by
  apply coe_injective
  rw [← self_mul_star, ← toQuaternion_star, ← toQuaternion_mul, ← norm_eq_mul_conj,
    toQuaternion_intCast, coe_intCast]

private lemma aux (x y z w : ℤ) : toQuaternion (fromQuaternion ⟨x,y,z,w⟩) = ⟨x,y,z,w⟩ := by
  apply leftInvOn_toQuaternion_fromQuaternion
  simp only [Set.mem_setOf]
  use x, y, z, w
  simp

private lemma aux2 (a b c d : ℝ) (ha : a ≤ 4⁻¹) (hb : b ≤ 4⁻¹) (hc : c ≤ 4⁻¹) (hd : d ≤ 4⁻¹)
    (H : ¬ (a = 4⁻¹ ∧ b = 4⁻¹ ∧ c = 4⁻¹ ∧ d = 4⁻¹)) :
    a + b + c + d < 1 := by
  apply lt_of_le_of_ne
  · calc
      _ ≤ (4 : ℝ)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ := by gcongr
      _ = 1 := by norm_num
  contrapose! H
  have invs : (1 : ℝ) - 4⁻¹ = 4⁻¹ + 4⁻¹ + 4⁻¹ := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply le_antisymm ‹_› <;>
  [ (have : a = 1 - (b + c + d) := by rw [← H]; ring);
    (have : b = 1 - (a + c + d) := by rw [← H]; ring);
    (have : c = 1 - (a + b + d) := by rw [← H]; ring);
    (have : d = 1 - (a + b + c) := by rw [← H]; ring) ] <;>
  rw [this, le_sub_comm, invs] <;>
  gcongr

open Quaternion in
lemma exists_near (a : ℍ) : ∃ q : 𝓞, dist a (toQuaternion q) < 1 := by
  have four_inv : (4⁻¹ : ℝ) = 2⁻¹ ^ 2 := by norm_num
  have (r : ℝ) : (r - round r) ^ 2 ≤ 4⁻¹ := by
    rw [four_inv, sq_le_sq]
    apply (abs_sub_round _).trans_eq
    rw [abs_of_nonneg]
    all_goals norm_num
  let x := round a.re
  let y := round a.imI
  let z := round a.imJ
  let w := round a.imK
  by_cases H : |a.re - x| = 2⁻¹ ∧ |a.imI - y| = 2⁻¹ ∧ |a.imJ - z| = 2⁻¹ ∧ |a.imK - w| = 2⁻¹
  · use fromQuaternion a
    convert zero_lt_one' ℝ
    rw [NormedRing.dist_eq, ← sq_eq_zero_iff, sq, ← Quaternion.normSq_eq_norm_mul_self, normSq_def']
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    rw [add_eq_zero_iff_of_nonneg (by positivity) (by positivity)]
    simp_rw [and_assoc, sq_eq_zero_iff, re_sub, imI_sub, imJ_sub, imK_sub, sub_eq_zero,
      ← Quaternion.ext_iff]
    symm
    apply leftInvOn_toQuaternion_fromQuaternion
    · simp only [Set.mem_setOf]
      have {r : ℝ} {z : ℤ} (h : |r - z| = 2⁻¹) : ∃ z' : ℤ, r = z' + 2⁻¹  := by
        cases (abs_eq (by positivity)).mp h with (rw [sub_eq_iff_eq_add'] at h)
        | inl h => use z
        | inr h => use z - 1; rw [h, Int.cast_sub, Int.cast_one, add_comm_sub]; norm_num

      obtain ⟨x', hx'⟩ := this H.1
      obtain ⟨y', hy'⟩ := this H.2.1
      obtain ⟨z', hz'⟩ := this H.2.2.1
      obtain ⟨w', hw'⟩ := this H.2.2.2
      use x', y', z', w', Or.inr ?_
      ext <;> simp [*]

  use fromQuaternion ⟨x,y,z,w⟩
  rw [aux]
  rw [NormedRing.dist_eq, ← sq_lt_one_iff₀ (_root_.norm_nonneg _), sq,
    ← Quaternion.normSq_eq_norm_mul_self, normSq_def']

  simp only [re_sub, imI_sub, imJ_sub, imK_sub]

  apply aux2 <;> try apply this
  contrapose! H
  suffices ∀ r : ℝ, |r| = 2⁻¹ ↔ r ^ 2 = 4⁻¹ by
    simpa [this]
  intro r
  rw [four_inv, sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (a := (2⁻¹ : ℝ))]
  norm_num

open Quaternion in
lemma quot_rem (a b : 𝓞) (hb : b ≠ 0) : ∃ q r : 𝓞, a = q * b + r ∧ norm r < norm b := by
  let a' := toQuaternion a
  let b' := toQuaternion b
  have hb' : b' ≠ 0 := toQuaternion_ne_zero_iff.mpr hb
  let q' := a' / b'
  obtain ⟨q : 𝓞, hq : dist q' (toQuaternion q) < 1⟩ : ∃ _, _ := exists_near q'
  refine ⟨q, a - q * b, (add_sub_cancel _ _).symm, ?_⟩
  rw [← Int.cast_lt (R := ℝ), ← normSq_toQuaternion, ← normSq_toQuaternion]
  rw [normSq_eq_norm_mul_self, normSq_eq_norm_mul_self]
  refine mul_self_lt_mul_self ?_ ?_
  · exact _root_.norm_nonneg (a - q * b).toQuaternion
  rw [toQuaternion_sub, ← dist_eq_norm]
  calc
    _ = dist (q' * b') (q.toQuaternion * b') := ?_
    _ = dist q' (q.toQuaternion) * ‖b'‖ := ?_
    _ < _ := ?_
  · rw [toQuaternion_mul]
    dsimp only [b', q']
    rw [div_mul_cancel₀ a' hb']
  · -- Surprised that this doesn't seem to exist in mathlib.
    rw [dist_eq_norm_sub', ← sub_mul, _root_.norm_mul, ← dist_eq_norm_sub']
  · rw [← norm_pos_iff] at hb'
    exact mul_lt_of_lt_one_left hb' hq

lemma left_ideal_princ (I : Submodule 𝓞 𝓞) : ∃ a : 𝓞, I = Submodule.span 𝓞 {a} := by
  by_cases h_bot : I = ⊥
  · use 0
    rw [Eq.comm]
    simp only [h_bot, Submodule.span_singleton_eq_bot]
  let S := {a : 𝓞 // a ∈ I ∧ a ≠ 0}
  have : Nonempty S := by
    simp only [ne_eq, nonempty_subtype, S]
    exact Submodule.exists_mem_ne_zero_of_ne_bot h_bot
  have hbdd : BddBelow <| Set.range (fun i : S ↦ norm i) := by
    use 0
    simp only [ne_eq, mem_lowerBounds, Set.mem_range]
    rintro _ ⟨_, rfl⟩
    exact norm_nonneg _
  obtain ⟨a, ha⟩ : ∃ a : S, norm a = ⨅ i : S, norm i :=
    exists_eq_ciInf_of_not_isPredPrelimit hbdd (Order.not_isPredPrelimit)
  use a
  apply le_antisymm
  · intro i hi
    rw [Submodule.mem_span_singleton]
    simp only [ne_eq]
    obtain ⟨q, r, hqr⟩ := quot_rem i a a.2.2
    rw [ha] at hqr
    have hrI : r ∈ I := by
      rw [show r = i - q • a by apply eq_sub_of_add_eq; rw [add_comm]; exact hqr.1.symm ]
      apply I.sub_mem hi (I.smul_mem _ a.2.1)
    have hr : r = 0 := by
      by_contra hr
      lift r to S using ⟨hrI, hr⟩
      apply (ciInf_le hbdd r).not_gt hqr.2
    rw [hr, add_zero] at hqr
    refine ⟨q, hqr.1.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact a.2.1

end Hurwitz
