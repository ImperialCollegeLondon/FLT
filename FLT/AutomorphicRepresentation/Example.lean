import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Tactic.Peel
/-

# Example of a space of automorphic forms

-/

/-- We define the profinite completion of ℤ explicitly as compatible elements of ℤ/Nℤ for
all positive integers `N`. We declare it as a subring of `∏_{N ≥ 1} (ℤ/Nℤ)`, and then promote it
to a type. -/
def ZHat : Type := {
  carrier := { f : Π M : ℕ+, ZMod M | ∀ (D N : ℕ+) (h : (D : ℕ) ∣ N),
    ZMod.castHom h (ZMod D) (f N) = f D },
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.neg_apply] at *
    peel hx with D N hD hx
    rw [ZMod.cast_neg hD, hx]
  add_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.add_apply] at *
    intro D N hD
    rw [ZMod.cast_add hD, ha _ _ hD, hb _ _ hD]
  one_mem' := by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.one_apply]
    intro D N hD
    rw [ZMod.cast_one hD]
  mul_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_setOf_eq, Pi.mul_apply] at *
    intro D N hD
    rw [ZMod.cast_mul hD, ha _ _ hD, hb _ _ hD]
  : Subring (Π n : ℕ+, ZMod n)}
deriving CommRing

namespace ZHat

instance : DFunLike ZHat ℕ+ (fun (N : ℕ+) ↦ ZMod N) where
  coe z := z.1
  coe_injective' M N := by simp_all

-- Try to avoid introducing `z.1` and `z.2`.
-- @[simp]
-- lemma val_apply (z : ZHat) (n : ℕ+) : z.1 n = z n := rfl

lemma prop (z : ZHat) (D N : ℕ+) (h : (D : ℕ) ∣ N) : ZMod.castHom h (ZMod D) (z N) = z D := z.2 ..

@[ext]
lemma ext (x y : ZHat) (h : ∀ n : ℕ+, x n = y n) : x = y := by
  cases x
  cases y
  congr
  ext n
  apply h

lemma ext_iff (x y : ZHat) : (∀ n : ℕ+, x n = y n) ↔ x = y :=
  ⟨ext x y, fun h n => by exact congrFun (congrArg DFunLike.coe h) n⟩

@[simp] lemma zero_val (n : ℕ+) : (0 : ZHat) n = 0 := rfl
@[simp] lemma one_val (n : ℕ+) : (1 : ZHat) n = 1 := rfl
@[simp] lemma ofNat_val (m : ℕ) [m.AtLeastTwo] (n : ℕ+) :
  (OfNat.ofNat m : ZHat) n = (OfNat.ofNat m : ZMod n) := rfl
@[simp] lemma natCast_val (m : ℕ) (n : ℕ+) : (m : ZHat) n = (m : ZMod n) := rfl

instance commRing : CommRing ZHat := inferInstance

--wooah, `import Mathlib` breaks this. TODO test this again after bump to Lean v4.8
lemma zeroNeOne : (0 : ZHat) ≠ 1 := by
  intro h
  have h2 : (0 : ZHat) 2 = (1 : ZHat) 2 := by simp [h]
  rw [zero_val, one_val] at h2
  revert h2 ; decide

instance nontrivial : Nontrivial ZHat := ⟨0, 1, zeroNeOne⟩

instance charZero : CharZero ZHat := ⟨ fun a b h ↦ by
  rw [← ext_iff] at h
  specialize h ⟨_, (max a b).succ_pos⟩
  apply_fun ZMod.val at h
  rwa [natCast_val, ZMod.val_cast_of_lt, natCast_val, ZMod.val_cast_of_lt] at h
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  · simp [Nat.succ_eq_add_one, Nat.lt_add_one_iff]
  ⟩
--lemma NonAssocSemiring.Nontrivial_iff (R : Type) [NonAssocSemiring R] :
--    Nontrivial R ↔ (0 : R) ≠ 1 :=
--  ⟨fun _ ↦ zero_ne_one' R, fun a ↦ ⟨0, 1, a⟩⟩

open BigOperators Nat Finset in
/-- A nonarchimedean analogue $0! + 1! + 2! + \cdots$ of $e=1/0! + 1/1! + 1/2! + \cdots$. -/
def e : ZHat := ⟨fun (n : ℕ+) ↦ ∑ i in range (n : ℕ), i !, by
  intros D N hDN
  dsimp only
  obtain ⟨k, hk⟩ := exists_add_of_le <| le_of_dvd N.pos hDN
  simp_rw [map_sum, map_natCast, hk, sum_range_add, add_right_eq_self]
  refine sum_eq_zero (fun i _ => ?_)
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.dvd_factorial D.pos le_self_add
⟩

open BigOperators Nat Finset in
lemma e_def (n : ℕ+) : e n = ∑ i in range (n : ℕ), (i ! : ZMod n) := rfl

/-- Nonarchimedean $e$ is not an integer. -/
lemma e_not_in_Int : ∀ a : ℤ, e ≠ a := sorry
-- This isn't necessary but isn't too hard to prove.

lemma torsionfree_aux (a b : ℕ) [NeZero b] (h : a ∣ b) (x : ZMod b) (hx : a ∣ x.val) :
    ZMod.castHom h (ZMod a) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  obtain ⟨y, hy⟩ := hx
  rw [hy]
  simp

-- ZHat is torsion-free. LaTeX proof in the notes.
lemma torsionfree (N : ℕ+) : Function.Injective (fun z : ZHat ↦ N * z) := by
  rw [← AddMonoidHom.coe_mulLeft, injective_iff_map_eq_zero]
  intro a ha
  rw [AddMonoidHom.coe_mulLeft] at ha
  rw [← ext_iff]
  intro j
  rw [zero_val, ← a.prop j (N * j) (by simp)]
  apply torsionfree_aux
  apply Nat.dvd_of_mul_dvd_mul_left N.pos
  rw [← PNat.mul_coe]
  apply Nat.dvd_of_mod_eq_zero
  have : N * a (N * j) = 0 := by
    have : ((N : ZHat) * a) (N * j) = 0 := by simp [ha]
    exact this -- missing lemma
  simpa only [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, ZMod.val_zero] using congrArg ZMod.val this

lemma y_mul_N_eq_z (N : ℕ+) (z : ZHat) (hz : z N = 0) (j : ℕ+) :
    N * ((z (N * j)).val / (N : ℕ) : ZMod j) = z j := by
  have hhj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
  rw [hz, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hhj
  rw [← Nat.cast_mul, mul_comm, Nat.div_mul_cancel hhj]
  have hhj' := z.prop j (N * j) (by simp only [PNat.mul_coe, dvd_mul_left])
  rw [← hhj']
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

-- LaTeX proof in the notes.
lemma multiples (N : ℕ+) (z : ZHat) : (∃ (y : ZHat), N * y = z) ↔ z N = 0 := by
  constructor
  · intro ⟨y, hy⟩
    rw [← hy]
    change N * (y N) = 0
    simp [ZMod.natCast_self]
  · intro h
    let y : ZHat := {
      val := fun j ↦ (z (N * j)).val / (N : ℕ)
      property := by
        intro j k hjk
        have hj := z.prop N (N * j) (by simp only [PNat.mul_coe, dvd_mul_right])
        have hk := z.prop N (N * k) (by simp only [PNat.mul_coe, dvd_mul_right])
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hj
        rw [h, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_zmod_eq_zero_iff_dvd] at hk
        have hNjk := z.prop (N * j) (N * k) (mul_dvd_mul (dvd_refl _) hjk)
        rw [ZMod.castHom_apply, ZMod.cast_eq_val] at hNjk
        simp only [PNat.mul_coe, map_natCast, ZMod.natCast_val, ZMod.eq_iff_modEq_nat]
        apply Nat.ModEq.mul_right_cancel' (c := N) (by simp)
        rw [Nat.div_mul_cancel hj, Nat.div_mul_cancel hk,
          mul_comm (j : ℕ) (N : ℕ), ← ZMod.eq_iff_modEq_nat, hNjk]
        simp
    }
    refine ⟨y, ?_⟩
    ext j
    exact y_mul_N_eq_z N z h j


end ZHat

open scoped TensorProduct in
/-- The "profinite completion" of ℚ is defined to be `ℚ ⊗ ZHat`, with `ZHat` the profinite
completion of `ℤ`. -/
abbrev QHat := ℚ ⊗[ℤ] ZHat

noncomputable example : QHat := (22 / 7) ⊗ₜ ZHat.e

namespace QHat

lemma canonicalForm (z : QHat) : ∃ (N : ℕ+) (z' : ZHat), z = (1 / N : ℚ) ⊗ₜ z' := by
  induction z using TensorProduct.induction_on with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | tmul q z =>
    refine ⟨⟨q.den, q.den_pos ⟩, q.num * z, ?_⟩
    simp only [← zsmul_eq_mul, TensorProduct.tmul_smul]
    simp only [PNat.mk_coe, zsmul_eq_mul]
    congr
    · simp only [← q.mul_den_eq_num, LinearMap.mul_apply', mul_assoc,
        one_div, ne_eq, Nat.cast_eq_zero, Rat.den_ne_zero, not_false_eq_true,
        mul_inv_cancel, mul_one]
    · simp
  | add x y hx hy =>
    obtain ⟨N₁, z₁, rfl⟩ := hx
    obtain ⟨N₂, z₂, rfl⟩ := hy
    refine ⟨N₁ * N₂, (N₁ : ℤ) * z₂ + (N₂ : ℤ) * z₁, ?_⟩
    simp only [TensorProduct.tmul_add, ← zsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [one_div, PNat.mul_coe, Nat.cast_mul, mul_inv_rev, zsmul_eq_mul, Int.cast_natCast,
      ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
    rw [add_comm]
    congr
    simp [mul_comm]

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

lemma rat_join_zHat : ratsub ⊔ zHatsub = ⊤ := sorry

end additive_structure_of_QHat

section multiplicative_structure_of_QHat

noncomputable abbrev unitsratsub : Subgroup QHatˣ :=
  (Units.map (i₁ : ℚ →* QHat)).range

noncomputable abbrev unitszHatsub : Subgroup QHatˣ :=
  (Units.map (i₂ : ZHat →* QHat)).range

noncomputable abbrev unitszsub : Subgroup QHatˣ :=
  (Units.map (Int.castRingHom QHat : ℤ →* QHat)).range

lemma unitsrat_meet_unitszHat : unitsratsub ⊓ unitszHatsub = unitszsub := sorry

-- this needs that ℤ is a PID.
lemma unitsrat_join_unitszHat : unitsratsub ⊔ unitszHatsub = ⊤ := sorry

end multiplicative_structure_of_QHat

end QHat

structure Hurwitz : Type where
  re : ℤ -- 1
  im_o : ℤ -- ω
  im_i : ℤ -- i
  im_oi : ℤ -- ωi -- note iω + ωi + 1 + i = 0

notation "𝓞" => Hurwitz -- 𝓞 = \MCO
namespace Hurwitz

lemma ext (z w : 𝓞) (h_re : z.re = w.re) (h_im_o : z.im_o = w.im_o)
    (h_im_i : z.im_i = w.im_i) (h_im_oi : z.im_oi = w.im_oi) : z = w :=
  by cases z; cases w; congr;

/-! ## zero (0) -/

/-- The Hurwitz number 0 -/
def zero : 𝓞 := ⟨0, 0, 0, 0⟩

/-- notation `0` for `zero` -/
instance : Zero 𝓞 := ⟨zero⟩

@[simp] lemma zero_re : re (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_o : im_o (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_i : im_i (0 : 𝓞) = 0 := rfl
@[simp] lemma zero_im_oi : im_oi (0 : 𝓞) = 0 := rfl

/-! ## one (1) -/

def one : 𝓞 := ⟨1, 0, 0, 0⟩

/-- Notation `1` for `one` -/
instance : One 𝓞 := ⟨one⟩

@[simp] lemma one_re : re (1 : 𝓞) = 1 := rfl
@[simp] lemma one_im_o : im_o (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_i : im_i (1 : 𝓞) = 0 := rfl
@[simp] lemma one_im_oi : im_oi (1 : 𝓞) = 0 := rfl

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

instance : AddCommGroup 𝓞 where
  add_assoc := by intros; apply ext <;> simp [add_assoc]
  zero_add := by intros; apply ext <;> simp
  add_zero := by intros; apply ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_left_neg := by intros; apply ext <;> simp
  add_comm := by intros; apply ext <;> simp [add_comm]

/-! ## mul (*) -/

-- multiplication

/-- Multiplication `z*w` of two Hurwitz numbers -/
def mul (z w : 𝓞) : 𝓞 :=
  ⟨z.re * w.re + sorry, sorry, sorry, sorry⟩

/-- Notation `*` for multiplication -/
instance : Mul 𝓞 := ⟨mul⟩

-- how `mul` reacts with `re` and `im`
@[simp] lemma mul_re (z w : 𝓞) : re (z * w) = re z * re w + sorry := rfl

-- @[simp] lemma mul_im_0 (z w : 𝓞) : sorry := rfl etc etc

instance ring : Ring 𝓞 := { (inferInstance : AddCommGroup 𝓞) with
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
}

/-- Conjugate; sends $a+bi+cj+dk$ to $a-bi-cj-dk$. -/
def conj : 𝓞 →ₐ[ℤ] 𝓞 where
  toFun z := ⟨z.re -z.im_o, -z.im_o, -z.im_i, -z.im_oi⟩ -- not right but something like this
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

def norm : 𝓞 → ℤ
| mk a b c d => sorry -- not a*a + b*b + c*c + d*d because of ω

lemma norm_eq_mul_conj (z : 𝓞) : (norm z : 𝓞) = z * conj z := sorry

lemma norm_zero : norm 0 = 0 := sorry

lemma norm_one : norm 1 = 1 := sorry

lemma norm_mul (x y : 𝓞) : norm (x * y) = norm x * norm y := sorry

lemma norm_nonneg (x : 𝓞) : 0 ≤ norm x := sorry

lemma norm_eq_zero (x : 𝓞) : norm x = 0 ↔ x = 0 := sorry

lemma quot_rem (a b : 𝓞) (hb : b ≠ 0) : ∃ q r : 𝓞, a = q * b + r ∧ norm r < norm b := sorry

lemma left_ideal_princ (I : Submodule 𝓞 𝓞) : ∃ a : 𝓞, I = Submodule.span 𝓞 {a} := sorry

open scoped TensorProduct

noncomputable def HurwitzHat : Type := 𝓞 ⊗[ℤ] ZHat

notation "𝓞^" => HurwitzHat

noncomputable instance : Ring 𝓞^ := Algebra.TensorProduct.instRing

noncomputable def HurwitzRat : Type := ℚ ⊗[ℤ] 𝓞

notation "D" => HurwitzRat

noncomputable instance : Ring D := Algebra.TensorProduct.instRing

noncomputable def HurwitzRatHat : Type := D ⊗[ℤ] ZHat

notation "D^" => HurwitzRatHat

noncomputable instance : Ring D^ := Algebra.TensorProduct.instRing

noncomputable abbrev j₁ : D →ₐ[ℤ] D^ := Algebra.TensorProduct.includeLeft -- (Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm.trans Algebra.TensorProduct.includeLeft

lemma injective_hRat :
    Function.Injective j₁ := sorry -- flatness

noncomputable abbrev j₂ : 𝓞^ →ₐ[ℤ] D^ :=
  ((Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm : ℚ ⊗ 𝓞^ ≃ₐ[ℤ] D ⊗ ZHat).toAlgHom.comp
  (Algebra.TensorProduct.includeRight : 𝓞^ →ₐ[ℤ] ℚ ⊗ 𝓞^)

lemma injective_zHat :
    Function.Injective j₂ := sorry -- flatness

-- should I rearrange tensors? Not sure if D^ should be (ℚ ⊗ 𝓞) ⊗ ℤhat or ℚ ⊗ (𝓞 ⊗ Zhat)
lemma canonicalForm (z : D^) : ∃ (N : ℕ+) (z' : 𝓞^), z = j₁ ((N⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ z' := by
  sorry

lemma completed_units (z : D^ˣ) : ∃ (u : Dˣ) (v : 𝓞^ˣ), (z : D^) = j₁ u * j₂ v := sorry

end Hurwitz
