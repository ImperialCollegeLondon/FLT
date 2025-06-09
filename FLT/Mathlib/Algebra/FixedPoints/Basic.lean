import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Fixed points of actions

We define types representing fixed points of actions on types, and
define inherited typeclasses on these fixed point types. For example
the fixed points of an action on an additive group is an additive group.

## Main definitions

Given types `M` and `A`, with `[SMul M A]`,
* `MulAction.FixedPoints M A` is the subtype of `A` consisting of the `a`
  such that `∀ m, m • a = a`.

Similarly, with `[VAdd M A]`,
* `AddAction.FixedPoints M A` is the subtype of `A` consisting of the `a`
  satisfying the unlikely-looking equation `∀ m, m +ᵥ a = a`.

## Notes

Note that the type `MulAction.FixedPoints` is the coercion to a type
of the term `MulAction.fixedPoints` (which, presumably for historical
reasons, is defined under a spurious extra hypothesis that `M` is a monoid).
The motivation for this file is that using `↥fixedPoints` can lead
typeclass inference on a wild goose chase.
-/

/-- If `M` acts on `A` then `FixedPoints M A` is the type of elements
of `A` which are fixed elementwise by all of `M`. -/
def MulAction.FixedPoints (M A : Type*) [SMul M A] : Type _ :=
  {a : A // ∀ m : M, m • a = a}

/-- If `M` acts on `A` then `FixedPoints M A` is the type of elements
of `A` which are fixed elementwise by all of `M`. -/
def AddAction.FixedPoints (M A : Type*) [VAdd M A] : Type _ :=
  {a : A // ∀ m : M, m +ᵥ a = a}

attribute [to_additive existing] MulAction.FixedPoints

namespace MulAction.FixedPoints

variable {M A : Type*}

@[to_additive (attr := ext)]
lemma ext [SMul M A] (a b : FixedPoints M A) (h : a.1 = b.1) : a = b := by
  cases a; cases b; subst h; rfl

-- TODO: don't know what I'm doing but Coe doesn't work because of semioutparam
@[to_additive]
instance [SMul M A] : CoeHead (FixedPoints M A) A where
  coe := Subtype.val

instance addZeroClass [AddZeroClass A] [DistribSMul M A] : AddZeroClass (FixedPoints M A) where
  zero := ⟨0, smul_zero⟩
  add a b := ⟨(a : A) + b, fun m ↦ by
    rw [smul_add m (a : A) b, a.prop m, b.prop m]⟩
  zero_add a := by
    ext
    exact zero_add (a : A)
  add_zero a := by
    ext
    exact add_zero (a : A)

lemma zero_def [AddZeroClass A] [DistribSMul M A] : (0 : FixedPoints M A) = ⟨0, smul_zero⟩ := rfl

lemma coe_add [AddZeroClass A] [DistribSMul M A] (a b : FixedPoints M A) :
    ((a + b : FixedPoints M A) : A) = a + b := rfl

-- TODO: I could use FixedPoints.addSubmonoid + coercion to addMonoid, but Is my `nsmul` better?
instance addMonoid [AddMonoid A] [DistribSMul M A] : AddMonoid (FixedPoints M A) where
  __ := addZeroClass
  add_assoc a b c := by
    ext
    exact add_assoc (a : A) b c
  nsmul n a := ⟨AddMonoid.nsmul n a, by
    intro m
    induction n with
    | zero => simp
    | succ n IH => rw [AddMonoid.nsmul_succ, smul_add, IH, a.prop]
  ⟩
  nsmul_zero a := by
    simp [zero_def]
  nsmul_succ n a := by
    ext
    simp [succ_nsmul, coe_add]

instance addCommMonoid [AddCommMonoid A] [DistribSMul M A] : AddCommMonoid (FixedPoints M A) where
  __ := addMonoid
  add_comm a b := by
    ext
    exact add_comm (a : A) b

-- should be in mathlib; current version assumes M a monoid but same proof
theorem smul_neg [AddGroup A] [DistribSMul M A] (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_cancel, smul_zero]

instance addGroup [AddGroup A] [DistribSMul M A] : AddGroup (FixedPoints M A) where
  __ := addMonoid
  neg a := ⟨-(a : A), fun m ↦ by
    rw [smul_neg, a.prop]⟩
  zsmul n a := ⟨SubNegMonoid.zsmul n a.1, fun m ↦ by
  induction n with
  | zero => simp
  | succ n _ => simp_all [add_zsmul, a.prop]
  | pred i IH => simp_all [sub_zsmul, smul_neg, a.prop]⟩
  zsmul_zero' a := by
    ext
    simp [zero_def]
  zsmul_succ' n a := by
    ext
    simp [coe_add, add_zsmul]
  zsmul_neg' n a := by
    ext
    simp [add_nsmul, add_zsmul]
  neg_add_cancel a := by
    ext
    simp [zero_def, coe_add]

variable (M A) in
instance addCommGroup [AddCommGroup A] [DistribSMul M A] : AddCommGroup (FixedPoints M A) where
  __ := addGroup
  add_comm a b := by
    ext
    simp [coe_add, add_comm]

variable (R : Type*) [CommRing R] in
instance module [AddCommGroup A] [Module R A] [DistribSMul M A] [SMulCommClass M R A] :
    Module R (FixedPoints M A) where
      __ := addCommGroup M A
      smul r a := ⟨r • a.1, fun m ↦ by rw [smul_comm, a.2]⟩
      one_smul a := by
        ext
        exact one_smul R (a : A)
      mul_smul r s a:= by
        ext
        exact mul_smul r s (a : A)
      smul_zero r := by
        ext
        exact smul_zero (r : R)
      smul_add r a b := by
        ext
        exact smul_add r (a : A) (b : A)
      add_smul r s a := by
        ext
        exact add_smul r s (a : A)
      zero_smul a := by
        ext
        exact zero_smul R (a : A)
