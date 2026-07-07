/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import FLT.Slop.BrauerInduction.Background.Group.Conjugacy

/-!
# Class functions

This file defines `ClassFun k G`, the type of `k`-valued functions on a group
`G` which are constant on conjugacy classes, and develops the basic pointwise
algebraic API for these functions.

A `ClassFun k G` is a function on the conjugacy classes `ConjClasses G` of `G`
with values in `k`; equivalently it is a function `G → k` which takes equal
values on conjugate elements. The file provides the coercion to functions on
`G` (evaluating through `ConjClasses.mk`), a smart constructor `ClassFun.ofFun`
turning a conjugacy-invariant function `G → k` into a class function,
extensionality, constant class functions, the inversion involution, and
pointwise additive, multiplicative, scalar, module, ring, and algebra
structures.

It also identifies class functions with the submodule of all functions
`G → k` satisfying the conjugacy-invariance condition, and records that the
space of class functions is finite-dimensional when `G` is finite.

## Main declarations

* `ClassFun`: class functions, as functions on conjugacy classes.
* `ClassFun.ofFun`: the smart constructor from a conjugacy-invariant `G → k`.
* `ClassFun.const`: the constant class function.
* `ClassFun.involution`: the involution `f ↦ fun g => f g⁻¹`.
* `ClassFun.toSubmodule`: the submodule of functions constant on conjugacy
  classes.
* `ClassFun.toSubmoduleEquiv`: the linear equivalence between `ClassFun k G`
  and `ClassFun.toSubmodule`.
* `ClassFun.evalRingHom`: evaluation at an element of `G`, as a ring
  homomorphism when the coefficients form a semiring.
* `ClassFun.constRingHom`: the inclusion of constant functions.
-/

@[expose] public section

namespace Slop
open Slop

universe u v w

/-- A class function is a `k`-valued function on the conjugacy classes of `G`. -/
structure ClassFun (k : Type u) (G : Type v) [Group G] where
  /-- The underlying function on conjugacy classes. -/
  toFun : ConjClasses G → k

namespace ClassFun

open BigOperators

variable {k : Type u} {G : Type v} [Group G]

variable {H : Type*} [Group H]

section Basic

instance : FunLike (ClassFun k G) G k where
  coe f g := f.toFun (ConjClasses.mk g)
  coe_injective := by
    rintro ⟨f⟩ ⟨g⟩ h
    congr 1
    funext c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    exact congrFun h x

@[simp]
lemma coe_mk (F : ConjClasses G → k) (x : G) :
    ClassFun.mk F x = F (ConjClasses.mk x) :=
  rfl

/--
The smart constructor: a function `G → k` that is constant on conjugacy classes
descends to a class function.
-/
def ofFun (f : G → k) (h : ∀ x y : G, IsConj x y → f x = f y) : ClassFun k G where
  toFun := Quotient.lift f h

@[simp]
lemma ofFun_apply (f : G → k) (h : ∀ x y : G, IsConj x y → f x = f y) (x : G) :
    ofFun f h x = f x :=
  rfl

@[ext]
lemma ext {f g : ClassFun k G}
    (h : ∀ x : G, f x = g x) :
    f = g :=
  DFunLike.ext f g h

/-- A class function takes equal values on conjugate elements. -/
theorem map_conj (f : ClassFun k G) (x y : G) (h : IsConj x y) :
    f x = f y := by
  change f.toFun (ConjClasses.mk x) = f.toFun (ConjClasses.mk y)
  rw [ConjClasses.mk_eq_mk_iff_isConj.mpr h]

lemma apply_eq_apply_of_isConj
    {f : ClassFun k G} {x y : G}
    (h : IsConj x y) :
    f x = f y :=
  f.map_conj x y h

@[simp]
lemma map_conj_eq (f : ClassFun k G) (g x : G) :
    f (x⁻¹ * g * x) = f g := by
  apply f.map_conj
  apply isConj_iff.mpr
  use x
  group

@[simp]
lemma map_conj_eq' (f : ClassFun k G) (g x : G) :
    f (x * g * x⁻¹) = f g := by
    have := map_conj_eq f g x⁻¹
    rw [← this]
    group

/-- The constant class function with value `a : k`. -/
def const (a : k) : ClassFun k G where
  toFun := fun _ => a

@[simp]
lemma const_apply (a : k) (g : G) :
    ClassFun.const (G := G) a g = a :=
  rfl

/-- The involution on class functions sending `f` to `g ↦ f g⁻¹`. -/
def involution (f : ClassFun k G) : ClassFun k G :=
  ofFun (fun g => f g⁻¹)
    (fun _ _ hxy => f.map_conj _ _ (IsConj.inv.mp hxy))

@[simp]
lemma involution_apply (f : ClassFun k G) (g : G) :
    involution f g = f g⁻¹ :=
  rfl

@[simp]
lemma involution_involution (f : ClassFun k G) :
    involution (involution f) = f := by
  ext g
  simp

end Basic

section PointwiseOperations

instance [Zero k] : Zero (ClassFun k G) where
  zero := ⟨fun _ => 0⟩

@[simp]
lemma zero_apply [Zero k] (g : G) :
    (0 : ClassFun k G) g = 0 :=
  rfl

instance [Add k] : Add (ClassFun k G) where
  add f g := ⟨fun c => f.toFun c + g.toFun c⟩

@[simp]
lemma add_apply [Add k]
    (f g : ClassFun k G) (x : G) :
    (f + g) x = f x + g x :=
  rfl

instance [Neg k] : Neg (ClassFun k G) where
  neg f := ⟨fun c => -f.toFun c⟩

@[simp]
lemma neg_apply [Neg k]
    (f : ClassFun k G) (x : G) :
    (-f) x = -f x :=
  rfl

instance [Sub k] : Sub (ClassFun k G) where
  sub f g := ⟨fun c => f.toFun c - g.toFun c⟩

@[simp]
lemma sub_apply [Sub k]
    (f g : ClassFun k G) (x : G) :
    (f - g) x = f x - g x :=
  rfl

instance [One k] : One (ClassFun k G) where
  one := ⟨fun _ => 1⟩

@[simp]
lemma one_apply [One k] (g : G) :
    (1 : ClassFun k G) g = 1 :=
  rfl

instance [Mul k] : Mul (ClassFun k G) where
  mul f g := ⟨fun c => f.toFun c * g.toFun c⟩

@[simp]
lemma mul_apply [Mul k]
    (f g : ClassFun k G) (x : G) :
    (f * g) x = f x * g x :=
  rfl

instance {R : Type w} [SMul R k] :
    SMul R (ClassFun k G) where
  smul r f := ⟨fun c => r • f.toFun c⟩

@[simp]
lemma smul_apply
    {R : Type w} [SMul R k]
    (r : R) (f : ClassFun k G) (x : G) :
    (r • f) x = r • f x :=
  rfl

end PointwiseOperations

section Monoid

variable [Monoid k]

instance : Monoid (ClassFun k G) where
  mul_assoc f g h := by
    ext x
    exact mul_assoc (f x) (g x) (h x)
  one_mul f := by
    ext x
    exact one_mul (f x)
  mul_one f := by
    ext x
    exact mul_one (f x)
  npow := fun n f => ⟨fun c => (f.toFun c) ^ n⟩
  npow_zero := by
    intro f
    ext x
    change (f x) ^ 0 = 1
    exact pow_zero _
  npow_succ := by
    intro n f
    ext x
    change
      (f x) ^ (n + 1) =
        (f x) ^ n * f x
    exact pow_succ _ _

@[simp]
lemma pow_apply
    (f : ClassFun k G) (n : ℕ) (x : G) :
    (f ^ n) x = (f x) ^ n :=
  rfl

end Monoid

section CommMonoid

variable [CommMonoid k]

instance : CommMonoid (ClassFun k G) :=
  { (inferInstance : Monoid (ClassFun k G)) with
    mul_comm := by
      intro f g
      ext x
      exact mul_comm (f x) (g x) }

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid k]

instance : AddCommMonoid (ClassFun k G) where
  add_assoc f g h := by
    ext x
    exact add_assoc (f x) (g x) (h x)
  zero_add f := by
    ext x
    exact zero_add (f x)
  add_zero f := by
    ext x
    exact add_zero (f x)
  add_comm f g := by
    ext x
    exact add_comm (f x) (g x)
  nsmul := fun n f => ⟨fun c => n • f.toFun c⟩
  nsmul_zero := by
    intro f
    ext g
    change (0 : ℕ) • f g = 0
    exact zero_nsmul (f g)
  nsmul_succ := by
    intro n f
    ext g
    change (n + 1) • f g = n • f g + f g
    exact succ_nsmul (f g) n

@[simp]
lemma nsmul_apply
    (n : ℕ) (f : ClassFun k G) (g : G) :
    (n • f) g = n • f g := by
  induction n with
  | zero => simp
  | succ n ih => simp [add_nsmul, ih]

@[simp]
lemma finset_sum_apply
    {ι : Type*} (s : Finset ι)
    (f : ι → ClassFun k G) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma sum_apply
    {ι : Type*} [Fintype ι]
    (f : ι → ClassFun k G) (g : G) :
    (∑ i, f i) g = ∑ i, f i g := by
  simp

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

instance : AddCommGroup (ClassFun k G) where
  neg_add_cancel f := by
    ext x
    exact neg_add_cancel (f x)
  sub_eq_add_neg f g := by
    ext x
    exact sub_eq_add_neg (f x) (g x)
  zsmul := fun n f => ⟨fun c => n • f.toFun c⟩
  zsmul_zero' := by
    intro f
    ext x
    exact zero_zsmul (f x)
  zsmul_succ' := by
    intro n f
    ext x
    change
      ((n : ℤ) + 1) • f x =
        (n : ℤ) • f x + f x
    simpa using (add_zsmul (f x) (n : ℤ) 1)
  zsmul_neg' := by
    intro n f
    ext x
    change
      (-(n.succ : ℤ)) • f x =
        -((n.succ : ℤ) • f x)
    exact neg_zsmul (f x) (n.succ : ℤ)

@[simp]
lemma zsmul_apply
    (n : ℤ) (f : ClassFun k G) (x : G) :
    (n • f) x = n • f x :=
  rfl

end AddCommGroup

section Semiring

variable [Semiring k]

instance : Semiring (ClassFun k G) :=
  { (inferInstance : AddCommMonoid (ClassFun k G)),
    (inferInstance : Monoid (ClassFun k G)) with
    left_distrib := by
      intro f g h
      ext x
      exact left_distrib (f x) (g x) (h x)
    right_distrib := by
      intro f g h
      ext x
      exact right_distrib (f x) (g x) (h x)
    zero_mul := by
      intro f
      ext x
      exact zero_mul (f x)
    mul_zero := by
      intro f
      ext x
      exact mul_zero (f x)
    natCast := fun n => n • (1 : ClassFun k G)
    natCast_zero := by
      ext x
      change (0 : ℕ) • (1 : k) = 0
      simp
    natCast_succ := by
      intro n
      ext x
      change
        (n + 1) • (1 : k) =
          n • (1 : k) + 1
      simp only [succ_nsmul (1 : k) n, nsmul_eq_mul, mul_one] }

@[simp]
lemma natCast_apply (n : ℕ) (x : G) :
    (n : ClassFun k G) x = (n : k) := by
  change n • (1 : k) = (n : k)
  simp

/-- Evaluation at a point `x : G` as a ring homomorphism on class functions. -/
def evalRingHom (x : G) : ClassFun k G →+* k where
  toFun := fun f => f x
  map_one' := by
    simp
  map_mul' := by
    intro f g
    simp
  map_zero' := by
    simp
  map_add' := by
    intro f g
    simp

@[simp]
lemma evalRingHom_apply (x : G) (f : ClassFun k G) :
    evalRingHom (G := G) (k := k) x f = f x :=
  rfl

end Semiring

section Ring

variable [Ring k]

instance : Ring (ClassFun k G) :=
  { (inferInstance : Semiring (ClassFun k G)),
    (inferInstance : AddCommGroup (ClassFun k G)) with
    intCast := fun z => z • (1 : ClassFun k G)
    intCast_ofNat := by
      intro n
      ext x
      simp
    intCast_negSucc := by
      intro n
      ext x
      simp }

@[simp]
lemma intCast_apply (z : ℤ) (x : G) :
    (z : ClassFun k G) x = (z : k) := by
  change z • (1 : k) = (z : k)
  simp

end Ring

section CommSemiring

variable [CommSemiring k]

instance : CommSemiring (ClassFun k G) :=
  { (inferInstance : Semiring (ClassFun k G)) with
    mul_comm := by
      intro f g
      ext x
      exact mul_comm (f x) (g x) }

end CommSemiring

section Algebra

variable [CommSemiring k]

/-- The ring homomorphism sending `a : k` to the constant class function with value `a`. -/
def constRingHom : k →+* ClassFun k G where
  toFun := ClassFun.const (G := G)
  map_zero' := by
    ext x
    rfl
  map_one' := by
    ext x
    rfl
  map_add' := by
    intro a b
    ext x
    rfl
  map_mul' := by
    intro a b
    ext x
    rfl

instance : Algebra k (ClassFun k G) where
  algebraMap := constRingHom (k := k) (G := G)
  commutes' := by
    intro c f
    ext x
    exact mul_comm c (f x)
  smul_def' := by
    intro c f
    ext x
    rfl

end Algebra

section CommRing

variable [CommRing k]

instance : CommRing (ClassFun k G) :=
  { (inferInstance : Ring (ClassFun k G)) with
    mul_comm := by
      intro f g
      ext x
      exact mul_comm (f x) (g x) }

end CommRing

section Module

variable {R : Type w}
variable [Semiring R] [AddCommMonoid k] [Module R k]

instance : Module R (ClassFun k G) where
  one_smul f := by
    ext x
    change (1 : R) • f x = f x
    exact one_smul R (f x)

  mul_smul r s f := by
    ext x
    change (r * s) • f x = r • s • f x
    exact mul_smul r s (f x)

  smul_zero r := by
    ext x
    change r • (0 : k) = 0
    exact smul_zero r

  smul_add r f g := by
    ext x
    change r • (f x + g x) =
      r • f x + r • g x
    exact smul_add r (f x) (g x)

  add_smul r s f := by
    ext x
    change (r + s) • f x =
      r • f x + s • f x
    exact add_smul r s (f x)

  zero_smul f := by
    ext x
    change (0 : R) • f x = 0
    exact zero_smul R (f x)

end Module

section Submodule

variable {R : Type w}
variable [Semiring R] [AddCommMonoid k] [Module R k]

/--
The submodule of functions on `G` that are constant on conjugacy classes.
-/
def toSubmodule : Submodule R (G → k) where
  carrier := {
    f | ∀ x y : G, IsConj x y → f x = f y
  }
  zero_mem' := by
    intro x y hxy
    rfl
  add_mem' := by
    intro f g hf hg x y hxy
    simp only [Pi.add_apply]
    rw [hf x y hxy, hg x y hxy]
  smul_mem' := by
    intro r f hf x y hxy
    simp only [Pi.smul_apply]
    rw [hf x y hxy]

/--
Class functions are linearly equivalent to the submodule of functions that are
constant on conjugacy classes.
-/
def toSubmoduleEquiv :
    ClassFun k G ≃ₗ[R]
      toSubmodule (R := R) (k := k) (G := G) where
  toFun f :=
    ⟨f, f.map_conj⟩
  invFun f :=
    ofFun (f : G → k) f.property
  left_inv f := by
    ext x
    rfl
  right_inv f := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl
  map_smul' r f := by
    ext x
    rfl

end Submodule

section FiniteDimensional

variable [DivisionRing k] [Finite G]

/--
The space of class functions on a finite group is finite-dimensional, since it
embeds linearly into the finite-dimensional function space `G → k`.
-/
noncomputable instance finiteDimensional :
    FiniteDimensional k (ClassFun k G) := by
  letI : Fintype G := Fintype.ofFinite G
  let coeLinearMap : ClassFun k G →ₗ[k] (G → k) := {
    toFun := fun f => f
    map_add' := by
      intro f g
      rfl
    map_smul' := by
      intro c f
      rfl
  }
  have h_injective : Function.Injective coeLinearMap := by
    intro f g h
    apply DFunLike.ext f g
    exact congrFun h
  exact Module.Finite.of_injective coeLinearMap h_injective

end FiniteDimensional

end ClassFun

end Slop
