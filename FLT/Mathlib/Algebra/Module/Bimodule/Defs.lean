/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Algebra.Defs

/-!
# A native right-module class, and bimodules

**This file is an experiment** (build one to throw away), to inform a design discussion:
see the `Right actions on tensor products (again)` and `product of modules over product
of rings` threads on Zulip.

`M` is an `(A, B)`-bimodule if it is a left `A`-module and a right `B`-module and the two
actions commute: `(a • m) <• b = a • (m <• b)`. Mathlib can already express this by
encoding the right action as a left action of the opposite ring:
`[Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]` (see
`Mathlib/Algebra/Module/Bimodule.lean`). This file instead prototypes a *native*
right-module class `RightModule B M`, with notation `m <• b`, together with a
`Prop`-valued mixin `Bimodule A M B` asserting that the two actions commute.

Deliberately, there is **no** instance in either direction between `RightModule B M`
and `Module Bᵐᵒᵖ M`, nor (in the commutative case) between `RightModule B M` and
`Module B M`. The point of the experiment is to discover how much of the `Module` API a
native right action must then duplicate, and how much can instead be recovered through
explicit `restrictScalars`-style transport; the transport definitions live in
`FLT.Mathlib.Algebra.Module.Bimodule.Basic`.

## Main definitions

* `RightModule B M`: the semiring `B` acts on the additive monoid `M` on the right;
  notation `m <• b`, scoped in the `Bimodule` namespace.
* `Bimodule A M B`: `M` is an `(A, B)`-bimodule, i.e. `M` carries a left `A`-action and a
  right `B`-action which commute. The argument order matches the mathematical
  notation `ₐM_b`. This is a mixin in the style of `SMulCommClass`, so "`𝔸_L` is an
  `(L, 𝔸_K)`-bimodule" is said with the pair of instances `RightModule 𝔸_K 𝔸_L` and
  `Bimodule L 𝔸_L 𝔸_K`.
* `RightModule.ofRingHom f`: a ring homomorphism `f : B →+* S` makes `S` a right
  `B`-module by right multiplication, `s <• b = s * f b`.
* `Bimodule.ofRingHom f`: if moreover `S` is a left `A`-module with
  `IsScalarTower A S S` (e.g. if `S` is an `A`-algebra) then `RightModule.ofRingHom f`
  makes `S` an `(A, B)`-bimodule. This is the primitive bimodule constructor: right
  multiplication by `f b` commutes with left multiplication (associativity) and with any
  tower action. The motivating example is `𝔸_L` as an `(L, 𝔸_K)`-bimodule, in
  `FLT.NumberField.AdeleRing.Bimodule`.

## Notation

* `m <• b` for `RightModule.rsmul m b`, scoped in the `Bimodule` namespace. This is
  deliberately the same arrow, with the same precedences, as mathlib's scoped
  `RightActions` notation `m <• b = MulOpposite.op b • m`, so that code written in the
  native and in the op-encoded style reads identically. Opening both scopes only causes
  ambiguity if both a `RightModule B M` and an `SMul Bᵐᵒᵖ M` instance are present.

## Naming

Lemmas are named by the left-to-right order of the elements appearing in the statement,
so `rsmul_one : m <• 1 = m` mirrors `one_smul`, `add_rsmul : (m + n) <• b = _` mirrors
`smul_add`, and `rsmul_add : m <• (b + c) = _` mirrors `add_smul`.
-/

@[expose] public section

/-- A right module structure of a semiring `B` on an additive commutative monoid `M`,
written `m <• b` (notation scoped in the `Bimodule` namespace): an action satisfying
`m <• (b * c) = (m <• b) <• c` which is additive in both variables.

This is `Module Bᵐᵒᵖ M` in all but encoding; deliberately, there is no instance in either
direction between the two spellings (`RightModule.moduleOp` and `RightModule.ofModuleOp`
are the corresponding `def`s). -/
class RightModule (B M : Type*) [Semiring B] [AddCommMonoid M] where
  /-- `rsmul m b`, written `m <• b`, is the right action of `b : B` on `m : M`. -/
  rsmul : M → B → M
  /-- One acts trivially: `m <• 1 = m`. Use `rsmul_one` instead. -/
  protected rsmul_one : ∀ (m : M), rsmul m 1 = m
  /-- Right actions compose contravariantly: `m <• (b * c) = (m <• b) <• c`.
  Use `rsmul_mul` instead. -/
  protected rsmul_mul : ∀ (m : M) (b c : B), rsmul m (b * c) = rsmul (rsmul m b) c
  /-- The action distributes over addition in `M`. Use `add_rsmul` instead. -/
  protected add_rsmul : ∀ (m n : M) (b : B), rsmul (m + n) b = rsmul m b + rsmul n b
  /-- The action is additive in the scalar. Use `rsmul_add` instead. -/
  protected rsmul_add : ∀ (m : M) (b c : B), rsmul m (b + c) = rsmul m b + rsmul m c
  /-- Zero is fixed by the action. Use `zero_rsmul` instead. -/
  protected zero_rsmul : ∀ (b : B), rsmul 0 b = 0
  /-- The zero scalar acts as zero. Use `rsmul_zero` instead. -/
  protected rsmul_zero : ∀ (m : M), rsmul m 0 = 0

namespace Bimodule

@[inherit_doc RightModule.rsmul]
scoped notation3:73 m:73 " <• " b:74 => RightModule.rsmul m b

end Bimodule

open scoped Bimodule

section RightModule

variable {B M : Type*} [Semiring B] [AddCommMonoid M] [RightModule B M]

@[simp]
theorem rsmul_one (m : M) : m <• (1 : B) = m :=
  RightModule.rsmul_one m

theorem rsmul_mul (m : M) (b c : B) : m <• (b * c) = (m <• b) <• c :=
  RightModule.rsmul_mul m b c

@[simp]
theorem add_rsmul (m n : M) (b : B) : (m + n) <• b = m <• b + n <• b :=
  RightModule.add_rsmul m n b

theorem rsmul_add (m : M) (b c : B) : m <• (b + c) = m <• b + m <• c :=
  RightModule.rsmul_add m b c

@[simp]
theorem zero_rsmul (b : B) : (0 : M) <• b = 0 :=
  RightModule.zero_rsmul b

@[simp]
theorem rsmul_zero (m : M) : m <• (0 : B) = 0 :=
  RightModule.rsmul_zero m

/-- Right action by `b : B`, bundled as an additive monoid homomorphism `M →+ M`. -/
@[simps]
def RightModule.rsmulAddMonoidHom (b : B) : M →+ M where
  toFun m := m <• b
  map_zero' := zero_rsmul b
  map_add' m n := add_rsmul m n b

end RightModule

section AddCommGroup

variable {B M : Type*} [Semiring B] [AddCommGroup M] [RightModule B M]

@[simp]
theorem neg_rsmul (m : M) (b : B) : (-m) <• b = -(m <• b) :=
  map_neg (RightModule.rsmulAddMonoidHom b) m

theorem sub_rsmul (m n : M) (b : B) : (m - n) <• b = m <• b - n <• b :=
  map_sub (RightModule.rsmulAddMonoidHom b) m n

end AddCommGroup

/-- `M` is an `(A, B)`-bimodule: `M` is simultaneously a left `A`-module and a right
`B`-module, and the two actions commute. The argument order `Bimodule A M B` matches the
mathematical notation. This is a mixin in the style of `SMulCommClass`, taking the two
actions as instance arguments.

Deliberately, a bimodule structure produces no `Module` instance for the right-hand ring:
there is no path from `Bimodule A M B` to `Module B M` or `Module Bᵐᵒᵖ M`. -/
class Bimodule (A : Type*) (M : Type*) (B : Type*) [Semiring A] [Semiring B]
    [AddCommMonoid M] [Module A M] [RightModule B M] : Prop where
  /-- The left and right actions commute. Use `smul_rsmul` instead. -/
  protected smul_rsmul : ∀ (a : A) (m : M) (b : B), (a • m) <• b = a • (m <• b)

@[simp]
theorem smul_rsmul {A M B : Type*} [Semiring A] [Semiring B] [AddCommMonoid M]
    [Module A M] [RightModule B M] [Bimodule A M B] (a : A) (m : M) (b : B) :
    (a • m) <• b = a • (m <• b) :=
  Bimodule.smul_rsmul a m b

section NatInt

variable {M B : Type*} [Semiring B]

/-- Every right module is a `(ℕ, B)`-bimodule. -/
instance Bimodule.nat [AddCommMonoid M] [RightModule B M] : Bimodule ℕ M B where
  smul_rsmul n m b := map_nsmul (RightModule.rsmulAddMonoidHom b) n m

/-- Every right module over an additive group is a `(ℤ, B)`-bimodule. -/
instance Bimodule.int [AddCommGroup M] [RightModule B M] : Bimodule ℤ M B where
  smul_rsmul n m b := map_zsmul (RightModule.rsmulAddMonoidHom b) n m

end NatInt

section SelfAction

variable {B : Type*} [Semiring B]

/-- A semiring is a right module over itself, acting by right multiplication.

Note the `K = L` caveat: if some other `RightModule B B` structure arises (e.g. from
`RightModule.ofRingHom` applied to an endomorphism of `B`) it will clash with this one. -/
instance Semiring.toRightModule : RightModule B B where
  rsmul := (· * ·)
  rsmul_one := mul_one
  rsmul_mul m b c := (mul_assoc m b c).symm
  add_rsmul := add_mul
  rsmul_add := mul_add
  zero_rsmul := zero_mul
  rsmul_zero := mul_zero

@[simp]
theorem rsmul_eq_mul (x b : B) : x <• b = x * b :=
  rfl

/-- A semiring `B` is an `(A, B)`-bimodule for any left action commuting with right
multiplication; in particular any `A`-algebra is an `(A, B := itself)`-bimodule. -/
instance IsScalarTower.toBimodule {A : Type*} [Semiring A] [Module A B]
    [IsScalarTower A B B] : Bimodule A B B :=
  ⟨fun a m b ↦ smul_mul_assoc a m b⟩

end SelfAction

section OfRingHom

variable {A B S : Type*} [Semiring A] [Semiring B] [Semiring S]

/-- A ring homomorphism `f : B →+* S` makes `S` a right `B`-module by right
multiplication: `s <• b = s * f b`.

This is a `def`, not an instance, because `f` cannot be inferred; compare
`RingHom.toAlgebra`. Instances built from it are definitionally transparent, so a
declaration site can (and should) restate the action as a `rfl`-lemma, e.g.
`x <• b = x * f b`. -/
@[instance_reducible]
def RightModule.ofRingHom (f : B →+* S) : RightModule B S where
  rsmul s b := s * f b
  rsmul_one m := by simp
  rsmul_mul m b c := by simp [mul_assoc]
  add_rsmul m n b := add_mul m n (f b)
  rsmul_add m b c := by simp [mul_add]
  zero_rsmul b := zero_mul (f b)
  rsmul_zero m := by simp

/-- The primitive bimodule constructor: if `S` is a left `A`-module whose action commutes
with right multiplication (`IsScalarTower A S S`, e.g. `S` an `A`-algebra), then any ring
homomorphism `f : B →+* S`, acting by right multiplication, makes `S` an
`(A, B)`-bimodule.

Stated with `letI` since the `RightModule` structure is data; at a declaration site where
`RightModule.ofRingHom f` has been registered as an instance, this proves the
corresponding `Bimodule A S B` instance directly. -/
theorem Bimodule.ofRingHom [Module A S] [IsScalarTower A S S] (f : B →+* S) :
    letI := RightModule.ofRingHom f
    Bimodule A S B :=
  letI := RightModule.ofRingHom f
  ⟨fun a m b ↦ smul_mul_assoc a m (f b)⟩

end OfRingHom
