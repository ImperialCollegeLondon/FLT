/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Mathlib.Algebra.Module.Bimodule.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Opposite

/-!
# Basic API for right modules and bimodules

This file continues the bimodule experiment of
`FLT.Mathlib.Algebra.Module.Bimodule.Defs`. It contains three kinds of material, which
should be read as three separate data points for the design discussion:

1. **Cheap duplication.** Lemmas about the right action which mirror the `Module` API and
   whose proofs are one-liners (sums, units cancellation, `compHom`-style restriction of
   the right scalars, restriction of the left scalars along a tower). This is the part of
   the duplication that costs essentially nothing.

2. **Transport.** `restrictScalars`-style `def`s (never instances) converting between
   `RightModule B M` and `Module Bᵐᵒᵖ M` (`RightModule.moduleOp`,
   `RightModule.ofModuleOp`), and in the commutative case between `RightModule B M` and
   `Module B M` (`RightModule.toModule`, `RightModule.ofModule`). These make the entire
   op-encoded `Module` API available locally via `letI`, at the price of carrying a
   non-instance module structure through a proof.

3. **A bundled-structure probe.** A minimal theory of right-linear maps
   `RightLinearMap B M N`, notation `M →ᵣ[B] N`, to measure what duplicating a bundled
   structure costs. Note that the additive half (`AddMonoidHomClass`) is *reused*, not
   duplicated: only the `rsmul`-side is new.
-/

@[expose] public section

open scoped Bimodule

section SumLemmas

variable {ι B M : Type*} [Semiring B] [AddCommMonoid M] [RightModule B M]

/-- The right action of a fixed scalar on a fixed element, as an additive monoid
homomorphism in the scalar. See `RightModule.rsmulAddMonoidHom` for additivity in the
module element. -/
def RightModule.rsmulScalarAddMonoidHom (m : M) : B →+ M where
  toFun b := m <• b
  map_zero' := rsmul_zero m
  map_add' := rsmul_add m

@[simp]
theorem RightModule.rsmulScalarAddMonoidHom_apply (m : M) (b : B) :
    RightModule.rsmulScalarAddMonoidHom m b = m <• b :=
  rfl

theorem Finset.sum_rsmul (s : Finset ι) (f : ι → M) (b : B) :
    (∑ i ∈ s, f i) <• b = ∑ i ∈ s, f i <• b :=
  map_sum (RightModule.rsmulAddMonoidHom b) f s

theorem Finset.rsmul_sum (m : M) (s : Finset ι) (f : ι → B) :
    m <• (∑ i ∈ s, f i) = ∑ i ∈ s, m <• f i :=
  map_sum (RightModule.rsmulScalarAddMonoidHom m) f s

end SumLemmas

section Units

variable {B M : Type*} [Semiring B] [AddCommMonoid M] [RightModule B M]

/-- Right action of a unit is injective; mirror of `smul_left_cancel`. -/
theorem rsmul_right_cancel (u : Bˣ) {m n : M} (h : m <• (u : B) = n <• (u : B)) : m = n := by
  have := congrArg (· <• ((u⁻¹ : Bˣ) : B)) h
  simpa [← rsmul_mul] using this

end Units

section CompHom

variable {B' B M : Type*} [Semiring B'] [Semiring B] [AddCommMonoid M]

/-- Restriction of the right scalars along a ring homomorphism `g : B' →+* B`; the mirror
of `Module.compHom`. Not an instance, since `g` cannot be inferred. -/
@[instance_reducible]
def RightModule.compHom [RightModule B M] (g : B' →+* B) : RightModule B' M where
  rsmul m b' := m <• g b'
  rsmul_one m := by simp
  rsmul_mul m b c := by simp [rsmul_mul]
  add_rsmul m n b := add_rsmul m n (g b)
  rsmul_add m b c := by simp [rsmul_add]
  zero_rsmul b := zero_rsmul (g b)
  rsmul_zero m := by simp

end CompHom

section RestrictScalars

variable {A' A M B : Type*} [Semiring A'] [Semiring A] [AddCommMonoid M] [Semiring B]

/-- Restriction of the left scalars of a bimodule along a scalar tower: an
`(A, B)`-bimodule is an `(A', B)`-bimodule for any `A'` acting on `A` and `M`
compatibly. Not an instance, since `A` cannot be inferred from the conclusion. -/
theorem Bimodule.restrictScalars (A : Type*) [Semiring A] [Module A' M] [Module A M]
    [SMul A' A] [IsScalarTower A' A M] [RightModule B M] [Bimodule A M B] :
    Bimodule A' M B :=
  ⟨fun a' m b ↦ by rw [← smul_one_smul A a' m, smul_rsmul, smul_one_smul]⟩

end RestrictScalars

section Transport

variable (B M : Type*) [Semiring B] [AddCommMonoid M]

open MulOpposite

/-- Reinterpret a right `B`-module as a left `Bᵐᵒᵖ`-module. Deliberately **not** an
instance: this is the explicit, `restrictScalars`-style bridge to the op-encoded world,
to be used via `letI` when a mathlib `Module` result is needed for a right action. -/
@[instance_reducible]
def RightModule.moduleOp [RightModule B M] : Module Bᵐᵒᵖ M where
  smul b m := m <• b.unop
  one_smul m := rsmul_one m
  mul_smul b c m := by
    change m <• (b * c).unop = (m <• c.unop) <• b.unop
    rw [unop_mul, rsmul_mul]
  smul_zero b := zero_rsmul b.unop
  smul_add b m n := add_rsmul m n b.unop
  add_smul b c m := rsmul_add m b.unop c.unop
  zero_smul m := rsmul_zero m

/-- Reinterpret a left `Bᵐᵒᵖ`-module as a right `B`-module. Deliberately **not** an
instance; inverse to `RightModule.moduleOp`. -/
@[instance_reducible]
def RightModule.ofModuleOp [Module Bᵐᵒᵖ M] : RightModule B M where
  rsmul m b := op b • m
  rsmul_one m := by simp
  rsmul_mul m b c := by rw [op_mul, mul_smul]
  add_rsmul m n b := smul_add (op b) m n
  rsmul_add m b c := by rw [op_add, add_smul]
  zero_rsmul b := smul_zero (op b)
  rsmul_zero m := by simp

/-- A module over a commutative semiring is a right module over it. Deliberately **not**
an instance: in the commutative world the two sides are interchangeable, but making this
an instance would let every left module silently acquire a right action (and vice versa
via `RightModule.toModule`), which is exactly the ambiguity the experiment avoids. -/
@[instance_reducible]
def RightModule.ofModule (B : Type*) [CommSemiring B] [Module B M] : RightModule B M where
  rsmul m b := b • m
  rsmul_one m := one_smul B m
  rsmul_mul m b c := by rw [mul_comm, mul_smul]
  add_rsmul m n b := smul_add b m n
  rsmul_add m b c := add_smul b c m
  zero_rsmul b := smul_zero b
  rsmul_zero m := zero_smul B m

/-- A right module over a commutative semiring is a module over it. Deliberately **not**
an instance; inverse to `RightModule.ofModule`. -/
@[instance_reducible]
def RightModule.toModule (B : Type*) [CommSemiring B] [RightModule B M] : Module B M where
  smul b m := m <• b
  one_smul m := rsmul_one m
  mul_smul b c m := by
    change m <• (b * c) = (m <• c) <• b
    rw [mul_comm, rsmul_mul]
  smul_zero b := zero_rsmul b
  smul_add b m n := add_rsmul m n b
  add_smul b c m := rsmul_add m b c
  zero_smul m := rsmul_zero m

/-- A bimodule structure transports to an `SMulCommClass` for the op-encoded actions:
this is the statement that the native and op-encoded notions of bimodule agree. -/
theorem Bimodule.smulCommClass_moduleOp (A : Type*) [Semiring A] [Module A M]
    [RightModule B M] [Bimodule A M B] :
    letI := RightModule.moduleOp B M
    SMulCommClass A Bᵐᵒᵖ M :=
  letI := RightModule.moduleOp B M
  ⟨fun a b m ↦ (smul_rsmul a m b.unop).symm⟩

end Transport

/-! ### Right-linear maps: the bundled-structure probe

A minimal duplicate of the `LinearMap` skeleton for right modules, to price bundled
structures. Additive structure (`AddMonoidHomClass` and everything it implies:
`map_zero`, `map_add`, `map_sum`, `map_neg`, ...) is inherited, not duplicated. -/

section RightLinearMapDef

variable (B M N : Type*) [Semiring B] [AddCommMonoid M] [AddCommMonoid N]

/-- A right `B`-linear map between right `B`-modules: an additive monoid homomorphism
commuting with the right action. Notation `M →ᵣ[B] N`, scoped in the `Bimodule`
namespace. -/
structure RightLinearMap [RightModule B M] [RightModule B N] extends M →+ N where
  /-- The map commutes with the right action. Use `RightLinearMap.map_rsmul` instead. -/
  protected map_rsmul' : ∀ (m : M) (b : B), toFun (m <• b) = toFun m <• b

@[inherit_doc]
scoped[Bimodule] notation:25 M " →ᵣ[" B "] " N => RightLinearMap B M N

end RightLinearMapDef

namespace RightLinearMap

variable {B M N P : Type*} [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
  [AddCommMonoid P] [RightModule B M] [RightModule B N] [RightModule B P]

instance : FunLike (M →ᵣ[B] N) M N where
  coe f := f.toAddMonoidHom
  coe_injective f g h := by
    cases f; cases g
    congr 1
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (M →ᵣ[B] N) M N where
  map_add f := f.toAddMonoidHom.map_add
  map_zero f := f.toAddMonoidHom.map_zero

@[ext]
theorem ext {f g : M →ᵣ[B] N} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem coe_toAddMonoidHom (f : M →ᵣ[B] N) : ⇑f.toAddMonoidHom = ⇑f :=
  rfl

@[simp]
theorem map_rsmul (f : M →ᵣ[B] N) (m : M) (b : B) : f (m <• b) = f m <• b :=
  f.map_rsmul' m b

/-- The identity as a right-linear map. -/
def id : M →ᵣ[B] M where
  __ := AddMonoidHom.id M
  map_rsmul' _ _ := rfl

@[simp]
theorem id_apply (m : M) : (id : M →ᵣ[B] M) m = m :=
  rfl

/-- Composition of right-linear maps. -/
def comp (g : N →ᵣ[B] P) (f : M →ᵣ[B] N) : M →ᵣ[B] P where
  __ := g.toAddMonoidHom.comp f.toAddMonoidHom
  map_rsmul' m b := by simp

@[simp]
theorem comp_apply (g : N →ᵣ[B] P) (f : M →ᵣ[B] N) (m : M) : g.comp f m = g (f m) :=
  rfl

end RightLinearMap
