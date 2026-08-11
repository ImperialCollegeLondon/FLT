/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transferring a module structure along a bare `Equiv`

Mathlib PR #42291 replaced `Equiv.module` and `Equiv.linearEquiv` with `AddEquiv`-based
versions, on the grounds that "it is typically easy to construct this richer equivalence".

That is not the case when transporting a structure along an *arbitrary* bijection, as in
`Finite.equivFin M : M ≃ Fin (Nat.card M)`: the target carries no additive structure at all
until it is transported along the bijection, so there is no `AddEquiv` to be had beforehand.
`FLT/Patching/Utils/StructureFiniteness.lean` needs exactly that, so we reinstate the original
`Equiv`-based forms here under primed names.
-/

@[expose] public section

namespace Equiv

variable {R α β : Type*} [Semiring R]

variable (R) in
/-- Transfer `Module` across an `Equiv`, where the additive structure on the source is itself
obtained by transporting the one on the target back along the equivalence. -/
protected abbrev module' (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := e.addCommMonoid
    Module R α :=
  letI := e.addCommMonoid
  e.addEquiv.module R

variable (R) in
/-- An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`, where the `R`-module
structure on `α` is the one obtained by transporting the `R`-module structure on `β` back
along `e`. -/
def linearEquiv' (e : α ≃ β) [AddCommMonoid β] [Module R β] :
    letI := e.addCommMonoid
    letI := e.module' R
    α ≃ₗ[R] β :=
  letI := e.addCommMonoid
  letI := e.module' R
  e.addEquiv.linearEquiv R

end Equiv
