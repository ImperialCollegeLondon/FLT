/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsSepClosed

/-!

# Torsion of an elliptic curve over a separably closed field

Let `E` be an elliptic curve over a separably closed field `k` and let `n` be a natural
number which is nonzero in `k`. Then the `n`-torsion subgroup of `E(k)` is free of rank 2
over `ℤ/nℤ`.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation

-- let k be a separably closed field (`DecidableEq` is needed for the group law on `(E⁄k).Point`)
variable (k : Type*) [Field k] [IsSepClosed k] [DecidableEq k]

-- Let E/k be an elliptic curve
variable (E : WeierstrassCurve k) [E.IsElliptic]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : k)]

-- then the n-torsion of E(k) is free rank 2 over ℤ/nℤ
theorem WeierstrassCurve.torsion_rank_two :
    Nonempty (AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) ≃+ (ZMod n) × (ZMod n)) :=
  sorry
