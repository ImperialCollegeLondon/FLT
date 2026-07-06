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

# The Weil pairing

Let `E` be an elliptic curve over a separably closed field `k` and let `n` be a natural
number which is nonzero in `k`. This file states the existence of the Weil pairing, a
bilinear pairing on the `n`-torsion of `E(k)` with values in the `n`-th roots of unity
of `k`.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points

-- let k be a separably closed field (`DecidableEq` is needed for the group law on `(E⁄k).Point`)
variable (k : Type*) [Field k] [IsSepClosed k] [DecidableEq k]

-- Let E/k be an elliptic curve
variable (E : WeierstrassCurve k) [E.IsElliptic]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : k)]

def WeierstrassCurve.weilPairing :
    AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
    AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
    Additive (rootsOfUnity n k) :=
  sorry
