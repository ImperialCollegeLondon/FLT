import Mathlib

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
