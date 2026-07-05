import Mathlib

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
