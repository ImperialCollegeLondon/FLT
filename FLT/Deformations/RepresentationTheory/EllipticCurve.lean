import FLT.Deformations.RepresentationTheory.GaloisRep -- definition of GaloisRep as cts action
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.ZMod
import FLT.EllipticCurve.Torsion

-- **TODO** fill in the sorry

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

open WeierstrassCurve WeierstrassCurve.Affine

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
noncomputable def WeierstrassCurve.galoisRep (n : ℕ) (hn : 0 < n) :
    GaloisRep K (ZMod n) (E.n_torsion n) :=
  let foo : TopologicalSpace (Module.End (ZMod n) (E.n_torsion n)) := moduleTopology (ZMod n) _
  { __ := WeierstrassCurve.torsionGaloisRepresentation _ _ (AlgebraicClosure K)
    continuous_toFun := sorry
  }
