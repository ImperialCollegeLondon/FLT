import FLT.Deformations.RepresentationTheory.GaloisRep -- definition of GaloisRep as cts action
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Instances.ZMod

-- **TODO** fill in these sorries

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable instance foo : AddCommGroup E⟮AlgebraicClosure K⟯ :=
  letI : DecidableEq (AlgebraicClosure K) := Classical.typeDecidableEq _
  inferInstance

abbrev WeierstrassCurve.n_torsion' (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E ⟮(AlgebraicClosure K)⟯) n

noncomputable instance bar (n : ℕ) : Module (ZMod n) (E.n_torsion' n) :=
  AddCommGroup.zmodModule sorry

def WeierstrassCurve.galoisRep (n : ℕ) (hn : 0 < n) : GaloisRep K (ZMod n) (E.n_torsion' n) := sorry
