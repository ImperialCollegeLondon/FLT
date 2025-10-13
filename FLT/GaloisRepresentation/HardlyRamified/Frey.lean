import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.Deformations.RepresentationTheory.EllipticCurve
import FLT.Basic.Reductions

variable (P : FLT.FreyPackage)

open GaloisRepresentation

theorem FLT.FreyPackage.FreyCurve.isHardlyRamified :
    have : Fact (P.p.Prime) := sorry
    let : Algebra ℤ_[P.p] (ZMod P.p) := sorry
    have : Module.Finite (ZMod P.p) (P.freyCurve.n_torsion' P.p) := sorry
    IsHardlyRamified (show Odd P.p from sorry) sorry
      (P.freyCurve.galoisRep P.p (show 0 < P.p from sorry)) :=
  sorry
