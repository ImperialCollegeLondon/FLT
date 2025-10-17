import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.Basic.FreyPackage

variable (P : FreyPackage)

open GaloisRepresentation

lemma FreyPackage.hp_odd : Odd P.p := Nat.Prime.odd_of_ne_two P.pp <|
  have := P.hp5; by linarith

noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

theorem FreyPackage.FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd sorry
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FLT.FreyPackage.FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry -- TODO prove this
