import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.Lift
import FLT.GaloisRepresentation.HardlyRamified.Family
import FLT.GaloisRepresentation.HardlyRamified.Threeadic
import FLT.Basic.FreyPackage
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.KnownIn1980s
import Mathlib.Tactic.Cases



variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

lemma Ideal.comap_ne_bot_of_isIntegral (R : Type*) {S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal S} (hI : I ≠ ⊥) :
    I.comap (algebraMap R S) ≠ ⊥ := by
  obtain ⟨i, hiI, hi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact Ideal.comap_ne_bot_of_algebraic_mem hi0 hiI <| Algebra.IsAlgebraic.isAlgebraic i

theorem galois_rep_reducible_of_frobenii (M : Type*) (p : ℕ) [Fact (Nat.Prime p)] [AddCommGroup M]
  [Module (ZMod p) M] [Module.Free (ZMod p) M] [Module.Finite (ZMod p) M]
    (ρ : GaloisRep ℚ (ZMod p) M) (S : Finset (IsDedekindDomain.HeightOneSpectrum
     (NumberField.RingOfIntegers ℚ))) (h : ∀ v ∉ S, 3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val →
      ↑p ∉ v.asIdeal → LinearMap.charpoly ((ρ.toLocal v)
       (Field.AbsoluteGaloisGroup.adicArithFrob v)) = Polynomial.map (algebraMap ℤ (ZMod p))
        ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ((toNatPrime v).val : ℤ))))
         : ¬ GaloisRep.IsIrreducible ρ := by
          knownin1980s

theorem EllipticCurve.torsion_has_rank2 {K : Type*} [Field K] (E : WeierstrassCurve K)
  [E.IsElliptic] [DecidableEq (AlgebraicClosure K)] (p : ℕ)
  [fact : Fact (Nat.Prime p)] (hp : (p : K) ≠ 0) :
  Module.rank (ZMod p) ((E.map (algebraMap K (AlgebraicClosure K))).n_torsion p) = 2 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := (E.map (algebraMap K (AlgebraicClosure K))).n_torsion p)
    rw[WeierstrassCurve.n_torsion_card] at this
    · simp only [Nat.card_eq_fintype_card, ZMod.card] at this
      have : 2 = Module.finrank (ZMod p) ((E.map (algebraMap K (AlgebraicClosure K))).n_torsion p)
        := by
        apply Nat.pow_right_injective (Nat.Prime.two_le fact.out)
        dsimp
        exact this
      rw[← Module.finrank_eq_rank, ← this]
      rfl
    · rw[show (p : AlgebraicClosure K) = (algebraMap K (AlgebraicClosure K)) (p : K) from rfl]
      rw[show (0 : AlgebraicClosure K) = (algebraMap K (AlgebraicClosure K)) 0 by simp]
      intro hyp
      apply RingHom.injective (algebraMap K (AlgebraicClosure K)) at hyp
      exact hp hyp

theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd (EllipticCurve.torsion_has_rank2 P.freyCurve P.p
      (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero this.out)))
        (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry
