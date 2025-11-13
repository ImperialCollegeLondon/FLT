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

set_option linter.unusedVariables false
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

set_option linter.unusedVariables false
theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd (EllipticCurve.torsion_has_rank2 P.freyCurve P.p
      (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero this.out)))
        (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) := knownin1980s

-- What follows is an experimental draft of an alternative strategy with reducibility, this is far
-- from ready.

theorem irreducible_of_irreducible_base_change {K E F : Type*} [Field K] [Field E] [Field F]
  [TopologicalSpace E] [IsTopologicalRing E] [TopologicalSpace F] [IsTopologicalRing F]
  [Algebra E F] {V : Type*} [AddCommGroup V] [Module E V] [Module.Finite E V] [ContinuousSMul E F]
  (ρ : GaloisRep K E V) : GaloisRep.IsIrreducible (GaloisRep.baseChange F ρ) →
  GaloisRep.IsIrreducible ρ := sorry

theorem reducible_conj_reducible_iff {K R : Type*} [Field K] [TopologicalSpace R] [Field R]
  [IsTopologicalRing R] {V W : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
  (ρ : GaloisRep K R V) (e : V ≃ₗ[R] W) : GaloisRep.IsIrreducible ρ ↔
  GaloisRep.IsIrreducible (GaloisRep.conj ρ e) := by sorry

set_option linter.unusedVariables false
theorem irreducible_of_isCompatible_iff {K : Type*} [Field K] [NumberField K]
  (E : Type*) [Field E] [NumberField E] (T : GaloisRepFamily K E 2) (comp : T.isCompatible)
  {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
  (φ : E →+* AlgebraicClosure ℚ_[p]) (ψ : E →+* AlgebraicClosure ℚ_[q]) :
  GaloisRep.IsIrreducible (T _ φ) ↔ GaloisRep.IsIrreducible (T _ ψ) := knownin1980s

theorem irreducible_of_irreducible_reduction {K R : Type*} [Field K] [TopologicalSpace R]
  [CommRing R] [IsTopologicalRing R] [IsLocalRing R] [IsDomain R] {V : Type*} [AddCommGroup V]
  [Module R V] [Module.Finite R V] [Module.Free R V] (ρ : GaloisRep K R V) : GaloisRep.IsIrreducible
    (GaloisRep.baseChange (IsLocalRing.ResidueField R) ρ) → GaloisRep.IsIrreducible
      (GaloisRep.baseChange (FractionRing R) ρ) := sorry

def tensor_associator {R : Type*} (S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra S T] [Algebra R T] [IsScalarTower R S T] (V : Type*) [AddCommGroup V] [Module R V] :
  TensorProduct R T V ≃ₗ[T] TensorProduct S T (TensorProduct R S V) := by exact
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T V).symm

theorem base_change_trans {K R : Type} (S T : Type*) [Field K] [TopologicalSpace R] [CommRing R]
  [IsTopologicalRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [TopologicalSpace T]
  [CommRing T] [IsTopologicalRing T] [Algebra R S] [ContinuousSMul R S] [Algebra S T] [Algebra R T]
  [ContinuousSMul S T] [IsScalarTower R S T] [ContinuousSMul R T]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
  (ρ : GaloisRep K R V) : GaloisRep.conj (GaloisRep.baseChange T ρ) (tensor_associator S T V) =
  (GaloisRep.baseChange T (GaloisRep.baseChange S ρ)) := by
    refine GaloisRep.ext_iff.mpr ?_
    intro σ
    sorry

lemma det_baseChange {K A B M : Type*} [Field K] [CommRing A] [TopologicalSpace A] [CommRing B]
  [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B] [AddCommGroup M]
  [Module A M] [IsTopologicalRing A] [Module.Finite A M] [Module.Free A M]
  (ρ : GaloisRep K A M) (g : Field.absoluteGaloisGroup K) :
    (GaloisRep.baseChange B ρ).det g = Algebra.algebraMap (ρ.det g) := by
  apply LinearMap.det_baseChange

theorem isAbsolutelyIrreducible_of_irreducible_odd {R : Type*} [TopologicalSpace R] [Field R]
  [IsTopologicalRing R] {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
  (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V) (ρodd : GaloisRep.det ρ complexConjugation
  = -1) (hρ : GaloisRep.IsIrreducible ρ) : GaloisRep.IsAbsolutelyIrreducible ρ := sorry

theorem FreyCurve.torsion_not_isIrreducible' :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) := by
    have hard_ram := FreyCurve.torsion_isHardlyRamified P
    intro irrep
    set ρ := (P.freyCurve.galoisRep P.p P.hppos)
    have fact : Fact (P.p.Prime) := ⟨P.pp⟩
    have lifts := IsHardlyRamified.lifts P.hp_odd ((P.freyCurve.map (algebraMap ℚ
      (AlgebraicClosure ℚ))).n_torsion P.p)
      (hV := EllipticCurve.torsion_has_rank2 P.freyCurve P.p
      (Nat.cast_ne_zero.mpr (FreyPackage.hp0 P))) ρ irrep hard_ram
    rcases lifts with ⟨R, rng, loc, top, trn, dom, alg, lh, fin, free, tm, almd,
      st, ctml, V, ab, mod, fin', free', rk2, σ, φ, hσ, σ_cong_ρ⟩
    have family := IsHardlyRamified.mem_isCompatible P.hp_odd rk2 hσ
    rcases family with ⟨E, fld, num, T, comp, hT⟩
    obtain ⟨hT1, hT2⟩ := hT
    rcases hT2 with ⟨alg'', smul, ψ, r', compσ⟩
    specialize hT1 Nat.fact_prime_three (show Odd 3 by decide)
    have i : E →+* AlgebraicClosure ℚ_[3] := by
      apply Classical.choice
      apply NumberField.Embeddings.instNonemptyRingHom
    specialize hT1 i
    rcases hT1 with ⟨R', rng', top', trn', loc', alg', fin'', free'', dom', alg''',
      sc', mtp', csm', W, ab', mod', fin''', free''', rk2', τ, r'', hτ⟩
    obtain ⟨hτ1, hτ2⟩ := hτ
    have reducible_three := IsHardlyRamified.three_adic' W rk2' hτ1
    have _ : FaithfulSMul R' (AlgebraicClosure ℚ_[3]) := sorry
    have _ : Algebra (FractionRing R') (AlgebraicClosure ℚ_[3]) :=
      FractionRing.liftAlgebra R' (AlgebraicClosure ℚ_[3])
    have _ : ContinuousSMul (FractionRing R') (AlgebraicClosure ℚ_[3]) := sorry
    have _ : IsScalarTower R' (FractionRing R') (AlgebraicClosure ℚ_[3]) := sorry
    have reducible_three' : ¬GaloisRep.IsIrreducible
      (GaloisRep.baseChange (AlgebraicClosure ℚ_[3]) τ) := by
      rw[reducible_conj_reducible_iff _ (tensor_associator (FractionRing R')
        (AlgebraicClosure ℚ_[3]) W)]
      rw[base_change_trans (FractionRing R') (AlgebraicClosure ℚ_[3]) τ]
      intro irrep3
      apply irreducible_of_irreducible_base_change _ at irrep3
      exact reducible_three irrep3
    rw[reducible_conj_reducible_iff _ r'', hτ2] at reducible_three'
    rw[irreducible_of_isCompatible_iff E T comp i ψ, ← compσ] at reducible_three'
    rw[← reducible_conj_reducible_iff _ r'] at reducible_three'
    have reducible_p : ¬GaloisRep.IsIrreducible (GaloisRep.baseChange (FractionRing R) σ) := by
      intro irrep_p
      apply isAbsolutelyIrreducible_of_irreducible_odd at irrep_p
      · have ⟨irrep_p⟩ := irrep_p
        haveI i2 : FaithfulSMul R (AlgebraicClosure ℚ_[P.p]) := sorry
        haveI i3 : Algebra (FractionRing R) (AlgebraicClosure ℚ_[P.p]) := FractionRing.liftAlgebra R
          (AlgebraicClosure ℚ_[P.p])
        haveI i4 : ContinuousSMul (FractionRing R) (AlgebraicClosure ℚ_[P.p]) := sorry
        haveI i5 : IsScalarTower R (FractionRing R) (AlgebraicClosure ℚ_[P.p]) := sorry
        specialize irrep_p (AlgebraicClosure ℚ_[P.p]) (AlgebraicClosure.instField ℚ_[P.p]) _ sorry
          i3 i4
        rw[← base_change_trans] at irrep_p
        rw[← reducible_conj_reducible_iff] at irrep_p
        exact reducible_three' irrep_p
      · rw[Module.rank_baseChange, Cardinal.lift_id, rk2]
      · rw[det_baseChange]
        suffices (σ.det complexConjugation) = -1 by
          rw[this]
          simp only [map_neg, map_one]
        apply odd_of_hardlyRamified (FreyPackage.hp_odd P) rk2
        exact hσ
    apply reducible_p
    apply irreducible_of_irreducible_reduction
    have _ : Algebra (IsLocalRing.ResidueField R) (ZMod P.p) := sorry
    have _ : IsScalarTower R (IsLocalRing.ResidueField R) (ZMod P.p) := sorry
    have _ : ContinuousSMul (IsLocalRing.ResidueField R) (ZMod P.p) := sorry
    have irrep_σ_p : (GaloisRep.baseChange (ZMod P.p) σ).IsIrreducible := by
      rw[reducible_conj_reducible_iff (GaloisRep.baseChange (ZMod P.p) σ) φ, σ_cong_ρ]
      exact irrep
    rw[reducible_conj_reducible_iff (GaloisRep.baseChange (ZMod P.p) σ)
      (tensor_associator (IsLocalRing.ResidueField R) (ZMod P.p) V)] at irrep_σ_p
    rw[base_change_trans] at irrep_σ_p
    exact irreducible_of_irreducible_base_change (GaloisRep.baseChange
    (IsLocalRing.ResidueField R) σ) irrep_σ_p
