import FLT.GaloisRepresentation.HardlyRamified.Frey
/-!

# Preliminary reductions of FLT

This file reduces Fermat's Last Theorem
to Mazur's theorem and the Wiles/Taylor--Wiles theorem.

# Main theorems

* `FLT.FreyPackage.false`: There is no Frey Package.
* `Wiles_Taylor_Wiles` : Fermat's Last Theorem is true.

-/

/-!

Given an elliptic curve over `ℚ`, the p-torsion points defined over an algebraic
closure of `ℚ` are a 2-dimensional Galois representation.

What can we say about the Galois
representation attached to the p-torsion of the Frey curve attached to a Frey package?

It follows (after a little work!) from a profound theorem of Mazur that this representation
must be irreducible.

-/

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

open WeierstrassCurve

theorem Mazur_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  knownin1980s

/-!

But it follows from a profound theorem of Ribet, and the even more profound theorem
(proved by Wiles) that the representation cannot be irreducible.

-/
/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

set_option linter.unusedVariables false in
theorem irreducible_of_isCompatible_iff {K : Type*} [Field K] [NumberField K]
  (E : Type*) [Field E] [NumberField E] (T : GaloisRepFamily K E 2) (comp : T.isCompatible)
  {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
  (φ : E →+* AlgebraicClosure ℚ_[p]) (ψ : E →+* AlgebraicClosure ℚ_[q]) :
  GaloisRep.IsIrreducible (T _ φ) ↔ GaloisRep.IsIrreducible (T _ ψ) := knownin1980s

open GaloisRepresentation in
theorem Wiles_Frey (P : FreyPackage) :
  haveI : Fact P.p.Prime := ⟨P.pp⟩
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
    letI fsmul : FaithfulSMul R' (AlgebraicClosure ℚ_[3]) :=
      faithfulSMul_of_padic_fractionRing 3 R' (AlgebraicClosure ℚ_[3])
    letI algf : Algebra (FractionRing R') (AlgebraicClosure ℚ_[3]) :=
      FractionRing.liftAlgebra R' (AlgebraicClosure ℚ_[3])
    have _ : ContinuousSMul (FractionRing R') (AlgebraicClosure ℚ_[3]) :=
      continuousSMul_of_fractionRing R' (AlgebraicClosure ℚ_[3])
    have _ : IsScalarTower R' (FractionRing R') (AlgebraicClosure ℚ_[3]) :=
      FractionRing.isScalarTower_liftAlgebra R' (AlgebraicClosure ℚ_[3])
    have reducible_three' : ¬GaloisRep.IsIrreducible
      (GaloisRep.baseChange (AlgebraicClosure ℚ_[3]) τ) := by
      rw[GaloisRep.reducible_conj_reducible_iff _ (GaloisRep.tensor_associator (FractionRing R')
        (AlgebraicClosure ℚ_[3]) W)]
      rw[GaloisRep.base_change_trans (FractionRing R') (AlgebraicClosure ℚ_[3]) τ]
      intro irrep3
      apply GaloisRep.irreducible_of_irreducible_base_change _ at irrep3
      exact reducible_three irrep3
    rw[GaloisRep.reducible_conj_reducible_iff _ r'', hτ2] at reducible_three'
    rw[irreducible_of_isCompatible_iff E T comp i ψ, ← compσ] at reducible_three'
    rw[← GaloisRep.reducible_conj_reducible_iff _ r'] at reducible_three'
    have reducible_p : ¬GaloisRep.IsIrreducible (GaloisRep.baseChange (FractionRing R) σ) := by
      intro irrep_p
      apply isAbsolutelyIrreducible_of_irreducible_odd at irrep_p
      · have ⟨irrep_p⟩ := irrep_p
        letI i2 : FaithfulSMul R (AlgebraicClosure ℚ_[P.p]) :=
          faithfulSMul_of_padic_fractionRing P.p R (AlgebraicClosure ℚ_[P.p])
        letI i3 : Algebra (FractionRing R) (AlgebraicClosure ℚ_[P.p]) := FractionRing.liftAlgebra R
          (AlgebraicClosure ℚ_[P.p])
        letI i4 : ContinuousSMul (FractionRing R) (AlgebraicClosure ℚ_[P.p]) :=
          continuousSMul_of_fractionRing R (AlgebraicClosure ℚ_[P.p])
        letI i5 : IsScalarTower R (FractionRing R) (AlgebraicClosure ℚ_[P.p]) :=
          FractionRing.isScalarTower_liftAlgebra R (AlgebraicClosure ℚ_[P.p])
        letI : IsTopologicalRing (AlgebraicClosure ℚ_[P.p]) :=
        { toIsTopologicalSemiring := Valued.isTopologicalDivisionRing.toIsTopologicalSemiring,
          toContinuousNeg := Valued.isTopologicalDivisionRing.toContinuousNeg }
        specialize irrep_p (AlgebraicClosure ℚ_[P.p]) (AlgebraicClosure.instField ℚ_[P.p])
          (PadicAlgCl.valued P.p).toTopologicalSpace
          { toIsTopologicalSemiring := Valued.isTopologicalDivisionRing.toIsTopologicalSemiring,
            toContinuousNeg := Valued.isTopologicalDivisionRing.toContinuousNeg } i3 i4
        rw[← GaloisRep.base_change_trans] at irrep_p
        rw[← GaloisRep.reducible_conj_reducible_iff] at irrep_p
        exact reducible_three' irrep_p
      · rw[Module.rank_baseChange, Cardinal.lift_id, rk2]
      · rw[GaloisRep.det_baseChange]
        suffices (σ.det complexConjugation) = -1 by
          rw[this]
          simp only [map_neg, map_one]
        apply odd_of_hardlyRamified (FreyPackage.hp_odd P) rk2
        exact hσ
    apply reducible_p
    apply irreducible_of_irreducible_reduction
    let f : R ⧸ IsLocalRing.maximalIdeal R →+* ZMod P.p := by
      apply Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) almd.algebraMap
      intro a ha
      rw[← RingHom.mem_ker]
      suffices (RingHom.ker almd.algebraMap) = (IsLocalRing.maximalIdeal R) by
        rw[this]
        exact ha
      rw[← IsLocalRing.isMaximal_iff]
      apply Ideal.Quotient.maximal_of_isField
      suffices (R ⧸ RingHom.ker almd.algebraMap) ≃+* (ZMod P.p) from
        MulEquiv.isField (Semifield.toIsField (ZMod P.p)) this
      apply RingHom.quotientKerEquivOfSurjective
      apply ZMod.ringHom_surjective
    letI _ : Algebra (IsLocalRing.ResidueField R) (ZMod P.p) := RingHom.toAlgebra f
    have _ : (algebraMap (IsLocalRing.ResidueField R) (ZMod P.p)) = f := rfl
    have _ : IsScalarTower R (IsLocalRing.ResidueField R) (ZMod P.p) := by
      refine { smul_assoc := ?_ }
      intro x y z
      change f (IsLocalRing.residue R x * y) * z = x • (f y * z)
      rw[Algebra.smul_def, map_mul, mul_assoc]
      rfl
    letI := compact_of_finite_Zp P.p R
    letI := hausdorff_of_finite_Zp P.p R
    letI := noetherian_of_finite_Zp P.p R
    have _ : ContinuousSMul (IsLocalRing.ResidueField R) (ZMod P.p) :=
      DiscreteTopology.instContinuousSMul (IsLocalRing.ResidueField R) (ZMod P.p)
    have irrep_σ_p : (GaloisRep.baseChange (ZMod P.p) σ).IsIrreducible := by
      rw[GaloisRep.reducible_conj_reducible_iff (GaloisRep.baseChange (ZMod P.p) σ) φ, σ_cong_ρ]
      exact irrep
    rw[GaloisRep.reducible_conj_reducible_iff (GaloisRep.baseChange (ZMod P.p) σ)
      (GaloisRep.tensor_associator (IsLocalRing.ResidueField R) (ZMod P.p) V)] at irrep_σ_p
    rw[GaloisRep.base_change_trans] at irrep_σ_p
    exact GaloisRep.irreducible_of_irreducible_base_change (GaloisRep.baseChange
    (IsLocalRing.ResidueField R) σ) irrep_σ_p

/-!

It follows that there is no Frey package.

-/

/-- There is no Frey package. This profound result is proved using
work of Mazur and Wiles/Ribet to rule out all possibilities for the
$p$-torsion in the corresponding Frey curve. -/
theorem FreyPackage.false (P : FreyPackage) : False := by
  -- by Wiles' result, the p-torsion is not irreducible
  apply Wiles_Frey P
  -- but by Mazur's result, the p-torsion is irreducible!
  exact Mazur_Frey P
  -- Contradiction!

/-- Fermat's Last Theorem is true -/
theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  -- Suppose Fermat's Last Theorem is false
  by_contra h
  -- then there exists a Frey package
  obtain ⟨P : FreyPackage⟩ := FreyPackage.of_not_FermatLastTheorem h
  -- but there is no Frey package
  exact P.false
