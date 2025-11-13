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
  sorry

/-!

But it follows from a profound theorem of Ribet, and the even more profound theorem
(proved by Wiles) that the representation cannot be irreducible.

-/
/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

open GaloisRepresentation in
theorem Wiles_Frey (P : FreyPackage) :
  haveI : Fact P.p.Prime := ⟨P.pp⟩
  ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) := by
    have hard_ram := FreyCurve.torsion_isHardlyRamified P
    intro irrep
    let ρ := (P.freyCurve.galoisRep P.p P.hppos)
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
    have h_charpoly := IsHardlyRamified.three_adic W rk2' hτ1
    rcases comp with ⟨S, Pv, comp⟩
    have comp3 := comp Nat.fact_prime_three i
    have compp := comp fact ψ
    let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → Polynomial ℤ :=
      fun v => (Polynomial.X - (1 : Polynomial ℤ)) *
        (Polynomial.X - (((toNatPrime v).val) : Polynomial ℤ))
    have Pv_known : ∀ v ∉ S, ↑3 ∉ v.asIdeal  → 5 ≤ (toNatPrime v).val →
      Pv v = Polynomial.map (Int.castRingHom E) (Q v) := by
        intro v hv1 hv2 hv3
        specialize comp3 v hv1 hv2
        obtain ⟨unr3, h_charpoly'⟩ := comp3
        have hfp : Fact (Nat.Prime (toNatPrime v)) := by
          rw[fact_iff]
          exact (toNatPrime v).property
        specialize h_charpoly v hv3
        have : (Polynomial.X - (1 : Polynomial R')) *
        (Polynomial.X - ((toNatPrime v) : Polynomial R')) =
          Polynomial.map (Int.castRingHom R') (Q v) := by unfold Q; simp;
        rw[this] at h_charpoly
        apply Polynomial.map_injective i
        · exact RingHom.injective i
        rw[Polynomial.map_map]
        have : i.comp (Int.castRingHom E) =
          Int.castRingHom (AlgebraicClosure ℚ_[3]) :=
            RingHom.eq_intCast' (i.comp (Int.castRingHom E))
        rw[this]
        have : Int.castRingHom (AlgebraicClosure ℚ_[3]) = alg'''.algebraMap.comp
          (Int.castRingHom R') :=
            RingHom.ext_int (Int.castRingHom (AlgebraicClosure ℚ_[3]))
              (Algebra.algebraMap.comp (Int.castRingHom R'))
        rw[this]
        change Polynomial.map i (Pv v) = Polynomial.mapRingHom (Algebra.algebraMap.comp
        (Int.castRingHom R')) (Q v)
        rw[← Polynomial.mapRingHom_comp]
        change Polynomial.map i (Pv v) =
          (Polynomial.map Algebra.algebraMap) ((Polynomial.map (Int.castRingHom R')) (Q v))
        rw[← h_charpoly', ← h_charpoly, ← hτ2]
        rw[conj_toLocal, charpoly_conj, baseChange_toLocal,
        charpoly_baseChange]
    have Pσ_known : ∀ v ∉ S, ↑3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val → ↑(P.p) ∉ v.asIdeal →
      (LinearMap.charpoly ((σ.toLocal v) (Field.AbsoluteGaloisGroup.adicArithFrob v))) =
        Polynomial.map (Int.castRingHom R) (Q v) := by
          intro v hv1 hv2 hv3 hv4
          specialize compp v hv1 hv4
          obtain ⟨unrp, h_charpoly'⟩ := compp
          specialize Pv_known v hv1 hv2 hv3
          rw[Pv_known] at h_charpoly'
          rw[Polynomial.map_map] at h_charpoly'
          have : ψ.comp (Int.castRingHom E) = Int.castRingHom (AlgebraicClosure ℚ_[P.p]) :=
            RingHom.eq_intCast' (ψ.comp (Int.castRingHom E))
          rw[this] at h_charpoly'
          apply Polynomial.map_injective alg''.algebraMap
          · rw[RingHom.injective_iff_ker_eq_bot]
            let I := RingHom.ker (Algebra.algebraMap : R →+* AlgebraicClosure ℚ_[P.p])
            have I_def : I = RingHom.ker (Algebra.algebraMap : R →+* AlgebraicClosure ℚ_[P.p]) :=
              rfl
            rw[← I_def]
            by_contra hyp
            have := Ideal.comap_ne_bot_of_isIntegral ℤ_[P.p] hyp
            rw[Submodule.ne_bot_iff] at this
            obtain ⟨a, ha, a_nz⟩ := this
            rw[I_def] at ha
            change (algebraMap R (AlgebraicClosure ℚ_[P.p])) ((algebraMap ℤ_[P.p] R) a) = 0 at ha
            rw[PadicInt.unitCoeff_spec a_nz] at ha
            simp only [map_mul, map_pow, map_natCast, mul_eq_zero, pow_eq_zero_iff',
              Nat.cast_eq_zero, ne_eq] at ha
            obtain ha | ⟨P_zero, ha⟩ := ha
            · change ((algebraMap ℤ_[P.p] R) ↑(PadicInt.unitCoeff a_nz)) ∈ I at ha
              have : IsUnit ((algebraMap ℤ_[P.p] R) ↑(PadicInt.unitCoeff a_nz)) := by
                apply RingHom.isUnit_map (algebraMap ℤ_[P.p] R)
                exact Units.isUnit (PadicInt.unitCoeff a_nz)
              have : I = ⊤ := by exact Ideal.eq_top_of_isUnit_mem I ha this
              revert this
              apply RingHom.ker_ne_top
            · revert P_zero
              apply Nat.Prime.ne_zero
              exact P.pp
          rw[Polynomial.map_map]
          have : alg''.algebraMap.comp (Int.castRingHom R) = Int.castRingHom
            (AlgebraicClosure ℚ_[P.p]) := RingHom.eq_intCast' (alg''.algebraMap.comp
              (Int.castRingHom R))
          rw[this, ← h_charpoly', ← compσ]
          rw[conj_toLocal, charpoly_conj, baseChange_toLocal,
          charpoly_baseChange]
    have Pρ_known : ∀ v ∉ S, ↑3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val → ↑(P.p) ∉ v.asIdeal →
      (LinearMap.charpoly ((ρ.toLocal v) (Field.AbsoluteGaloisGroup.adicArithFrob v))) =
        Polynomial.map (Algebra.algebraMap) (Q v) := by
          intro v hv1 hv2 hv3 hv4
          have : Polynomial.map (Algebra.algebraMap : ℤ →+* ZMod (P.p)) (Q v) =
            Polynomial.map (Algebra.algebraMap) (Polynomial.map (Int.castRingHom R) (Q v)) := by
              rw[Polynomial.map_map]
              have : ((Algebra.algebraMap : R →+* (ZMod (P.p))).comp (Int.castRingHom R)) =
                Int.castRingHom (ZMod (P.p)) := by
                exact RingHom.eq_intCast' (α := ZMod P.p)
                  (Algebra.algebraMap.comp (Int.castRingHom R))
              rw[this]
              rfl
          rw[← σ_cong_ρ, this, ← Pσ_known v hv1 hv2 hv3 hv4, conj_toLocal,
          charpoly_conj, baseChange_toLocal, charpoly_baseChange]
    apply galois_rep_reducible_of_frobenii at Pρ_known
    exact Pρ_known irrep

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
