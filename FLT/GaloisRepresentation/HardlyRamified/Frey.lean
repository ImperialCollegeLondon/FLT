import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.Lift
import FLT.GaloisRepresentation.HardlyRamified.Family
import FLT.GaloisRepresentation.HardlyRamified.Threeadic
import FLT.Basic.FreyPackage
import FLT.EllipticCurve.Torsion
import Mathlib.Tactic.Cases
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Charpoly.BaseChange


variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

section GaloisRep_API

variable {K : Type*} {L : Type*} [Field K] [Field L]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
variable [Algebra A B] [ContinuousSMul A B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable [Module.Finite A M] [Module.Free A M] [Module.Finite A N] [Module.Free A N]

lemma charpoly_base_change (ρ : GaloisRep K A M) (g : Field.absoluteGaloisGroup K) :
  LinearMap.charpoly (GaloisRep.baseChange B ρ g) =
    Polynomial.map Algebra.algebraMap (LinearMap.charpoly (ρ g)) := by
  apply LinearMap.charpoly_baseChange

lemma charpoly_conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) (g : Field.absoluteGaloisGroup K) :
  LinearMap.charpoly ((GaloisRep.conj ρ e) g) = LinearMap.charpoly (ρ g) := by
  apply LinearEquiv.charpoly_conj

omit [Module.Finite A M] [Module.Free A M] [Module.Finite A N] [Module.Free A N] in
lemma conj_commutes_with_to_local [NumberField K]
   (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (ρ : GaloisRep K A M)
     (e : M ≃ₗ[A] N) : (GaloisRep.conj ρ e).toLocal v = GaloisRep.conj (ρ.toLocal v) e := by
  rfl

lemma to_local_commutes_with_base_change [NumberField K]
   (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (ρ : GaloisRep K A M) :
    (GaloisRep.baseChange B ρ).toLocal v = GaloisRep.baseChange B (ρ.toLocal v) := by
  rfl

end GaloisRep_API

lemma polynomial_map_trans (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C) (P : Polynomial A) :
    Polynomial.map g (Polynomial.map f P) = Polynomial.map (g.comp f) P := by
  change (⇑(Polynomial.mapRingHom g) ∘ ⇑(Polynomial.mapRingHom f)) P =
    ⇑(Polynomial.mapRingHom (g.comp f)) P
  rw[← RingHom.coe_comp, Polynomial.mapRingHom_comp]

lemma ideal_in_integral_extension_overlap (R S : Type*) [CommRing R] [Nontrivial R] [CommRing S]
  [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ a : R, a ≠ 0 ∧ (algebraMap R S) a ∈ I := by
    obtain ⟨a, ha, a_nz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨P, P_mon, hP⟩ := Algebra.IsIntegral.isIntegral (R := R) a
    obtain ⟨Q, hQ1, hQ2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P
      (Polynomial.Monic.ne_zero_of_ne (zero_ne_one' R) P_mon) 0
    simp only [map_zero, sub_zero] at hQ1 hQ2
    rw[Polynomial.X_dvd_iff] at hQ2
    rw[hQ1] at hP
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, mul_eq_zero, pow_eq_zero_iff', ne_eq,
      Polynomial.rootMultiplicity_eq_zero_iff, Polynomial.IsRoot.def, Classical.not_imp] at hP
    obtain ⟨hP, _⟩ | hP := hP
    · contradiction
    rw[show (Q = Q -
      Polynomial.C (Q.coeff 0) +
      Polynomial.C (Q.coeff 0)) by simp] at hP
    rw[Polynomial.eval₂_add, Polynomial.eval₂_C] at hP
    obtain ⟨Q', hQ'⟩ := Polynomial.X_dvd_sub_C (p := Q)
    rw[hQ'] at hP
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hP
    use Q.coeff 0
    rw[← neg_eq_iff_add_eq_zero] at hP
    rw[← hP, Submodule.neg_mem_iff]
    exact ⟨hQ2, by exact
      Ideal.IsTwoSided.mul_mem_of_left (Polynomial.eval₂ (algebraMap R S) a Q') ha⟩

theorem galois_rep_reducible_of_frobenii (M : Type*) (p : ℕ) [Fact (Nat.Prime p)] [AddCommGroup M]
  [Module (ZMod p) M] [Module.Free (ZMod p) M] [Module.Finite (ZMod p) M]
    (ρ : GaloisRep ℚ (ZMod p) M) (S : Finset (IsDedekindDomain.HeightOneSpectrum
     (NumberField.RingOfIntegers ℚ))) (h : ∀ v ∉ S, 3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val →
      ↑p ∉ v.asIdeal → LinearMap.charpoly ((ρ.toLocal v)
       (Field.AbsoluteGaloisGroup.adicArithFrob v)) = Polynomial.map (algebraMap ℤ (ZMod p))
        ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ((toNatPrime v).val : ℤ))))
         : ¬ GaloisRep.IsIrreducible ρ := by
          sorry

theorem EllipticCurve.torsion_has_rank2 {K : Type*} [Field K] (E : WeierstrassCurve K)
  [E.IsElliptic] [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (p : ℕ)
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
    IsHardlyRamified P.hp_odd (EllipticCurve.torsion_has_rank2 P.freyCurve P.p (by sorry))
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
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
        rw[polynomial_map_trans]
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
        rw[conj_commutes_with_to_local, charpoly_conj, to_local_commutes_with_base_change,
        charpoly_base_change]
    have Pσ_known : ∀ v ∉ S, ↑3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val → ↑(P.p) ∉ v.asIdeal →
      (LinearMap.charpoly ((σ.toLocal v) (Field.AbsoluteGaloisGroup.adicArithFrob v))) =
        Polynomial.map (Int.castRingHom R) (Q v) := by
          intro v hv1 hv2 hv3 hv4
          specialize compp v hv1 hv4
          obtain ⟨unrp, h_charpoly'⟩ := compp
          specialize Pv_known v hv1 hv2 hv3
          rw[Pv_known] at h_charpoly'
          rw[polynomial_map_trans] at h_charpoly'
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
            obtain ⟨a, a_nz, ha⟩ := ideal_in_integral_extension_overlap ℤ_[P.p] R I hyp
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
          rw[polynomial_map_trans]
          have : alg''.algebraMap.comp (Int.castRingHom R) = Int.castRingHom
            (AlgebraicClosure ℚ_[P.p]) := RingHom.eq_intCast' (alg''.algebraMap.comp
              (Int.castRingHom R))
          rw[this, ← h_charpoly', ← compσ]
          rw[conj_commutes_with_to_local, charpoly_conj, to_local_commutes_with_base_change,
          charpoly_base_change]
    have Pρ_known : ∀ v ∉ S, ↑3 ∉ v.asIdeal → 5 ≤ (toNatPrime v).val → ↑(P.p) ∉ v.asIdeal →
      (LinearMap.charpoly ((ρ.toLocal v) (Field.AbsoluteGaloisGroup.adicArithFrob v))) =
        Polynomial.map (Algebra.algebraMap) (Q v) := by
          intro v hv1 hv2 hv3 hv4
          have : Polynomial.map (Algebra.algebraMap : ℤ →+* ZMod (P.p)) (Q v) =
            Polynomial.map (Algebra.algebraMap) (Polynomial.map (Int.castRingHom R) (Q v)) := by
              rw[polynomial_map_trans]
              have : ((Algebra.algebraMap : R →+* (ZMod (P.p))).comp (Int.castRingHom R)) =
                Int.castRingHom (ZMod (P.p)) := by
                exact RingHom.eq_intCast' (α := ZMod P.p)
                  (Algebra.algebraMap.comp (Int.castRingHom R))
              rw[this]
              rfl
          rw[← σ_cong_ρ, this, ← Pσ_known v hv1 hv2 hv3 hv4, conj_commutes_with_to_local,
          charpoly_conj, to_local_commutes_with_base_change, charpoly_base_change]
    apply galois_rep_reducible_of_frobenii at Pρ_known
    exact Pρ_known irrep
