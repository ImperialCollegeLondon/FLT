import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.ModThree -- will be needed for proof
import FLT.Assumptions.KnownIn1980s
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Localization

universe u

open scoped TensorProduct

/-- `toNatPrime v` returns the underlying rational prime of the height-one prime `v`
of `ℤ = NumberField.RingOfIntegers ℚ`.
-/

noncomputable def toNatPrime
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
  Nat.Primes := by
  refine ⟨Ideal.absNorm (Ideal.under ℤ v.asIdeal), ?_⟩
  have vnezero : NeZero v.asIdeal := ⟨v.ne_bot⟩
  apply Nat.absNorm_under_prime

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

-- TODO -- make some API for "I have a rank 1 quotient where Galois acts trivially"
-- e.g. this implies trace(Frob_p) is (1+p)

/--
A 3-adic hardly ramified representation has trace(Frob_p) = 1 + p for all p ≠ 2,3
-/
instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] :
    TopologicalSpace (IsLocalRing.ResidueField R) := moduleTopology R (IsLocalRing.ResidueField R)

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] :
    ContinuousAdd (IsLocalRing.ResidueField R) := ModuleTopology.continuousAdd R
    (IsLocalRing.ResidueField R)

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] :
    ContinuousSMul R (IsLocalRing.ResidueField R) := ModuleTopology.continuousSMul R
    (IsLocalRing.ResidueField R)

noncomputable instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] :
    Module R (IsLocalRing.ResidueField R) :=
    RingHom.toModule (IsLocalRing.residue R)

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [CompactSpace R] [T2Space R] [IsNoetherianRing R] :
    DiscreteTopology (IsLocalRing.ResidueField R) := by
    rw[discreteTopology_iff_isOpen_singleton_zero]
    have := (IsModuleTopology.isOpenQuotientMap_of_surjective (B := IsLocalRing.ResidueField R)
    (φ := {
      toFun := (IsLocalRing.residue R).toFun
      map_add' := (IsLocalRing.residue R).map_add'
      map_smul' := by
        intro m x
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.id_apply]
        change (IsLocalRing.residue R) (m * x) = (IsLocalRing.residue R) m *
        (IsLocalRing.residue R) x
        exact rfl
    }) IsLocalRing.residue_surjective).isOpenMap
    specialize this (IsLocalRing.maximalIdeal R) (IsLocalRing.isOpen_maximalIdeal R)
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk] at this
    suffices h : ((fun a ↦ (IsLocalRing.residue R) a) '' ↑(IsLocalRing.maximalIdeal R)) = {0} by
      rw[← h]
      exact this
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Set.mem_singleton_iff]
    constructor <;> intro h
    · obtain ⟨y, hy1, hy2⟩ := h
      rw[← hy2]
      exact (IsLocalRing.residue_eq_zero_iff y).mpr hy1
    · use (0 : IsLocalRing.ResidueField R).out
      have := Quot.out_eq (0 : IsLocalRing.ResidueField R)
      constructor
      · rw[← IsLocalRing.notMem_maximalIdeal, not_not]
        exact (IsLocalRing.residue_eq_zero_iff
          (Quotient.out (0 : IsLocalRing.ResidueField R))).mp this
      rw[h]
      exact this

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] : IsTopologicalRing (IsLocalRing.ResidueField R) := sorry

lemma compact_of_finite_Zp (p : ℕ) [Fact p.Prime] (R : Type*) [AddCommMonoid R] [Module ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsModuleTopology ℤ_[p] R] :
    CompactSpace R := sorry

lemma hausdorff_of_finite_Zp (p : ℕ) [Fact p.Prime] (R : Type*) [AddCommMonoid R] [Module ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsModuleTopology ℤ_[p] R] :
    T2Space R := sorry

lemma noetherian_of_finite_Zp (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] : IsNoetherianRing R := sorry

theorem irreducible_of_irreducible_reduction {K R : Type*} [Field K] [TopologicalSpace R]
  [CommRing R] [IsTopologicalRing R] [IsLocalRing R] [IsDomain R] {V : Type*} [AddCommGroup V]
  [Module R V] [Module.Finite R V] [Module.Free R V] (ρ : GaloisRep K R V) : GaloisRep.IsIrreducible
    (GaloisRep.baseChange (IsLocalRing.ResidueField R) ρ) → GaloisRep.IsIrreducible
      (GaloisRep.baseChange (FractionRing R) ρ) := sorry

lemma continuousSMul_of_fractionRing (R S : Type*) [CommRing R] [IsDomain R] [TopologicalSpace R]
  [IsTopologicalRing R] [Field S] [TopologicalSpace S] [alg : Algebra R S] [FaithfulSMul R S]
  [ContinuousSMul R S] :
  haveI : Algebra (FractionRing R) S := FractionRing.liftAlgebra R S
  ContinuousSMul (FractionRing R) S := sorry

lemma Ideal.comap_ne_bot_of_isIntegral (R : Type*) {S : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] {I : Ideal S} (hI : I ≠ ⊥) :
    I.comap (algebraMap R S) ≠ ⊥ := by
  obtain ⟨i, hiI, hi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact Ideal.comap_ne_bot_of_algebraic_mem hi0 hiI <| Algebra.IsAlgebraic.isAlgebraic i

lemma faithfulSMul_of_padic_fractionRing (p : ℕ) [Fact p.Prime] (R S : Type*) [CommRing R]
  [IsDomain R] [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R]
  [Module.Free ℤ_[p] R] [Field S] [CharZero S] [TopologicalSpace S] [alg : Algebra R S]
  : FaithfulSMul R S := sorry

namespace GaloisRepresentation.IsHardlyRamified

set_option linter.unusedVariables false in
theorem ribets_lemma (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsDomain R] [IsModuleTopology ℤ_[p] R]
    (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : GaloisRep.IsIrreducible (GaloisRep.baseChange (FractionRing R) ρ))
    (hρ' : has_trivial_quotient (IsLocalRing.ResidueField R)
    (GaloisRep.baseChange (IsLocalRing.ResidueField R) ρ)) : ∃ (W : Type u)
    (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W) (_ : Module.Free R W)
    (σ : GaloisRep ℚ R W) (e : (FractionRing R) ⊗[R] V ≃ₗ[FractionRing R] (FractionRing R) ⊗[R] W),
    GaloisRep.conj (GaloisRep.baseChange (FractionRing R) ρ) e =
    (GaloisRep.baseChange (FractionRing R) σ) ∧ ¬ has_trivial_quotient (IsLocalRing.ResidueField R)
    (GaloisRep.baseChange (IsLocalRing.ResidueField R) σ) := by
      knownin1980s

--set_option maxHeartbeats 10000000 in
theorem three_adic' {R : Type u} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsDomain R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ¬GaloisRep.IsIrreducible (GaloisRep.baseChange (FractionRing R) ρ) := by
    intro irrep
    have _ := compact_of_finite_Zp 3 R
    have _ := hausdorff_of_finite_Zp 3 R
    have _ := noetherian_of_finite_Zp 3 R
    have _ : Module.Free (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] V) :=
      Module.Free.tensor
    have _ : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite (IsLocalRing.ResidueField R)
    have mod_three := IsHardlyRamified.mod_three ((IsLocalRing.ResidueField R) ⊗[R] V)
      (ρ := GaloisRep.baseChange (IsLocalRing.ResidueField R) ρ) (by
        rw[Module.rank_baseChange, Cardinal.lift_id]
        exact hV) (baseChange_hardlyRamified (show Odd 3 by decide) _ hV ρ hρ)
    obtain ⟨W, _, _, _, _, σ, e, he, hσ⟩ := ribets_lemma 3 V hV irrep mod_three
    apply hσ
    have rk_W_2 : Module.rank R W = 2 := by
      rw[← hV]
      have : Module.rank (FractionRing R) ((FractionRing R) ⊗[R] W) =
        Module.rank (FractionRing R) ((FractionRing R) ⊗[R] V) := LinearEquiv.rank_eq (id e.symm)
      rw[Module.rank_baseChange, Module.rank_baseChange] at this
      rw[Cardinal.lift_id, Cardinal.lift_id] at this
      exact this
    apply IsHardlyRamified.mod_three ((IsLocalRing.ResidueField R) ⊗[R] W)
    · apply baseChange_hardlyRamified (show Odd 3 by decide) _ rk_W_2
      rw[← hardlyRamified_of_hardlyRamified_isogenous (show Odd 3 by decide) hV rk_W_2 ρ σ e he]
      exact hρ

theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsDomain R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ v (hp5 : 5 ≤ (toNatPrime v).val),
      (ρ.toLocal v (Frob v)).charpoly =
      (Polynomial.X - (1 : Polynomial R)) * (Polynomial.X - ((toNatPrime v) : Polynomial R)) := by
      sorry


end GaloisRepresentation.IsHardlyRamified
