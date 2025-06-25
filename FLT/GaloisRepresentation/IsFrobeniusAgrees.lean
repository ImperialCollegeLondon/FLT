import Mathlib.Tactic
import FLT.GaloisRepresentation.PadicGaloisRep
import FLT.GaloisRepresentation.AssociatedPrime
import FLT.GaloisRepresentation.CompatibleFamily

open NumberField CompatibleFamily

set_option maxHeartbeats 4000000

/-Special thanks to Amelia Livingston for help on this file-/

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]

lemma comap_symm' [FiniteDimensional K L] (g : (L ≃ₐ[K] L)) :
    (galRestrict A K L B g).symm = galRestrict A K L B g.symm := by rfl

lemma trans_symm_self (g : (L ≃ₐ[K] L)) :
    (AlgEquiv.trans (AlgEquiv.symm g) g) = AlgEquiv.refl := by
  ext x
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq]

lemma restrictNormal_symm (N : Type) [Field N] [Algebra K N] [Algebra N L] [FiniteDimensional K L]
    [IsScalarTower K N L] [Normal K N] (g : (L ≃ₐ[K] L)) :
    (AlgEquiv.restrictNormal g N).symm = (AlgEquiv.restrictNormal g.symm N) := by
  ext x
  refine' AlgEquiv.injective (AlgEquiv.restrictNormal g N) _
  simp only [AlgEquiv.apply_symm_apply]
  rw [← AlgEquiv.trans_apply, ← AlgEquiv.restrictNormal_trans, trans_symm_self]
  refine' (algebraMap N L).injective _
  simp only [AlgEquiv.restrictNormal_commutes, AlgEquiv.coe_refl, id_eq]

lemma comap_symm'' (C N : Type) [CommRing C] [Field N] [Algebra K N] [Algebra N L]
  [FiniteDimensional K L] [Algebra C B] [Algebra A C] [Algebra C N] [Algebra A N]
  [IsScalarTower A C N] [IsScalarTower A K N] [IsIntegralClosure C A N]
  [FiniteDimensional K N] [NoZeroSMulDivisors B L] [Algebra C L]
  [IsScalarTower C B L] [IsScalarTower C N L]
  [IsScalarTower K N L] [Normal K N]  (g : (L ≃ₐ[K] L)) (x : C) :
  (algebraMap C B) (((galRestrict A K N C) (AlgEquiv.restrictNormal g N)) x) =
  (galRestrict A K L B) g (algebraMap C B x) := by
  refine' NoZeroSMulDivisors.algebraMap_injective B L _
  rw [
    algebraMap_galRestrict_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ N L, algebraMap_galRestrict_apply,
    ← IsScalarTower.algebraMap_apply, AlgEquiv.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply
    ]

/--When `K` and `L` are number fields, `IsFrobeniusFinite` is equivalent to `IsFrobenius` -/
lemma IsFrobenius'_agrees_NumberField (k l : Type) [Field l] [Field k] [Algebra k l]
    (g : (l ≃ₐ[k] l))
    [NumberField k] (P : Ideal (𝓞 k)) [Ideal.IsMaximal P]
    [NumberField l] [FiniteDimensional k l]  [IsGalois k l] : IsFrobenius' k l g P ↔
    @IsFrobeniusFinite (𝓞 k) k l (𝓞 l) _ _ _ _ _ _ _ _ _ _ _ _ _ _ g P _ := by
  constructor
  · intro hf
    rw [IsFrobenius'] at hf
    specialize hf l
    rw [← AlgEquiv_restrict_to_domain_fix k l IsGalois.to_normal g]
    exact hf
  · intro hfin
    intro N _ _ _ _ _ _ _
    unfold IsFrobeniusFinite at hfin
    cases' hfin with Q hQ
    cases' hQ with hQ hQ'
    cases' hQ' with hmax h'
    cases' h' with hinc hfrob
    use ToDownstairs (𝓞 N) (𝓞 l) Q
    have h1 : --I think this is the 'easy' part
        IsInvariant ((galRestrict ((𝓞 k)) k N (𝓞 N)) ((AlgEquiv.restrictNormalHom N) g))
        (ToDownstairs ((𝓞 N)) ((𝓞 l)) Q) := by
          ext x
          unfold IsInvariant at hQ
          have : ∀ x, x ∈ Ideal.comap (((galRestrict ((𝓞 k)) k l (𝓞 l)) g)).symm Q ↔ x ∈ Q := by
            intro x
            change Q = Ideal.comap ((galRestrict ((𝓞 k)) k l (𝓞 l)) g).symm Q at hQ
            rw [← hQ]
          constructor
          intro h2
          unfold AlgEquiv.restrictNormalHom
          dsimp only [MonoidHom.mk'_apply]
          · simp only [ToDownstairs, Ideal.mem_comap, RingHom.coe_coe] at h2 this ⊢
            show algebraMap _ _ _ ∈ _
            have h3 : (algebraMap (𝓞 N) (𝓞 l)) ((AlgEquiv.symm ((galRestrict ((𝓞 k)) k N (𝓞 N)) (AlgEquiv.restrictNormal g N))) x) =
              (AlgEquiv.symm ((galRestrict (𝓞 k) k l (𝓞 l)) g) (algebraMap (𝓞 N) (𝓞 l) x)) := by
              rw [comap_symm']
              rw [restrictNormal_symm]
              rw [comap_symm'']
              rw [comap_symm']
            rw [h3]
            specialize this (algebraMap (𝓞 N) (𝓞 l) x)
            rw [this]
            exact h2
          · intro h
            have h3 : (algebraMap (𝓞 N) (𝓞 l)) ((AlgEquiv.symm ((galRestrict ((𝓞 k)) k N (𝓞 N)) (AlgEquiv.restrictNormal g N))) x) =
              (AlgEquiv.symm ((galRestrict (𝓞 k) k l (𝓞 l)) g) (algebraMap (𝓞 N) (𝓞 l) x)) := by
              rw [comap_symm']
              rw [restrictNormal_symm]
              rw [comap_symm'']
              rw [comap_symm']
            simp only [ToDownstairs, Ideal.mem_comap, RingHom.coe_coe] at this h ⊢
            erw [h3] at h
            specialize this (algebraMap (𝓞 N) (𝓞 l) x)
            rw [← this]
            exact h
    use h1
    have h2 : Ideal.IsMaximal (ToDownstairs ((𝓞 N)) ((𝓞 l)) Q) :=
      IsMaximal_ToDownstairs_IsMaximal N l Q
    have h3 : Ideal.map (algebraMap (𝓞 k) (𝓞 N)) P ≤ ToDownstairs ((𝓞 N)) ((𝓞 l)) Q := by
      unfold ToDownstairs
      sorry
    constructor
    · exact h2
    · constructor
      · exact h3
      · dsimp
        sorry
