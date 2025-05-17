import FLT.Patching.Utils.AdicTopology
import FLT.Deformations.Lemmas
import Mathlib.Topology.UniformSpace.DiscreteUniformity

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

variable (R) in
/-- A topological ring is proartinian if it is linearly topologized, complete hausdorff,
and all its discrete quotients are artinian. -/
class IsProartinian : Prop where
  toIsLinearTopology : IsLinearTopology R R
  toT0Space : T0Space R
  toCompleteSpace : letI := IsTopologicalAddGroup.toUniformSpace R; CompleteSpace R
  isArtinianRing_quotient : ∀ I : Ideal R, IsOpen (X := R) I → IsArtinianRing (R ⧸ I)

attribute [instance low] IsProartinian.toIsLinearTopology
  IsProartinian.toT0Space IsProartinian.toCompleteSpace

lemma isProartinian_iff_isArtinianRing [DiscreteTopology R] :
    IsProartinian R ↔ IsArtinianRing R := by
  constructor
  · intro _
    have := IsProartinian.isArtinianRing_quotient (⊥ : Ideal R) (isOpen_discrete _)
    exact (RingEquiv.quotientBot R).surjective.isArtinianRing
  · intro _
    exact ⟨inferInstance, inferInstance, inferInstance, fun I _ ↦ inferInstance⟩

instance [DiscreteTopology R] [IsArtinianRing R] : IsProartinian R := by
  rwa [isProartinian_iff_isArtinianRing]

instance [IsLocalRing R] [IsLocalRing.IsAdicTopology R] [IsNoetherianRing R] [CompactSpace R] :
    IsProartinian R := by
  constructor
  · infer_instance
  · infer_instance
  · infer_instance
  · intro I hI
    have : Finite (R ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
    infer_instance

section IsLocalRing

open IsLocalRing

variable [IsLocalRing R] [IsLocalRing S]

lemma isOpen_maximalIdeal_of_isProartinian [IsProartinian R] :
    IsOpen (X := R) (maximalIdeal R) := by
  obtain ⟨I, hI, hI'⟩ := exists_ideal_isMaximal_and_isOpen_of_isLinearTopology R
  exact (isMaximal_iff _).mp hI ▸ hI'

lemma exists_maximalIdeal_pow_le_of_isProartinian [IsProartinian R]
    (I : Ideal R) (hI : IsOpen (X := R) I) :
    ∃ n, maximalIdeal R ^ n ≤ I := by
  by_cases hI' : I = ⊤
  · exact ⟨1, by simp [hI']⟩
  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  rw [jacobson_eq_maximalIdeal _ bot_ne_top,
    ← IsLocalRing.map_maximalIdeal _ Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.zero_eq_bot, ← le_bot_iff, Ideal.map_le_iff_le_comap,
    ← RingHom.ker, Ideal.mk_ker] at hn
  exact ⟨n, hn⟩

lemma isContinuous_of_isProartinian_of_isLocalHom
    [IsLocalRing.IsAdicTopology R]
    (f : R →+* S) [IsProartinian S] [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero
  simp only [ContinuousAt, map_zero]
  rw [(IsLocalRing.hasBasis_maximalIdeal_pow R).tendsto_iff
    (IsLinearTopology.hasBasis_open_ideal (R := S))]
  intro I hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  replace hn := (Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) n).trans hn
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap] at hn
  exact ⟨n, trivial, hn⟩
