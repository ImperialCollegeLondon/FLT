module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Connected.Separation
public import FLT.Patching.Utils.InverseLimit
public import FLT.Patching.Utils.Lemmas
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.Topology.Algebra.LinearTopology

@[expose] public section

variable (R) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace IsLocalRing

/--
`IsAdicTopology R` says that the topology on the local topological ring `R`
is the maximal ideal-adic one, that is, that a basis of neighbourhoods of `0` in `R`
is given by powers of the maximal ideal of `R`.
-/
class IsAdicTopology (R) [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Prop where
  isAdic : IsAdic (maximalIdeal R)

variable [IsAdicTopology R]

instance (priority := 100) :
    NonarchimedeanRing R :=
  IsLocalRing.IsAdicTopology.isAdic (R := R) ▸ RingSubgroupsBasis.nonarchimedean _

lemma isOpen_maximalIdeal_pow'' (n : ℕ) : IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  (isAdic_iff.mp IsLocalRing.IsAdicTopology.isAdic).1 _

lemma isOpen_maximalIdeal' : IsOpen (X := R) (maximalIdeal R) :=
  pow_one (maximalIdeal R) ▸ isOpen_maximalIdeal_pow'' R 1

open Filter Topology in
lemma hasBasis_maximalIdeal_pow :
    Filter.HasBasis (𝓝 (0 : R)) (fun _ ↦ True) fun n ↦ ↑(maximalIdeal R ^ n) :=
  IsLocalRing.IsAdicTopology.isAdic (R := R) ▸ Ideal.hasBasis_nhds_zero_adic (maximalIdeal R)

instance (priority := 100) : IsLinearTopology R R := .mk_of_hasBasis _ (hasBasis_maximalIdeal_pow R)

instance (priority := 100) [IsNoetherianRing R] : T2Space R := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  rintro x (hx : x ∉ (⊥ : Ideal R))
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hx
  obtain ⟨n, hn⟩ : ∃ n, x ∉ maximalIdeal R ^ n := by simpa using hx
  exact ⟨_, (isOpen_maximalIdeal_pow'' R n).mem_nhds (zero_mem _), hn⟩

-- This is actually an iff
instance (priority := 100) [IsArtinianRing R] : DiscreteTopology R := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  convert isOpen_maximalIdeal_pow'' R n
  rw [← jacobson_eq_maximalIdeal _ bot_ne_top, hn]
  rfl

lemma Submodule.isCompact_of_fg {R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M]
    [Module R M]
    [TopologicalSpace M] [IsModuleTopology R M] [CompactSpace R] {N : Submodule R M} (hN : N.FG) :
    IsCompact (X := M) N := by
  have := IsModuleTopology.toContinuousAdd R M
  obtain ⟨s, hs⟩ := hN
  have : LinearMap.range (Fintype.linearCombination R (α := s) Subtype.val) = N := by
    simp [hs]
  rw [← this]
  refine isCompact_range ?_
  simp only [Fintype.linearCombination, Finset.univ_eq_attach, LinearMap.coe_mk,
    AddHom.coe_mk]
  continuity

lemma Ideal.isCompact_of_fg {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] {I : Ideal R} (hI : I.FG) : IsCompact (X := R) I :=
  Submodule.isCompact_of_fg hI

lemma IsModuleTopology.compactSpace
    (R M : Type*) [CommRing R] [TopologicalSpace R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
    [CompactSpace R] [Module.Finite R M] : CompactSpace M :=
  ⟨Submodule.isCompact_of_fg (Module.Finite.fg_top (R := R))⟩

variable {R} in
omit [IsLocalRing R] [IsAdicTopology R] in
lemma isCompact_of_isNoetherianRing [IsNoetherianRing R] [CompactSpace R] (I : Ideal R) :
    IsCompact (X := R) I := Ideal.isCompact_of_fg (IsNoetherian.noetherian _)

variable {R} in
lemma isOpen_iff_finite_quotient' [CompactSpace R] {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  constructor
  · intro H
    exact AddSubgroup.quotient_finite_of_isOpen _ H
  · intro H
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
    exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
      (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow'' R n)

instance (n : ℕ) : DiscreteTopology (R ⧸ maximalIdeal R ^ n) :=
  QuotientAddGroup.discreteTopology (isOpen_maximalIdeal_pow'' R n)

instance [IsNoetherianRing R] : IsHausdorff (maximalIdeal R) R where
  haus' x hx := show x ∈ (⊥ : Ideal R) by
    rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top]
    simpa [SModEq.zero] using hx

instance [CompactSpace R] : IsPrecomplete (maximalIdeal R) R where
  prec' f H := by
    simp_rw [← Ideal.one_eq_top, smul_eq_mul, mul_one] at H
    have : ∀ i, T2Space (R ⧸ (maximalIdeal R) ^ i) := inferInstance
    have := denseRange_inverseLimit (ι := ℕᵒᵈ) (R ⧸ maximalIdeal R ^ ·)
      (fun i j h ↦ Ideal.quotientMap _ (.id R) (by exact Ideal.pow_le_pow_right h))
      (fun i j h ↦ continuous_coinduced_dom.mpr (continuous_algebraMap _ _))
      (fun x : R ↦ ⟨fun i ↦ algebraMap _ _ x, by simp⟩)
      (fun i ↦ (Ideal.Quotient.mk_surjective).denseRange)
    have := ((isCompact_range (Continuous.subtype_mk (continuous_pi
      fun i ↦ continuous_algebraMap _ _) _)).isClosed.closure_eq.symm.trans
      this.closure_eq).ge (Set.mem_univ <| by exact ⟨fun i ↦ f i, fun i j e ↦ by
        simpa using (H e).symm⟩)
    simpa [funext_iff, eq_comm (b := Ideal.Quotient.mk _ (f _))] using this

variable {R} in
lemma compactSpace_of_finite_residueField [IsNoetherianRing R] [Finite (ResidueField R)]
    [IsAdicComplete (maximalIdeal R) R] :
    CompactSpace R := by
  let f : R →+* Π i : ℕ, R ⧸ (maximalIdeal R) ^ i := algebraMap _ _
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have : ∀ i, Finite (R ⧸ (maximalIdeal R) ^ i) := fun i ↦
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  have hf : Continuous f := by continuity
  have : Topology.IsClosedEmbedding f := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
      refine (f.map_zero ▸ (hf.tendsto 0).le_comap).antisymm ?_
      apply (hasBasis_maximalIdeal_pow R).ge_iff.mpr ?_
      rintro i -
      exact ⟨Set.pi {i} fun i ↦ {0}, set_pi_mem_nhds (Set.finite_singleton i) (by simp),
        by simp [Set.subset_def, f, Ideal.Quotient.eq_zero_iff_mem]⟩
    · change Function.Injective (Pi.ringHom _)
      rw [injective_iff_map_eq_zero]
      intro a ha
      change a ∈ (⊥ : Ideal R)
      rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
      simpa [Pi.ringHom, funext_iff, Ideal.Quotient.eq_zero_iff_mem] using ha
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨g, rfl⟩ : ∃ y : ℕ → R, x = fun i ↦ Ideal.Quotient.mk _ (y i) := by
        simp_rw [funext_iff]
        exact Classical.skolem (p := (x · = Ideal.Quotient.mk _ ·)).mp
          fun i ↦ by simpa only [eq_comm] using Ideal.Quotient.mk_surjective (x i)
      have : IsPrecomplete (maximalIdeal R) R := inferInstance
      have := mt (IsPrecomplete.prec this (f := g))
      simp_rw [← Ideal.one_eq_top, smul_eq_mul, mul_one] at this
      simp only [Set.mem_compl_iff, Set.mem_range, eq_comm, funext_iff, Pi.algebraMap_apply,
        Ideal.Quotient.algebraMap_eq, not_exists, not_forall, SModEq, Ideal.Quotient.mk_eq_mk, f]
          at hx this
      obtain ⟨i, j, e, H⟩ := this hx
      refine ⟨_, ?_, isOpen_set_pi ((Set.finite_singleton i).insert j)
        (s := fun i ↦ {Ideal.Quotient.mk _ (g i)})
        (fun _ _ ↦ isOpen_discrete _), by simp⟩
      rintro _ hx ⟨x, rfl⟩
      simp only [Set.insert_pi, Set.singleton_pi, Set.mem_inter_iff, Set.mem_preimage,
        Function.eval, Pi.algebraMap_apply, Ideal.Quotient.algebraMap_eq, Set.mem_singleton_iff,
        f] at hx
      obtain ⟨hx₁, hx₂⟩ := hx
      apply_fun Ideal.quotientMap (maximalIdeal R ^ i) (.id R) (Ideal.pow_le_pow_right e) at hx₁
      simp [hx₂, H] at hx₁
  exact this.compactSpace

-- TODO: `TotallyDisconnectedSpace` is unnecessary. See
-- https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite
-- A partial proof can be found at `FLT/Patching/Utils/CompactHausdorffRings`.
omit [IsAdicTopology R] in
/--
Any profinite noetherian ring has the `𝔪`-adic topology.
-/
instance (priority := 100) [IsNoetherianRing R]
    [CompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] :
    IsAdicTopology R := by
  refine ⟨isAdic_iff.mpr ⟨isOpen_maximalIdeal_pow R, ?_⟩⟩
  intro s hs
  obtain ⟨I, hI, hIs⟩ := exists_ideal_isOpen_and_subset hs
  have : Finite (R ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact ⟨n, subset_trans hn hIs⟩

lemma Continuous.of_isLocalHom {R S : Type*} [CommRing R] [IsLocalRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsAdicTopology R] [CommRing S] [IsLocalRing S] [TopologicalSpace S]
    [IsTopologicalRing S] [IsAdicTopology S] (f : R →+* S) [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero
  unfold ContinuousAt
  rw [map_zero]
  apply ((hasBasis_maximalIdeal_pow R).tendsto_iff (hasBasis_maximalIdeal_pow S)).mpr ?_
  simp only [SetLike.mem_coe, true_and, forall_const, ← SetLike.le_def, ← Ideal.mem_comap,
    ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  intro n
  exact ⟨n, Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) _⟩

abbrev withIdeal {R} [CommRing R] [IsLocalRing R] : WithIdeal R := ⟨maximalIdeal R⟩

attribute [local instance] withIdeal

instance {R} [CommRing R] [IsLocalRing R] : IsAdicTopology R := ⟨rfl⟩

end IsLocalRing
