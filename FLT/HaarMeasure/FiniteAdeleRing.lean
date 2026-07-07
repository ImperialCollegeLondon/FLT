/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.HaarMeasure.Quotient
public import FLT.HaarMeasure.HaarChar.AddEquiv
public import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.Lemmas
public import FLT.NumberField.Completion.Finite
public import FLT.NumberField.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!

We show that `GLₙ(𝔸ᶠ)` and `PGLₙ(𝔸ᶠ)` are unimodular.

-/

@[expose] public section

variable {ι : Type*}
    {G : ι → Type*}
    [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
    {C : (i : ι) → Subgroup (G i)}
    [hCopen : Fact (∀ (i : ι), IsOpen (C i : Set (G i)))]
    [hCcompact : ∀ i, CompactSpace (C i)]
    -- [∀ i, MeasurableSpace (G i)]
    -- [∀ i, BorelSpace (G i)]
    -- [∀ i, LocallyCompactSpace (G i)] -- follows from the hypotheses, but needed for *statement*
    [∀ i, SecondCountableTopology (G i)]

open MeasureTheory Measure

namespace RestrictedProduct

open ContinuousMulEquiv Filter Topology in
lemma modularCharacter_eq [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
    [Countable ι] (g : Πʳ i, [G i, C i]) :
    modularCharacter g = ∏ᶠ i, modularCharacter (g i) := by
  let (i : _) := borel (G i)
  have (i : _) : BorelSpace (G i) := ⟨rfl⟩
  simp only [modularCharacter_eq_mulEquivHaarChar]
  convert mulEquivHaarChar_restrictedProductCongrRight (C := C)
    (fun i ↦ MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct (g i)) _) (by
    filter_upwards [g.2] with i (hi : g i ∈ C i)
    refine (MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct (g i)) _).bijOn fun a ↦ ?_
    simp [ConjAct.smul_def, hi, Subgroup.mul_mem_cancel_left, Subgroup.mul_mem_cancel_right])
  ext a i
  simp [ConjAct.smul_def]

instance isUnimodularGroup [Countable ι] [∀ i, IsUnimodularGroup (G i)] :
    IsUnimodularGroup (Πʳ i, [G i, C i]) where
  modularCharacter_eq_one := by
    ext g; simp [modularCharacter_eq, IsUnimodularGroup.modularCharacter_eq_one]

open IsDedekindDomain

open scoped NumberField Adele in
instance {K : Type*} [Field K] [NumberField K] :
    IsUnimodularGroup 𝔸ᶠ[K]ˣ :=
  have : Fact (∀ (v : HeightOneSpectrum (𝓞 K)), IsOpen (X := (v.adicCompletion K)ˣ)
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :=
    ⟨fun v ↦ Submonoid.isOpen_units (by exact Valued.isOpen_integer (v.adicCompletion K))⟩
  have (v : HeightOneSpectrum (𝓞 K)) : CompactSpace
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units :=
    isCompact_iff_compactSpace.mp (Submonoid.units_isCompact
      (NumberField.isCompact_adicCompletionIntegers K v))
  have : IsUnimodularGroup
    Πʳ (i : HeightOneSpectrum (𝓞 K)), [(HeightOneSpectrum.adicCompletion K i)ˣ,
      ↑(Submonoid.ofClass (HeightOneSpectrum.adicCompletionIntegers K i)).units] :=
    isUnimodularGroup
  (ContinuousMulEquiv.restrictedProductUnits _ fun _ ↦
    by exact Valued.isOpen_integer _).isUnimodularGroup

instance {M : Type*} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

open scoped NumberField Adele in
instance {K n : Type*} [Field K] [NumberField K] [Fintype n] [DecidableEq n] :
    IsUnimodularGroup (GL n 𝔸ᶠ[K]) :=
  have : Fact (∀ (v : HeightOneSpectrum (𝓞 K)), IsOpen (X := GL n (v.adicCompletion K))
      ((HeightOneSpectrum.adicCompletionIntegers K v).matrix (n := n)).units) :=
    ⟨fun v ↦ Submonoid.isOpen_units (NumberField.isOpenAdicCompletionIntegers K v).matrix⟩
  have (v : HeightOneSpectrum (𝓞 K)) : CompactSpace
      ((HeightOneSpectrum.adicCompletionIntegers K v).matrix (n := n)).units :=
    isCompact_iff_compactSpace.mp (Submonoid.units_isCompact
      (NumberField.isCompact_adicCompletionIntegers K v).matrix)
  (ContinuousMulEquiv.restrictedProductMatrixUnits fun _ ↦
    by exact Valued.isOpen_integer _).isUnimodularGroup

lemma unitsMap_algebraMap_le_center {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] :
    (Units.map (algebraMap R S).toMonoidHom).range ≤ .center _ := by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes]

instance {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] :
    (Units.map (algebraMap R S).toMonoidHom).range.Normal :=
  Subgroup.normal_of_le_center _ unitsMap_algebraMap_le_center

instance {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [SeparatelyContinuousMul G]
    [BorelSpace G] [PolishSpace G]
    (H : Subgroup G) [IsClosed (X := G) H] : BorelSpace (G ⧸ H) :=
  ⟨continuous_quotient_mk'.map_eq_borel (Y := G ⧸ H) QuotientGroup.mk_surjective⟩

instance {M : Type*} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

lemma Module.FaithfullyFlat.smul_top_eq_top_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FaithfullyFlat R M] {I : Ideal R} :
    (I • ⊤ : Submodule R M) = ⊤ ↔ I = ⊤ := by
  refine ⟨fun H ↦ ?_, (· ▸ Submodule.top_smul _)⟩
  have := ((TensorProduct.quotTensorEquivQuotSMul M I).trans
    (Submodule.quotEquivOfEq _ _ H)).subsingleton
  refine Ideal.Quotient.subsingleton_iff.mp ?_
  exact Module.FaithfullyFlat.rTensor_reflects_triviality R M _

lemma Ideal.map_eq_top_iff
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {I : Ideal R} : I.map (algebraMap R S) = ⊤ ↔ I = ⊤ := by
  refine ⟨fun H ↦ Module.FaithfullyFlat.smul_top_eq_top_iff (M := S).mp ?_, (· ▸ Ideal.map_top _)⟩
  rw [Ideal.smul_top_eq_map, H, Submodule.restrictScalars_top]

lemma Finsupp.linearCombination_comm {R I : Type*} [CommSemiring R] (u v : I →₀ R) :
    Finsupp.linearCombination R u v = Finsupp.linearCombination R v u := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_congr_of_eq_on_inter
    (by simp +contextual) (by simp +contextual) (by simp [mul_comm])

lemma Module.Free.exists_comp_linearMap_eq_id
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
    [Nontrivial A] : ∃ f : A →ₗ[R] R, f ∘ₗ Algebra.linearMap R A = .id := by
  obtain ⟨I, b⟩ := Module.Free.exists_basis R A
  let v := b.repr 1
  have : Ideal.span (Set.range v) = ⊤ := by
    rw [← Ideal.map_eq_top_iff (S := A), Ideal.map_span, Ideal.eq_top_iff_one,
      ← b.linearCombination_repr 1, Finsupp.linearCombination_apply]
    refine sum_mem fun i hi ↦ ?_
    simp only [Algebra.smul_def, ← Set.range_comp]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, rfl⟩)
  obtain ⟨a, ha⟩ := ((Finsupp.range_linearCombination _).trans this).ge (Set.mem_univ 1)
  rw [Finsupp.linearCombination_comm] at ha
  refine ⟨Finsupp.linearCombination R a ∘ₗ b.repr, ?_⟩
  ext
  simpa

lemma IsModuleTopology.isClosed_one_of_exists_linearMap
    (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (H : ∃ f : A →ₗ[R] R, f ∘ₗ Algebra.linearMap R A = .id)
    [TopologicalSpace R] [TopologicalSpace A]
    [IsModuleTopology R A] [T1Space A] : IsClosed (X := A) (1 : Submodule R A) := by
  nontriviality A
  have := IsModuleTopology.toContinuousAdd R A
  obtain ⟨f, hf⟩ := H
  convert ContinuousLinearMap.isClosed_ker ⟨Algebra.linearMap R A ∘ₗ f - .id,
    IsModuleTopology.continuous_of_linearMap _⟩
  ext a
  suffices (∃ y, (algebraMap R A) y = a) ↔ algebraMap R A (f a) = a by simpa [sub_eq_zero]
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  rintro ⟨y, rfl⟩
  simpa using congr(algebraMap R A ($hf y))

lemma Submonoid.isClosed_units {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsClosed (U : Set M)) : IsClosed (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

lemma Units.range_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (hf : Function.Injective f) :
    (Units.map f).range = (MonoidHom.mrange f).units := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩; simp [Submonoid.mem_units_iff]
  · rintro ⟨⟨a, ha⟩, b, hb⟩; exact ⟨⟨a, b, hf <| by simp [*], hf <| by simp [*]⟩, by ext; simp [ha]⟩

open Matrix in
lemma isClosed_unitsMap_matrix
    (n R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R]
    [Fintype n] [DecidableEq n] :
    IsClosed (X := GL n R) (Units.map (algebraMap R (Matrix n n R)).toMonoidHom).range := by
  cases isEmpty_or_nonempty n
  · simp
  nontriviality R
  have : IsClosed (X := Matrix n n R) (algebraMap R (Matrix n n R)).range := by
    convert IsModuleTopology.isClosed_one_of_exists_linearMap R (Matrix n n R) ?_
    · ext; simp
    · exact ⟨entryLinearMap _ _ (Classical.arbitrary _) (Classical.arbitrary _), by ext; simp⟩
  convert Submonoid.isClosed_units this
  rw [Units.range_map (hf := by exact FaithfulSMul.algebraMap_injective _ _)]
  rfl

open scoped NumberField Adele in
instance {K n : Type*} [Field K] [NumberField K] [Fintype n] [DecidableEq n] :
    IsUnimodularGroup (GL n 𝔸ᶠ[K] ⧸
      (Units.map (algebraMap 𝔸ᶠ[K] (Matrix n n 𝔸ᶠ[K])).toMonoidHom).range) :=
  QuotientGroup.isUnimodularGroup _ unitsMap_algebraMap_le_center (isClosed_unitsMap_matrix _ _)

end RestrictedProduct
