import FLT.Deformations.RepresentationTheory.Frobenius
import FLT.Deformations.RepresentationTheory.IntegralClosure
import FLT.NumberField.Completion.Finite
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.FinitePlaces

variable {K L : Type*} [Field K] [Field L]
variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {n : Type*} [Fintype n] [DecidableEq n]

open NumberField

variable [NumberField K]

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal
local notation3 "κ" => IsLocalRing.ResidueField
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)
local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

/-- Given a field extension, this is a map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.mapAux (f : K →+* L) : Γ L →* Γ K where
  toFun σ :=
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    ((σ.restrictScalars K).toAlgHom.comp
      (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ)).restrictNormal' (Kᵃˡᵍ)
  map_one' := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans (by simp)
  map_mul' σ₁ σ₂ := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (AlgebraicClosure.map f).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans ?_
    refine ((AlgHom.restrictNormal_commutes _ _ _).trans ?_).symm
    simpa [absoluteGaloisGroup] using AlgHom.restrictNormal_commutes _ _ _

/-- Given a field extension, this is a continuous map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.map (f : K →+* L) : Γ L →ₜ* Γ K where
  __ := Field.absoluteGaloisGroup.mapAux f
  continuous_toFun := by
    classical
    letI := f.toAlgebra
    let F : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ := IsAlgClosed.lift
    letI := F.toRingHom.toAlgebra
    apply continuous_of_continuousAt_one (Field.absoluteGaloisGroup.mapAux f)
    rw [ContinuousAt, map_one]
    refine ((galGroupBasis L (Lᵃˡᵍ)).nhds_one_hasBasis.tendsto_iff
      (galGroupBasis K (Kᵃˡᵍ)).nhds_one_hasBasis).mpr ?_
    rintro _ ⟨_, ⟨K', hK', rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨.adjoin _ (K'.map F), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
    · have : FiniteDimensional _ _ := hK'
      obtain ⟨s, hs⟩ := K'.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType K K'))
      obtain rfl := IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
      simp only [IntermediateField.adjoin_map, IntermediateField.adjoin_adjoin_right,
        ← Finset.coe_image]
      refine IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
    · exact F.injective ((AlgHom.restrictNormal_commutes _ _ _).trans
        (hσ ⟨F x, IntermediateField.subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩))

set_option allowUnsafeReducibility true in
attribute [reducible] Field.absoluteGaloisGroup

lemma Field.absoluteGaloisGroup.lift_map (f : K →+* L) (σ : Γ L) (x : Kᵃˡᵍ) :
    AlgebraicClosure.map f (map f σ x) = σ (AlgebraicClosure.map f x) := by
  letI := f.toAlgebra
  letI := (AlgebraicClosure.map f).toAlgebra
  exact AlgHom.restrictNormal_commutes _ _ _

instance finiteIndex_fixingSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let f : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup → E →ₐ[K] L := Quotient.lift
    (fun f ↦ f.toAlgHom.comp E.val)
    (by rintro _ τ ⟨σ, rfl⟩; ext x; exact DFunLike.congr_arg τ (σ.2 x))
  have : Function.Injective f := by
    rintro ⟨σ⟩ ⟨τ⟩ (H : σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val)
    refine Quotient.sound ⟨⟨.op (τ⁻¹ * σ), fun x ↦ ?_⟩, by simp⟩
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] using DFunLike.congr_fun H x
  have := Finite.of_injective _ this
  exact Subgroup.finiteIndex_of_finite_quotient

open IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    CompactSpace (L ≃ₐ[K] L) := by
  classical
  letI := IsTopologicalGroup.toUniformSpace (L ≃ₐ[K] L)
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨IsTopologicalGroup.totallyBounded fun s hs ↦ ?_, ?_⟩
  · obtain ⟨E, hE, H⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hs
    refine ⟨_, inferInstance, H⟩
  · rintro f hf -
    have := hf.1
    have (x : L) :
        ∃ σ₀ : L ≃ₐ[K] L, ∃ t ∈ f, ∀ σ ∈ t, ∀ τ : L ≃ₐ[K] L, σ (τ x) = σ₀ (τ x) := by
      have : FiniteDimensional K K⟮x⟯ :=
        adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      obtain ⟨t, htf, H⟩ := ((Filter.HasBasis.cauchy_iff
        (by exact (galGroupBasis K L).nhds_one_hasBasis.comap _)).mp hf).2 _ (by
            exact ⟨_, ⟨normalClosure K K⟮x⟯ L, inferInstanceAs (FiniteDimensional K _), rfl⟩, rfl⟩)
      obtain ⟨σ, hσ⟩ := f.nonempty_of_mem htf
      refine ⟨σ, t, htf, fun τ hτ τ₀ ↦ ?_⟩
      have : σ (τ.symm (τ (τ₀ x))) = τ (τ₀ x) := H τ hτ σ hσ ⟨τ (τ₀ x), by
        refine SetLike.le_def.mp (le_iSup _ (τ.toAlgHom.comp <| τ₀.toAlgHom.comp (val _))) ?_
        exact ⟨⟨_, subset_adjoin _ _ (by simp)⟩, rfl⟩⟩
      simpa using this.symm
    choose σ₀ t htf H using this
    have H' (s σ hσ) := H s σ hσ .refl
    dsimp at H'
    let F : L ≃ₐ[K] L :=
    { toFun x := σ₀ x x
      invFun x := (σ₀ x).symm x
      left_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf (σ₀ x x)))
        dsimp
        have H' := H' _ _ hσ₁
        have : σ x = (σ₀ (σ₀ x x) x) := by simpa using H _ _ hσ₂ (σ₀ x).symm
        rw [← H', AlgEquiv.symm_apply_eq, H', ← this, H']
      right_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf ((σ₀ x).symm x)))
        dsimp
        replace H := H _ _ hσ₁ σ.symm
        simp only [AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_apply_eq, AlgEquiv.symm_symm] at H
        rw [← H' _ _ hσ₂, H]
      map_mul' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x * y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_mul]
      map_add' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x + y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_add]
      commutes' := by simp }
    refine ⟨F, Set.mem_univ _, ?_⟩
    rw [((galGroupBasis K L).nhds_hasBasis F).ge_iff]
    rintro _ ⟨_, ⟨E, hE, rfl⟩, rfl⟩
    simp only [Set.image_mul_left]
    have ⟨s, hs⟩ := E.toSubmodule.fg_iff_finiteDimensional.mpr hE
    refine f.mem_of_superset ((Filter.biInter_finset_mem s).mpr fun i _ ↦ htf i) ?_
    rintro σ hσ ⟨x, hx⟩
    change F.symm (σ x) = x
    induction hs.ge hx using Submodule.span_induction with
    | zero | add | smul => simp_all
    | mem x h =>
      rw [AlgEquiv.symm_apply_eq]
      simp [F, ← H' _ _ (Set.mem_iInter₂.mp hσ _ h)]

open scoped IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) L := by
  constructor
  intro x y
  rw [isOpen_iff_forall_mem_open]
  rintro σ (hσ : _ = _)
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  refine ⟨_, ?_, K⟮x⟯.fixingSubgroup_isOpen.smul σ, 1, one_mem _, by simp⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have := (mem_fixingSubgroup_iff _).mp hτ x (IntermediateField.mem_adjoin_simple_self K x)
  simp only [smul_eq_mul, Set.mem_setOf_eq, mul_smul, this, hσ]

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_fLT IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

attribute [local instance] Valued.toNormedField in
lemma isIntegral_of_spectralNorm_le_one
    {K L Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Field K] [Field L]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] [Algebra K L] [Algebra.IsAlgebraic K L]
    {x : L} (hx : spectralNorm K L x ≤ 1) : IsIntegral (Valued.v : Valuation K Γ₀).integer x := by
  have : minpoly K x ∈ Polynomial.lifts (Valued.v : Valuation K Γ₀).integer.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at this
    split_ifs at this with h
    · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly K x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at this
      simpa [Valuation.mem_integer_iff] using this
    obtain h | h := (le_of_not_lt h).eq_or_lt
    · simp [← h, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, one_mem]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_mem]
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic this
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K,
    Subring.algebraMap_def, hP, minpoly.aeval]

lemma spectralAlgNorm_mul {K : Type*} [NontriviallyNormedField K]
    {L : Type*} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [CompleteSpace K] [IsUltrametricDist K] (x y : L) :
    spectralAlgNorm K L (x * y) = spectralAlgNorm K L x * spectralAlgNorm K L y := by
  sorry -- This is proved in https://github.com/leanprover-community/mathlib4/pull/23333

lemma spectralNorm_inv
    {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra.IsAlgebraic K L] (x : L) :
    spectralNorm K L (x⁻¹) = (spectralNorm K L x)⁻¹ := by
  by_cases H : x = 0
  · simp [H, spectralNorm_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← spectralAlgNorm_def, ← spectralAlgNorm_def, ← spectralAlgNorm_mul (K := K) x x⁻¹,
    mul_inv_cancel₀ H, spectralAlgNorm_one]

noncomputable instance : NontriviallyNormedField Kᵥ := Valued.toNontriviallyNormedField

instance valuationRing_integralClosure
    {L : Type*} [Field L] [Algebra Kᵥ L] [Algebra.IsAlgebraic Kᵥ L] :
    ValuationRing (IntegralClosure 𝒪ᵥ L) := by
  refine ValuationSubring.instValuationRingSubtypeMem ⟨(integralClosure 𝒪ᵥ L).toSubring, ?_⟩
  intro x
  obtain hx | hx := le_total (spectralNorm Kᵥ L x) 1
  · exact .inl (isIntegral_of_spectralNorm_le_one hx)
  · have := inv_le_one_of_one_le₀ hx
    rw [← spectralNorm_inv] at this
    exact .inr (isIntegral_of_spectralNorm_le_one this)

/-- The local inertia subgroup of a number field at a prime, defined as a subgroup
of the local galois group. -/
noncomputable
def localInertiaGroup : Subgroup (Γ Kᵥ) :=
  (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).toAddSubgroup.inertia (Γ Kᵥ)

open IntermediateField in
/-- The subgroup of the local galois group which is the kernel of the canonical map `Iᵥ → k(v)ˣ`.
Note that this definition is somewhat cheating, abusing the fact that the field corresponding
to this subgroup is `Kᵘʳ(ᵖ⁻¹√ϖ)` (where `p` is `#k(v)` and not the characteristic)
and that all units in `Kᵘʳ` have `p-1`-th roots.

TODO: show that this is indeed the right group. -/
noncomputable
def localTameAbelianInertiaGroup : Subgroup (Γ Kᵥ) where
  carrier := { σ | ∀ x, x ^ (Nat.card (κ 𝒪ᵥ) - 1) ∈ fixedField (localInertiaGroup v) → σ x = x }
  mul_mem' {σ τ} hσ hτ x hx := by dsimp; rw [hτ x hx, hσ x hx]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ x hx := by
    conv_lhs => rw [← hσ x hx]
    simp [AlgEquiv.aut_inv]

instance : CharZero Kᵥ :=
  ((algebraMap K Kᵥ).charZero_iff (algebraMap K Kᵥ).injective).mp inferInstance

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

instance : Finite (IsLocalRing.ResidueField 𝒪ᵥ) := inferInstance

instance finite_adicCompletionIntegers_quotient
    {I : Ideal 𝒪ᵥ} [I.IsPrime] [NeZero I] : Finite (𝒪ᵥ ⧸ I) := by
  obtain rfl := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime 𝒪ᵥ).mp
      inferInstance).2.unique ⟨NeZero.ne _, ‹I.IsPrime›⟩ ⟨IsDiscreteValuationRing.not_a_field 𝒪ᵥ,
      inferInstanceAs (𝔪 _).IsPrime⟩
  exact inferInstanceAs <| Finite (IsLocalRing.ResidueField _)

instance neZero_maximalIdeal_integralClosure :
    NeZero (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) := by
  have : 𝒪ᵥ ≠ ⊤ := by
    refine fun h ↦ IsDiscreteValuationRing.not_isField 𝒪ᵥ (h ▸ ?_)
    exact (Subring.topEquiv (R := Kᵥ)).isField _ (Semifield.toIsField Kᵥ)
  exact ⟨(Ideal.bot_lt_of_maximal (𝔪 _)
    (not_isField_integralClosure (L := Kᵥᵃˡᵍ) _ this)).ne'⟩

/-- An arbitrary choice of an (arithmetic) frobenious element of a local galois group. -/
noncomputable
def Field.AbsoluteGaloisGroup.adicArithFrob : Γ Kᵥ :=
  arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

lemma Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob :
    IsArithFrobAt 𝒪ᵥ Frobᵥ (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) :=
  .arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))
