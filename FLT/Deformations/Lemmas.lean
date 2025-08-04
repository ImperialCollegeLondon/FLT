import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.DiscreteUniformity

lemma IsLinearTopology.exists_ideal_isMaximal_and_isOpen
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [Nontrivial R] [T0Space R] :
    ∃ I : Ideal R, I.IsMaximal ∧ IsOpen (X := R) I := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.hasBasis_open_ideal.mem_iff.mp
    ((isClosed_singleton (x := (1 : R))).isOpen_compl.mem_nhds (x := 0) (by simp))
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I (by simpa [Ideal.eq_top_iff_one] using hI')
  exact ⟨J, hJ, AddSubgroup.isOpen_mono (H₁ := I.toAddSubgroup) (H₂ := J.toAddSubgroup) hIJ hI⟩

/-- The continuous group homomorphism on units induced by a `ContinuousMonoidHom`. -/
@[simps!]
def Units.mapₜ {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f,
  continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.2.comp Units.continuous_val,
    MulOpposite.continuous_op.comp (f.2.comp Units.continuous_coe_inv)⟩)⟩

/-- The `ContinuousAlgHom` between spaces of square matrices induced by an `ContinuousAlgHom`
between their coefficients. This is Matrix.map as an `ContinuousAlgHom`. -/
@[simps!]
def ContinuousAlgHom.mapMatrix
    {R A B n : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B)
    [Fintype n] [DecidableEq n] :
    Matrix n n A →A[R] Matrix n n B :=
  ⟨f.1.mapMatrix, Continuous.matrix_map continuous_id' f.2⟩

/-- Coerce a `ContinuousAlgHom` to `ContinuousMonoidHom`. -/
def ContinuousAlgHom.toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) : A →ₜ* B :=
  ⟨f.1.toMonoidHom, f.2⟩

@[simp]
lemma ContinuousAlgHom.coe_toContinuousMonoidHom
    {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B) :
    (f.toContinuousMonoidHom : A → B) = f := rfl

instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G] :
    MulAction α (M →* G) where
  smul a f := ⟨⟨a • f, by simp⟩, by simp⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]

@[simp]
lemma MonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    (a : α) (f : M →* G) :
    ⇑(a • f) = a • ⇑f := rfl

instance {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G] :
    MulAction α (M →ₜ* G) where
  smul a f := ⟨a • f, .const_smul f.2 _⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]

@[simp]
lemma ContinuousMonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G]
    (a : α) (f : M →ₜ* G) :
    ⇑(a • f) = a • ⇑f := rfl

instance {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G :=
  ⟨fun _ ↦ .mul (continuous_const.mul continuous_id) continuous_const⟩

@[to_additive]
instance IsTopologicalGroup.discreteUniformity
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] :
    letI := IsTopologicalGroup.toUniformSpace G
    DiscreteUniformity G := by
  simp only [discreteUniformity_iff_idRel_mem_uniformity]
  exact ⟨{1}, by simp [Set.subset_def, div_eq_one]⟩

lemma IsLocalRing.map_maximalIdeal {R S} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f) :
    (maximalIdeal R).map f = maximalIdeal S := by
  have := (IsLocalRing.local_hom_TFAE f).out 0 4
  rw [← this.mp (by exact .of_surjective f hf), Ideal.map_comap_of_surjective f hf]

lemma IsLocalRing.ResidueField.map_surjective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (H : Function.Surjective f) :
    Function.Surjective (IsLocalRing.ResidueField.map f) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.mk_surjective.comp H)

open Topology in
@[to_additive]
lemma MonoidHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Group α] [MulOneClass β] {f : α →* β} [DiscreteTopology β] [IsTopologicalGroup α] :
    Continuous f ↔ IsOpen (X := α) f.ker := by
  refine ⟨fun H ↦ H.1 {1} (isOpen_discrete _), fun H ↦ continuous_of_continuousAt_one _ ?_⟩
  simpa [ContinuousAt] using Filter.eventually_of_mem (H.mem_nhds (by simp)) (by simp)

lemma RingHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Ring α] [Semiring β] {f : α →+* β} [DiscreteTopology β] [IsTopologicalAddGroup α] :
    Continuous f ↔ IsOpen (X := α) (RingHom.ker f) :=
  AddMonoidHom.continuous_iff_isOpen_ker (f := f.toAddMonoidHom)

open Topology in
lemma continuousAt_discrete_rng {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {x : α} [DiscreteTopology β] :
    ContinuousAt f x ↔ ∀ᶠ y in 𝓝 x, f y = f x := by
  simp [ContinuousAt]

nonrec
instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A] :
    IsLocalHom (ContinuousAlgHom.id R A) := by
  convert isLocalHom_id A
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

lemma ContinuousAlgHom.isLocalHom_toRingHom {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B]
    [TopologicalSpace A] [TopologicalSpace B]
    {f : A →A[R] B} :
    IsLocalHom f.toRingHom ↔ IsLocalHom f :=
  ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A ≃A[R] B) : IsLocalHom (f : A →A[R] B) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]

instance {A B : Type*} [Semiring A] [Semiring B]
    (F : Type*) [EquivLike F A B] [RingEquivClass F A B] (f : F) :
    IsLocalHom (RingHomClass.toRingHom f) := by
  convert isLocalHom_equiv f
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance ContinuousAlgHom.isLocalHom_comp {R A B C : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B →A[R] C} {f : A →A[R] B}
    [IsLocalHom g] [IsLocalHom f] :
    IsLocalHom (g.comp f) := by
  convert RingHom.isLocalHom_comp g.toRingHom f.toRingHom
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R : Type*} [CommSemiring R] : IsLocalHom (algebraMap R R) :=
  isLocalHom_id R

open IsLocalRing in
instance {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (ResidueField R)) :=
  isLocalHom_residue

/-- Given a field extension, this is an arbitrarily chosen map between their `AlgebraicClosure`s. -/
noncomputable
def AlgebraicClosure.map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    AlgebraicClosure K →+* AlgebraicClosure L :=
  letI := f.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toRingHom

lemma AlgebraicClosure.map_algebraMap {K L : Type*} [Field K] [Field L] (f : K →+* L) (x) :
    map f (algebraMap K _ x) = algebraMap _ _ (f x) :=
    letI := f.toAlgebra
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).commutes _

lemma IntermediateField.adjoin_adjoin_right
    {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] (s : Set E) : adjoin L (adjoin K s : Set E) = adjoin L s := by
  apply le_antisymm
  · exact adjoin_le_iff.mpr (adjoin_le_iff (T := (adjoin L s).restrictScalars K).mpr
      (subset_adjoin _ _))
  · exact adjoin.mono _ _ _ (subset_adjoin _ _)

nonrec
lemma IsModuleTopology.continuous_det {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace (Module.End A M)] [IsModuleTopology A (Module.End A M)] :
    Continuous (LinearMap.det : Module.End A M →* A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s A M)
  · obtain ⟨s, ⟨b⟩⟩ := H
    have : IsModuleTopology A (Matrix s s A) := IsModuleTopology.instPi
    have : ContinuousAdd (Module.End A M) := IsModuleTopology.toContinuousAdd A _
    letI e : Module.End A M ≃A[A] Matrix s s A :=
    { __ := algEquivMatrix b,
      continuous_toFun := continuous_of_linearMap (algEquivMatrix b).toLinearMap,
      continuous_invFun := continuous_of_linearMap (algEquivMatrix b).symm.toLinearMap }
    rw [e.symm.isQuotientMap.continuous_iff]
    convert continuous_id.matrix_det (R := A) (n := s)
    ext M
    exact LinearMap.det_toLin b M
  rw [LinearMap.det, dif_neg H]
  exact continuous_of_const fun x ↦ congrFun rfl

/-- `End_A(A) ≃ A`. -/
def Module.endSelf {A : Type*} [CommSemiring A] : Module.End A A ≃ₐ[A] A :=
  AlgEquiv.ofLinearEquiv (LinearMap.ringLmapEquivSelf A A A) (by simp) (by simp)

/-- Given a `ContinuousMonoidHom` from a group to a monoid, we may lift it to map into the group
of units of the monoid. -/
@[simps!]
def ContinuousMonoidHom.toHomUnits {G M : Type*} [Group G] [Monoid M] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace M] (f : G →ₜ* M) : G →ₜ* Mˣ :=
  ⟨MonoidHom.toHomUnits f, continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨f.continuous, by
    simpa [← map_inv] using MulOpposite.continuous_op.comp (f.continuous.comp continuous_inv)⟩)⟩

/-- `Units.val` as a `ContinuousMonoidHom`. -/
@[simps!]
def Units.coeHomₜ (M : Type*) [Monoid M] [TopologicalSpace M] : Mˣ →ₜ* M :=
  ⟨coeHom M, Units.continuous_val⟩

instance {A n m : Type*} [CommRing A] [TopologicalSpace A]
    [Finite n] [Finite m] [IsTopologicalRing A] :
    IsModuleTopology A (Matrix n m A) := IsModuleTopology.instPi

/-- We can upgrade an `AlgEquiv` between algebras with the module topology
into a `ContinuousAlgEquiv`. -/
def ContinuousAlgEquiv.ofIsModuleTopology {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace R] [IsModuleTopology R A] [IsModuleTopology R B] (e : A ≃ₐ[R] B) :
    A ≃A[R] B where
  __ := e
  continuous_toFun :=
    letI := IsModuleTopology.toContinuousAdd R B
    IsModuleTopology.continuous_of_linearMap e.toLinearMap
  continuous_invFun :=
    letI := IsModuleTopology.toContinuousAdd R A
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

@[simp]
lemma ContinuousMonoidHom.mk_toMonoidHom {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : (ContinuousMonoidHom.mk f hf) = f := rfl

@[simp]
lemma ContinuousMonoidHom.coe_mk {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
  [TopologicalSpace N] (f : M →* N) (hf : Continuous f) : ⇑(ContinuousMonoidHom.mk f hf) = f := rfl

instance {G K L : Type*} [Field K] [Field L] [Algebra K L] [Monoid G] [MulSemiringAction G L]
    [SMulCommClass G K L]
    (E : IntermediateField K L) [Normal K E] : MulSemiringAction G E where
  smul σ x := ⟨σ • x, by
    convert ((MulSemiringAction.toAlgHom K L σ).restrictNormal E x).2
    exact ((MulSemiringAction.toAlgHom K L σ).restrictNormal_commutes E x).symm⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

open NumberField in
instance {G K : Type*} [Field K] [Monoid G] [MulSemiringAction G K] :
    MulSemiringAction G (𝓞 K) where
  smul σ x := ⟨σ • x, x.2.map (MulSemiringAction.toAlgHom ℤ K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

lemma Subring.algebraMap_def {R : Type*} [CommRing R] (S : Subring R) :
    algebraMap S R = S.subtype := rfl

instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (R : ValuationSubring K)
    [FaithfulSMul K A] : FaithfulSMul R A :=
  Subsemiring.instFaithfulSMulSubtypeMem R

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K]
    (E : IntermediateField K L) [FiniteDimensional K E] : NumberField E where
  to_finiteDimensional := .trans ℚ K E

instance {K L : Type*} [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L] :
    Algebra O L where
  smul r x := r.1 • x
  algebraMap := (algebraMap K L).comp (algebraMap O K)
  commutes' _ _ := by simp [Algebra.commutes]
  smul_def' _ _ := by simp [← Algebra.smul_def]; rfl

instance IntermediateField.smulCommClass_of_normal
    {K L G : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField K L)
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] [Normal K E] :
    SMulCommClass G K E where
  smul_comm g k e := Subtype.ext <| smul_comm g k e.1

instance ValuationSubring.smulCommClass
    (K L G : Type*) [Field K] [Semiring L] (O : ValuationSubring K) [Algebra K L]
    [Monoid G] [MulSemiringAction G L] [SMulCommClass G K L] :
    SMulCommClass G O L where
  smul_comm g o l := smul_comm g o.1 l

theorem Subgroup.index_op {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective

instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [Subgroup.index_op]; exact Subgroup.FiniteIndex.index_ne_zero⟩

lemma IsTopologicalGroup.totallyBounded {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ∀ s ∈ nhds (1 : G), ∃ H : Subgroup G, H.FiniteIndex ∧ ↑H ⊆ s) :
    letI := IsTopologicalGroup.toUniformSpace G
    TotallyBounded (Set.univ : Set G) := by
  letI := IsTopologicalGroup.toUniformSpace G
  rintro s ⟨t, ht1, hts⟩
  obtain ⟨H, hH, hHs⟩ := H _ ht1
  have : Finite (Gᵐᵒᵖ ⧸ H.op) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (MulOpposite.unop ∘ Quotient.out : Gᵐᵒᵖ ⧸ H.op → G),
    Set.finite_range _, fun x _ ↦
      Set.mem_iUnion₂_of_mem ⟨QuotientGroup.mk (.op x), rfl⟩ (hts (hHs ?_))⟩
  dsimp only
  rw [Function.comp_apply, SetLike.mem_coe, div_eq_mul_inv, ← MulOpposite.unop_op (x⁻¹),
    ← MulOpposite.unop_mul, ← Subgroup.mem_op, MulOpposite.op_inv, ← QuotientGroup.eq]
  simp

noncomputable
instance Additive.instDistrbMulAction
    {G M : Type*} [Monoid G] [Monoid M] [MulDistribMulAction G M] :
    DistribMulAction G (Additive M) where
  smul g m := .ofMul (g • m.toMul)
  one_smul m := one_smul _ m.toMul
  mul_smul g h m := mul_smul g h m.toMul
  smul_zero g := smul_one (N := M) g
  smul_add g m n := MulDistribMulAction.smul_mul g m.toMul n.toMul
