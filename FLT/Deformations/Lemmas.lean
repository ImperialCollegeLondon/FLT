import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.LinearTopology
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
