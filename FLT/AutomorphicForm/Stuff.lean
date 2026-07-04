/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.AutomorphicForm.GroupTheoryStuff
public import FLT.Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Data.Int.SuccPred
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.MetricSpace.Polish

/-! # Random assortments of API lemmas missing in mathlib. -/

@[expose] public section

attribute [-simp] RingHom.toMonoidHom_eq_coe

@[simp]
lemma RingHom.coe_toMonoidHom {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) : ⇑f.toMonoidHom = f := rfl

/-- `Set.matrix` is equivalent to matrices on the subtype. -/
@[simps]
def Set.matrixEquiv {m n α : Type*} (S : Set α) :
    S.matrix (m := m) (n := n) ≃ Matrix m n S where
  toFun f i j := ⟨f.1 i j, f.2 i j⟩
  invFun f := ⟨fun i j ↦ f i j, fun i j ↦ (f i j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Subring.matrix` is equivalent to matrices on the subtype. -/
@[simps!]
def Subring.matrixEquiv {n α : Type*} [Ring α] [Fintype n] [DecidableEq n] (S : Subring α) :
    S.matrix (n := n) ≃+* Matrix n n S where
  __ := Set.matrixEquiv _
  map_mul' _ _ := by ext i j; simp [Set.matrixEquiv, Matrix.mul_apply]
  map_add' _ _ := rfl

lemma IsPrincipalIdealRing.exists_isCoprime_and_dvd_pow
    {R : Type*} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R] (a b : R) (ha : a ≠ 0) :
    ∃ x y N, a = x * y ∧ IsCoprime x b ∧ y ∣ b ^ N := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => cases ha rfl
  | h₂ a ha' => refine ⟨1, a, 0, by simp [isCoprime_one_left, ha'.dvd]⟩
  | h₃ a p ha' hp IH =>
    obtain ⟨x, y, N, rfl, hxb, hyb⟩ := IH ha'
    by_cases hpb : p ∣ b
    · exact ⟨x, y * p, N + 1, by ring, hxb, pow_succ b N ▸ mul_dvd_mul hyb hpb⟩
    · exact ⟨x * p, y, N, by ring, hxb.mul_left (hp.coprime_iff_not_dvd.mpr hpb), hyb⟩

instance ConjAct.continuousConstSMul {G} [TopologicalSpace G] [DivInvMonoid G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G where
  continuous_const_smul _ := IsTopologicalGroup.continuous_conj _

open Pointwise in
lemma ConjAct.isOpen_smul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {U : Subgroup G} (hU : IsOpen (U : Set G)) (g : ConjAct G) :
    IsOpen ((g • U : Subgroup G) : Set G) :=
  (Homeomorph.smul g).isOpen_image.mpr hU

lemma Polynomial.Monic.not_irreducible_iff_of_natDegree_eq_two {R : Type*} [CommRing R]
    [NoZeroDivisors R] {p : Polynomial R} (hp : p.Monic) (hp' : p.natDegree = 2) :
    ¬ Irreducible p ↔ ∃ a b, p = (.X - .C a) * (.X - .C b) := by
  cases subsingleton_or_nontrivial R
  · simp [Subsingleton.elim (α := R) _ 0, Subsingleton.elim (α := Polynomial R) _ 0]
  refine ⟨fun H ↦ ?_, ?_⟩
  · obtain ⟨a, b, e₁, e₂⟩ :=
      (Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff hp hp').mp H
    refine ⟨-a, -b, ?_⟩
    ext (n|_|_|_)
    · simpa
    · simp [Polynomial.coeff_mul, Finset.antidiagonal, e₂]
    · trans 1
      · simpa [← hp']
      · rw [zero_add, Polynomial.coeff_mul_add_eq_of_natDegree_le] <;> simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
      · compute_degree; lia
      · simp [hp']
  · rintro ⟨a, b, rfl⟩; simp [irreducible_mul_iff, Polynomial.not_isUnit_X_sub_C]

lemma IsPrimitiveRoot.iff_of_prime {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime) {x : R} :
    IsPrimitiveRoot x p ↔ x ^ p = 1 ∧ x ≠ 1 :=
  ⟨fun H ↦ ⟨H.pow_eq_one, H.ne_one hp.one_lt⟩, fun H ↦ IsPrimitiveRoot.iff_orderOf.mpr
    ((hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one H.1)).resolve_left (by simp [H.2]))⟩

@[simp]
theorem Matrix.det_algebraMap {R n α : Type*} [CommSemiring R] [CommRing α] [Algebra R α]
    {r : R} [DecidableEq n] [Fintype n] :
    (algebraMap R (Matrix n n α) r).det = algebraMap R α r ^ Fintype.card n :=
  (Matrix.det_diagonal ..).trans (by simp)

lemma Set.injOn_image_iff {α β γ : Type*} {f : α → β} {g : β → γ} {s : Set α}
    (hf : s.InjOn f) :
    (f '' s).InjOn g ↔ s.InjOn (g ∘ f) := by
  simp [Set.InjOn] at hf ⊢
  grind

-- Finiteness not necessary?
lemma Algebra.norm_one_tmul
    (R A : Type*) {B : Type*} [CommRing R] [CommRing A] [Ring B] [Algebra R A]
    [Algebra R B] (x : B) [Module.Free R B] [Module.Finite R B] :
    Algebra.norm A ((1 : A) ⊗ₜ[R] x) = algebraMap R A (Algebra.norm R x) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  classical
  obtain ⟨I, b⟩ := Module.Free.exists_basis R B
  cases @nonempty_fintype _ (Module.Finite.finite_basis b)
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (b.baseChange A), RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.algebraMap_eq_smul_one]

@[simp]
lemma Algebra.norm_eq_det {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (m : Matrix n n R) : Algebra.norm R m = m.det ^ Fintype.card n := by
  rw [Algebra.norm_eq_matrix_det (Matrix.stdBasis R n n)]
  have : (Algebra.leftMulMatrix (Matrix.stdBasis R n n)) m =
    Matrix.comp _ _ _ _ _ (m.map (algebraMap _ _)) := by
    ext i j
    simp [Algebra.leftMulMatrix_eq_repr_mul, Matrix.stdBasis, Matrix.mul_apply,
      Pi.single_apply, ite_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  rw [this, ← Matrix.det_det]
  simp

@[simp]
lemma vecCons_one_one
  {α : Type*} [One α] : (![1, 1] : Fin 2 → α) = 1 := by ext i; fin_cases i <;> rfl

@[simp]
lemma WithZero.lt_ofAdd_one {a : WithZero (Multiplicative ℤ)} :
    a < ↑(Multiplicative.ofAdd (1 : ℤ)) ↔ a ≤ 1 := by
  induction a with
  | zero => simp
  | coe a => simp [← Multiplicative.toAdd_lt, ← Multiplicative.toAdd_le,
      ← Int.lt_add_one_iff]

@[simp]
lemma WithZero.mul_ofAdd_one_le_one_iff {a : WithZero (Multiplicative ℤ)} :
    a * ↑(Multiplicative.ofAdd (1 : ℤ)) ≤ 1 ↔ a < 1 := by
  induction a with
  | zero => simp
  | coe a => simp [← Multiplicative.toAdd_lt,
      ← Multiplicative.toAdd_le, ← WithZero.coe_mul]
section

lemma MeasureSpace.comap_symm {α β : Type*} (m : MeasurableSpace α) (e : α ≃ β) :
    m.comap e.symm = m.map e := by
  ext
  simp [MeasurableSpace.map_def, MeasurableSpace.measurableSet_comap,
    Equiv.preimage_eq_iff_eq_image, Equiv.image_symm_eq_preimage]

instance {M : Type*} [MeasurableSpace M] [TopologicalSpace M] [BorelSpace M] :
    BorelSpace Mᵐᵒᵖ := by
  constructor
  rw [MulOpposite.instMeasurableSpace, BorelSpace.measurable_eq (α := M),
    ← MulOpposite.opEquiv_apply, ← MeasureSpace.comap_symm, borel_comap,
    MulOpposite.opEquiv_symm_apply]

instance {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology

instance {X : Type*} [TopologicalSpace X] [PolishSpace X] : PolishSpace Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.polishSpace

instance {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [PolishSpace M] : PolishSpace Mˣ :=
  Units.isClosedEmbedding_embedProduct.polishSpace

open MeasureTheory in
theorem MeasurableEquiv.restrict_preimage {α β : Type*}
    {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    μ.restrict (e ⁻¹' s) = ((μ.map e).restrict s).map e.symm := by
  rw [e.restrict_map, Measure.map_map e.symm.measurable e.measurable]
  simp

/-- smul as a `ContinuousAddEquiv`. -/
@[simps!]
def ContinuousAddEquiv.smul {G α : Type*} [Group G] [TopologicalSpace α] [AddMonoid α]
    [DistribMulAction G α]
    [ContinuousConstSMul G α] (g : G) : α ≃ₜ+ α where
  __ := Homeomorph.smul g
  map_add' := smul_add g

@[simp]
lemma ContinuousAddEquiv.smul_inv {G α : Type*} [Group G] [TopologicalSpace α] [AddMonoid α]
    [DistribMulAction G α]
    [ContinuousConstSMul G α] (g : G) :
  ContinuousAddEquiv.smul g⁻¹ (α := α) = (ContinuousAddEquiv.smul g).symm := by ext; simp

/-- `MulOpposite.op` as a `MeasurableEquiv`. -/
def MulOpposite.opMeasurableEquiv {M : Type*} [MeasurableSpace M] : M ≃ᵐ Mᵐᵒᵖ where
  __ := MulOpposite.opEquiv
  measurable_toFun := measurable_mul_op
  measurable_invFun := measurable_mul_unop

/-- `Units.opEquiv` (taking `x` to `x`) as a `ContinuousMulEquiv`. -/
@[simps!]
def Units.opContinuousMulEquiv {M : Type*} [Monoid M] [TopologicalSpace M] :
    Mᵐᵒᵖˣ ≃ₜ* Mˣᵐᵒᵖ where
  __ := Units.opEquiv
  continuous_toFun := by
    refine continuous_induced_rng.mpr (continuous_induced_rng.mpr ?_)
    exact (MulOpposite.continuous_unop.prodMap MulOpposite.continuous_unop).comp
      (continuous_induced_dom (f := Units.embedProduct Mᵐᵒᵖ))
  continuous_invFun :=
    continuous_induced_rng.mpr (continuous_prodMk.mpr ⟨by fun_prop, by fun_prop⟩)

@[simp]
lemma Units.coe_opContinuousMulEquiv_symm_apply
    {M : Type*} [Monoid M] [TopologicalSpace M] (x : Mˣᵐᵒᵖ) :
    (Units.opContinuousMulEquiv.symm x).1 = .op x.unop := rfl

@[simp]
lemma Units.coe_opContinuousMulEquiv_symm_apply_inv
    {M : Type*} [Monoid M] [TopologicalSpace M] (x : Mˣᵐᵒᵖ) :
    ((Units.opContinuousMulEquiv.symm x)⁻¹).1 = .op ↑(x.unop⁻¹) := rfl

instance {R : Type*} [Ring R] [TopologicalSpace R] [IsOpenUnits R] : IsOpenUnits Rᵐᵒᵖ where
  isOpenEmbedding_unitsVal := by
    refine .of_comp _ MulOpposite.opHomeomorph.symm.isOpenEmbedding ?_
    convert (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).comp
      (MulOpposite.opHomeomorph.symm.isOpenEmbedding.comp
        Units.opContinuousMulEquiv.isOpenEmbedding)
    ext; simp

/-- smul as a `ContinuousMulEquiv`. -/
@[simps!]
def MulDistribMulAction.toContinuousMulEquiv
    {G : Type*} (x : G) (M : Type*) [Group G] [Monoid M] [MulDistribMulAction G M]
    [TopologicalSpace M] [ContinuousConstSMul G M] : M ≃ₜ* M where
  __ := MulDistribMulAction.toMulEquiv _ x
  continuous_toFun := continuous_const_smul _
  continuous_invFun := continuous_const_smul _

attribute [simp] Subgroup.mem_subgroupOf AddSubgroup.mem_addSubgroupOf

lemma Subgroup.FiniteIndex.of_compactSpace {G : Type*} [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] [CompactSpace G] (U : Subgroup G)
    (h : IsOpen (X := G) U) : U.FiniteIndex :=
  Subgroup.finiteIndex_iff_finite_quotient.mpr (Subgroup.quotient_finite_of_isOpen _ h)

instance {G : Type*} [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] (K : Subgroup G) :
    SeparatelyContinuousMul K where
  continuous_const_mul := by
    simp only [continuous_def]
    rintro x _ ⟨t, ht, rfl⟩
    exact ⟨_, (continuous_const_mul x.1).isOpen_preimage _ ht, rfl⟩
  continuous_mul_const := by
    simp only [continuous_def]
    rintro x _ ⟨t, ht, rfl⟩
    exact ⟨_, (continuous_mul_const x.1).isOpen_preimage _ ht, rfl⟩

lemma Subgroup.IsFiniteRelIndex.of_isCompact {G : Type*} [Group G]
    [TopologicalSpace G] [SeparatelyContinuousMul G] {U K : Subgroup G}
    (hU : IsOpen (X := G) U) (hK : IsCompact (X := G) K) : U.IsFiniteRelIndex K :=
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
    (.of_compactSpace _ (hU.preimage continuous_subtype_val))

instance {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul G] (H : Subgroup G) :
    MeasurableMul H where
  measurable_const_mul := by
    rintro x _ ⟨t, ht, rfl⟩
    exact ⟨_, measurable_const_mul x.1 ht, rfl⟩
  measurable_mul_const := by
    rintro x _ ⟨t, ht, rfl⟩
    exact ⟨_, measurable_mul_const x.1 ht, rfl⟩

end
