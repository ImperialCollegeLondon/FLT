/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

attribute [-simp] RingHom.toMonoidHom_eq_coe

@[simp]
lemma RingHom.coe_toMonoidHom {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) : ⇑f.toMonoidHom = f := rfl

@[simps]
def Set.matrixEquiv {m n α : Type*} (S : Set α) :
    S.matrix (m := m) (n := n) ≃ Matrix m n S where
  toFun f i j := ⟨f.1 i j, f.2 i j⟩
  invFun f := ⟨fun i j ↦ f i j, fun i j ↦ (f i j).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simps!]
def Subring.matrixEquiv {n α : Type*} [Ring α] [Fintype n] [DecidableEq n] (S : Subring α) :
    S.matrix (n := n) ≃+* Matrix n n S where
  __ := Set.matrixEquiv _
  map_mul' _ _ := by ext i j; simp [Set.matrixEquiv, Matrix.mul_apply]
  map_add' _ _ := rfl

lemma continuous_iff_continuousAt_one
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M : Type*} {hom : Type*} [MulOneClass M]
    [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M]
    [MonoidHomClass hom G M] {f : hom} : Continuous ⇑f ↔ ContinuousAt (⇑f) 1 :=
  ⟨Continuous.continuousAt, continuous_of_continuousAt_one _⟩

lemma MonoidHom.continuous_of_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [ContinuousMul H]
    (hφ : IsOpen (φ.ker : Set G)) : Continuous φ := by
  refine continuous_of_continuousAt_one _ ?_
  intro U hU
  simp only [Filter.mem_map]
  exact Filter.mem_of_superset (hφ.mem_nhds (by simp)) (Set.preimage_mono
    (Set.singleton_subset_iff.mpr (mem_of_mem_nhds (by simpa using hU))))

lemma MonoidHom.continuous_iff_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [DiscreteTopology H] :
    Continuous φ ↔ IsOpen (φ.ker : Set G) :=
  ⟨fun h ↦ (isOpen_discrete {1}).preimage h, MonoidHom.continuous_of_isOpen_ker⟩

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

instance {G} [TopologicalSpace G] [DivInvMonoid G] [ContinuousMul G] :
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
      ← Multiplicative.toAdd_le, ← WithZero.coe_mul, Int.add_one_le_iff]
