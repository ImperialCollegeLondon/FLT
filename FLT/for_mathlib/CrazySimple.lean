import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.Artinian
import FLT.for_mathlib.Con
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Equiv
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Algebra.Category.AlgebraCat.Basic

variable (K : Type*) [Field K]
variable (A : Type*) [Ring A]



-- Theorem 2.21
/-
Theorem 2.21. Let Mn(R) be a full matrix ring on the ring R, then any ideal I is of the form Mn(I)
for some ideal I of R.
Proof. If I is an ideal of R, then as scalar multiplication and matrix addition happen component-wise
it is clear that Mn(I) is an ideal of Mn(R). Further- more, if Mn(I1) = Mn(I2) for ideals I1,I2,
it is clear that I1 = I2 because matrices are equal if and only if each component is equal.
Next, suppose that J is an ideal of Mn(R). Let I denote the set of elements in the top left entry
of the matrices of J , then I is an ideal of R. This is because first, it’s trivially closed under
addition and secondly, if it’s not closed under multiplication of elements in R, then it contradicts
J is an ideal of Mn(R). Let eij be the matrix with 0 in every entry apart from the ijth entry.
Let M ∈ J , then e1jMej1 = mije11 ∈ J so that mij ∈ I and hence J ⊆ Mn(I). On the other hand, let N = (nij) ∈ Mn(I), and take M = (mij) ∈ J such that m11 = nij. Then nijeij = m11eij = ei1Me1j = m11eij ∈ J. Therefore, as J is closed under addition, and ij were arbitrary it follows that N ∈ J . Therefore, Mn(I) ⊆ I which means that Mn(I) = J .
-/

open BigOperators Matrix Quaternion

local notation "M[" ι "," R "]" => Matrix ι ι R

section two_two_one

variable (ι : Type*) [Fintype ι] [h : Nonempty ι] [DecidableEq ι]

/--
If `I` is a two-sided-ideal of `A`, then `Mₙ(I) := {(xᵢⱼ) | ∀ i j, xᵢⱼ ∈ I}` is a two-sided-ideal of
`Mₙ(A)`.
-/
@[simps]
def RingCon.mapMatrix (I : RingCon A) : RingCon M[ι, A] where
  r X Y := ∀ i j, I (X i j) (Y i j)
  iseqv :=
  { refl := fun X i j ↦ I.refl (X i j)
    symm := fun h i j ↦ I.symm (h i j)
    trans := fun h1 h2 i j ↦ I.trans (h1 i j) (h2 i j) }
  mul' h h' := fun i j ↦ by
    simpa only [Matrix.mul_apply] using I.sum fun k _ ↦ I.mul (h _ _) (h' _ _)
  add' {X X' Y Y'} h h' := fun i j ↦ by
    simpa only [Matrix.add_apply] using I.add (h _ _) (h' _ _)

@[simp] lemma RingCon.mem_mapMatrix (I : RingCon A) (x) : x ∈ I.mapMatrix ι ↔ ∀ i j, x i j ∈ I :=
  Iff.rfl

/--
The two-sided-ideals of `A` corresponds bijectively to that of `Mₙ(A)`.
Given an ideal `I ≤ A`, we send it to `Mₙ(I)`.
Given an ideal `J ≤ Mₙ(A)`, we send it to `{x₀₀ | x ∈ J}`.
-/
@[simps]
def RingCon.equivRingConMatrix (oo : ι) : RingCon A ≃ RingCon M[ι, A] where
  toFun I := I.mapMatrix ι
  invFun J := RingCon.fromIdeal
    ((fun (x : M[ι, A]) => x oo oo) '' J)
    ⟨0, J.zero_mem, rfl⟩
    (by rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, J.add_mem hx hy, rfl⟩)
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨-x, J.neg_mem hx, rfl⟩)
    (by
      rintro x _ ⟨y, hy, rfl⟩
      exact ⟨Matrix.diagonal (fun _ ↦ x) * y, J.mul_mem_left _ _ hy, by simp⟩)
    (by
      rintro _ y ⟨x, hx, rfl⟩
      exact ⟨x * Matrix.diagonal (fun _ ↦ y), J.mul_mem_right _ _ hx, by simp⟩)
  right_inv J := SetLike.ext fun x ↦ by
    simp only [mem_fromIdeal, Set.mem_image, SetLike.mem_coe, mem_mapMatrix]
    constructor
    · intro h
      choose y hy1 hy2 using h
      rw [matrix_eq_sum_std_basis x]
      refine J.sum_mem _ fun i _ ↦ J.sum_mem _ fun j _ ↦ ?_
      suffices
          stdBasisMatrix i j (x i j) =
          stdBasisMatrix i oo 1 * y i j * stdBasisMatrix oo j 1 by
        rw [this]
        exact J.mul_mem_right _ _ (J.mul_mem_left _ _ <| hy1 _ _)
      ext a b
      by_cases hab : a = i ∧ b = j
      · rcases hab with ⟨ha, hb⟩
        subst ha hb
        simp only [stdBasisMatrix, and_self, ↓reduceIte, StdBasisMatrix.mul_right_apply_same,
          StdBasisMatrix.mul_left_apply_same, one_mul, mul_one]
        exact (hy2 a b).symm
      · conv_lhs =>
          dsimp [stdBasisMatrix]
          rw [if_neg (by tauto)]
        rw [not_and_or] at hab
        rcases hab with ha | hb
        · rw [mul_assoc, Matrix.StdBasisMatrix.mul_left_apply_of_ne (h := ha)]
        · rw [Matrix.StdBasisMatrix.mul_right_apply_of_ne (hbj := hb)]
    · intro hx i j
      refine ⟨stdBasisMatrix oo i 1 * x * stdBasisMatrix j oo 1,
        J.mul_mem_right _ _ (J.mul_mem_left _ _ hx), ?_⟩
      rw [Matrix.StdBasisMatrix.mul_right_apply_same, Matrix.StdBasisMatrix.mul_left_apply_same,
        mul_one, one_mul]
  left_inv I := SetLike.ext fun x ↦ by
    simp only [mem_fromIdeal, Set.mem_image, SetLike.mem_coe, mem_mapMatrix]
    constructor
    · intro h
      choose y hy1 hy2 using h
      exact hy2 ▸ hy1 _ _
    · intro h
      exact ⟨of fun _ _ => x, by simp [h], rfl⟩

/--
The two-sided-ideals of `A` corresponds bijectively to that of `Mₙ(A)`.
Given an ideal `I ≤ A`, we send it to `Mₙ(I)`.
Given an ideal `J ≤ Mₙ(A)`, we send it to `{x₀₀ | x ∈ J}`.
-/
@[simps!]
def RingCon.equivRingConMatrix' (oo : ι) : RingCon A ≃o RingCon M[ι, A] where
__ := RingCon.equivRingConMatrix A _ oo
map_rel_iff' {I J} := by
  simp only [equivRingConMatrix_apply, RingCon.le_iff]
  constructor
  · intro h x hx
    specialize @h (of fun _ _ => x) (by simpa)
    simpa using h
  · intro h X hX i j
    exact h <| hX i j

end two_two_one

section simple_ring

open MulOpposite

variable [IsSimpleOrder (RingCon A)] [Algebra K A] (h : FiniteDimensional K A)

instance : Nontrivial A := by
  refine subsingleton_or_nontrivial A |>.resolve_left fun r => ?_
  obtain ⟨x, y, hxy⟩ := (inferInstance : IsSimpleOrder (RingCon A)).1
  exact hxy $ SetLike.ext fun a => (show a = 0 from Subsingleton.elim _ _) ▸
    by simp [RingCon.zero_mem]

variable (D : Type*) [DivisionRing D]

/--
Division rings are a simple ring
-/
instance : IsSimpleOrder (RingCon D) where
  exists_pair_ne := ⟨⊥, ⊤, by
    apply_fun (· 0 1)
    convert false_ne_true
    -- Change after https://github.com/leanprover-community/mathlib4/pull/12860
    exact iff_false_iff.mpr zero_ne_one⟩
  eq_bot_or_eq_top r := by
    obtain h | h := _root_.forall_or_exists_not (fun x ↦ x ∈ r ↔ x = 0)
    · left
      exact SetLike.ext fun x ↦ (h x).trans (by rfl)
    · right
      obtain ⟨x, hx⟩ := h
      refine SetLike.ext fun y ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
      have hx' : x ≠ 0 := by rintro rfl; simp [r.zero_mem] at hx
      rw [show y = y * x * x⁻¹ by field_simp]
      refine r.mul_mem_right _ _ <| r.mul_mem_left _ _ (by tauto)

instance op_simple : IsSimpleOrder (RingCon (Aᵐᵒᵖ)) :=
  RingCon.toMopOrderIso.symm.isSimpleOrder

/--
The canonical map from `Aᵒᵖ` to `Hom(A, A)`
-/
@[simps]
def mopToEnd : Aᵐᵒᵖ →+* Module.End A A where
  toFun a :=
    { toFun := fun x ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by aesop
  map_mul' := by aesop


/--
The canonical map from `A` to `Hom(A, A)ᵒᵖ`
-/
@[simps]
def toEndMop : A →+* (Module.End A A)ᵐᵒᵖ where
  toFun a := op
    { toFun := fun x ↦ x * a
      map_add' := by simp [add_mul]
      map_smul' := by intros; simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by intros; apply_fun MulOpposite.unop using unop_injective; ext; simp
  map_mul' := by intros; apply_fun MulOpposite.unop using unop_injective; ext; simp

/--
the map `Aᵒᵖ → Hom(A, A)` is bijective
-/
noncomputable def mopEquivEnd : Aᵐᵒᵖ ≃+* Module.End A A :=
  RingEquiv.ofBijective (mopToEnd A) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr $
    SetLike.ext fun α => ⟨by rintro (ha : mopToEnd A α = 0); simpa using (DFunLike.ext_iff.mp ha) 1,
      by rintro rfl; ext; simp⟩, fun φ => ⟨op (φ 1), by ext; simp⟩⟩

/--
the map `Aᵒᵖ → Hom(A, A)` is bijective
-/
noncomputable def equivEndMop : A ≃+* (Module.End A A)ᵐᵒᵖ :=
  RingEquiv.ofBijective (toEndMop A) ⟨RingHom.injective_iff_ker_eq_bot _ |>.mpr $ SetLike.ext
    fun α => ⟨fun ha => by
      simp only [RingHom.mem_ker, toEndMop_apply, op_eq_zero_iff, DFunLike.ext_iff,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at ha
      simpa using ha 1, fun (ha : α = 0) => by simp [ha]⟩,
      fun φ => ⟨φ.unop 1, unop_injective $ by ext; simp⟩⟩

/--
For any ring `D`, `Mₙ(D) ≅ Mₙ(D)ᵒᵖ`.
-/
@[simps]
def matrixEquivMatrixMop (n : ℕ) (D : Type*) [Ring D] :
    Matrix (Fin n) (Fin n) Dᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ where
  toFun := fun M => MulOpposite.op (M.transpose.map (fun d => MulOpposite.unop d))
  invFun := fun M => (MulOpposite.unop M).transpose.map (fun d => MulOpposite.op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective $ by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop

instance matrix_simple_ring (ι : Type*) [ne : Nonempty ι] [Fintype ι] [DecidableEq ι]
    (R : Type*) [Ring R] [IsSimpleOrder (RingCon R)] :
    IsSimpleOrder (RingCon M[ι, R]) :=
  RingCon.equivRingConMatrix' _ ι (ne.some) |>.symm.isSimpleOrder

-- Do we need this?
-- lemma simple_ring_simple_matrix (R : Type*) [Ring R] [IsSimpleOrder (RingCon R)] :
--     IsSimpleOrder (RingCon M[Fin 1, R]) := inferInstance

universe u

lemma Ideal.eq_of_le_of_isSimpleModule {A : Type u} [Ring A]
    (I : Ideal A) [simple : IsSimpleModule A I]
    (J : Ideal A) (ineq : J ≤ I) (a : A) (ne_zero : a ≠ 0) (mem : a ∈ J) : J = I := by
  obtain eq | eq : Submodule.comap I.subtype J = ⊥ ∨ Submodule.comap I.subtype J = ⊤ :=
    simple.2 _
  · rw [Submodule.eq_bot_iff] at eq
    specialize eq ⟨a, ineq mem⟩ (by simpa [Subtype.ext_iff])
    rw [Subtype.ext_iff] at eq
    exact ne_zero eq |>.elim
  · simp only [Submodule.comap_subtype_eq_top] at eq
    exact le_antisymm ineq eq

lemma minimal_ideal_isSimpleModule {A : Type u} [Ring A]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥)
    (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I) :
    IsSimpleModule A I := by
  letI ins1 : Nontrivial I := by
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr I_nontrivial)
    exact ⟨0, y, hy.symm⟩
  refine ⟨fun J ↦ ?_⟩
  rw [or_iff_not_imp_left]
  intro hJ
  specialize I_minimal (J.map I.subtype : Ideal A) (by
    contrapose! hJ
    apply_fun Submodule.comap (f := I.subtype) at hJ
    rw [Submodule.comap_map_eq_of_injective (hf := Submodule.injective_subtype _)] at hJ
    rw [hJ, Submodule.comap_bot]
    rw [LinearMap.ker_eq_bot]
    exact Submodule.injective_subtype _)
  apply_fun Submodule.map (f := I.subtype) using Submodule.map_injective_of_injective
    (hf := Submodule.injective_subtype I)
  simp only [Submodule.map_top, Submodule.range_subtype]
  contrapose! I_minimal
  refine lt_of_le_of_ne (fun x hx ↦ ?_) I_minimal
  simp only [Submodule.mem_map, Submodule.coeSubtype, Subtype.exists, exists_and_right,
    exists_eq_right] at hx
  exact hx.1

lemma Wedderburn_Artin.aux.one_eq
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∃ (n : ℕ) (x : Fin n → A) (i : Fin n → I), ∑ j : Fin n, i j * x j = 1 := by

  letI I' : RingCon A := RingCon.span I
  have I'_is_everything : I' = ⊤ := simple.2 I' |>.resolve_left (fun r ↦ by
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr I_nontrivial)
    have hy' : y.1 ∈ I' := by
      change I' y 0
      exact .of _ _ <| by simp [y.2]
    rw [r] at hy'
    change _ = _ at hy'
    aesop)
  have one_mem_I' : 1 ∈ I' := by rw [I'_is_everything]; trivial

  rw [RingCon.mem_span_ideal_iff_exists_fin] at one_mem_I'
  obtain ⟨n, finn, x, y, hy⟩ := one_mem_I'
  exact ⟨Fintype.card n, x ∘ (Fintype.equivFin _).symm, y ∘ (Fintype.equivFin _).symm, hy ▸
    Fintype.sum_bijective (Fintype.equivFin _).symm (Equiv.bijective _) _ _ fun k ↦ rfl⟩

private noncomputable abbrev Wedderburn_Artin.aux.n
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) : ℕ := by
  classical
  exact Nat.find <| Wedderburn_Artin.aux.one_eq I I_nontrivial

private noncomputable abbrev Wedderburn_Artin.aux.x
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Fin (Wedderburn_Artin.aux.n I I_nontrivial) → A  := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose

private noncomputable abbrev Wedderburn_Artin.aux.i
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Fin (Wedderburn_Artin.aux.n I I_nontrivial) → I := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose_spec.choose

open Wedderburn_Artin.aux in
private noncomputable abbrev Wedderburn_Artin.aux.nxi_spec
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∑ j : Fin (n I I_nontrivial), (i I I_nontrivial j) * (x I I_nontrivial j) = 1 := by
  classical
  exact (Nat.find_spec <| Wedderburn_Artin.aux.one_eq I I_nontrivial).choose_spec.choose_spec

private lemma Wedderburn_Artin.aux.n_ne_zero
    {A : Type u} [Ring A] [Nontrivial A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Wedderburn_Artin.aux.n I I_nontrivial ≠ 0 := by
  by_contra hn
  let n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  let x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  let i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  let e : Fin n ≃ Fin 0 := Fin.castOrderIso hn
  have one_eq := calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Fin 0, i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ rfl)
    _ = 0 := by simp
  simp at one_eq

open Wedderburn_Artin.aux in
private noncomputable abbrev Wedderburn_Artin.aux.nxi_ne_zero
    {A : Type u} [Ring A] [Nontrivial A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    ∀ j, x I I_nontrivial j ≠ 0 ∧ i I I_nontrivial j ≠ 0 := by
  classical
  let n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  have n_ne : n ≠ 0 := Wedderburn_Artin.aux.n_ne_zero I I_nontrivial
  let x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  let i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 := Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  by_contra! H
  obtain ⟨j, (hj : x j ≠ 0 → i j = 0)⟩ := H
  refine Nat.find_min (aux.one_eq I I_nontrivial) (m := n - 1)
    (show n - 1 < n by omega) ?_

  let e : Fin n ≃ Option (Fin (n - 1)) :=
    (Fin.castOrderIso <| by omega).toEquiv.trans (finSuccEquiv' (j.cast <| by omega))
  have one_eq := calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Option (Fin (n - 1)), i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ by simp)
  simp only [Equiv.symm_trans_apply, OrderIso.toEquiv_symm, Fin.symm_castOrderIso,
    RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fintype.sum_option, finSuccEquiv'_symm_none,
    Fin.cast_trans, Fin.cast_eq_self, finSuccEquiv'_symm_some, e] at one_eq
  if xj_eq : x j = 0
  then rw [xj_eq, mul_zero, zero_add] at one_eq; exact ⟨_, _, one_eq.symm⟩
  else erw [hj xj_eq, Submodule.coe_zero, zero_mul, zero_add] at one_eq; exact ⟨_, _, one_eq.symm⟩

private lemma Wedderburn_Artin.aux.equivIdeal
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I) :
    ∃ (n : ℕ), Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  letI n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  have n_ne : n ≠ 0 := Wedderburn_Artin.aux.n_ne_zero I I_nontrivial
  letI x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  letI i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal

  letI g : (Fin n → I) →ₗ[A] A := {
    toFun := fun v ↦ ∑ j : Fin n, v j * x j
    map_add' := by
      intro v1 v2
      simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro a v
      simp [Finset.mul_sum, mul_assoc]
  }

  have g_surj : Function.Surjective g := by
    intro a
    refine ⟨fun j ↦ ⟨a * (i j).1, I.mul_mem_left _ (i j).2⟩, ?_⟩
    simp [g, mul_assoc, ← Finset.mul_sum, one_eq]

  have g_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    by_contra!
    obtain ⟨⟨y, (hy1 : ∑ j : Fin n, _ = 0)⟩, hy2⟩ :=
      Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr this)
    replace hy2 : y ≠ 0 := by contrapose! hy2; subst hy2; rfl
    obtain ⟨j, hj⟩ : ∃ (j : Fin n), y j ≠ 0 := by contrapose! hy2; ext; rw [hy2]; rfl
    have eq1 : Ideal.span {(y j).1} = I :=
      Ideal.eq_of_le_of_isSimpleModule (ineq := by simp [Ideal.span_le]) (a := (y j).1)
        (ne_zero := by contrapose! hj; rwa [Subtype.ext_iff]) (Ideal.subset_span (by simp))

    have mem : (i j).1 ∈ Ideal.span {(y j).1} := eq1.symm ▸ (i j).2
    rw [Ideal.mem_span_singleton'] at mem
    obtain ⟨r, hr⟩ := mem
    have hr' : (i j).1 - r * (y j).1 = 0 := by rw [hr, sub_self]
    apply_fun (r * ·) at hy1
    simp only [Finset.mul_sum, ← mul_assoc, mul_zero] at hy1
    have one_eq' : ∑ _, _ - ∑ _, _ = 1 - 0 := congr_arg₂ (· - ·) one_eq hy1
    rw [← Finset.sum_sub_distrib, sub_zero] at one_eq'
    let e : Fin n ≃ Option (Fin (n - 1)) :=
      (Fin.castOrderIso <| by omega).toEquiv.trans (finSuccEquiv' (j.cast <| by omega))

    have one_eq' := calc 1
      _ = _ := one_eq'.symm
      _ = ∑ k : Option (Fin (n - 1)),
            (i (e.symm k) * x (e.symm k) - r * y (e.symm k) * x (e.symm k)) :=
          Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ by simp)
      _ = ∑ k : Option (Fin (n - 1)),
            ((i (e.symm k) - r * y (e.symm k)) * x (e.symm k)) :=
          Finset.sum_congr rfl (fun _ _ ↦ by simp only [sub_mul, mul_assoc])

    simp only [Equiv.symm_trans_apply, OrderIso.toEquiv_symm, Fin.symm_castOrderIso,
      RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fintype.sum_option, finSuccEquiv'_symm_none,
      Fin.cast_trans, Fin.cast_eq_self, hr', zero_mul, finSuccEquiv'_symm_some, zero_add,
      e] at one_eq'
    set f := _
    change 1 = ∑ k : Fin (n - 1), (i ∘ f - (r • y) ∘ f) k * (x ∘ f) k at one_eq'
    exact Nat.find_min (Wedderburn_Artin.aux.one_eq I I_nontrivial) (m := n - 1)
      (show n - 1 < n by omega) ⟨_, _, one_eq'.symm⟩
  exact ⟨n, ⟨LinearEquiv.ofBijective g ⟨g_inj, g_surj⟩⟩⟩

set_option maxHeartbeats 800000 in
/--
For `A`-module `M`,
`Hom(Mⁿ, Mⁿ) ≅ Mₙ(Hom(M, M))`

-/
@[simps]
def endPowEquivMatrix
    (A : Type u) [Ring A] (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ):
    Module.End A (Fin n → M) ≃+* M[Fin n, Module.End A M] where
  toFun := fun f ↦ Matrix.of fun i j ↦
  { toFun := fun x ↦ f (Function.update 0 j x) i
    map_add' := fun x y ↦ by
      dsimp
      change _ = (f _ + f _) i
      rw [← f.map_add]
      congr!
      ext
      simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, Pi.add_apply]
      aesop
    map_smul' := fun x y ↦ by
      dsimp
      change _ = (x • f _) _
      rw [← f.map_smul, ← Function.update_smul]
      simp }
  invFun M :=
  { toFun := fun x ↦ ∑ i : Fin n, Function.update 0 i (∑ j : Fin n, M i j (x j))
    map_add' := by
      intro x y
      dsimp
      simp only [map_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ext j : 1
      simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, Pi.add_apply]
      split_ifs with h
      · subst h
        rw [Finset.sum_add_distrib]
      · simp
    map_smul' := by
      intro a x
      dsimp
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ext j : 1
      simp only [Function.update, _root_.map_smul, eq_rec_constant, Pi.zero_apply, dite_eq_ite,
        Pi.smul_apply, smul_ite, smul_zero]
      split_ifs with h
      · subst h
        rw [Finset.smul_sum]
      · simp }
  left_inv f := by
    dsimp
    ext i x j : 3
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_single,
      Function.comp_apply, Finset.sum_apply, Function.update, eq_rec_constant, Pi.zero_apply,
      dite_eq_ite, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [← Fintype.sum_apply, ← map_sum]
    congr! 1
    ext k : 1
    simp [Pi.single, Function.update]
  right_inv M := by
    dsimp
    ext i j x : 3
    simp only [Function.update, eq_rec_constant, Pi.zero_apply, dite_eq_ite, Finset.sum_apply,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, of_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid]
    rw [show ∑ k : Fin n, ((M i k) (if k = j then x else 0)) =
      ∑ k : Fin n, if k = j then (M i k x) else 0
      from Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> aesop]
    simp
  map_mul' := by
    intro f g
    dsimp
    ext i j x : 2
    simp only [of_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_apply, LinearMap.coeFn_sum,
      Finset.sum_apply, LinearMap.mul_apply, AddSubmonoid.coe_finset_sum,
      Submodule.coe_toAddSubmonoid]
    rw [← Fintype.sum_apply, ← map_sum]
    congr! 1
    ext k : 1
    simp [Function.update]
  map_add' := by
    intro f g
    dsimp
    ext i j x : 2
    simp

example : true := rfl

theorem Wedderburn_Artin_ideal_version
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal
  exact ⟨n, I, inferInstance, ⟨e⟩⟩

theorem Wedderburn_Artin
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty (A ≃+* M[Fin n, (Module.End A I)ᵐᵒᵖ]) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal

  let endEquiv : Module.End A A ≃+* Module.End A (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }

  exact ⟨n, I, inferInstance, ⟨equivEndMop A |>.trans <|
    endEquiv.op.trans <| (endPowEquivMatrix A I n).op.trans <| (matrixEquivMatrixMop _ _).symm⟩⟩

theorem Wedderburn_Artin'
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (S : Type u) (h : DivisionRing S),
    Nonempty (A ≃+* (M[Fin n, S])) := by
  classical
  obtain ⟨n, I, inst, e⟩ := Wedderburn_Artin A
  exact ⟨n, (Module.End A I)ᵐᵒᵖ, inferInstance, e⟩

end simple_ring

universe u v w
section central_simple
variable (k : Type*) [Field k] [h : IsAlgClosed k]
variable (K : Type*) [Field K]
variable {A: Type*} [Ring A] [Algebra k A]
variable (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B]

instance: IsArtinianRing K := inferInstance

lemma IsArtinianRing.of_finiteDimensional : IsArtinianRing B := by
  rw [IsArtinianRing, ← monotone_stabilizes_iff_artinian]
  let n := FiniteDimensional.finrank K B
  intro ⟨f, hf⟩; unfold Monotone at hf
  simp only [OrderHom.coe_mk]
  use n ; intro m hmn; have lecon := hf hmn
  rw [← LE.le.le_iff_eq]
  · exact lecon
  · by_contra hf0
    -- rw [← lt_iff_not_le (y := f m) (x := f n)] at hf0
    sorry

  --exact FiniteDimensional.finite_basis_extends_to_basis

lemma Matrix.mem_center_iff (R : Type*) [Ring R] (n : ℕ) (M) :
    M ∈ Subring.center M[Fin n, R] ↔ ∃ α : (Subring.center R), M = α • 1 := by
  constructor
  · if h : n = 0
    then subst h; exact fun _ => ⟨0, Subsingleton.elim _ _⟩
    else
      intro h
      rw [Subring.mem_center_iff] at h
      have diag : Matrix.IsDiag M := by
        intro i j hij
        specialize h (stdBasisMatrix i i 1)
        rw [← Matrix.ext_iff] at h
        specialize h i j
        simpa only [StdBasisMatrix.mul_left_apply_same, one_mul,
          StdBasisMatrix.mul_right_apply_of_ne (hbj := hij.symm)] using h
      have (i j : Fin n) : M i i = M j j := by
        specialize h (stdBasisMatrix i j 1)
        rw [← Matrix.ext_iff] at h
        specialize h i j
        simpa [Eq.comm] using h
      obtain ⟨b, hb⟩ : ∃ (b : R), M = b • 1 := by
        refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, ?_⟩
        ext i j
        if heq : i = j
        then
          subst heq; rw [this i ⟨0, by omega⟩]; simp
        else
          rw [diag heq]
          simp only [smul_apply, smul_eq_mul]
          rwa [Matrix.one_apply_ne, mul_zero]
      suffices b ∈ Subring.center R by aesop
      simp only [Subring.mem_center_iff]
      intro g
      specialize h (Matrix.diagonal (fun _ => g))
      rw [← Matrix.ext_iff] at h
      specialize h ⟨0, by omega⟩ ⟨0, by omega⟩
      rw [hb] at h
      simp_all only [hb, diagonal_mul, smul_apply, one_apply_eq, smul_eq_mul,
        mul_one, mul_diagonal, isDiag_smul_one, implies_true]

  · rintro ⟨α, ha⟩
    rw [Subring.mem_center_iff]
    intro g ; aesop

@[simps]
def Matrix.centerEquivBase (n : ℕ) (hn : 0 < n) (R : Type*) [Ring R]:
    Subring.center (M[Fin n, R]) ≃+* (Subring.center R) where
  toFun A := ⟨(A.1 ⟨0, by omega⟩ ⟨0, by omega⟩), by
    have hA : A.1 ∈ Subring.center (M[Fin n, R]) := A.2
    obtain ⟨a, ha⟩ := (Matrix.mem_center_iff R n A.1).1 hA
    rw [← Matrix.ext_iff] at ha
    specialize ha ⟨0, by omega⟩ ⟨0, by omega⟩
    aesop⟩
  invFun a := ⟨a • 1, by
    rw [Subring.mem_center_iff]; intro A; ext i j; simp [mul_comm]⟩
  left_inv := by
    if hn : n = 0
    then
      subst hn
      exact fun _ => Subsingleton.elim _ _
    else
      rintro ⟨A, hA⟩
      rw [Matrix.mem_center_iff] at hA
      obtain ⟨α, rfl⟩ := hA
      simp only [trace_smul, trace_one, Fintype.card_fin,
        smul_eq_mul, Subtype.mk.injEq]
      ext
      simp only [smul_apply, one_apply_eq, Submonoid.mk_smul,
        smul_eq_mul, smul_one_mul]
  right_inv := by
    intro ; simp only [smul_apply, one_apply_eq]; aesop
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    rw [Matrix.mem_center_iff] at hA hB
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨b, rfl⟩ := hB
    simp only [Subring.center_toSubsemiring, Subsemiring.center_toSubmonoid,
      Submonoid.mk_mul_mk, mul_smul_one, smul_apply, one_apply_eq]
  map_add' := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    rw [Matrix.mem_center_iff] at hA hB
    obtain ⟨a, rfl⟩ := hA
    obtain ⟨b, rfl⟩ := hB
    simp only [AddMemClass.mk_add_mk, add_apply, smul_apply, one_apply_eq]

theorem ringequiv_perserve_center (R1 R2 : Type*) [Ring R1] [Ring R2] (h : R1 ≃+* R2) :
    ∀ x ∈ Subring.center R1, h.toRingHom x ∈ Subring.center R2 := by
  intro x hx
  rw [Subring.mem_center_iff]
  intro y ; rw [Subring.mem_center_iff] at hx
  --simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  have y_eq : y = h.toRingHom (h.symm.toRingHom y) := by simp
  rw [y_eq, ← h.toRingHom.map_mul, ← h.toRingHom.map_mul] ;
  simp_all only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply,
     _root_.map_mul]

variable {B} in
@[simps]
def algebraMapEndIdealMop (I : Ideal B) : K →+* (Module.End B I)ᵐᵒᵖ where
  toFun k := .op $
  { toFun := fun x => k • x
    map_add' := fun x y => by simp
    map_smul' := fun k' x => by ext; simp }
  map_one' := MulOpposite.unop_injective $ by ext; simp
  map_mul' _ _ := MulOpposite.unop_injective $ by ext; simp [MulAction.mul_smul]
  map_zero' := MulOpposite.unop_injective $ by ext; simp
  map_add' _ _ := MulOpposite.unop_injective $ by ext; simp [add_smul]

instance (I : Ideal B) : Algebra K (Module.End B I)ᵐᵒᵖ where
  __ := algebraMapEndIdealMop K I
  commutes' := by
    rintro r ⟨x⟩
    refine MulOpposite.unop_injective ?_
    ext ⟨i, hi⟩
    simp only [algebraMapEndIdealMop_apply, MulOpposite.unop_mul, MulOpposite.unop_op,
      LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, SetLike.mk_smul_of_tower_mk,
      SetLike.val_smul_of_tower]
    change (x (r • ⟨i, hi⟩)).1 = _
    convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) using 1
    simp only [SetLike.mk_smul_of_tower_mk, algebraMap_smul]
    rw [SetLike.val_smul_of_tower]
    rw [Algebra.smul_def]
    rfl
  smul k x := .op $ (algebraMapEndIdealMop K I k).unop * x.unop
  smul_def' := by
    rintro r ⟨x⟩
    refine MulOpposite.unop_injective ?_
    ext ⟨i, hi⟩
    simp only [algebraMapEndIdealMop_apply, MulOpposite.unop_op, MulOpposite.op_mul,
      MulOpposite.op_unop, MulOpposite.unop_smul, LinearMap.smul_apply, SetLike.val_smul_of_tower,
      MulOpposite.unop_mul, LinearMap.mul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      SetLike.mk_smul_of_tower_mk]
    change r • (x ⟨i, hi⟩).1 = (x (r • ⟨i, hi⟩)).1
    convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) |>.symm using 1
    · rw [Algebra.smul_def]; rfl
    · congr; ext; simp

lemma algebraEndIdealMop.algebraMap_eq (I : Ideal B) :
    algebraMap K (Module.End B I)ᵐᵒᵖ = algebraMapEndIdealMop K I := rfl

#check AlgEquiv.ofRingEquiv
lemma simple_eq_central_simple_prev
    [sim : IsSimpleOrder (RingCon B)] (centerEquiv : Subalgebra.center B = ⊥):
    ∃ (n : ℕ) (S : Type u) (div_ring : DivisionRing S) (alg : Algebra K S),
    Nonempty (B ≃ₐ[K] (M[Fin n, S])) := by
  classical
  have hB : IsArtinianRing B := IsArtinianRing.of_finiteDimensional K B
  obtain ⟨n, I, inst_I, ⟨e⟩⟩ := Wedderburn_Artin_ideal_version B

  let endEquiv : Module.End B B ≃+* Module.End B (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }

  refine ⟨n, (Module.End B I)ᵐᵒᵖ, inferInstance, inferInstance,
    ⟨AlgEquiv.ofRingEquiv (f := equivEndMop B |>.trans $
      endEquiv.op.trans $ (endPowEquivMatrix B I n).op.trans (matrixEquivMatrixMop _ _).symm) ?_⟩⟩
  intro r
  rw [Matrix.algebraMap_eq_diagonal]
  ext i j
  apply MulOpposite.unop_injective
  simp only [RingEquiv.coe_trans, Function.comp_apply, RingEquiv.op_apply_apply, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, MulOpposite.unop_op, endPowEquivMatrix_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, matrixEquivMatrixMop_symm_apply, map_apply, transpose_apply, of_apply,
    diagonal, Pi.algebraMap_apply, algebraEndIdealMop.algebraMap_eq, algebraMapEndIdealMop_apply,
    endEquiv]
  split_ifs with h
  · subst h
    ext x : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_op]
    sorry
  · sorry

-- theorem simple_eq_central_simple
--     [hsim : IsSimpleOrder (RingCon B)] (hctr : Subalgebra.center B = ⊥)
--     (n : ℕ) (S : Type*) (hn : 0 < n) [h : DivisionRing S]
--     [Module K S] (Wdb: B ≃+* (M[Fin n, S])):
--     Nonempty (Subring.center S ≃+* K) ∧ FiniteDimensional K S := by
--   have hB : IsArtinianRing B := IsArtinianRing.of_finiteDimensional K B

--   constructor
--   · have center_equiv : Subring.center B ≃+* Subring.center (M[Fin n, S]) := {
--     toFun := fun a ↦ Wdb.toRingHom.restrict (Subring.center B)
--       (Subring.center (M[Fin n, S])) (ringequiv_perserve_center B (M[Fin n, S]) Wdb) a

--     invFun := fun A ↦ Wdb.symm.toRingHom.restrict (Subring.center (M[Fin n, S]))
--       (Subring.center B) (ringequiv_perserve_center (M[Fin n, S]) B Wdb.symm) A
--     left_inv := by
--       simp only [RingEquiv.toRingHom_eq_coe]
--       rw [Function.LeftInverse]; intro x; aesop
--     right_inv := by
--       simp only [RingEquiv.toRingHom_eq_coe]
--       rw [Function.RightInverse]; intro x; aesop
--     map_mul' := by simp only [RingEquiv.toRingHom_eq_coe, Subring.center_toSubsemiring,
--       Subsemiring.center_toSubmonoid, _root_.map_mul, implies_true]
--     map_add' := by simp only [RingEquiv.toRingHom_eq_coe, map_add, implies_true]
--   }
--     have equiv : Subring.center (M[Fin n, S]) ≃+* K := by
--       exact RingEquiv.symm (RingEquiv.trans hctr.symm center_equiv)
--     have equiv' : Subring.center S ≃+* K := by
--       exact RingEquiv.trans (Matrix.centerEquivBase n hn S).symm equiv
--     rw [← exists_true_iff_nonempty]
--     use equiv'

--   · rw [FiniteDimensional]
--     obtain ⟨(I : Ideal B), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal B, J ≠ ⊥ → ¬ J < I)⟩ :=
--       IsArtinian.set_has_minimal (R := B) (M := B) {I | I ≠ ⊥}
--       ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
--     haveI : IsSimpleModule B I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal

--     sorry

theorem simple_eq_matrix_algclo (h : IsSimpleOrder (RingCon A)) :
    ∃ (n : ℕ), Nonempty (A ≃+* M[Fin n, k]) := by
  sorry

end central_simple
