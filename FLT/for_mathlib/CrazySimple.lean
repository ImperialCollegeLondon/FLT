import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.Artinian
import FLT.for_mathlib.Con
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Equiv
import Mathlib.LinearAlgebra.Matrix.IsDiag

variable (A : Type*) [Ring A]

open BigOperators Matrix Quaternion MulOpposite

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

variable (K D : Type*) [Field K] [IsSimpleOrder (RingCon A)] [Algebra K A] [DivisionRing D]

/--
Division rings are a simple ring
-/
instance : IsSimpleOrder (RingCon D) where
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
@[simps!]
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
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
    (I : Ideal A) (I_nontrivial : I ≠ ⊥) :
    Wedderburn_Artin.aux.n I I_nontrivial ≠ 0 := by
  by_contra hn
  let n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  let x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  let i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  let e : Fin n ≃ Fin 0 := Fin.castOrderIso hn
  simpa using calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Fin 0, i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e e.bijective _ _ (fun _ ↦ rfl)
    _ = 0 := by simp

open Wedderburn_Artin.aux in
private noncomputable abbrev Wedderburn_Artin.aux.nxi_ne_zero
    {A : Type u} [Ring A] [simple : IsSimpleOrder (RingCon A)]
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
    ∃ (n : ℕ) (_ : n ≠ 0), Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  letI n : ℕ := Wedderburn_Artin.aux.n I I_nontrivial
  have n_ne : n ≠ 0 := Wedderburn_Artin.aux.n_ne_zero I I_nontrivial
  letI x : Fin n → A := Wedderburn_Artin.aux.x I I_nontrivial
  letI i : Fin n → I := Wedderburn_Artin.aux.i I I_nontrivial
  have one_eq : ∑ j : Fin n, (i j) * (x j) = 1 :=
    Wedderburn_Artin.aux.nxi_spec I I_nontrivial

  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal

  letI g : (Fin n → I) →ₗ[A] A :=
  { toFun := fun v ↦ ∑ j : Fin n, v j * x j
    map_add' := fun v1 v2 => by simp [add_mul, Finset.sum_add_distrib]
    map_smul' := fun a v => by simp [Finset.mul_sum, mul_assoc] }

  have g_surj : Function.Surjective g := fun a =>
    ⟨fun j ↦ ⟨a * (i j), I.mul_mem_left _ (i j).2⟩,
      by simp [g, mul_assoc, ← Finset.mul_sum, one_eq]⟩

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
  exact ⟨n, n_ne, ⟨LinearEquiv.ofBijective g ⟨g_inj, g_surj⟩⟩⟩

set_option maxHeartbeats 800000 in
/--
For `A`-module `M`,
`Hom(Mⁿ, Mⁿ) ≅ Mₙ(Hom(M, M))`

-/
@[simps]
def endPowEquivMatrix
    (M : Type*) [AddCommGroup M] [Module A M] (n : ℕ):
    Module.End A (Fin n → M) ≃+* M[Fin n, Module.End A M] where
  toFun f := Matrix.of fun i j ↦
  { toFun := fun x ↦ f (Function.update 0 j x) i
    map_add' := fun x y ↦ show  f _ i = (f _ + f _) i by
      rw [← f.map_add, ← Function.update_add, add_zero]
    map_smul' := fun x y ↦ show f _ _ = (x • f _) _ by
      rw [← f.map_smul, ← Function.update_smul, smul_zero] }
  invFun M :=
  { toFun := fun x ↦ ∑ i : Fin n, Function.update 0 i (∑ j : Fin n, M i j (x j))
    map_add' := fun x y ↦ by
      simp only [map_add, ← Finset.sum_add_distrib, Pi.add_apply]
      exact Finset.sum_congr rfl fun i _ ↦ funext fun j => by
        rw [← Function.update_add, zero_add, ← Finset.sum_add_distrib]
    map_smul' := by
      intro a x
      simp only [Pi.smul_apply, LinearMapClass.map_smul, RingHom.id_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Function.update_smul, smul_zero, Finset.smul_sum] }
  left_inv f := by
    ext i x j : 3
    simp only [of_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearMap.coe_single,
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
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, of_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show ∑ k : Fin n, ((M i k) (if k = j then x else 0)) =
      ∑ k : Fin n, if k = j then (M i k x) else 0
      from Finset.sum_congr rfl fun k _ ↦ by split_ifs <;> aesop]
    simp
  map_mul' f g := by
    ext i j x : 2
    simp only [of_apply, LinearMap.coe_mk, AddHom.coe_mk, mul_apply, LinearMap.coeFn_sum,
      Finset.sum_apply, LinearMap.mul_apply, AddSubmonoid.coe_finset_sum,
      Submodule.coe_toAddSubmonoid]
    rw [← Fintype.sum_apply, ← map_sum]
    congr! 1
    ext k : 1
    simp [Function.update]
  map_add' _ _ := by ext i j x : 2; simp

theorem Wedderburn_Artin_ideal_version
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (_ : n ≠ 0) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty ((Fin n → I) ≃ₗ[A] A) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, hn, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal
  exact ⟨n, hn, I, inferInstance, ⟨e⟩⟩

theorem Wedderburn_Artin
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (_ : n ≠ 0) (I : Ideal A) (_ : IsSimpleModule A I),
    Nonempty (A ≃+* M[Fin n, (Module.End A I)ᵐᵒᵖ]) := by
  classical
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : IsSimpleModule A I := minimal_ideal_isSimpleModule I I_nontrivial I_minimal
  obtain ⟨n, hn, ⟨e⟩⟩ := Wedderburn_Artin.aux.equivIdeal I I_nontrivial I_minimal

  let endEquiv : Module.End A A ≃+* Module.End A (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }

  exact ⟨n, hn, I, inferInstance, ⟨equivEndMop A |>.trans <|
    endEquiv.op.trans <| (endPowEquivMatrix A I n).op.trans <| (matrixEquivMatrixMop _ _).symm⟩⟩

theorem Wedderburn_Artin'
    (A : Type u) [Ring A] [IsArtinianRing A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (_ : n ≠ 0) (S : Type u) (h : DivisionRing S),
    Nonempty (A ≃+* (M[Fin n, S])) := by
  classical
  obtain ⟨n, hn, I, inst, e⟩ := Wedderburn_Artin A
  exact ⟨n, hn, (Module.End A I)ᵐᵒᵖ, inferInstance, e⟩

end simple_ring

universe u v w
section central_simple

variable (K : Type u) (B : Type v) [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

lemma Matrix.mem_center_iff (R : Type*) [Ring R] (n : ℕ) (M) :
    M ∈ Subring.center M[Fin n, R] ↔ ∃ α : (Subring.center R), M = α • 1 := by
  constructor
  · if h : n = 0 then subst h; exact fun _ => ⟨0, Subsingleton.elim _ _⟩
    else
      intro h
      rw [Subring.mem_center_iff] at h
      have diag : Matrix.IsDiag M := fun i j hij => by
        simpa only [StdBasisMatrix.mul_left_apply_same, one_mul,
          StdBasisMatrix.mul_right_apply_of_ne (hbj := hij.symm)] using
          Matrix.ext_iff.2 (h (stdBasisMatrix i i 1)) i j
      have (i j : Fin n) : M i i = M j j := by
        simpa [Eq.comm] using Matrix.ext_iff.2 (h (stdBasisMatrix i j 1)) i j
      obtain ⟨b, hb⟩ : ∃ (b : R), M = b • 1 := by
        refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, Matrix.ext fun i j => ?_⟩
        if heq : i = j then subst heq; rw [this i ⟨0, by omega⟩]; simp
        else simp [diag heq, Matrix.one_apply_ne heq]
      suffices b ∈ Subring.center R by aesop
      refine Subring.mem_center_iff.mpr fun g => ?_
      simpa [hb] using Matrix.ext_iff.2 (h (Matrix.diagonal fun _ => g)) ⟨0, by omega⟩ ⟨0, by omega⟩

  · rintro ⟨α, ha⟩; rw [Subring.mem_center_iff]; aesop

lemma Matrix.mem_center_iff' (K R : Type*) [Field K] [Ring R] [Algebra K R] (n : ℕ) (M) :
    M ∈ Subalgebra.center K M[Fin n, R] ↔
    ∃ α : (Subalgebra.center K R), M = α • 1 :=
  Matrix.mem_center_iff R n M

/--
For a matrix ring `Mₙₙ(R)`, the center of the matrix ring `Z(Mₙₙ(R))` is isomorphic to the center
`Z(R)` of `R`.
-/
@[simps]
def Matrix.centerEquivBase (n : ℕ) (hn : 0 < n) (R : Type*) [Ring R]:
    Subring.center (M[Fin n, R]) ≃+* (Subring.center R) where
  toFun A := ⟨(A.1 ⟨0, by omega⟩ ⟨0, by omega⟩), by
    obtain ⟨a, ha⟩ := (Matrix.mem_center_iff R n A.1).1 A.2
    simpa only [ha, smul_apply, one_apply_eq] using Subring.mul_mem _ a.2 $ Subring.one_mem _⟩
  invFun a := ⟨a • 1, Subring.mem_center_iff.2 fun A => Matrix.ext fun i j => by simp [mul_comm]⟩
  left_inv := by
    if hn : n = 0
    then subst hn; exact fun _ => Subsingleton.elim _ _
    else rintro ⟨A, hA⟩; obtain ⟨α, rfl⟩ := Matrix.mem_center_iff _ _ _ |>.1 hA; simp
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

theorem RingEquiv.mem_center_iff {R1 R2 : Type*} [Ring R1] [Ring R2] (e : R1 ≃+* R2) :
    ∀ x, x ∈ Subring.center R1 ↔ e x ∈ Subring.center R2 := fun x => by
  simpa only [Subring.mem_center_iff] using
    ⟨fun h r => e.symm.injective $ by simp [h], fun h r => e.injective $ by simpa using h (e r)⟩

variable {B} in
/--
For a `K`-algebra B, there is a map from `I : Ideal B` to `End(I)ᵒᵖ` defined by `k ↦ x ↦ k • x`.
-/
@[simps]
def algebraMapEndIdealMop (I : Ideal B) : K →+* (Module.End B I)ᵐᵒᵖ where
  toFun k := .op $
  { toFun := fun x => k • x
    map_add' := fun x y => by simp
    map_smul' := fun k' x => by ext; simp }
  map_one' := unop_injective $ by ext; simp
  map_mul' _ _ := unop_injective $ by ext; simp [MulAction.mul_smul]
  map_zero' := unop_injective $ by ext; simp
  map_add' _ _ := unop_injective $ by ext; simp [add_smul]

instance (I : Ideal B) : Algebra K (Module.End B I)ᵐᵒᵖ where
  __ := algebraMapEndIdealMop K I
  commutes' := fun r ⟨x⟩ => MulOpposite.unop_injective $ DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext $ show (x (r • ⟨i, hi⟩)).1 = r • (x ⟨i, hi⟩).1 by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) using 1 <;> aesop
  smul k x := .op $ (algebraMapEndIdealMop K I k).unop * x.unop
  smul_def' := fun r ⟨x⟩ => MulOpposite.unop_injective $ DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext $ by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) |>.symm using 1 <;> aesop

lemma algebraEndIdealMop.algebraMap_eq (I : Ideal B) :
    algebraMap K (Module.End B I)ᵐᵒᵖ = algebraMapEndIdealMop K I := rfl

lemma Wedderburn_Artin_algebra_version
    [sim : IsSimpleOrder (RingCon B)]:
    ∃ (n : ℕ) (_ : n ≠ 0) (S : Type v) (div_ring : DivisionRing S) (alg : Algebra K S),
    Nonempty (B ≃ₐ[K] (M[Fin n, S])) := by
  classical
  have hB : IsArtinianRing B := .of_finite K B
  obtain ⟨n, hn, I, inst_I, ⟨e⟩⟩ := Wedderburn_Artin_ideal_version B

  let endEquiv : Module.End B B ≃+* Module.End B (Fin n → I) :=
  { toFun := fun f ↦ e.symm ∘ₗ f ∘ₗ e
    invFun := fun f ↦ e ∘ₗ f ∘ₗ e.symm
    left_inv := by intro f; ext; simp
    right_inv := by intro f; ext; simp
    map_add' := by intros f g; ext; simp
    map_mul' := by intros f g; ext; simp }

  refine ⟨n, hn, (Module.End B I)ᵐᵒᵖ, inferInstance, inferInstance,
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
    rw [show r • x = Function.update (0 : Fin n → I) i (r • x) i by simp]
    refine congr_fun (e.injective ?_) i
    simp only [equivEndMop_apply, MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.apply_symm_apply]
    rw [show Function.update (0 : Fin n → I) i (r • x) = r • Function.update (0 : Fin n → I) i x
      by ext : 1; simp [Function.update]]
    rw [← Algebra.commutes, ← smul_eq_mul, ← e.map_smul]
    exact congr_arg e $ by ext; simp
  · ext x : 1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MulOpposite.unop_zero, LinearMap.zero_apply]
    rw [show (0 : I) = Function.update (0 : Fin n → I) i (r • x) j
      by simp [Function.update, if_neg (Ne.symm h)]]
    refine congr_fun (e.injective ?_) j
    simp only [equivEndMop_apply, MulOpposite.unop_op, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.apply_symm_apply, map_zero]
    rw [show Function.update (0 : Fin n → I) i (r • x) = r • Function.update (0 : Fin n → I) i x
      by ext : 1; simp [Function.update]]
    rw [← Algebra.commutes, ← smul_eq_mul, ← e.map_smul]
    exact congr_arg e $ by ext; simp

theorem is_central_of_wdb
    (hctr : Subalgebra.center K B = ⊥)
    (n : ℕ) (S : Type*) (hn : 0 < n) [h : DivisionRing S]
    [Algebra K S] (Wdb: B ≃ₐ[K] M[Fin n, S]) :
    Subalgebra.center K S = ⊥ := by
  rw [eq_bot_iff] at hctr ⊢
  intro x hx
  have hx' : (Matrix.diagonal fun _ => x) ∈ Subalgebra.center K M[Fin n, S] :=
    Matrix.mem_center_iff' _ _ _ _ |>.2 $
      ⟨⟨x, hx⟩, by ext; simp only [diagonal, of_apply]; split_ifs <;> aesop⟩
  have hx'' : Wdb.symm (Matrix.diagonal fun _ => x) ∈ Subalgebra.center K B := by
    rw [Subalgebra.mem_center_iff] at hx' ⊢
    exact fun b => Wdb.injective $ by simpa using hx' (Wdb b)
  obtain ⟨s, (hs : algebraMap _ _ s = _)⟩ := hctr hx''
  exact ⟨s, show algebraMap _ _ _ = _ by
    simpa using Matrix.ext_iff.2 congr(Wdb $hs) ⟨0, by omega⟩ ⟨0, by omega⟩⟩

theorem is_fin_dim_of_wdb
    (n : ℕ) (S : Type*) (hn : 0 < n) [h : DivisionRing S]
    [Algebra K S] (Wdb: B ≃ₐ[K] M[Fin n, S]) :
    FiniteDimensional K S := by
  classical
  obtain ⟨⟨s, span_eq⟩⟩ : FiniteDimensional K M[Fin n, S] :=
    FiniteDimensional.of_injective Wdb.symm.toLinearEquiv.toLinearMap Wdb.symm.injective
  refine ⟨⟨s.image (fun M : M[Fin n, S] => M ⟨0, by omega⟩ ⟨0, by omega⟩), ?_⟩⟩
  rw [eq_top_iff] at span_eq ⊢
  rintro x -
  obtain ⟨r, hr⟩ := mem_span_finset.1 $ span_eq (by trivial : (diagonal fun _ => x) ∈ ⊤)
  apply_fun (· ⟨0, by omega⟩ ⟨0, by omega⟩) at hr
  simp only [sum_apply, smul_apply, diagonal_apply_eq] at hr
  exact hr ▸ Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ $ Submodule.subset_span $ by simpa using ⟨i, hi, rfl⟩

lemma bijective_algebraMap_of_finiteDimensional_divisionRing_over_algClosed
    (K D : Type*) [Field K] [IsAlgClosed K] [DivisionRing D] [alg : Algebra K D]
    [FiniteDimensional K D] : Function.Bijective (algebraMap K D) := by
  letI ins1 := Algebra.IsIntegral.of_finite K D
  have surj : Function.Surjective (algebraMap K D) :=
    IsAlgClosed.algebraMap_surjective_of_isIntegral
  exact ⟨(algebraMap K D).injective, surj⟩

theorem simple_eq_matrix_algClosed [IsAlgClosed K] [IsSimpleOrder (RingCon B)] :
    ∃ (n : ℕ) (_ : n ≠ 0), Nonempty (B ≃ₐ[K] M[Fin n, K]) := by
  rcases Wedderburn_Artin_algebra_version K B with ⟨n, hn, S, ins1, ins2, ⟨e⟩⟩
  have := is_fin_dim_of_wdb K B n S (by omega) e

  exact ⟨n, hn, ⟨e.trans $ AlgEquiv.mapMatrix $ AlgEquiv.symm $
    AlgEquiv.ofBijective (Algebra.ofId _ _) $
      bijective_algebraMap_of_finiteDimensional_divisionRing_over_algClosed _ _⟩⟩

end central_simple
