import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.SimpleModule
import Mathlib.RingTheory.Artinian
import FLT.for_mathlib.Con
import Mathlib.Algebra.Quaternion

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
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, J.add_mem hx hy, rfl⟩)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, J.neg_mem hx, rfl⟩)
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
        refine J.mul_mem_right _ _ (J.mul_mem_left _ _ <| hy1 _ _)
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
the map `Aᵒᵖ → Hom(A, A)` is bijective
-/
noncomputable def mopEquivEnd : Aᵐᵒᵖ ≃+* Module.End A A := by
  refine RingEquiv.ofBijective (mopToEnd A) ⟨?_, ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    ext α
    constructor
    · intro ha
      change ((mopToEnd A) α) = 0 at ha
      rw [DFunLike.ext_iff] at ha
      specialize ha 1
      simp at ha
      exact ha

    · intro ha
      change α = 0 at ha
      ext ; simp [ha]

  · intro φ
    use (op (φ 1))
    ext ; simp

/--
For any ring `D`, `Mₙ(D) ≅ Mₙ(D)ᵒᵖ`.
-/
def maxtrixEquivMatrixMop (n : ℕ) (D : Type*) [Ring D] :
    Matrix (Fin n) (Fin n) Dᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ where
  toFun := fun M => MulOpposite.op (M.transpose.map (fun d => MulOpposite.unop d))
  invFun := fun M => (MulOpposite.unop M).transpose.map (fun d => MulOpposite.op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' := by simp; intros x y; rw[← op_mul]; rw [← Pi.mul_apply]; rw [transpose_map]; sorry
  map_add' x y := by aesop

instance matrix_simple_ring (ι : Type*) [ne : Nonempty ι] [Fintype ι] [DecidableEq ι]
    (R : Type*) [Ring R] [IsSimpleOrder (RingCon R)] :
    IsSimpleOrder (RingCon M[ι, R]) :=
  RingCon.equivRingConMatrix' _ ι (ne.some) |>.symm.isSimpleOrder

-- Do we need this?
-- lemma simple_ring_simple_matrix (R : Type*) [Ring R] [IsSimpleOrder (RingCon R)] :
--     IsSimpleOrder (RingCon M[Fin 1, R]) := inferInstance

universe u

theorem Wedderburn_Artin
    (A : Type u) [Ring A] [IsArtinianRing A] [Nontrivial A] [simple : IsSimpleOrder (RingCon A)] :
    ∃ (n : ℕ) (S : Type u) (h : DivisionRing S),
    Nonempty (A ≃+* (M[Fin n, S])) := by
  classical
  -- let `I` be a minimal left ideal
  obtain ⟨(I : Ideal A), (I_nontrivial : I ≠ ⊥), (I_minimal : ∀ J : Ideal A, J ≠ ⊥ → ¬ J < I)⟩ :=
      IsArtinian.set_has_minimal (R := A) (M := A) {I | I ≠ ⊥}
    ⟨⊤, show ⊤ ≠ ⊥ by aesop⟩
  haveI : Nontrivial I := by
    obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr I_nontrivial)
    exact ⟨0, y, hy.symm⟩
  haveI : IsSimpleModule A I := ⟨fun J ↦ by
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
    exact hx.1⟩

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

  have aux : ∃ (n : ℕ) (x : Fin n → A) (i : Fin n → I), ∑ j : Fin n, i j * x j = 1 := by
    rw [RingCon.mem_span_ideal_iff_exists_fin] at one_mem_I'
    obtain ⟨n, finn, x, y, hy⟩ := one_mem_I'
    exact ⟨Fintype.card n, x ∘ (Fintype.equivFin _).symm, y ∘ (Fintype.equivFin _).symm, hy ▸
      Fintype.sum_bijective (Fintype.equivFin _).symm (Equiv.bijective _) _ _ fun k ↦ rfl⟩

  letI n := Nat.find aux
  obtain ⟨x, i, one_eq⟩ : ∃ (x : Fin n → A) (i : Fin n → I), ∑ j : Fin n, i j * x j = 1 :=
    Nat.find_spec aux
  if n_eq : n = 0
  then
  let e : Fin n ≃ Fin 0 := Fin.castIso n_eq
  have one_eq := calc 1
    _ = _ := one_eq.symm
    _ = ∑ j : Fin 0, i (e.symm j) * x (e.symm j) :=
        Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ rfl)
    _ = 0 := by simp
  simp at one_eq
  else

  have ne_zero : ∀ j, x j ≠ 0 ∧ i j ≠ 0 := by
    by_contra! H
    obtain ⟨j, hj⟩ := H
    refine Nat.find_min aux (m := n - 1) (show n - 1 < n by omega) ?_ -- delete `j`-th

    let e : Fin n ≃ Option (Fin (n - 1)) :=
      (Fin.castIso <| by omega).toEquiv.trans (finSuccEquiv' (j.cast <| by omega))
    have one_eq := calc 1
      _ = _ := one_eq.symm
      _ = ∑ j : Option (Fin (n - 1)), i (e.symm j) * x (e.symm j) :=
          Fintype.sum_bijective e (Equiv.bijective _) _ _ (fun _ ↦ rfl)

    simp only [Equiv.symm_trans_apply, OrderIso.toEquiv_symm, Fin.symm_castIso,
      RelIso.coe_fn_toEquiv, Fin.castIso_apply, Fintype.sum_option, finSuccEquiv'_symm_none,
      Fin.cast_trans, Fin.cast_eq_self, finSuccEquiv'_symm_some, e] at one_eq
    if xj_eq : x j = 0
    then
    rw [xj_eq, mul_zero, zero_add] at one_eq
    exact ⟨_, _, one_eq.symm⟩
    else
    rw [hj xj_eq, Submodule.coe_zero, zero_mul, zero_add] at one_eq
    exact ⟨_, _, one_eq.symm⟩

  refine ⟨n, Module.End A I, Module.End.divisionRing, ?_⟩
  sorry

end simple_ring
