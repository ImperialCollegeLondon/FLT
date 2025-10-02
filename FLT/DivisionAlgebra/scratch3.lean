import FLT.HaarMeasure.HaarChar.Ring
import Mathlib

variable (R : Type*) [Ring R] [Nontrivial R] [Algebra ℝ R] [Module.Finite ℝ R] [Module.Free ℝ R]
  [TopologicalSpace R] [IsModuleTopology ℝ R]

def basis_non_zero_in_one (B : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R) :
  ∃ i, B.coord i 1 ≠ 0 := by
  by_contra t
  simp only [Module.Basis.coord_apply, ne_eq, not_exists, Decidable.not_not] at t
  have w (a b : R) : (∀ x, (B.coord x) a = (B.coord x) b) →
      (a = b) := (Module.Basis.ext_elem_iff B).mpr
  specialize w 1 0
  have (x : Fin (Module.finrank ℝ R)) : (B.coord x) 1 =
      (B.coord x) 0 := by
    simpa using t x
  apply w at this
  contrapose this
  exact one_ne_zero

noncomputable
def basis_map :
    Module.Basis (Fin (Module.finrank ℝ R)) ℝ R → (Fin (Module.finrank ℝ R) → R) :=
  fun B i =>
    if i = Classical.choose (basis_non_zero_in_one R B)
    then B i - (∑ x, B x - 1)
    else B i

lemma basis_map_spans (B : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R) :
    ⊤ ≤ Submodule.span ℝ (Set.range (basis_map R B)) := by
  obtain ⟨a, ha⟩ : ∃ a, Classical.choose (basis_non_zero_in_one R B) = a := by
    exact exists_eq'
  suffices h : B a ∈ Submodule.span ℝ (Set.range (basis_map R B)) by
    have (i : Fin (Module.finrank ℝ R)) : B i ∈ Submodule.span ℝ (Set.range (basis_map R B)) := by
      rcases (eq_or_ne i a) with h | h
      · aesop
      · refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ?_
        use (fun j => if j = i then 1 else 0)
        simp_rw [basis_map, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
          reduceIte]
        aesop
    simp only [← Module.Basis.span_eq B]
    refine Submodule.span_le.mpr ?_
    intro x hx
    aesop
  refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ?_
  simp_rw [basis_map, ha, smul_ite]
  have h : {a} ∪ ({i | i ≠ a} : (Finset (Fin (Module.finrank ℝ R)))) =
      Set.univ (α := (Fin (Module.finrank ℝ R))) := by
    ext i
    simpa using eq_or_ne i a
  simp_rw [← Set.toFinset_univ, ← h]
  simp only [ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ,
    true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter, not_true_eq_false,
    and_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte]
  have s (c : Fin (Module.finrank ℝ R) → ℝ) : ∑ x with ¬x = a, c x • B x =
      ∑ x with ¬x = a, if x = a then c x • (B x - (B a +
      ∑ x with ¬x = a, B x - 1)) else c x • B x :=
    Finset.sum_congr rfl (by aesop)
  -- probably should take these two haves (h,s) out as private theorems
  simp_rw [← s]
  have : (B a - (B a + ∑ x with ¬x = a, B x - 1)) = 1 - ∑ x with ¬x = a, B x := by grind
  rw [this, ← (Module.Basis.sum_equivFun B 1), Module.Basis.equivFun_apply]
  simp_rw [sub_eq_add_neg, smul_add, smul_neg, Finset.smul_sum, ← sub_eq_add_neg, ← mul_smul]
  nth_rw 1 [← Set.toFinset_univ]
  simp only [←h, ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter,
    not_true_eq_false, and_false, not_false_eq_true, Finset.sum_insert]
  simp_rw [sub_eq_add_neg, add_assoc, neg_add_eq_sub]
  use (fun i => if i = a then (1 : ℝ) / (B.repr 1 a)
                  else - ((B.repr 1 i) / (B.repr 1 a)) + ((1 : ℝ) / (B.repr 1 a)))
  simp only [↓reduceIte, one_div]
  have : (∑ x with ¬x = a, (if x = a then ((B.repr 1) a)⁻¹
      else -((B.repr 1) x / (B.repr 1) a) + ((B.repr 1) a)⁻¹) • B x) =
      (∑ x with ¬x = a, (-((B.repr 1) x / (B.repr 1) a) + ((B.repr 1) a)⁻¹) • B x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have : x ≠ a := by
      simpa using hx
    simp only [this, reduceIte]
  rw [this]
  simp_rw [Eq.symm (Finset.sum_sub_distrib _ _)]
  simp_rw [Eq.symm (@Finset.sum_add_distrib _ _ _ _ _ _)] -- not sure why it needs the @?
  have : ((B.repr 1) a) ≠ 0 := by
    simpa [← ha, ← Module.Basis.coord_apply] using Classical.choose_spec (basis_non_zero_in_one R B)
  simp only [ne_eq, this, not_false_eq_true, inv_mul_cancel₀, one_smul, add_eq_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp_rw [← sub_smul, ← add_smul]
  ring_nf
  exact zero_smul ℝ (B i)

lemma basis_map_independent (B : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R) :
    LinearIndependent ℝ (basis_map R B) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact basis_map_spans R B
  · exact Fintype.card_fin (Module.finrank ℝ R)

noncomputable
def basis_map_is_basis (a : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R) :
    Module.Basis (Fin (Module.finrank ℝ R)) ℝ R :=
  Module.Basis.mk (v := basis_map R a) (basis_map_independent R a) (basis_map_spans R a)

lemma basis_existance :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ R)) ℝ R, ∑ x, b x = 1 := by
  use basis_map_is_basis R (Module.finBasis ℝ R)
  obtain ⟨a, ha⟩ : ∃ a, Classical.choose (basis_non_zero_in_one R (Module.finBasis ℝ R)) = a := by
    exact exists_eq'
  have h : {a} ∪ ({i | i ≠ a} : (Finset (Fin (Module.finrank ℝ R)))) =
      Set.univ (α := (Fin (Module.finrank ℝ R))) := by
    ext i
    simpa using eq_or_ne i a
  simp_rw [basis_map_is_basis, Module.Basis.coe_mk, ← Set.toFinset_univ, ← h]
  simp only [ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ,
    true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter, not_true_eq_false,
    and_false, not_false_eq_true, Finset.sum_insert, basis_map, ha, reduceIte]
  nth_rw 1 [← Set.toFinset_univ]
  simp only [← h, ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter,
    not_true_eq_false, and_false, not_false_eq_true, Finset.sum_insert]
  have r : (Module.finBasis ℝ R) a - ((Module.finBasis ℝ R) a +
      ∑ x with ¬x = a, (Module.finBasis ℝ R) x - 1) =
      1 - ∑ x with ¬x = a, (Module.finBasis ℝ R) x := by grind
  have s : ∑ x with ¬x = a, (Module.finBasis ℝ R) x = ∑ x with ¬x = a,
      if x = a then (Module.finBasis ℝ R) x - (∑ x, (Module.finBasis ℝ R) x - 1)
      else (Module.finBasis ℝ R) x := Finset.sum_congr rfl (by aesop)
  simp_rw [r, s, sub_add_cancel] -- this proof is horrible

noncomputable
abbrev iso : R ≃ₗ[ℝ] (Fin (Module.finrank ℝ R) → ℝ) := by
  exact Module.Basis.equivFun
    (ι := Fin (Module.finrank ℝ R)) (R := ℝ) (M := R) (Classical.choose (basis_existance R))

noncomputable
abbrev iso' : R ≃ₜ+ (Fin (Module.finrank ℝ R) → ℝ) where
  toFun := iso R
  invFun := (iso R).symm
  map_add' _ _ := LinearEquiv.map_add _ _ _
  left_inv _ := LinearEquiv.symm_apply_apply _ _
  right_inv _ := LinearEquiv.apply_symm_apply _ _
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals try infer_instance
    exact IsModuleTopology.toContinuousAdd ℝ R

variable [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

lemma ringHaarChar_eq1' (y : (Fin (Module.finrank ℝ R) → ℝ)ˣ)
    (hy : ∃ a : ℝ, y.val = algebraMap ℝ (Fin (Module.finrank ℝ R) → ℝ) a)
    (hy' : IsUnit ((iso R).symm y)) :
    MeasureTheory.ringHaarChar y = MeasureTheory.ringHaarChar (IsUnit.unit hy') := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (iso' R).symm
  intro x
  obtain ⟨a, ha⟩ := hy
  have h1 : (iso' R).symm x = ∑ j, x j • (Classical.choose (basis_existance R)) j :=
    Module.Basis.equivFun_symm_apply _ _
    -- need to fix imports, as this should just be immediate
  have h2 : (iso' R).symm (↑y * x) =
      ∑ j, (↑y * x) j • (Classical.choose (basis_existance R)) j :=
    Module.Basis.equivFun_symm_apply _ _
  have : a • (∑ x, (Classical.choose (basis_existance R)) x) =
      (∑ x, a • (Classical.choose (basis_existance R)) x) := Finset.smul_sum
  simp_rw [ContinuousAddEquiv.mulLeft_apply, IsUnit.unit_spec, h1, h2,
    Module.Basis.equivFun_symm_apply, ha, Pi.mul_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← this, Algebra.smul_mul_assoc,
    Classical.choose_spec (basis_existance R), one_mul, Finset.smul_sum, ← IsScalarTower.smul_assoc,
    smul_eq_mul] -- I perhaps could have oversqueezed this lemma
