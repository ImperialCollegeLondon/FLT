import Mathlib
import FLT.HaarMeasure.HaarChar.Ring

section basics

variable {T R : Type*} [Ring R] [Nontrivial R]

lemma ex_ne_zero_coeff_one [Semiring T] [Module T R]
    (B : Module.Basis (Fin (Module.finrank T R)) T R) : ∃ i, B.coord i 1 ≠ 0 := by
  by_contra t
  simp only [Module.Basis.coord_apply, ne_eq, not_exists] at t
  have w (a b : R) : (∀ x, (B.coord x) a = (B.coord x) b) →
      (a = b) := (Module.Basis.ext_elem_iff B).mpr
  specialize w 1 0
  have (x : Fin (Module.finrank T R)) : (B.coord x) 1 =
      (B.coord x) 0 := by
    simpa using t x
  apply w at this
  contrapose this
  exact one_ne_zero

/-- The basis change map mapping `B i ↦ B i - (∑ x, B x - 1)` where `i` is from
  `ex_ne_zero_coeff_one`. -/
noncomputable
def basis_change_map [Semiring T] [Module T R] :
    Module.Basis (Fin (Module.finrank T R)) T R → (Fin (Module.finrank T R) → R) :=
  fun B i =>
    if i = Classical.choose (ex_ne_zero_coeff_one B)
    then B i - (∑ x, B x - 1)
    else B i

section Module

variable [Field T] [Module T R]

lemma basis_change_map_spans
    (B : Module.Basis (Fin (Module.finrank T R)) T R) :
    ⊤ ≤ Submodule.span T (Set.range (basis_change_map B)) := by
  obtain ⟨a, ha⟩ : ∃ a, Classical.choose (ex_ne_zero_coeff_one B) = a := by
    exact exists_eq'
  suffices h : B a ∈ Submodule.span T (Set.range (basis_change_map B)) by
    have (i : Fin (Module.finrank T R)) :
        B i ∈ Submodule.span T (Set.range (basis_change_map B)) := by
      rcases (eq_or_ne i a) with h | h
      · aesop
      · refine (Submodule.mem_span_range_iff_exists_fun T).mpr ?_
        use (fun j => if j = i then 1 else 0)
        simp_rw [basis_change_map, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, reduceIte]
        aesop
    simp only [← Module.Basis.span_eq B]
    refine Submodule.span_le.mpr ?_
    intro x hx
    aesop
  refine (Submodule.mem_span_range_iff_exists_fun T).mpr ?_
  simp_rw [basis_change_map, ha, smul_ite]
  have h : {a} ∪ ({i | i ≠ a} : (Finset (Fin (Module.finrank T R)))) =
      Set.univ (α := (Fin (Module.finrank T R))) := by
    ext i
    simpa using eq_or_ne i a
  simp_rw [← Set.toFinset_univ, ← h]
  simp only [ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ,
    true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter, not_true_eq_false,
    and_false, not_false_eq_true, Finset.sum_insert, ↓reduceIte]
  have s (c : Fin (Module.finrank T R) → T) : ∑ x with ¬x = a, c x • B x =
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
  use (fun i => if i = a then (1 : T) / (B.repr 1 a)
                  else - ((B.repr 1 i) / (B.repr 1 a)) + ((1 : T) / (B.repr 1 a)))
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
  simp_rw [Eq.symm (@Finset.sum_add_distrib _ _ _ _ _ _)]
  have : ((B.repr 1) a) ≠ 0 := by
    simpa [← ha, ← Module.Basis.coord_apply] using Classical.choose_spec (ex_ne_zero_coeff_one B)
  simp only [ne_eq, this, not_false_eq_true, inv_mul_cancel₀, one_smul, add_eq_left]
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp_rw [← sub_smul, ← add_smul]
  ring_nf
  exact zero_smul T (B i)

lemma basis_change_map_lin_independent (B : Module.Basis (Fin (Module.finrank T R)) T R) :
    LinearIndependent T (basis_change_map B) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact basis_change_map_spans B
  · exact Fintype.card_fin (Module.finrank T R)

/-- For any basis `a`, `basis_change_map a` is a basis. -/
noncomputable
def basis_change_map_is_basis (a : Module.Basis (Fin (Module.finrank T R)) T R) :
    Module.Basis (Fin (Module.finrank T R)) T R :=
  Module.Basis.mk (v := basis_change_map a) (basis_change_map_lin_independent a)
    (basis_change_map_spans a)

variable [Module.Finite T R]

-- This could probably go in Mathlib.LinearAlgebra.Basic; or create a new file?
lemma ex_basis_sum_basis_eq_one :
    ∃ b : Module.Basis (Fin (Module.finrank T R)) T R, ∑ x, b x = 1 := by
  use basis_change_map_is_basis (Module.finBasis T R)
  obtain ⟨a, ha⟩ : ∃ a, Classical.choose (ex_ne_zero_coeff_one (Module.finBasis T R)) = a := by
    exact exists_eq'
  have h : {a} ∪ ({i | i ≠ a} : (Finset (Fin (Module.finrank T R)))) =
      Set.univ (α := (Fin (Module.finrank T R))) := by
    ext i
    simpa using eq_or_ne i a
  simp_rw [basis_change_map_is_basis, Module.Basis.coe_mk, ← Set.toFinset_univ, ← h]
  simp only [ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter, Finset.mem_univ,
    true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter, not_true_eq_false,
    and_false, not_false_eq_true, Finset.sum_insert, basis_change_map, ha, reduceIte]
  nth_rw 1 [← Set.toFinset_univ]
  simp only [← h, ne_eq, Finset.singleton_union, Finset.coe_insert, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.toFinset_insert, Set.toFinset_setOf, Finset.mem_filter,
    not_true_eq_false, and_false, not_false_eq_true, Finset.sum_insert]
  have r : (Module.finBasis T R) a - ((Module.finBasis T R) a +
      ∑ x with ¬x = a, (Module.finBasis T R) x - 1) =
      1 - ∑ x with ¬x = a, (Module.finBasis T R) x := by grind
  have s : ∑ x with ¬x = a, (Module.finBasis T R) x = ∑ x with ¬x = a,
      if x = a then (Module.finBasis T R) x - (∑ x, (Module.finBasis T R) x - 1)
      else (Module.finBasis T R) x := Finset.sum_congr rfl (by aesop)
  simp_rw [r, s, sub_add_cancel] -- this proof is horrible


/-
I need to break the file here.
iso should go in FLT.Mathlib.Topology.Module.ModuleTopology
ringHaarChar_eq should go in the HaarMeasure files somewhere
  maybe make a new file where I can also include the results of ℝ → ℝ^d.
-/

variable [TopologicalSpace T] [TopologicalSpace R] [IsModuleTopology T R] [IsTopologicalRing T]

/-- The topological equivalence of `R` and `ℝ^(dim ℝ R)` as additive groups. -/
noncomputable
abbrev iso (b : Module.Basis (Fin (Module.finrank T R)) T R) :
    R ≃ₜ+ (Fin (Module.finrank T R) → T) where
  toFun := Module.Basis.equivFun b
  invFun := (Module.Basis.equivFun _).symm
  map_add' _ _ := LinearEquiv.map_add _ _ _
  left_inv _ := LinearEquiv.symm_apply_apply _ _
  right_inv _ := LinearEquiv.apply_symm_apply _ _
  continuous_toFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals infer_instance
  continuous_invFun := by
    convert IsModuleTopology.continuous_of_linearMap _
    all_goals try infer_instance
    · exact IsModuleTopology.toContinuousAdd T R

end Module

section Algebra

variable [Field T] [Algebra T R] [Module.Finite T R] [TopologicalSpace T] [TopologicalSpace R]
  [IsModuleTopology T R] [IsTopologicalRing T] [IsTopologicalRing R] [LocallyCompactSpace T]
  [LocallyCompactSpace R]

-- I now need Algebra and not module to get that smul is associative... maybe there is a nicer way
-- to show this rather than changing assumption to algebra...
-- maybe [IsScalarTower T R R]?

local instance : MeasurableSpace R := by
  exact borel R -- I can probably use the Borelize tactic but not sure how it works.

local instance : BorelSpace R := by
  exact { measurable_eq := rfl }

instance : MeasurableSpace (Fin (Module.finrank T R) → T) := by
  exact borel (Fin (Module.finrank T R) → T)

instance : BorelSpace (Fin (Module.finrank T R) → T) := by
  exact { measurable_eq := rfl }

lemma ringHaarChar_eq (y : (Fin (Module.finrank T R) → T)ˣ)
    (hy : ∃ a : T, y.val = algebraMap T (Fin (Module.finrank T R) → T) a)
    (hy' : IsUnit ((Module.Basis.equivFun
      (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R)))).symm y)) :
    MeasureTheory.ringHaarChar y = MeasureTheory.ringHaarChar (R := R) (IsUnit.unit hy') := by
  apply MeasureTheory.addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    (iso (Classical.choose (ex_basis_sum_basis_eq_one))).symm
  intro x
  obtain ⟨a, ha⟩ := hy
  have h1 : (iso (Classical.choose (ex_basis_sum_basis_eq_one))).symm x =
      ∑ j, x j • (Classical.choose (ex_basis_sum_basis_eq_one)) j :=
    Module.Basis.equivFun_symm_apply _ _
  have h2 : (iso (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R)))).symm (↑y * x) =
      ∑ j, (↑y * x) j • (Classical.choose (ex_basis_sum_basis_eq_one)) j :=
    Module.Basis.equivFun_symm_apply _ _
  have : a • (∑ x, (Classical.choose (ex_basis_sum_basis_eq_one)) x) =
      (∑ x, a • (Classical.choose (ex_basis_sum_basis_eq_one (T := T))) x) :=
    Finset.smul_sum (N := R)
  simp_rw [ContinuousAddEquiv.mulLeft_apply, IsUnit.unit_spec, h1, h2,
    Module.Basis.equivFun_symm_apply, ha, Pi.mul_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← this]
  simp_rw [smul_mul_assoc, Classical.choose_spec (ex_basis_sum_basis_eq_one),
    one_mul, Finset.smul_sum, ← IsScalarTower.smul_assoc, smul_eq_mul]

theorem foo (t : Tˣ) : MeasureTheory.ringHaarChar (Units.map (algebraMap T R).toMonoidHom t) =
    (MeasureTheory.ringHaarChar t) ^ (Module.finrank T R) := by
  let t' := (MulEquiv.piUnits (ι := Fin (Module.finrank T R)) (M := fun _ => T)).symm
    (fun (i : Fin (Module.finrank T R)) => t)
  have h : IsUnit ((Module.Basis.equivFun
      (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R)))).symm t') := by
    simp only [Module.Basis.equivFun_symm_apply]
    refine isUnit_iff_exists.mpr ?_
    let t'inv := (MulEquiv.piUnits (ι := Fin (Module.finrank T R)) (M := fun _ => T)).symm
      (fun (i : Fin (Module.finrank T R)) => t⁻¹)
    use ((Module.Basis.equivFun
      (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R)))).symm t'inv)
    simp only [Module.Basis.equivFun_symm_apply]
    simp_rw [Algebra.smul_def]
    have : ∑ i, (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R))) i = 1 := by
        exact Classical.choose_spec (ex_basis_sum_basis_eq_one (T := T) (R := R))

    sorry
  have hmm1 := ringHaarChar_eq (T := T) (R := R) t' ⟨t.val, rfl⟩ h
  have hmm2 : MeasureTheory.ringHaarChar h.unit =
      MeasureTheory.ringHaarChar (Units.map (algebraMap T R).toMonoidHom t) := by
    have : h.unit = (Units.map (algebraMap T R).toMonoidHom t) := by
      ext
      simp only [Module.Basis.equivFun_symm_apply, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
        Units.coe_map, MonoidHom.coe_coe]
      unfold t'
      simp only [MulEquiv.val_piUnits_symm_apply]
      have (x : Fin (Module.finrank T R)) :
          t.val • (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R))) x =
          (algebraMap T R) t.val * Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R)) x
          := by
        exact Algebra.smul_def (R := T) (A := R) _ _
      simp_rw [this]
      rw [← @Finset.mul_sum]
      have : ∑ i, (Classical.choose (ex_basis_sum_basis_eq_one (T := T) (R := R))) i = 1 := by
        exact Classical.choose_spec (ex_basis_sum_basis_eq_one (T := T) (R := R))
      simp [this]
    simp_rw [this]
  rw [hmm2] at hmm1
  rw [← hmm1]
  unfold t'
  have : MeasureTheory.ringHaarChar (MulEquiv.piUnits.symm (fun (i : Fin (Module.finrank T R)) ↦ t))
       = ∏ (i : Fin (Module.finrank T R)), MeasureTheory.ringHaarChar ((fun i ↦ t) i) := by
    have := MeasureTheory.ringHaarChar_pi (ι := Fin (Module.finrank T R))
      (A := fun _ : Fin (Module.finrank T R) => T) (fun (i : Fin (Module.finrank T R)) ↦ t)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this ⊢
    exact this
  simp_rw [this]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Algebra

end basics
