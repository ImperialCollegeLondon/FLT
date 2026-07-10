/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.FiveTerm
public import Mathlib.Algebra.DirectSum.Module

/-!
# The two spectral sequences of a double complex

A double complex `A^{i,j}` (first-quadrant, i.e. trivial for `i < 0` or `j < 0`)
has a total complex `Tot^n = ⨁_i A^{i, n-i}` carrying two filtrations — by
columns (`colF`) and by rows (`rowF`) — each of which is bounded *at every
degree* even though it is globally unbounded.  Feeding these into the graded
convergence theorem of `FLT.Slop.SpectralSequence.FilteredComplex` produces the
two classical spectral sequences, both converging to the associated graded of
the cohomology `H^n(Tot)` of the same total complex (for the respective
filtrations).  This is the first result of Vakil, *The Rising Sea*, §1.7.

## Main definitions

* `DoubleComplex` : a double complex of modules, with all-pairs differentials
  (only the consecutive components are meaningful) and anticommuting `dh`, `dv`.
* `DoubleComplex.Tot`, `DoubleComplex.totalD` : the total complex and its total
  differential.
* `DoubleComplex.colF`, `DoubleComplex.rowF` and `DoubleComplex.colFiltered`,
  `DoubleComplex.rowFiltered` : the column/row filtrations and the two filtered
  complexes they define on the total complex.

## Main results

* `DoubleComplex.colPageZeroEquiv`, `DoubleComplex.rowPageZeroEquiv` : the
  zeroth pages of both spectral sequences are the double complex itself.
* `DoubleComplex.colPageOneEquiv`, `DoubleComplex.rowPageOneEquiv` :
  `ᴵE₁ ≅ ker(dv)/im(dv)` and `ᴵᴵE₁ ≅ ker(dh)/im(dh)` — the first pages are the
  vertical/horizontal cohomology (FOAG §1.7), built via the reusable
  `homologyEquivOfSquares`.
* `DoubleComplex.colPageEquivGrH`, `DoubleComplex.rowPageEquivGrH` :
  **convergence** — for a first-quadrant double complex both spectral sequences
  converge to the associated graded of `H^n(Tot)`.
* `DoubleComplex.colFiltered_five_term_exact`,
  `DoubleComplex.rowFiltered_five_term_exact` : the five-term exact sequences
  `0 → E_2^{1,0} → H¹(Tot) → E_2^{0,1} →^{d₂} E_2^{2,0} → H²(Tot)` of the two
  spectral sequences.
-/

@[expose] public section

open Submodule LinearMap DirectSum

/-- A **double complex** of modules, with all-pairs differentials: only the
components `dh i (i+1) j j` (horizontal) and `dv i i j (j+1)` (vertical) are
meaningful; the flexible index slots avoid dependent-type transport when forming
the total complex.  The differentials anticommute, so the total differential
squares to zero on the nose. -/
structure DoubleComplex (R : Type*) [Ring R] where
  /-- The modules. -/
  A : ℤ → ℤ → Type*
  [addCommGroup : ∀ i j, AddCommGroup (A i j)]
  [module : ∀ i j, Module R (A i j)]
  /-- The horizontal differential; only `dh i (i+1) j j` is meaningful. -/
  dh : ∀ i i' j j' : ℤ, A i j →ₗ[R] A i' j'
  /-- The vertical differential; only `dv i i j (j+1)` is meaningful. -/
  dv : ∀ i i' j j' : ℤ, A i j →ₗ[R] A i' j'
  /-- The horizontal differential squares to zero. -/
  dh_dh : ∀ (i i' i'' j j' j'' : ℤ), i' = i + 1 → i'' = i' + 1 → j' = j → j'' = j →
    ∀ x : A i j, dh i' i'' j' j'' (dh i i' j j' x) = 0
  /-- The vertical differential squares to zero. -/
  dv_dv : ∀ (i j j' j'' : ℤ), j' = j + 1 → j'' = j' + 1 →
    ∀ x : A i j, dv i i j' j'' (dv i i j j' x) = 0
  /-- The horizontal and vertical differentials anticommute. -/
  anticomm : ∀ (i i' j jh jv jt : ℤ), i' = i + 1 → jh = j → jv = j + 1 → jt = j + 1 →
    ∀ x : A i j, dv i' i' jh jt (dh i i' j jh x) + dh i i' jv jt (dv i i j jv x) = 0

attribute [instance] DoubleComplex.addCommGroup DoubleComplex.module

namespace DoubleComplex

variable {R : Type*} [Ring R] (K : DoubleComplex R)

/-- The total module `Tot^n = ⊕_i A^{i, n-i}`. -/
abbrev Tot (n : ℤ) := ⨁ i : ℤ, K.A i (n - i)

/-- The total differential `dh + dv` (meaningful for `m = n + 1`). -/
noncomputable def totalD (n m : ℤ) : K.Tot n →ₗ[R] K.Tot m :=
  DirectSum.toModule R ℤ _ fun i ↦
    (DirectSum.lof R ℤ (fun i' ↦ K.A i' (m - i')) (i + 1)).comp
      (K.dh i (i + 1) (n - i) (m - (i + 1)))
    + (DirectSum.lof R ℤ (fun i' ↦ K.A i' (m - i')) i).comp (K.dv i i (n - i) (m - i))

@[simp] lemma totalD_lof (n m i : ℤ) (x : K.A i (n - i)) :
    K.totalD n m (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) i x)
      = DirectSum.lof R ℤ (fun i' ↦ K.A i' (m - i')) (i + 1)
          (K.dh i (i + 1) (n - i) (m - (i + 1)) x)
        + DirectSum.lof R ℤ (fun i' ↦ K.A i' (m - i')) i (K.dv i i (n - i) (m - i) x) := by
  simp [totalD]

lemma totalD_totalD (n m t : ℤ) (hm : m = n + 1) (ht : t = m + 1) (x : K.Tot n) :
    K.totalD m t (K.totalD n m x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i a =>
    rw [← DirectSum.lof_eq_of R, totalD_lof, map_add, totalD_lof, totalD_lof]
    rw [K.dh_dh i (i + 1) (i + 1 + 1) (n - i) (m - (i + 1)) (t - (i + 1 + 1)) rfl rfl
      (by omega) (by omega) a]
    rw [K.dv_dv i (n - i) (m - i) (t - i) (by omega) (by omega) a]
    rw [map_zero, map_zero, zero_add, add_zero, ← map_add]
    rw [K.anticomm i (i + 1) (n - i) (m - (i + 1)) (m - i) (t - (i + 1)) rfl (by omega)
      (by omega) (by omega) a]
    rw [map_zero]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, add_zero]

/-- The **column filtration** `F_I^p Tot^n = ⊕_{i ≥ p} A^{i, n-i}`. -/
def colF (p n : ℤ) : Submodule R (K.Tot n) :=
  ⨆ (i : ℤ) (_ : p ≤ i), LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) i)

/-- The **row filtration** `F_II^p Tot^n = ⊕_{n-i ≥ p} A^{i, n-i}`. -/
def rowF (p n : ℤ) : Submodule R (K.Tot n) :=
  ⨆ (i : ℤ) (_ : p ≤ n - i),
    LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) i)

lemma totalD_mem_colF (p n m : ℤ) {x : K.Tot n} (hx : x ∈ K.colF p n) :
    K.totalD n m x ∈ K.colF p m := by
  have hmap : (K.colF p n).map (K.totalD n m) ≤ K.colF p m := by
    rw [colF, Submodule.map_iSup]
    refine iSup_le fun i ↦ ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hi ↦ ?_
    rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
    rw [totalD_lof]
    refine add_mem ?_ ?_
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (m - i'')) i'))
        (i + 1) (by omega) ⟨_, rfl⟩
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (m - i'')) i'))
        i hi ⟨_, rfl⟩
  exact hmap (Submodule.mem_map_of_mem hx)

lemma totalD_mem_rowF (p n m : ℤ) (hm : m = n + 1) {x : K.Tot n} (hx : x ∈ K.rowF p n) :
    K.totalD n m x ∈ K.rowF p m := by
  have hmap : (K.rowF p n).map (K.totalD n m) ≤ K.rowF p m := by
    rw [rowF, Submodule.map_iSup]
    refine iSup_le fun i ↦ ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hi ↦ ?_
    rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
    rw [totalD_lof]
    refine add_mem ?_ ?_
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (m - i'')) i'))
        (i + 1) (by omega) ⟨_, rfl⟩
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (m - i'')) i'))
        i (by omega) ⟨_, rfl⟩
  exact hmap (Submodule.mem_map_of_mem hx)

/-- The filtered complex given by the column filtration on the total complex. -/
noncomputable def colFiltered : FilteredComplex R where
  X := K.Tot
  d := K.totalD
  d_comp_d := fun i j k hj hk x ↦ K.totalD_totalD i j k hj hk x
  F := K.colF
  F_le := fun p n ↦ by
    refine iSup₂_le fun i hi ↦ ?_
    exact le_iSup₂ (f := fun i' _ ↦
      LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i (by omega)
  d_mem_F := fun p i j _ x hx ↦ K.totalD_mem_colF p i j hx

/-- The filtered complex given by the row filtration on the total complex. -/
noncomputable def rowFiltered : FilteredComplex R where
  X := K.Tot
  d := K.totalD
  d_comp_d := fun i j k hj hk x ↦ K.totalD_totalD i j k hj hk x
  F := K.rowF
  F_le := fun p n ↦ by
    refine iSup₂_le fun i hi ↦ ?_
    exact le_iSup₂ (f := fun i' _ ↦
      LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i (by omega)
  d_mem_F := fun p i j hj x hx ↦ K.totalD_mem_rowF p i j hj hx

/-- The two filtered complexes share the underlying complex, hence they have the
same cohomology: both spectral sequences abut to `H^n(Tot)`. -/
lemma colFiltered_homology_eq_rowFiltered_homology (n : ℤ) :
    K.colFiltered.homology n = K.rowFiltered.homology n := rfl

/-! ### The zeroth pages: the double complex itself

The associated graded of the column filtration at `(p, n)` is the single entry
`A^{p, n-p}`, by the direct-sum decomposition; combined with `pageZeroEquiv` this
identifies the zeroth page of the first spectral sequence with the double complex
itself, and similarly for the row filtration. -/

section GradedPieces

lemma lof_injective (i n : ℤ) :
    Function.Injective (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) i) :=
  Function.LeftInverse.injective
    (g := DirectSum.component R ℤ (fun i' ↦ K.A i' (n - i')) i)
    fun b ↦ DirectSum.component.lof_self (R := R) (ι := ℤ)
      (M := fun i' ↦ K.A i' (n - i')) i b

lemma colF_eq_sup (p n : ℤ) :
    K.colF p n = LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) p)
      ⊔ K.colF (p + 1) n := by
  apply le_antisymm
  · refine iSup₂_le fun i hi ↦ ?_
    rcases eq_or_lt_of_le hi with rfl | h
    · exact le_sup_left
    · exact le_trans (le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i (by omega))
        le_sup_right
  · refine sup_le ?_ ?_
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) p le_rfl
    · refine iSup₂_le fun i hi ↦ ?_
      exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i (by omega)

lemma colF_le_ker_component (p n : ℤ) :
    K.colF (p + 1) n
      ≤ LinearMap.ker (DirectSum.component R ℤ (fun i' ↦ K.A i' (n - i')) p) := by
  refine iSup₂_le fun i hi ↦ ?_
  rintro x ⟨a, rfl⟩
  rw [LinearMap.mem_ker, DirectSum.component.of]
  rw [dif_neg (by omega : ¬ i = p)]

lemma comap_colF_eq_bot (p n : ℤ) :
    Submodule.comap
        (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) p)).subtype
        (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) p))
      ⊓ Submodule.comap
          (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) p)).subtype
          (K.colF (p + 1) n) = ⊥ := by
  refine le_bot_iff.mp fun x hx ↦ ?_
  obtain ⟨-, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' : (x : K.Tot n) ∈ K.colF (p + 1) n := hx2
  obtain ⟨a, ha⟩ := x.2
  have hcomp : DirectSum.component R ℤ (fun i' ↦ K.A i' (n - i')) p (x : K.Tot n) = 0 :=
    K.colF_le_ker_component p n hx2'
  rw [← ha, DirectSum.component.lof_self] at hcomp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  rw [← ha, hcomp, map_zero]
  rfl

/-- The associated graded piece of the column filtration is a single entry of the
double complex: `gr^p_I Tot^n ≅ A^{p, n-p}`. -/
noncomputable def colGrEquiv (p n : ℤ) :
    (↥(K.colF p n) ⧸ (K.colF (p + 1) n).comap (K.colF p n).subtype) ≃ₗ[R] K.A p (n - p) :=
  (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (K.colF_eq_sup p n)) (by
      ext ξ
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨η, hη, rfl⟩
        simpa using hη
      · intro hξ
        exact ⟨(LinearEquiv.ofEq _ _ (K.colF_eq_sup p n)).symm ξ, by simpa using hξ,
          (LinearEquiv.ofEq _ _ (K.colF_eq_sup p n)).apply_symm_apply ξ⟩)).trans
    (((LinearMap.quotientInfEquivSupQuotient _ _).symm.trans
      (Submodule.quotEquivOfEqBot _ (K.comap_colF_eq_bot p n))).trans
      (LinearEquiv.ofInjective _ (K.lof_injective p n)).symm)

/-- **The zeroth page of the first (column-filtered) spectral sequence of a double
complex is the double complex itself**: `ᴵE_0^{p,n} ≅ A^{p, n-p}`. -/
noncomputable def colPageZeroEquiv (p n : ℤ) :
    K.colFiltered.page 0 p n ≃ₗ[R] K.A p (n - p) :=
  (K.colFiltered.pageZeroEquiv p n).trans (K.colGrEquiv p n)

lemma rowF_eq_sup (p n : ℤ) :
    K.rowF p n = LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) (n - p))
      ⊔ K.rowF (p + 1) n := by
  apply le_antisymm
  · refine iSup₂_le fun i hi ↦ ?_
    by_cases h : p + 1 ≤ n - i
    · exact le_trans (le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i h)
        le_sup_right
    · have hip : i = n - p := by omega
      subst hip
      exact le_sup_left
  · refine sup_le ?_ ?_
    · exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) (n - p)
        (by omega)
    · refine iSup₂_le fun i hi ↦ ?_
      exact le_iSup₂ (f := fun i' _ ↦
        LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i (by omega)

lemma rowF_le_ker_component (p n : ℤ) :
    K.rowF (p + 1) n
      ≤ LinearMap.ker (DirectSum.component R ℤ (fun i' ↦ K.A i' (n - i')) (n - p)) := by
  refine iSup₂_le fun i hi ↦ ?_
  rintro x ⟨a, rfl⟩
  rw [LinearMap.mem_ker, DirectSum.component.of]
  rw [dif_neg (by omega : ¬ i = n - p)]

lemma comap_rowF_eq_bot (p n : ℤ) :
    Submodule.comap
        (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) (n - p))).subtype
        (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) (n - p)))
      ⊓ Submodule.comap
          (LinearMap.range (DirectSum.lof R ℤ (fun i' ↦ K.A i' (n - i')) (n - p))).subtype
          (K.rowF (p + 1) n) = ⊥ := by
  refine le_bot_iff.mp fun x hx ↦ ?_
  obtain ⟨-, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' : (x : K.Tot n) ∈ K.rowF (p + 1) n := hx2
  obtain ⟨a, ha⟩ := x.2
  have hcomp : DirectSum.component R ℤ (fun i' ↦ K.A i' (n - i')) (n - p) (x : K.Tot n) = 0 :=
    K.rowF_le_ker_component p n hx2'
  rw [← ha, DirectSum.component.lof_self] at hcomp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  rw [← ha, hcomp, map_zero]
  rfl

/-- The associated graded piece of the row filtration is a single entry of the
double complex. -/
noncomputable def rowGrEquiv (p n : ℤ) :
    (↥(K.rowF p n) ⧸ (K.rowF (p + 1) n).comap (K.rowF p n).subtype)
      ≃ₗ[R] K.A (n - p) (n - (n - p)) :=
  (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (K.rowF_eq_sup p n)) (by
      ext ξ
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨η, hη, rfl⟩
        simpa using hη
      · intro hξ
        exact ⟨(LinearEquiv.ofEq _ _ (K.rowF_eq_sup p n)).symm ξ, by simpa using hξ,
          (LinearEquiv.ofEq _ _ (K.rowF_eq_sup p n)).apply_symm_apply ξ⟩)).trans
    (((LinearMap.quotientInfEquivSupQuotient _ _).symm.trans
      (Submodule.quotEquivOfEqBot _ (K.comap_rowF_eq_bot p n))).trans
      (LinearEquiv.ofInjective _ (K.lof_injective (n - p) n)).symm)

/-- **The zeroth page of the second (row-filtered) spectral sequence of a double
complex is the double complex itself**: `ᴵᴵE_0^{p,n} ≅ A^{n-p, p}` (the second
index appears as `n - (n - p)`). -/
noncomputable def rowPageZeroEquiv (p n : ℤ) :
    K.rowFiltered.page 0 p n ≃ₗ[R] K.A (n - p) (n - (n - p)) :=
  (K.rowFiltered.pageZeroEquiv p n).trans (K.rowGrEquiv p n)

end GradedPieces

/-! ### First-quadrant boundedness -/

section FirstQuadrant

variable (hfq : ∀ i j : ℤ, i < 0 ∨ j < 0 → Subsingleton (K.A i j))

include hfq

lemma colF_eq_bot {p n : ℤ} (hp : n < p) : K.colF p n = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun i hi ↦ ?_)
  rintro y ⟨a, rfl⟩
  haveI := hfq i (n - i) (Or.inr (by omega))
  rw [Subsingleton.elim a 0, map_zero]
  exact zero_mem _

lemma colF_eq_top {p n : ℤ} (hp : p ≤ 0) : K.colF p n = ⊤ := by
  have key : ∀ x : K.Tot n, x ∈ K.colF p n := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of i a =>
      by_cases h : p ≤ i
      · refine le_iSup₂ (f := fun i' _ ↦
          LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i h ?_
        rw [← DirectSum.lof_eq_of R]
        exact ⟨a, rfl⟩
      · haveI := hfq i (n - i) (Or.inl (by omega))
        rw [Subsingleton.elim a 0, map_zero]
        exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
  exact top_le_iff.mp fun x _ ↦ key x

lemma rowF_eq_bot {p n : ℤ} (hp : n < p) : K.rowF p n = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun i hi ↦ ?_)
  rintro y ⟨a, rfl⟩
  haveI := hfq i (n - i) (Or.inl (by omega))
  rw [Subsingleton.elim a 0, map_zero]
  exact zero_mem _

lemma rowF_eq_top {p n : ℤ} (hp : p ≤ 0) : K.rowF p n = ⊤ := by
  have key : ∀ x : K.Tot n, x ∈ K.rowF p n := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact zero_mem _
    | of i a =>
      by_cases h : p ≤ n - i
      · refine le_iSup₂ (f := fun i' _ ↦
          LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (n - i'')) i')) i h ?_
        rw [← DirectSum.lof_eq_of R]
        exact ⟨a, rfl⟩
      · haveI := hfq i (n - i) (Or.inr (by omega))
        rw [Subsingleton.elim a 0, map_zero]
        exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
  exact top_le_iff.mp fun x _ ↦ key x

/-- **The first spectral sequence of a first-quadrant double complex converges**:
once `r` passes the (spot-dependent) bounds, the page `ᴵE_r^{p,n}` is the
associated graded, for the column filtration, of `H^n(Tot)`. -/
noncomputable def colPageEquivGrH {r p n : ℤ} (hr1 : n + 1 < p + r) (hr2 : p - r + 1 ≤ 0) :
    K.colFiltered.page r p n ≃ₗ[R]
      (↥(K.colFiltered.FH p n) ⧸
        (K.colFiltered.FH (p + 1) n).comap (K.colFiltered.FH p n).subtype) :=
  K.colFiltered.pageEquivGrHOfBounded (K.colF_eq_bot hfq hr1) (K.colF_eq_top hfq hr2)

/-- **The second spectral sequence of a first-quadrant double complex converges**:
once `r` passes the (spot-dependent) bounds, the page `ᴵᴵE_r^{p,n}` is the
associated graded, for the row filtration, of the *same* `H^n(Tot)`. -/
noncomputable def rowPageEquivGrH {r p n : ℤ} (hr1 : n + 1 < p + r) (hr2 : p - r + 1 ≤ 0) :
    K.rowFiltered.page r p n ≃ₗ[R]
      (↥(K.rowFiltered.FH p n) ⧸
        (K.rowFiltered.FH (p + 1) n).comap (K.rowFiltered.FH p n).subtype) :=
  K.rowFiltered.pageEquivGrHOfBounded (K.rowF_eq_bot hfq hr1) (K.rowF_eq_top hfq hr2)

/-- The column filtration of a first-quadrant double complex is `FirstQuadrant`. -/
theorem colFiltered_firstQuadrant : K.colFiltered.FirstQuadrant :=
  ⟨fun h ↦ K.colF_eq_bot hfq h, fun h ↦ K.colF_eq_top hfq h⟩

/-- The row filtration of a first-quadrant double complex is `FirstQuadrant`. -/
theorem rowFiltered_firstQuadrant : K.rowFiltered.FirstQuadrant :=
  ⟨fun h ↦ K.rowF_eq_bot hfq h, fun h ↦ K.rowF_eq_top hfq h⟩

/-- **Five-term exact sequence of the first (column) spectral sequence** of a
first-quadrant double complex:
`0 → ᴵE_2^{1,0} → H¹(Tot) → ᴵE_2^{0,1} →^{d₂} ᴵE_2^{2,0} → H²(Tot)`. -/
theorem colFiltered_five_term_exact :
    Function.Injective (FilteredComplex.f1 (K.colFiltered_firstQuadrant hfq)) ∧
    Function.Exact (FilteredComplex.f1 (K.colFiltered_firstQuadrant hfq))
      (FilteredComplex.f2 (K.colFiltered_firstQuadrant hfq)) ∧
    Function.Exact (FilteredComplex.f2 (K.colFiltered_firstQuadrant hfq)) K.colFiltered.d2 ∧
    Function.Exact K.colFiltered.d2 (FilteredComplex.f4 (K.colFiltered_firstQuadrant hfq)) :=
  K.colFiltered.five_term_exact (K.colFiltered_firstQuadrant hfq)

/-- **Five-term exact sequence of the second (row) spectral sequence** of a
first-quadrant double complex:
`0 → ᴵᴵE_2^{1,0} → H¹(Tot) → ᴵᴵE_2^{0,1} →^{d₂} ᴵᴵE_2^{2,0} → H²(Tot)`. -/
theorem rowFiltered_five_term_exact :
    Function.Injective (FilteredComplex.f1 (K.rowFiltered_firstQuadrant hfq)) ∧
    Function.Exact (FilteredComplex.f1 (K.rowFiltered_firstQuadrant hfq))
      (FilteredComplex.f2 (K.rowFiltered_firstQuadrant hfq)) ∧
    Function.Exact (FilteredComplex.f2 (K.rowFiltered_firstQuadrant hfq)) K.rowFiltered.d2 ∧
    Function.Exact K.rowFiltered.d2 (FilteredComplex.f4 (K.rowFiltered_firstQuadrant hfq)) :=
  K.rowFiltered.five_term_exact (K.rowFiltered_firstQuadrant hfq)

end FirstQuadrant

/-! ### The first page: `E₁` is the vertical/horizontal cohomology

The zeroth page of the column spectral sequence is the double complex itself
(`colPageZeroEquiv`), and — as we now show — its differential `d₀` corresponds
under that identification to the *vertical* differential `dv`.  Consequently the
first page `ᴵE₁^{p,n}` is the vertical cohomology of the `p`-th column.  Dually,
the row spectral sequence has `d₀ = dh` (horizontal), so `ᴵᴵE₁` is horizontal
cohomology.  This is the differential-level half of Vakil, *The Rising Sea*,
§1.7 (`E₁ = H(gr)` made concrete for a double complex). -/

section FirstPage

/-- A single entry `lof_i α` with `p ≤ i` lies in the column filtration `colF^p`. -/
lemma lof_mem_colF {p i : ℤ} (a : ℤ) (h : p ≤ i) (α : K.A i (a - i)) :
    (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) i α) ∈ K.colF p a :=
  (le_iSup₂ (f := fun j (_ : p ≤ j) ↦
    LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (a - i'')) j)) i h)
    (LinearMap.mem_range_self _ _)

/-- A single entry `lof_p α` is a `0`-cocycle of the column filtration. -/
lemma lof_mem_Z_zero (p a : ℤ) (α : K.A p (a - p)) :
    (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) p α)
      ∈ K.colFiltered.Z 0 p a (a + 1) := by
  rw [K.colFiltered.Z_zero]
  exact K.lof_mem_colF a le_rfl α

/-- Forward evaluation of the E₀-identification on the class of a single entry:
`ᴵE₀^{p,a} ≅ A^{p,a-p}` sends `[lof_p α]` to `α`. -/
lemma colPageZeroEquiv_mk (p a : ℤ) (α : K.A p (a - p))
    (h : (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) p α)
        ∈ K.colFiltered.Z 0 p a (a + 1)) :
    K.colPageZeroEquiv p a (Submodule.Quotient.mk ⟨_, h⟩) = α := by
  rw [colPageZeroEquiv, colGrEquiv, FilteredComplex.pageZeroEquiv]
  rw [LinearEquiv.trans_apply, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  erw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rw [LinearMap.quotientInfEquivSupQuotient_symm_apply_left _ _ _
    (LinearMap.mem_range.mpr ⟨α, rfl⟩)]
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  apply K.lof_injective p a
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

/-- Inverse form of `colPageZeroEquiv_mk`: the E₀-identification sends `α` back to
the class of the single entry `lof_p α`. -/
lemma colPageZeroEquiv_symm_apply (p a : ℤ) (α : K.A p (a - p)) :
    (K.colPageZeroEquiv p a).symm α
      = Submodule.Quotient.mk ⟨_, K.lof_mem_Z_zero p a α⟩ :=
  (LinearEquiv.symm_apply_eq _).2 (K.colPageZeroEquiv_mk p a α _).symm

/-- **The differential `d₀` of the column spectral sequence is the vertical
differential `dv`.**  Under the identification `ᴵE₀^{p,a} ≅ A^{p,a-p}`
(`colPageZeroEquiv`), the page-zero differential `d₀ : ᴵE₀^{p,a} → ᴵE₀^{p,a+1}`
becomes `dv : A^{p,a-p} → A^{p,(a+1)-p}`.  Hence `ᴵE₁^{p,a} = H_dv^{a-p}` of the
`p`-th column. -/
theorem colPageZeroEquiv_dPageAux (p a : ℤ) (x : K.colFiltered.page 0 p a) :
    K.colPageZeroEquiv p (a + 1)
        (K.colFiltered.dPageAux 0 p p a (a + 1) (by ring) rfl x)
      = K.dv p p (a - p) ((a + 1) - p) (K.colPageZeroEquiv p a x) := by
  obtain ⟨α, rfl⟩ : ∃ α, (K.colPageZeroEquiv p a).symm α = x :=
    ⟨K.colPageZeroEquiv p a x, (K.colPageZeroEquiv p a).symm_apply_apply x⟩
  rw [LinearEquiv.apply_symm_apply, K.colPageZeroEquiv_symm_apply,
    K.colFiltered.dPageAux_mk]
  have hcls : (Submodule.Quotient.mk
        (K.colFiltered.dZ 0 p p a (a + 1) (by ring) rfl
          ⟨_, K.lof_mem_Z_zero p a α⟩) : K.colFiltered.page 0 p (a + 1))
      = Submodule.Quotient.mk
          ⟨_, K.lof_mem_Z_zero p (a + 1) (K.dv p p (a - p) ((a + 1) - p) α)⟩ := by
    rw [K.colFiltered.pageπ_eq_iff]
    have hval : (↑(K.colFiltered.dZ 0 p p a (a + 1) (by ring) rfl
          ⟨_, K.lof_mem_Z_zero p a α⟩) : K.colFiltered.X (a + 1))
        = DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) (p + 1)
            (K.dh p (p + 1) (a - p) ((a + 1) - (p + 1)) α)
          + DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) p
            (K.dv p p (a - p) ((a + 1) - p) α) := by
      rw [FilteredComplex.dZ_coe]
      exact K.totalD_lof a (a + 1) p α
    rw [hval, K.colFiltered.B_zero]
    change _ ∈ K.colF (p + 1) (a + 1)
    have hb : (↑(⟨DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) p
              (K.dv p p (a - p) ((a + 1) - p) α),
            K.lof_mem_Z_zero p (a + 1) (K.dv p p (a - p) ((a + 1) - p) α)⟩ :
          ↥(K.colFiltered.Z 0 p (a + 1) ((a + 1) + 1))) : K.colFiltered.X (a + 1))
        = DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) p
            (K.dv p p (a - p) ((a + 1) - p) α) := rfl
    rw [hb]
    have hmem : DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) (p + 1)
        (K.dh p (p + 1) (a - p) ((a + 1) - (p + 1)) α) ∈ K.colF (p + 1) (a + 1) :=
      K.lof_mem_colF (a + 1) (by omega) _
    convert hmem using 1
    abel
  rw [hcls, K.colPageZeroEquiv_mk]

/-- Flexible-degree form of `colPageZeroEquiv_dPageAux`: the target degree `m` is
a free variable (`m = n + 1`).  Used to name both the incoming and outgoing
page-zero differentials at a spot with clean indices. -/
theorem colPageZeroEquiv_dPageAux' (p n m : ℤ) (hm : m = n + 1)
    (x : K.colFiltered.page 0 p n) :
    K.colPageZeroEquiv p m (K.colFiltered.dPageAux 0 p p n m (by ring) hm x)
      = K.dv p p (n - p) (m - p) (K.colPageZeroEquiv p n x) := by
  subst hm
  exact K.colPageZeroEquiv_dPageAux p n x

/-- The outgoing vertical differential at spot `(p, a)`:
`dv : A^{p,a-p} → A^{p,(a+1)-p}`. -/
noncomputable abbrev dvOut (p a : ℤ) : K.A p (a - p) →ₗ[R] K.A p ((a + 1) - p) :=
  K.dv p p (a - p) ((a + 1) - p)

/-- The incoming vertical differential at spot `(p, a)`:
`dv : A^{p,(a-1)-p} → A^{p,a-p}`. -/
noncomputable abbrev dvIn (p a : ℤ) : K.A p ((a - 1) - p) →ₗ[R] K.A p (a - p) :=
  K.dv p p ((a - 1) - p) (a - p)

/-- **`ᴵE₁` is the vertical cohomology of the double complex** (FOAG §1.7,
first spectral sequence).  Under the identification `ᴵE₀^{p,•} ≅ A^{p, •-p}`,
the first page `ᴵE₁^{p,a}` is the homology of the `p`-th column at the vertical
differential: `ᴵE₁^{p,a} ≅ ker(dv)/im(dv)`. -/
noncomputable def colPageOneEquiv (p a : ℤ) :
    K.colFiltered.page 1 p a ≃ₗ[R]
      (↥(ker (K.dvOut p a)) ⧸ (range (K.dvIn p a)).comap (ker (K.dvOut p a)).subtype) :=
  (K.colFiltered.pageSuccEquiv' 0 p p p a (by ring) (by ring)).trans <|
    homologyEquivOfSquares
      (e := K.colPageZeroEquiv p a)
      (fout := K.colFiltered.dPageAux 0 p p a (a + 1) (by ring) rfl)
      (gout := K.dvOut p a)
      (eout := K.colPageZeroEquiv p (a + 1))
      (hout := fun x ↦ K.colPageZeroEquiv_dPageAux' p a (a + 1) (by ring) x)
      (fin_ := K.colFiltered.dPageAux 0 p p (a - 1) a (by ring) (by ring))
      (gin := K.dvIn p a)
      (hin := by
        rw [← LinearMap.range_comp]
        have hcomp : (K.colPageZeroEquiv p a : K.colFiltered.page 0 p a →ₗ[R] _).comp
              (K.colFiltered.dPageAux 0 p p (a - 1) a (by ring) (by ring))
            = (K.dvIn p a).comp
              (K.colPageZeroEquiv p (a - 1) : K.colFiltered.page 0 p (a - 1) →ₗ[R] _) := by
          refine LinearMap.ext fun x ↦ ?_
          simpa using K.colPageZeroEquiv_dPageAux' p (a - 1) a (by ring) x
        rw [hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top])

/-! #### Row version: `d₀ = dh`

The dual statement for the second (row-filtered) spectral sequence: under the
identification `ᴵᴵE₀^{p,a} ≅ A^{a-p, a-(a-p)}` (`rowPageZeroEquiv`), the page-zero
differential is the *horizontal* differential `dh`.  Hence `ᴵᴵE₁ = H_dh`.  The
one wrinkle over the column case: the surviving `dh` term from `totalD_lof` sits
at family index `(a-p)+1`, while `rowPageZeroEquiv (a+1)`'s generator is at
`(a+1)-p`; these are equal only propositionally, so a `lof`-index transport is
needed (handled by the flexible-index `rowPageZeroEquiv_mk'`). -/

/-- A single entry `lof_i α` with `p ≤ a - i` lies in the row filtration `rowF^p`. -/
lemma lof_mem_rowF {p i : ℤ} (a : ℤ) (h : p ≤ a - i) (α : K.A i (a - i)) :
    (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) i α) ∈ K.rowF p a :=
  (le_iSup₂ (f := fun j (_ : p ≤ a - j) ↦
    LinearMap.range (DirectSum.lof R ℤ (fun i'' ↦ K.A i'' (a - i'')) j)) i h)
    (LinearMap.mem_range_self _ _)

/-- A single entry `lof_{a-p} β` is a `0`-cocycle of the row filtration. -/
lemma lof_mem_rowZ_zero (p a : ℤ) (β : K.A (a - p) (a - (a - p))) :
    (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) (a - p) β)
      ∈ K.rowFiltered.Z 0 p a (a + 1) := by
  rw [K.rowFiltered.Z_zero]
  exact K.lof_mem_rowF a (by omega) β

/-- Forward evaluation of the row E₀-identification on the class of a single entry:
`ᴵᴵE₀^{p,a} ≅ A^{a-p, a-(a-p)}` sends `[lof_{a-p} β]` to `β`. -/
lemma rowPageZeroEquiv_mk (p a : ℤ) (β : K.A (a - p) (a - (a - p)))
    (h : (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) (a - p) β)
        ∈ K.rowFiltered.Z 0 p a (a + 1)) :
    K.rowPageZeroEquiv p a (Submodule.Quotient.mk ⟨_, h⟩) = β := by
  rw [rowPageZeroEquiv, rowGrEquiv, FilteredComplex.pageZeroEquiv]
  rw [LinearEquiv.trans_apply, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  erw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
  rw [LinearMap.quotientInfEquivSupQuotient_symm_apply_left _ _ _
    (LinearMap.mem_range.mpr ⟨β, rfl⟩)]
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  apply K.lof_injective (a - p) a
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

/-- Flexible-index form of `rowPageZeroEquiv_mk`: the generator may sit at any
index `j` propositionally equal to `a - p`, at the cost of a cast on the value. -/
lemma rowPageZeroEquiv_mk' (p a j : ℤ) (hj : j = a - p) (β : K.A j (a - j))
    (h : (DirectSum.lof R ℤ (fun i' ↦ K.A i' (a - i')) j β)
        ∈ K.rowFiltered.Z 0 p a (a + 1)) :
    K.rowPageZeroEquiv p a (Submodule.Quotient.mk ⟨_, h⟩) = hj ▸ β := by
  subst hj
  exact K.rowPageZeroEquiv_mk p a β h

/-- Inverse form of `rowPageZeroEquiv_mk`. -/
lemma rowPageZeroEquiv_symm_apply (p a : ℤ) (β : K.A (a - p) (a - (a - p))) :
    (K.rowPageZeroEquiv p a).symm β
      = Submodule.Quotient.mk ⟨_, K.lof_mem_rowZ_zero p a β⟩ :=
  (LinearEquiv.symm_apply_eq _).2 (K.rowPageZeroEquiv_mk p a β _).symm

/-- **The differential `d₀` of the row spectral sequence is the horizontal
differential `dh`.**  Under `rowPageZeroEquiv : ᴵᴵE₀^{p,a} ≅ A^{a-p, a-(a-p)}`,
the page-zero differential `d₀ : ᴵᴵE₀^{p,a} → ᴵᴵE₀^{p,a+1}` becomes
`dh : A^{a-p, a-(a-p)} → A^{(a+1)-p, (a+1)-((a+1)-p)}`.  Hence
`ᴵᴵE₁^{p,a} = H_dh` (horizontal cohomology). -/
theorem rowPageZeroEquiv_dPageAux (p a : ℤ) (x : K.rowFiltered.page 0 p a) :
    K.rowPageZeroEquiv p (a + 1)
        (K.rowFiltered.dPageAux 0 p p a (a + 1) (by ring) rfl x)
      = K.dh (a - p) ((a + 1) - p) (a - (a - p)) ((a + 1) - ((a + 1) - p))
          (K.rowPageZeroEquiv p a x) := by
  obtain ⟨β, rfl⟩ : ∃ β, (K.rowPageZeroEquiv p a).symm β = x :=
    ⟨K.rowPageZeroEquiv p a x, (K.rowPageZeroEquiv p a).symm_apply_apply x⟩
  rw [LinearEquiv.apply_symm_apply, K.rowPageZeroEquiv_symm_apply,
    K.rowFiltered.dPageAux_mk]
  -- membership of the surviving `dh` term (at index `(a-p)+1`) as a 0-cocycle
  have hz : (DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) ((a - p) + 1)
        (K.dh (a - p) ((a - p) + 1) (a - (a - p)) ((a + 1) - ((a - p) + 1)) β))
      ∈ K.rowFiltered.Z 0 p (a + 1) ((a + 1) + 1) := by
    rw [K.rowFiltered.Z_zero]
    exact K.lof_mem_rowF (a + 1) (by omega) _
  have hcls : (Submodule.Quotient.mk
        (K.rowFiltered.dZ 0 p p a (a + 1) (by ring) rfl
          ⟨_, K.lof_mem_rowZ_zero p a β⟩) : K.rowFiltered.page 0 p (a + 1))
      = Submodule.Quotient.mk ⟨_, hz⟩ := by
    rw [K.rowFiltered.pageπ_eq_iff]
    have hval : (↑(K.rowFiltered.dZ 0 p p a (a + 1) (by ring) rfl
          ⟨_, K.lof_mem_rowZ_zero p a β⟩) : K.rowFiltered.X (a + 1))
        = DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) ((a - p) + 1)
            (K.dh (a - p) ((a - p) + 1) (a - (a - p)) ((a + 1) - ((a - p) + 1)) β)
          + DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) (a - p)
            (K.dv (a - p) (a - p) (a - (a - p)) ((a + 1) - (a - p)) β) := by
      rw [FilteredComplex.dZ_coe]
      exact K.totalD_lof a (a + 1) (a - p) β
    rw [hval, K.rowFiltered.B_zero]
    change _ ∈ K.rowF (p + 1) (a + 1)
    have hb : (↑(⟨DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) ((a - p) + 1)
              (K.dh (a - p) ((a - p) + 1) (a - (a - p)) ((a + 1) - ((a - p) + 1)) β),
            hz⟩ : ↥(K.rowFiltered.Z 0 p (a + 1) ((a + 1) + 1))) : K.rowFiltered.X (a + 1))
        = DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) ((a - p) + 1)
            (K.dh (a - p) ((a - p) + 1) (a - (a - p)) ((a + 1) - ((a - p) + 1)) β) := rfl
    rw [hb]
    have hmem : DirectSum.lof R ℤ (fun i' ↦ K.A i' ((a + 1) - i')) (a - p)
        (K.dv (a - p) (a - p) (a - (a - p)) ((a + 1) - (a - p)) β) ∈ K.rowF (p + 1) (a + 1) :=
      K.lof_mem_rowF (a + 1) (by omega) _
    convert hmem using 1
    abel
  rw [hcls, K.rowPageZeroEquiv_mk' p (a + 1) ((a - p) + 1) (by ring) _ hz]
  -- transport the surviving `dh` index `(a-p)+1` to `(a+1)-p`
  exact (fun k (e : (a - p) + 1 = k) ↦
    (by subst e; rfl :
      (e ▸ K.dh (a - p) ((a - p) + 1) (a - (a - p)) ((a + 1) - ((a - p) + 1)) β
          : K.A k ((a + 1) - k))
        = K.dh (a - p) k (a - (a - p)) ((a + 1) - k) β)) ((a + 1) - p) (by ring)

/-- Flexible-degree form of `rowPageZeroEquiv_dPageAux`: the target degree `m` is
a free variable (`m = n + 1`). -/
theorem rowPageZeroEquiv_dPageAux' (p n m : ℤ) (hm : m = n + 1)
    (x : K.rowFiltered.page 0 p n) :
    K.rowPageZeroEquiv p m (K.rowFiltered.dPageAux 0 p p n m (by ring) hm x)
      = K.dh (n - p) (m - p) (n - (n - p)) (m - (m - p)) (K.rowPageZeroEquiv p n x) := by
  subst hm
  exact K.rowPageZeroEquiv_dPageAux p n x

/-- The outgoing horizontal differential at spot `(p, a)`:
`dh : A^{a-p, a-(a-p)} → A^{(a+1)-p, (a+1)-((a+1)-p)}`. -/
noncomputable abbrev dhOut (p a : ℤ) :
    K.A (a - p) (a - (a - p)) →ₗ[R] K.A ((a + 1) - p) ((a + 1) - ((a + 1) - p)) :=
  K.dh (a - p) ((a + 1) - p) (a - (a - p)) ((a + 1) - ((a + 1) - p))

/-- The incoming horizontal differential at spot `(p, a)`:
`dh : A^{(a-1)-p, (a-1)-((a-1)-p)} → A^{a-p, a-(a-p)}`. -/
noncomputable abbrev dhIn (p a : ℤ) :
    K.A ((a - 1) - p) ((a - 1) - ((a - 1) - p)) →ₗ[R] K.A (a - p) (a - (a - p)) :=
  K.dh ((a - 1) - p) (a - p) ((a - 1) - ((a - 1) - p)) (a - (a - p))

/-- **`ᴵᴵE₁` is the horizontal cohomology of the double complex** (FOAG §1.7,
second spectral sequence).  Under the identification `ᴵᴵE₀^{p,•} ≅ A^{•-p, •-(•-p)}`,
the first page `ᴵᴵE₁^{p,a}` is the homology of the appropriate row at the
horizontal differential: `ᴵᴵE₁^{p,a} ≅ ker(dh)/im(dh)`. -/
noncomputable def rowPageOneEquiv (p a : ℤ) :
    K.rowFiltered.page 1 p a ≃ₗ[R]
      (↥(ker (K.dhOut p a)) ⧸ (range (K.dhIn p a)).comap (ker (K.dhOut p a)).subtype) :=
  (K.rowFiltered.pageSuccEquiv' 0 p p p a (by ring) (by ring)).trans <|
    homologyEquivOfSquares
      (e := K.rowPageZeroEquiv p a)
      (fout := K.rowFiltered.dPageAux 0 p p a (a + 1) (by ring) rfl)
      (gout := K.dhOut p a)
      (eout := K.rowPageZeroEquiv p (a + 1))
      (hout := fun x ↦ K.rowPageZeroEquiv_dPageAux' p a (a + 1) (by ring) x)
      (fin_ := K.rowFiltered.dPageAux 0 p p (a - 1) a (by ring) (by ring))
      (gin := K.dhIn p a)
      (hin := by
        rw [← LinearMap.range_comp]
        have hcomp : (K.rowPageZeroEquiv p a : K.rowFiltered.page 0 p a →ₗ[R] _).comp
              (K.rowFiltered.dPageAux 0 p p (a - 1) a (by ring) (by ring))
            = (K.dhIn p a).comp
              (K.rowPageZeroEquiv p (a - 1) : K.rowFiltered.page 0 p (a - 1) →ₗ[R] _) := by
          refine LinearMap.ext fun x ↦ ?_
          simpa using K.rowPageZeroEquiv_dPageAux' p (a - 1) a (by ring) x
        rw [hcomp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top])

end FirstPage

end DoubleComplex
