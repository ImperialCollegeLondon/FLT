/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.ExactCouple.Basic
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Graded exact couples and the bidegree of the differentials

This file upgrades `FLT.Slop.ExactCouple.Basic` to the **graded** setting,
following the classical bookkeeping of Weibel (*An Introduction to Homological
Algebra*, §5.9) and McCleary (*A User's Guide to Spectral Sequences*, §2.2).

In every exact couple that occurs in nature the modules `D`, `E` carry a grading
(by an abelian group `ι` of "degrees" — a single degree `ℤ`, a bidegree `ℤ × ℤ`,
etc.) and the three maps `i, j, k` are **homogeneous** of fixed degrees
`di, dj, dk`.  The differential `d = j ∘ k` is then homogeneous of degree
`dj + dk`, and — this is the whole point of gradings — the derived couple is
again graded, with `i'` of degree `di`, `j'` of degree `dj - di`, and `k'` of
degree `dk`.  Consequently the differential of the derived couple,
`d' = j' ∘ k'`, has degree

```
    deg d' = (dj - di) + dk = (dj + dk) - di = deg d - di.
```

Iterating, the `r`-th derived differential has degree `deg d - r • di`:
**each derivation drops the differential's degree by `di`.**  This degree-shift
is the defining structural feature of a graded spectral sequence.  For example,
the exact couple of a filtered complex has bidegrees `di = (-1, 1)`,
`dj = (0, 0)`, `dk = (1, 0)`, and its page `r` is the classical page `E_{r+1}`;
the closed form gives its `r`-th differential the degree `(r + 1, -r)`, the
familiar bidegree of the classical `d_{r+1} : E_{r+1}^{p,q} → E_{r+1}^{p+r+1, q-r}`.

## Main definitions and results

* `GradedExactCouple R ι` : an `ExactCouple R` together with `ι`-gradings of `D`
  and `E` (the `D`-grading internally direct) and homogeneity of `i, j, k`.
* `GradedExactCouple.homog_d` : `d = j ∘ k` is homogeneous of degree `dj + dk`.
* `DirectSum.IsInternal.inf_range_le_map` : the key linear-algebra lemma —
  a homogeneous element in the image of a homogeneous map is the image of a
  homogeneous element (this is *why* the derived `j'` drops degree by `di`).
* `GradedExactCouple.derI_homog`, `derK_homog`, `derJ_homog` : the derived maps
  are homogeneous of degrees `di`, `dk`, `dj - di` for the derived gradings.
* `GradedExactCouple.derivedCouple_homog_d` : the derived differential
  `d' = j' ∘ k'` is homogeneous of degree `(dj + dk) - di` — the bidegree drop.
* `GradedExactCouple.derivedGraded`, `gradedDerived` : the derived couple is
  again a graded exact couple (the new ingredient being `isInternal_derGradD`:
  `im i` is a graded submodule), and the iteration, with the closed form
  `gradedDerived_homog_d` : `deg d_r = (dj + dk) - r • di`.

All of `ExactCouple`'s content (the derived couple is exact, `d² = 0`, the pages)
is inherited verbatim; this file adds only the degree bookkeeping.

## Tags

exact couple, graded exact couple, spectral sequence, bidegree
-/

@[expose] public section

open LinearMap Submodule Function DirectSum

universe u

/-! ## The homogeneous-image lemma -/

/-- If a grading `𝒟` of `M` is internally direct and `i : M → M` is homogeneous
of degree `a` (i.e. `i (𝒟 s) ⊆ 𝒟 (s + a)`), then a homogeneous element of degree
`q` lying in `range i` already lies in `i (𝒟 (q - a))`.  Equivalently:
`𝒟 q ⊓ range i ≤ (𝒟 (q - a)).map i`.  This is the algebraic heart of the
degree-shift of the derived `j'` of a graded exact couple. -/
theorem DirectSum.IsInternal.inf_range_le_map {ι R M : Type*} [DecidableEq ι]
    [AddGroup ι] [Ring R] [AddCommGroup M] [Module R M] {𝒟 : ι → Submodule R M}
    (hint : DirectSum.IsInternal 𝒟) {a : ι} {i : M →ₗ[R] M}
    (hi : ∀ s, (𝒟 s).map i ≤ 𝒟 (s + a)) (q : ι) :
    𝒟 q ⊓ LinearMap.range i ≤ (𝒟 (q - a)).map i := by
  classical
  letI := hint.chooseDecomposition
  rintro y ⟨hyq, x, rfl⟩
  refine ⟨(DirectSum.decompose 𝒟 x (q - a) : M), (DirectSum.decompose 𝒟 x (q - a)).2, ?_⟩
  have hmem : ∀ s, i ((DirectSum.decompose 𝒟 x s : M)) ∈ 𝒟 (s + a) :=
    fun s ↦ hi s ⟨_, (DirectSum.decompose 𝒟 x s).2, rfl⟩
  have hix : i x = ∑ s ∈ (DirectSum.decompose 𝒟 x).support,
      i ((DirectSum.decompose 𝒟 x s : M)) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒟 x, map_sum]
  have key0 : (DirectSum.decompose 𝒟 (i x)) q
      = ∑ s ∈ (DirectSum.decompose 𝒟 x).support,
          (DirectSum.decompose 𝒟 (i ((DirectSum.decompose 𝒟 x s : M)))) q := by
    rw [hix, DirectSum.decompose_sum, DirectSum.sum_apply]
  have key : i x = ∑ s ∈ (DirectSum.decompose 𝒟 x).support,
      ((DirectSum.decompose 𝒟 (i ((DirectSum.decompose 𝒟 x s : M)))) q : M) := by
    rw [← DirectSum.decompose_of_mem_same 𝒟 hyq, key0, AddSubmonoidClass.coe_finsetSum]
  have hterm : ∀ s ∈ (DirectSum.decompose 𝒟 x).support,
      ((DirectSum.decompose 𝒟 (i ((DirectSum.decompose 𝒟 x s : M)))) q : M)
        = if s = q - a then i ((DirectSum.decompose 𝒟 x s : M)) else 0 := by
    intro s _
    by_cases h : s = q - a
    · have h' : s + a = q := by rw [h, sub_add_cancel]
      rw [if_pos h, ← h']; exact DirectSum.decompose_of_mem_same 𝒟 (hmem s)
    · have h' : s + a ≠ q := fun hc ↦ h (by rw [← hc, add_sub_cancel_right])
      rw [if_neg h]; exact DirectSum.decompose_of_mem_ne 𝒟 (hmem s) h'
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at key
  by_cases hs : q - a ∈ (DirectSum.decompose 𝒟 x).support
  · rw [if_pos hs] at key; exact key.symm
  · rw [if_neg hs] at key
    have hz : (DirectSum.decompose 𝒟 x (q - a) : M) = 0 := by
      rw [DFinsupp.notMem_support_iff.mp hs]; rfl
    rw [hz, map_zero]; exact key.symm

/-! ## Graded exact couples -/

/-- A **graded exact couple** of `R`-modules over the degree group `ι`: an
`ExactCouple R` with `ι`-gradings `gradD`, `gradE` of its two modules, such that
`gradD` is internally direct and the three maps `i, j, k` are homogeneous of
degrees `di, dj, dk`.  (Only the `D`-grading is required to be internally direct;
that is all the derived-couple degree bookkeeping needs.) -/
structure GradedExactCouple (R : Type*) [Ring R] (ι : Type*) [AddCommGroup ι]
    [DecidableEq ι] extends ExactCouple.{u} R where
  /-- Degree of `i`. -/
  di : ι
  /-- Degree of `j`. -/
  dj : ι
  /-- Degree of `k`. -/
  dk : ι
  /-- The grading of `D`. -/
  gradD : ι → Submodule R toExactCouple.D
  /-- The grading of `E`. -/
  gradE : ι → Submodule R toExactCouple.E
  /-- `D` is internally direct-sum decomposed by `gradD`. -/
  internalD : DirectSum.IsInternal gradD
  /-- `i` is homogeneous of degree `di`. -/
  homog_i : ∀ p, (gradD p).map toExactCouple.i ≤ gradD (p + di)
  /-- `j` is homogeneous of degree `dj`. -/
  homog_j : ∀ p, (gradD p).map toExactCouple.j ≤ gradE (p + dj)
  /-- `k` is homogeneous of degree `dk`. -/
  homog_k : ∀ p, (gradE p).map toExactCouple.k ≤ gradD (p + dk)

namespace GradedExactCouple

variable {R : Type*} [Ring R] {ι : Type*} [AddCommGroup ι] [DecidableEq ι]
  (C : GradedExactCouple.{u} R ι)

/-- The differential `d = j ∘ k` is homogeneous of degree `dj + dk`. -/
theorem homog_d (p : ι) :
    (C.gradE p).map C.d ≤ C.gradE (p + (C.dj + C.dk)) := by
  rintro _ ⟨e, he, rfl⟩
  have h1 : C.k e ∈ C.gradD (p + C.dk) := C.homog_k p ⟨e, he, rfl⟩
  have h2 : C.j (C.k e) ∈ C.gradE ((p + C.dk) + C.dj) := C.homog_j _ ⟨_, h1, rfl⟩
  rw [show C.d e = C.j (C.k e) from rfl]
  rwa [show (p + C.dk) + C.dj = p + (C.dj + C.dk) by abel] at h2

/-! ## The derived gradings and homogeneity of the derived maps

The derived couple (from `FLT.Slop.ExactCouple.Basic`) has `D' = im i` (the subtype
`C.derD`) and `E' = ker d / im d` (`C.derE`).  We grade them by:

* `derGradD p = (gradD p).comap derD.subtype`  (the part of `gradD p` lying in
  `im i`, viewed inside the subtype `derD`);
* `derGradE p = ((gradE p) ∩ ker d).image in derE`.

Then `i'` has degree `di`, `k'` has degree `dk`, and — using the homogeneous-image
lemma — `j'` has degree `dj - di`. -/

/-- The grading of `D' = im i` (a submodule of the subtype `C.derD`). -/
def derGradD (p : ι) : Submodule R C.derD := (C.gradD p).comap C.derD.subtype

/-- The grading of `E' = ker d / im d`. -/
def derGradE (p : ι) : Submodule R C.derE :=
  ((C.gradE p).comap (LinearMap.ker C.d).subtype).map C.derEmk

/-- `i'` is homogeneous of degree `di`. -/
theorem derI_homog (p : ι) :
    (C.derGradD p).map C.derI ≤ C.derGradD (p + C.di) := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [derGradD, Submodule.mem_comap, Submodule.coe_subtype] at hy ⊢
  rw [ExactCouple.derI_coe]
  exact C.homog_i p ⟨(y : C.D), hy, rfl⟩

/-- `k'` is homogeneous of degree `dk`. -/
theorem derK_homog (p : ι) :
    (C.derGradE p).map C.derK ≤ C.derGradD (p + C.dk) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  simp only [derGradE] at hξ
  obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hξ
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at he
  simp only [derGradD, Submodule.mem_comap, Submodule.coe_subtype]
  rw [show C.derK (C.derEmk e) = C.derK (Submodule.Quotient.mk e) from rfl,
    ExactCouple.derK_mk]
  exact C.homog_k p ⟨(e : C.E), he, rfl⟩

/-- `j'` is homogeneous of degree `dj - di`.  This is the step that uses the
homogeneous-image lemma: an element of `derGradD p = gradD p ∩ im i` is
`i` of a homogeneous element of degree `p - di`, on which `j` lands in degree
`(p - di) + dj = p + (dj - di)`. -/
theorem derJ_homog (p : ι) :
    (C.derGradD p).map C.derJ ≤ C.derGradE (p + (C.dj - C.di)) := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [derGradD] at hy
  -- (y : D) ∈ gradD p and ∈ range i (it is in the subtype derD)
  have hyr : (y : C.D) ∈ LinearMap.range C.i := y.2
  obtain ⟨x', hx'mem, hx'⟩ :=
    C.internalD.inf_range_le_map C.homog_i p ⟨hy, hyr⟩
  -- x' ∈ gradD (p - di), i x' = (y : D)
  have hyeq : y = ⟨C.i x', ⟨x', rfl⟩⟩ := Subtype.ext hx'.symm
  rw [hyeq, ExactCouple.derJ_apply]
  -- derJ y = derJAux x' = [j x']
  have hjmem : C.j x' ∈ C.gradE ((p - C.di) + C.dj) := C.homog_j _ ⟨x', hx'mem, rfl⟩
  simp only [derGradE, ExactCouple.derJAux_apply, Submodule.mem_map]
  refine ⟨⟨C.j x', by simp [LinearMap.mem_ker]⟩, ?_, ?_⟩
  · simp only [Submodule.mem_comap, Submodule.coe_subtype]
    rwa [show (p - C.di) + C.dj = p + (C.dj - C.di) by abel] at hjmem
  · rfl

/-- **The bidegree drop.**  The derived differential `d' = j' ∘ k'` is
homogeneous of degree `(dj + dk) - di = deg d - di`: passing to the derived
couple drops the differential's degree by `di`. -/
theorem derivedCouple_homog_d (p : ι) :
    (C.derGradE p).map C.derivedCouple.d ≤ C.derGradE (p + ((C.dj + C.dk) - C.di)) := by
  rintro _ ⟨w, hw, rfl⟩
  -- d' w = j' (k' w); k' w has degree p + dk, then j' drops by di
  rw [show C.derivedCouple.d w = C.derJ (C.derK w) from rfl]
  have h1 : C.derK w ∈ C.derGradD (p + C.dk) := C.derK_homog p ⟨w, hw, rfl⟩
  have h2 := C.derJ_homog (p + C.dk) ⟨C.derK w, h1, rfl⟩
  rwa [show (p + C.dk) + (C.dj - C.di) = p + ((C.dj + C.dk) - C.di) by abel] at h2

/-! ## Iterating: the derived couple is again a graded exact couple

The last thing needed to turn a graded exact couple into a *graded* spectral
sequence is to package `derivedCouple` back into a `GradedExactCouple`, with the
derived gradings `derGradD`, `derGradE` and degrees `di, dj - di, dk`.  The only
new fact required is that `derGradD` is internally direct, i.e. that `im i` is a
graded submodule of `D`.  This holds because `im i = ⨆ s, i (gradD s)` and each
`i (gradD s)` lands in `gradD (s + di) ⊓ im i` (homogeneity of `i`). -/

/-- `im i = range C.i` is a graded submodule: the derived `D`-grading `derGradD`
is internally direct.  This is the only new ingredient needed to iterate. -/
theorem isInternal_derGradD : DirectSum.IsInternal C.derGradD := by
  classical
  have hsub : Function.Injective C.derD.subtype := C.derD.subtype_injective
  -- The images `gradD p ⊓ im i` of the derived grading, viewed back in `D`.
  have hGind : iSupIndep (fun p ↦ C.derD ⊓ C.gradD p) :=
    (C.internalD.submodule_iSupIndep).mono (fun p ↦ inf_le_right)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep_def.mpr (fun p ↦ ?_), ?_⟩
  · -- Independence: reflect along the injective `subtype`.
    rw [disjoint_iff, ← (Submodule.map_injective_of_injective hsub).eq_iff,
      Submodule.map_inf C.derD.subtype hsub, Submodule.map_bot]
    simp only [Submodule.map_iSup, derGradD, Submodule.map_comap_subtype]
    exact disjoint_iff.mp (iSupIndep_def.mp hGind p)
  · -- `⨆ p, derGradD p = ⊤`: reflect along `subtype`;
    -- this reduces to `⨆ p, im i ⊓ gradD p = im i`.
    rw [← (Submodule.map_injective_of_injective hsub).eq_iff, Submodule.map_subtype_top]
    simp only [Submodule.map_iSup, derGradD, Submodule.map_comap_subtype]
    refine le_antisymm (iSup_le (fun _ ↦ inf_le_left)) ?_
    have hDtop : C.derD = ⨆ s, (C.gradD s).map C.i := by
      change LinearMap.range C.i = _
      rw [← Submodule.map_top, ← C.internalD.submodule_iSup_eq_top, Submodule.map_iSup]
    nth_rewrite 1 [hDtop]
    refine iSup_le (fun s ↦ ?_)
    refine le_trans (le_inf ?_ (C.homog_i s)) (le_iSup (fun i ↦ C.derD ⊓ C.gradD i) (s + C.di))
    rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩

/-- The **derived graded exact couple**: `derivedCouple` regraded by `derGradD`,
`derGradE`, with degrees `di`, `dj - di`, `dk`.  Iterating this gives the pages
of the associated graded spectral sequence. -/
noncomputable def derivedGraded (C : GradedExactCouple.{u} R ι) :
    GradedExactCouple.{u} R ι where
  toExactCouple := C.derivedCouple
  di := C.di
  dj := C.dj - C.di
  dk := C.dk
  gradD := C.derGradD
  gradE := C.derGradE
  internalD := C.isInternal_derGradD
  homog_i := C.derI_homog
  homog_j := C.derJ_homog
  homog_k := C.derK_homog

/-- The `r`-th derived graded couple (`gradedDerived 0 = C`), grading the pages of
the spectral sequence of a graded exact couple. -/
noncomputable def gradedDerived (C : GradedExactCouple.{u} R ι) :
    ℕ → GradedExactCouple.{u} R ι
  | 0 => C
  | (n + 1) => (C.gradedDerived n).derivedGraded

@[simp] theorem gradedDerived_zero : C.gradedDerived 0 = C := rfl

@[simp] theorem gradedDerived_succ (r : ℕ) :
    C.gradedDerived (r + 1) = (C.gradedDerived r).derivedGraded := rfl

/-- The underlying exact couple of the `r`-th derived graded couple is the
`r`-th derived couple: the graded and the ungraded iterations agree, so the
degree information of `gradedDerived` applies to the pages `ExactCouple.page`
of the underlying couple. -/
theorem gradedDerived_toExactCouple (r : ℕ) :
    (C.gradedDerived r).toExactCouple = C.toExactCouple.derived r := by
  induction r with
  | zero => rfl
  | succ n ih =>
    change ((C.gradedDerived n).toExactCouple).derivedCouple =
      (C.toExactCouple.derived n).derivedCouple
    rw [ih]

@[simp] theorem gradedDerived_di (r : ℕ) : (C.gradedDerived r).di = C.di := by
  induction r with
  | zero => rfl
  | succ n ih => rw [gradedDerived, derivedGraded, ih]

@[simp] theorem gradedDerived_dk (r : ℕ) : (C.gradedDerived r).dk = C.dk := by
  induction r with
  | zero => rfl
  | succ n ih => rw [gradedDerived, derivedGraded, ih]

/-- The `j`-degree drops by `di` at every page: `dj_r = dj - r • di`. -/
@[simp] theorem gradedDerived_dj (r : ℕ) : (C.gradedDerived r).dj = C.dj - r • C.di := by
  induction r with
  | zero => change C.dj = C.dj - (0 : ℕ) • C.di; rw [zero_smul, sub_zero]
  | succ n ih =>
    change (C.gradedDerived n).dj - (C.gradedDerived n).di = C.dj - (n + 1) • C.di
    rw [ih, gradedDerived_di, succ_nsmul]; abel

/-- **Closed form for the page differentials' degree.**  The differential
`d_r = j_r ∘ k_r` of the `r`-th page is homogeneous of degree
`(dj + dk) - r • di`: each derivation drops the differential's degree by `di`. -/
theorem gradedDerived_homog_d (r : ℕ) (p : ι) :
    ((C.gradedDerived r).gradE p).map (C.gradedDerived r).d ≤
      (C.gradedDerived r).gradE (p + ((C.dj + C.dk) - r • C.di)) := by
  have h := (C.gradedDerived r).homog_d p
  rw [gradedDerived_dj, gradedDerived_dk] at h
  rwa [show p + ((C.dj - r • C.di) + C.dk) = p + ((C.dj + C.dk) - r • C.di) by abel] at h

end GradedExactCouple
