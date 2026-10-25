/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.ExactCouple.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Tactic.Abel

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

* `GradedExactCouple R ι` : an `ExactCouple R` together with internal direct-sum
  `ι`-gradings of `D` and `E`, and homogeneity of `i, j, k`.
* `GradedExactCouple.homog_d` : `d = j ∘ k` is homogeneous of degree `dj + dk`.
* `DirectSum.IsInternal.inf_range_le_map` : the key linear-algebra lemma —
  a homogeneous element in the image of a homogeneous map is the image of a
  homogeneous element (this is *why* the derived `j'` drops degree by `di`).
* `GradedExactCouple.derI_homog`, `derK_homog`, `derJ_homog` : the derived maps
  are homogeneous of degrees `di`, `dk`, `dj - di` for the derived gradings.
* `GradedExactCouple.derivedCouple_homog_d` : the derived differential
  `d' = j' ∘ k'` is homogeneous of degree `(dj + dk) - di` — the bidegree drop.
* `GradedExactCouple.derivedGraded`, `gradedDerived` : the derived couple is
  again a graded exact couple (`isInternal_derGradD` and `isInternal_derGradE`),
  and the iteration, with the closed form
  `gradedDerived_homog_d` : `deg d_r = (dj + dk) - r • di`.

All of `ExactCouple`'s content (the derived couple is exact, `d² = 0`, the pages)
is inherited verbatim; this file adds only the degree bookkeeping.

## Tags

exact couple, graded exact couple, spectral sequence, bidegree
-/

@[expose] public section

open LinearMap Submodule Function DirectSum

universe u

/-! ## General lemmas about homogeneous maps -/

private theorem decomposeMapHomogeneous
    {ι R M N : Type*} [DecidableEq ι] [AddGroup ι]
    [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    (A : ι → Submodule R M) [DirectSum.Decomposition A]
    (B : ι → Submodule R N) [DirectSum.Decomposition B]
    {a : ι} {f : M →ₗ[R] N} (hf : ∀ p, (A p).map f ≤ B (p + a))
    (x : M) (p : ι) :
    (DirectSum.decompose B (f x) (p + a) : N) =
      f (DirectSum.decompose A x p : M) := by
  classical
  have hmem : ∀ q, f (DirectSum.decompose A x q : M) ∈ B (q + a) :=
    fun q ↦ hf q ⟨_, (DirectSum.decompose A x q).2, rfl⟩
  have hfx : f x = ∑ q ∈ (DirectSum.decompose A x).support,
      f (DirectSum.decompose A x q : M) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose A x, map_sum]
  have key0 : DirectSum.decompose B (f x) (p + a) =
      ∑ q ∈ (DirectSum.decompose A x).support,
        DirectSum.decompose B (f (DirectSum.decompose A x q : M)) (p + a) := by
    rw [hfx, DirectSum.decompose_sum, DirectSum.sum_apply]
  have key : (DirectSum.decompose B (f x) (p + a) : N) =
      ∑ q ∈ (DirectSum.decompose A x).support,
        (DirectSum.decompose B (f (DirectSum.decompose A x q : M)) (p + a) : N) := by
    rw [key0, AddSubmonoidClass.coe_finsetSum]
  have hterm : ∀ q ∈ (DirectSum.decompose A x).support,
      (DirectSum.decompose B (f (DirectSum.decompose A x q : M)) (p + a) : N) =
        if q = p then f (DirectSum.decompose A x q : M) else 0 := by
    intro q _
    by_cases h : q = p
    · rw [if_pos h, h]
      exact DirectSum.decompose_of_mem_same B (hmem p)
    · rw [if_neg h]
      exact DirectSum.decompose_of_mem_ne B (hmem q) (fun h' ↦ h (add_right_cancel h'))
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at key
  by_cases hp : p ∈ (DirectSum.decompose A x).support
  · rwa [if_pos hp] at key
  · rw [if_neg hp] at key
    have hz : (DirectSum.decompose A x p : M) = 0 := by
      rw [DFinsupp.notMem_support_iff.mp hp]
      rfl
    rwa [hz, map_zero]

/-- Let `f : M → N` be homogeneous of degree `a` for internal gradings `A` and
`B`. A degree-`q` element in `range f` is the image of an element of degree
`q - a`. -/
theorem DirectSum.IsInternal.inf_range_le_map {ι R M N : Type*} [DecidableEq ι]
    [AddGroup ι] [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] {A : ι → Submodule R M}
    {B : ι → Submodule R N} (hA : DirectSum.IsInternal A)
    (hB : DirectSum.IsInternal B) {a : ι} {f : M →ₗ[R] N}
    (hf : ∀ p, (A p).map f ≤ B (p + a)) (q : ι) :
    B q ⊓ LinearMap.range f ≤ (A (q - a)).map f := by
  classical
  letI := hA.chooseDecomposition
  letI := hB.chooseDecomposition
  rintro _ ⟨hy, x, rfl⟩
  refine ⟨(DirectSum.decompose A x (q - a) : M),
    (DirectSum.decompose A x (q - a)).2, ?_⟩
  calc
    f (DirectSum.decompose A x (q - a) : M) =
        (DirectSum.decompose B (f x) ((q - a) + a) : N) :=
      (decomposeMapHomogeneous A B hf x (q - a)).symm
    _ = f x := by
      rw [sub_add_cancel]
      exact DirectSum.decompose_of_mem_same B hy

private theorem isInternalComapSubtypeOfIsHomogeneous
    {ι R M : Type*} [DecidableEq ι] [Ring R] [AddCommGroup M] [Module R M]
    (A : ι → Submodule R M) [DirectSum.Decomposition A]
    (S : Submodule R M) (hS : DirectSum.SetLike.IsHomogeneous A S) :
    DirectSum.IsInternal (fun p ↦ (A p).comap S.subtype) := by
  classical
  have hsub : Function.Injective S.subtype := S.subtype_injective
  have hind : iSupIndep (fun p ↦ S ⊓ A p) :=
    (DirectSum.Decomposition.isInternal (ℳ := A)).submodule_iSupIndep.mono
      (fun _ ↦ inf_le_right)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep_def.mpr (fun p ↦ ?_), ?_⟩
  · rw [disjoint_iff, ← (Submodule.map_injective_of_injective hsub).eq_iff,
      Submodule.map_inf S.subtype hsub, Submodule.map_bot]
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype]
    exact disjoint_iff.mp (iSupIndep_def.mp hind p)
  · rw [← (Submodule.map_injective_of_injective hsub).eq_iff,
      Submodule.map_subtype_top]
    simp only [Submodule.map_iSup, Submodule.map_comap_subtype]
    apply le_antisymm (iSup_le (fun _ ↦ inf_le_left))
    intro x hx
    rw [← DirectSum.sum_support_decompose A x]
    exact Submodule.sum_mem _ fun p _ ↦
      Submodule.mem_iSup_of_mem p ⟨hS p hx, (DirectSum.decompose A x p).2⟩

private theorem isInternalMapMkQOfIsHomogeneous
    {ι R M : Type*} [DecidableEq ι] [Ring R] [AddCommGroup M] [Module R M]
    (A : ι → Submodule R M) [DirectSum.Decomposition A]
    (B : Submodule R M) (hB : DirectSum.SetLike.IsHomogeneous A B) :
    DirectSum.IsInternal (fun p ↦ (A p).map B.mkQ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep_def.mpr (fun p ↦ ?_), ?_⟩
  · rw [Submodule.disjoint_def]
    intro ξ hξp hξrest
    obtain ⟨a, ha, haξ⟩ := Submodule.mem_map.mp hξp
    have hξrest' : ξ ∈ ⨆ q : {q // q ≠ p}, (A q).map B.mkQ := by
      simpa [iSup_subtype] using hξrest
    rw [← Submodule.map_iSup] at hξrest'
    obtain ⟨b, hb, hbξ⟩ := Submodule.mem_map.mp hξrest'
    have hb0 : (DirectSum.decompose A b p : M) = 0 := by
      refine Submodule.iSup_induction (fun q : {q // q ≠ p} ↦ A q)
        (motive := fun x ↦ (DirectSum.decompose A x p : M) = 0) hb ?_ ?_ ?_
      · intro q x hx
        exact DirectSum.decompose_of_mem_ne A hx q.property
      · simp
      · intro x y hx hy
        simp [hx, hy]
    have hc : a - b ∈ B := by
      rw [← Submodule.ker_mkQ B, LinearMap.mem_ker, map_sub, haξ, hbξ, sub_self]
    have hcproj : (DirectSum.decompose A (a - b) p : M) ∈ B := hB p hc
    have haB : a ∈ B := by
      simpa [DirectSum.decompose_sub, DirectSum.decompose_of_mem_same A ha, hb0] using hcproj
    calc
      ξ = B.mkQ a := haξ.symm
      _ = 0 := (Submodule.Quotient.mk_eq_zero B).mpr haB
  · rw [← Submodule.map_iSup,
      (DirectSum.Decomposition.isInternal (ℳ := A)).submodule_iSup_eq_top,
      Submodule.map_top, Submodule.range_mkQ]

/-! ## Graded exact couples -/

/-- A **graded exact couple** of `R`-modules over the degree group `ι`: an
`ExactCouple R` with internal direct-sum `ι`-gradings `gradD`, `gradE` of its two
modules, such that the three maps `i, j, k` are homogeneous of degrees
`di, dj, dk`. -/
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
  /-- `E` is internally direct-sum decomposed by `gradE`. -/
  internalE : DirectSum.IsInternal gradE
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
    ExactCouple.coe_derK_mk]
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
    C.internalD.inf_range_le_map C.internalD C.homog_i p ⟨hy, hyr⟩
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
derived gradings `derGradD`, `derGradE` and degrees `di, dj - di, dk`.  The image
`im i` is graded because `i` is homogeneous.  The homology `ker d / im d` is
graded because the kernel and image of a homogeneous map are homogeneous and an
internal grading descends through a homogeneous quotient. -/

/-- `im i = range C.i` is a graded submodule: the derived `D`-grading `derGradD`
is internally direct. -/
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

/-- The homology `ker d / im d` inherits an internal grading from `E`: the
derived `E`-grading `derGradE` is internally direct. -/
theorem isInternal_derGradE : DirectSum.IsInternal C.derGradE := by
  letI : DirectSum.Decomposition C.gradE := C.internalE.chooseDecomposition
  let Z : ι → Submodule R (LinearMap.ker C.d) :=
    fun p ↦ (C.gradE p).comap (LinearMap.ker C.d).subtype
  have hker : DirectSum.SetLike.IsHomogeneous C.gradE (LinearMap.ker C.d) := by
    intro p x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← decomposeMapHomogeneous C.gradE C.gradE C.homog_d x p, hx]
    simp
  have hZ : DirectSum.IsInternal Z :=
    isInternalComapSubtypeOfIsHomogeneous C.gradE (LinearMap.ker C.d) hker
  letI : DirectSum.Decomposition Z := hZ.chooseDecomposition
  have hsubtype : ∀ p, (Z p).map (LinearMap.ker C.d).subtype ≤ C.gradE (p + 0) := by
    intro p
    rintro _ ⟨z, hz, rfl⟩
    simpa [Z] using hz
  have hdecomp_coe (e : LinearMap.ker C.d) (p : ι) :
      ((DirectSum.decompose Z e p : LinearMap.ker C.d) : C.E) =
        (DirectSum.decompose C.gradE (e : C.E) p : C.E) := by
    have h := (decomposeMapHomogeneous Z C.gradE hsubtype e p).symm
    rw [add_zero] at h
    exact h
  have himd : DirectSum.SetLike.IsHomogeneous Z C.imd := by
    intro p e he
    rw [Submodule.mem_comap] at he ⊢
    obtain ⟨x, hx⟩ := he
    change C.d x = (e : C.E) at hx
    refine ⟨(DirectSum.decompose C.gradE x (p - (C.dj + C.dk)) : C.E), ?_⟩
    have hmap := decomposeMapHomogeneous
      C.gradE C.gradE C.homog_d x (p - (C.dj + C.dk))
    rw [sub_add_cancel] at hmap
    calc
      C.d (DirectSum.decompose C.gradE x (p - (C.dj + C.dk)) : C.E) =
          (DirectSum.decompose C.gradE (C.d x) p : C.E) := hmap.symm
      _ = (DirectSum.decompose C.gradE (e : C.E) p : C.E) := by rw [hx]
      _ = ((DirectSum.decompose Z e p : LinearMap.ker C.d) : C.E) :=
        (hdecomp_coe e p).symm
  change DirectSum.IsInternal (fun p ↦ (Z p).map C.imd.mkQ)
  exact isInternalMapMkQOfIsHomogeneous Z C.imd himd

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
  internalE := C.isInternal_derGradE
  homog_i := C.derI_homog
  homog_j := C.derJ_homog
  homog_k := C.derK_homog

@[simp] theorem derivedGraded_toExactCouple :
    C.derivedGraded.toExactCouple = C.toExactCouple.derivedCouple := rfl

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
@[simp] theorem gradedDerived_toExactCouple (r : ℕ) :
    (C.gradedDerived r).toExactCouple = C.toExactCouple.derived r := by
  induction r with
  | zero => rfl
  | succ n ih =>
    change ((C.gradedDerived n).toExactCouple).derivedCouple =
      (C.toExactCouple.derived n).derivedCouple
    rw [ih]

/-- The module on the `r`-th page, equipped below with `pageGrading`. -/
noncomputable abbrev gradedPage (r : ℕ) : Type u := (C.gradedDerived r).E

/-- The internal grading on the `r`-th page. -/
noncomputable abbrev pageGrading (r : ℕ) (p : ι) : Submodule R (C.gradedPage r) :=
  (C.gradedDerived r).gradE p

/-- Every page grading is an internal direct sum. -/
theorem pageGrading_isInternal (r : ℕ) : DirectSum.IsInternal (C.pageGrading r) :=
  (C.gradedDerived r).internalE

/-- The differential on the `r`-th graded page. -/
noncomputable abbrev gradedPageDiff (r : ℕ) : C.gradedPage r →ₗ[R] C.gradedPage r :=
  (C.gradedDerived r).d

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

/-- The differential on `gradedPage r` is homogeneous of degree
`(dj + dk) - r • di` for its internal page grading. -/
theorem pageGrading_homog_diff (r : ℕ) (p : ι) :
    (C.pageGrading r p).map (C.gradedPageDiff r) ≤
      C.pageGrading r (p + ((C.dj + C.dk) - r • C.di)) :=
  C.gradedDerived_homog_d r p

end GradedExactCouple
