/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact couples and their derived couples

This file formalizes **exact couples** and the **derived couple** construction,
following the Stacks Project (tag 011P) and the classical references (Weibel,
*An Introduction to Homological Algebra*, §5.9; McCleary, *A User's Guide to
Spectral Sequences*, §2.2; exact couples originate with Massey, *Exact couples
in algebraic topology*, Ann. of Math. 56 (1952)).

An exact couple is the most economical packaging of the data that produces a
spectral sequence: two modules `D`, `E` and three maps

```
      i
  D ─────→ D
   ↖      ╱
  k ╲    ╱ j
     ╲  ↙
      E
```

which are exact at each of the three vertices (`im i = ker j`, `im j = ker k`,
`im k = ker i`).  Setting `d = j ∘ k : E → E` one has `d ∘ d = 0` (because
`k ∘ j = 0`), and the **derived couple** `(D', E', i', j', k')` with

* `D' = im i`,
* `E' = ker d / im d = H(E, d)`,

is again an exact couple.  Iterating produces the pages `E, E', E'', …` of a
spectral sequence, with `E_{r+1}` the homology of `(E_r, d_r)` by construction.

## Main definitions and results

* `ExactCouple R` : the structure (two `R`-modules and three exact maps).
* `ExactCouple.d`, `ExactCouple.d_comp_d` : the differential `d = j ∘ k` and
  `d ∘ d = 0`.
* `ExactCouple.derivedCouple : ExactCouple R` : the derived couple, whose three
  exactness conditions (`derived_exact_ij`, `derived_exact_jk`,
  `derived_exact_ki`) are the content of the derived-couple theorem.
* `ExactCouple.derived : ℕ → ExactCouple R`, `ExactCouple.page`,
  `ExactCouple.pageDiff` : the spectral sequence obtained by iterating, with
  `pageDiff_comp_pageDiff` (`d_r ∘ d_r = 0`) and `pageSuccEquiv`
  (`E_{r+1} ≃ₗ ker d_r / im d_r`, definitionally the identity).

Everything is at the level of modules over an arbitrary ring `R`.

## Tags

exact couple, derived couple, spectral sequence
-/

@[expose] public section

open LinearMap Submodule Function

universe u

/-- An **exact couple** of `R`-modules: modules `D`, `E` with maps
`i : D → D`, `j : D → E`, `k : E → D` that are exact at each vertex. -/
structure ExactCouple (R : Type*) [Ring R] where
  /-- The module on the two `i`-related vertices. -/
  D : Type u
  /-- The module on the `E`-vertex. -/
  E : Type u
  [addCommGroupD : AddCommGroup D]
  [moduleD : Module R D]
  [addCommGroupE : AddCommGroup E]
  [moduleE : Module R E]
  /-- The self-map `i : D → D`. -/
  i : D →ₗ[R] D
  /-- The map `j : D → E`. -/
  j : D →ₗ[R] E
  /-- The map `k : E → D`. -/
  k : E →ₗ[R] D
  /-- Exactness at the target `D`:  `im i = ker j`. -/
  exact_ij : Function.Exact i j
  /-- Exactness at `E`:  `im j = ker k`. -/
  exact_jk : Function.Exact j k
  /-- Exactness at the source `D`:  `im k = ker i`. -/
  exact_ki : Function.Exact k i

attribute [instance] ExactCouple.addCommGroupD ExactCouple.moduleD
  ExactCouple.addCommGroupE ExactCouple.moduleE

namespace ExactCouple

variable {R : Type*} [Ring R] (C : ExactCouple.{u} R)

/-! ## The three "consecutive composites vanish" facts -/

@[simp] lemma j_i (x : C.D) : C.j (C.i x) = 0 := C.exact_ij.apply_apply_eq_zero x

@[simp] lemma k_j (x : C.D) : C.k (C.j x) = 0 := C.exact_jk.apply_apply_eq_zero x

@[simp] lemma i_k (x : C.E) : C.i (C.k x) = 0 := C.exact_ki.apply_apply_eq_zero x

lemma j_comp_i : C.j ∘ₗ C.i = 0 := by ext x; simp

lemma k_comp_j : C.k ∘ₗ C.j = 0 := by ext x; simp

lemma i_comp_k : C.i ∘ₗ C.k = 0 := by ext x; simp

/-! ## The differential `d = j ∘ k` on `E` -/

/-- The differential `d = j ∘ k : E → E`. -/
def d : C.E →ₗ[R] C.E := C.j ∘ₗ C.k

@[simp] lemma d_apply (x : C.E) : C.d x = C.j (C.k x) := rfl

/-- `d ∘ d = 0`, because `k ∘ j = 0`. -/
lemma d_d (x : C.E) : C.d (C.d x) = 0 := by simp [d]

lemma d_comp_d : C.d ∘ₗ C.d = 0 := by ext x; simp

/-! ## The pieces of the derived couple

`D' = im i`, and `E' = ker d / im d` (`im d ≤ ker d` since `d² = 0`).  We model
`im d` inside `ker d` as `imd`, the comap of `range d` along the inclusion. -/

/-- `D' = im i`, the module on the two `i'`-related vertices of the derived couple. -/
abbrev derD : Submodule R C.D := LinearMap.range C.i

/-- `im d`, viewed as a submodule of `ker d`. -/
abbrev imd : Submodule R (LinearMap.ker C.d) :=
  (LinearMap.range C.d).comap (LinearMap.ker C.d).subtype

/-- `E' = ker d / im d`, the homology of `(E, d)`; the `E`-vertex of the derived couple. -/
abbrev derE : Type u := (LinearMap.ker C.d) ⧸ C.imd

/-- The quotient map `ker d → E'`. -/
abbrev derEmk : (LinearMap.ker C.d) →ₗ[R] C.derE := (C.imd).mkQ

/-! ### The derived map `i' : D' → D'` -/

/-- `i' : D' → D'`, the restriction of `i` (which maps `im i` into `im i`). -/
def derI : C.derD →ₗ[R] C.derD :=
  C.i.restrict (fun y _ ↦ ⟨y, rfl⟩)

@[simp] lemma derI_coe (y : C.derD) : (C.derI y : C.D) = C.i (y : C.D) :=
  rfl

/-! ### The universal map `J : D → E'` and the derived map `j'` -/

/-- The auxiliary map `J : D → E'`, `x ↦ [j x]`, used to construct the derived
map `j'`.  Note `j x ∈ ker d` for every `x` (as `k (j x) = 0`), so this is
defined on all of `D`; it vanishes on `ker i = im k`, hence descends to
`j' : D' → E'`. -/
def derJAux : C.D →ₗ[R] C.derE :=
  C.derEmk ∘ₗ C.j.codRestrict (LinearMap.ker C.d) (fun x ↦ by simp [LinearMap.mem_ker])

@[simp] lemma derJAux_apply (x : C.D) :
    C.derJAux x = Submodule.Quotient.mk ⟨C.j x, by simp [LinearMap.mem_ker]⟩ := rfl

/-- `J` vanishes on `ker i = im k`. -/
lemma ker_i_le_ker_derJAux : LinearMap.ker C.i ≤ LinearMap.ker C.derJAux := by
  intro x hx
  obtain ⟨e, rfl⟩ := (C.exact_ki x).mp hx
  rw [LinearMap.mem_ker, derJAux_apply]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [Submodule.mem_comap]
  exact ⟨e, by simp⟩

/-- `j' : D' → E'`, induced by `J : D → E'` via the first isomorphism theorem. -/
noncomputable def derJ : C.derD →ₗ[R] C.derE :=
  (Submodule.liftQ (LinearMap.ker C.i) C.derJAux C.ker_i_le_ker_derJAux).comp
    (C.i.quotKerEquivRange).symm.toLinearMap

@[simp] lemma derJ_apply (x : C.D) : C.derJ ⟨C.i x, ⟨x, rfl⟩⟩ = C.derJAux x := by
  rw [derJ, LinearMap.comp_apply]
  have : (C.i.quotKerEquivRange).symm ⟨C.i x, ⟨x, rfl⟩⟩ = (LinearMap.ker C.i).mkQ x :=
    C.i.quotKerEquivRange_symm_apply_image x _
  rw [LinearEquiv.coe_coe, this]
  exact Submodule.liftQ_apply _ _ _

/-- `range j' = range J`: every element of `D' = im i` is `i x`, and
`j' (i x) = J x`. -/
lemma range_derJ : LinearMap.range C.derJ = LinearMap.range C.derJAux := by
  apply le_antisymm
  · rintro _ ⟨⟨y, x, rfl⟩, rfl⟩
    exact ⟨x, (C.derJ_apply x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨C.i x, x, rfl⟩, C.derJ_apply x⟩

/-! ### The derived map `k' : E' → D'` -/

/-- `k` maps `ker d` into `D' = im i`:  if `d e = 0` then `j (k e) = 0`, so
`k e ∈ ker j = im i`. -/
lemma k_mem_derD {e : C.E} (he : e ∈ LinearMap.ker C.d) : C.k e ∈ C.derD :=
  (C.exact_ij _).mp (by simpa [LinearMap.mem_ker] using he)

/-- The auxiliary map for the derived `k'`: the map `k` restricted to `ker d`,
corestricted to `D' = im i`. -/
def derKAux : (LinearMap.ker C.d) →ₗ[R] C.derD :=
  C.k.restrict (fun _e he ↦ C.k_mem_derD he)

@[simp] lemma derKAux_coe (e : LinearMap.ker C.d) : (C.derKAux e : C.D) = C.k (e : C.E) :=
  rfl

/-- `derKAux` vanishes on `im d`, so it descends to `k' : E' → D'`. -/
lemma imd_le_ker_derKAux : C.imd ≤ LinearMap.ker C.derKAux := by
  intro e he
  rw [Submodule.mem_comap] at he
  obtain ⟨e0, he0⟩ := he
  have he0' : (↑e : C.E) = C.d e0 := he0.symm
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  rw [derKAux_coe, Submodule.coe_zero, he0']
  simp

/-- `k' : E' → D'`, induced by `derKAux` on the quotient. -/
def derK : C.derE →ₗ[R] C.derD :=
  Submodule.liftQ C.imd C.derKAux C.imd_le_ker_derKAux

@[simp] lemma derK_mk (e : LinearMap.ker C.d) :
    (C.derK (Submodule.Quotient.mk e) : C.D) = C.k (e : C.E) := by
  rw [derK, Submodule.liftQ_apply, derKAux_coe]

/-! ## The derived couple is exact

The three diagram chases below are the content of the derived-couple theorem. -/

/-- Exactness of the derived couple at the target `D'`:  `im i' = ker j'`. -/
theorem derived_exact_ij : Function.Exact C.derI C.derJ := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · -- ker j' ⊆ im i'
    rintro ⟨y, x, rfl⟩ hy
    rw [LinearMap.mem_ker, derJ_apply, derJAux_apply] at hy
    -- `[j x] = 0`  means  `j x ∈ im d`, i.e. `j x = j (k w)` for some `w`
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    -- `hw : C.d w = C.j x`
    have hw' : C.j (C.k w) = C.j x := by have h := hw; simp only [d_apply] at h; exact h
    -- so `j (x - k w) = 0`, hence `x - k w = i x'`
    have hxke : C.j (x - C.k w) = 0 := by rw [map_sub, hw']; simp
    obtain ⟨x', hx'⟩ := (C.exact_ij _).mp hxke
    -- then `i x = i (i x')`, i.e. `⟨i x, _⟩ = i' ⟨i x', _⟩`
    refine ⟨⟨C.i x', ⟨x', rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change C.i (C.i x') = C.i x
    rw [hx', map_sub, i_k, sub_zero]
  · -- im i' ⊆ ker j'
    rintro _ ⟨⟨y, x, rfl⟩, rfl⟩
    rw [LinearMap.mem_ker]
    change C.derJ ⟨C.i (C.i x), ⟨C.i x, rfl⟩⟩ = 0
    rw [derJ_apply, derJAux_apply]
    -- `j (i x) = 0`, so this class is literally zero
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ⟨0, by simp⟩)

/-- Exactness of the derived couple at `E'`:  `im j' = ker k'`. -/
theorem derived_exact_jk : Function.Exact C.derJ C.derK := by
  rw [LinearMap.exact_iff, range_derJ]
  apply le_antisymm
  · -- ker k' ⊆ im J
    intro ξ hξ
    obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.mem_ker] at hξ
    have hke : C.k (e : C.E) = 0 := by
      have := congrArg (Subtype.val) hξ
      rwa [derK_mk, Submodule.coe_zero] at this
    obtain ⟨a, ha⟩ := (C.exact_jk (e : C.E)).mp hke
    refine ⟨a, ?_⟩
    rw [derJAux_apply]
    apply congrArg
    exact Subtype.ext ha
  · -- im J ⊆ ker k'
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker, derJAux_apply]
    apply Subtype.ext
    rw [derK_mk, Submodule.coe_zero]
    simp

/-- Exactness of the derived couple at the source `D'`:  `im k' = ker i'`. -/
theorem derived_exact_ki : Function.Exact C.derK C.derI := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · -- ker i' ⊆ im k'
    rintro ⟨y, x, rfl⟩ hy
    rw [LinearMap.mem_ker] at hy
    have hiy : C.i (C.i x) = 0 := by
      have := congrArg (Subtype.val) hy
      rwa [derI_coe, Submodule.coe_zero] at this
    -- `i (i x) = 0`, so `i x ∈ ker i = im k`, say `i x = k e`
    obtain ⟨e, he⟩ := (C.exact_ki _).mp hiy
    -- and `e ∈ ker d`, since `d e = j (k e) = j (i x) = 0`
    have hedk : e ∈ LinearMap.ker C.d := by
      rw [LinearMap.mem_ker, d_apply, he]; simp
    refine ⟨Submodule.Quotient.mk ⟨e, hedk⟩, ?_⟩
    apply Subtype.ext
    rw [derK_mk, he]
  · -- im k' ⊆ ker i'
    intro y hy
    obtain ⟨ξ, rfl⟩ := hy
    obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [derI_coe, derK_mk, Submodule.coe_zero]
    simp

/-- The **derived couple** of an exact couple. -/
@[stacks 011P]
noncomputable def derivedCouple : ExactCouple.{u} R where
  D := C.derD
  E := C.derE
  i := C.derI
  j := C.derJ
  k := C.derK
  exact_ij := C.derived_exact_ij
  exact_jk := C.derived_exact_jk
  exact_ki := C.derived_exact_ki

/-! ## The spectral sequence of an exact couple

Iterating the derived-couple construction yields the pages of a spectral
sequence:  `E_0 = E`, `E_{r+1} = ker d_r / im d_r`. -/

/-- The `r`-th derived couple (`derived 0 = C`). -/
noncomputable def derived (C : ExactCouple.{u} R) : ℕ → ExactCouple.{u} R
  | 0 => C
  | (n + 1) => (C.derived n).derivedCouple

@[simp] lemma derived_zero : C.derived 0 = C := rfl

@[simp] lemma derived_succ (r : ℕ) :
    C.derived (r + 1) = (C.derived r).derivedCouple := rfl

/-- The `r`-th page `E_r` of the spectral sequence of the exact couple. -/
noncomputable abbrev page (r : ℕ) : Type u := (C.derived r).E

/-- The `r`-th differential `d_r : E_r → E_r`. -/
noncomputable def pageDiff (r : ℕ) : C.page r →ₗ[R] C.page r := (C.derived r).d

@[simp] lemma pageDiff_zero : C.pageDiff 0 = C.d := rfl

/-- `d_r ∘ d_r = 0`. -/
theorem pageDiff_comp_pageDiff (r : ℕ) : C.pageDiff r ∘ₗ C.pageDiff r = 0 :=
  (C.derived r).d_comp_d

/-- By construction, `E_{r+1}` is the homology of `(E_r, d_r)`: the identity
map is a linear equivalence `E_{r+1} ≃ₗ ker d_r / im d_r`. -/
noncomputable def pageSuccEquiv (r : ℕ) :
    C.page (r + 1) ≃ₗ[R]
      (LinearMap.ker (C.pageDiff r) ⧸
        (LinearMap.range (C.pageDiff r)).comap (LinearMap.ker (C.pageDiff r)).subtype) :=
  LinearEquiv.refl R _

end ExactCouple
