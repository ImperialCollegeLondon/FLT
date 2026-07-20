/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# The spectral sequence of a filtered complex

This file formalizes the construction of the spectral sequence associated to a
filtered differential object, following the Stacks Project:

* Section 12.23 (tag 012A): "Spectral sequences: filtered differential objects"
* Section 12.24 (tag 012K): "Spectral sequences: filtered complexes"

Following the Stacks Project, the heart of the construction is the case of a
*filtered differential object*: a module `M` equipped with a differential
`d : M →ₗ[R] M` satisfying `d ∘ d = 0` and a decreasing filtration
`F : ℤ → Submodule R M` preserved by `d`.  The spectral sequence of a filtered
*complex* has a separate graded implementation in `FilteredComplex.lean`, whose
underlying object is mathlib's standard `CochainComplex (ModuleCat R) ℤ`.  The
final section of this file also records a lower-level totalization constructor
from raw consecutive differential data.

## Main definitions

Let `K = (M, d, F)` be a filtered differential module.  For `r p : ℤ` we define
(compare Stacks, tag 012A; we use the equivalent presentation of `E_r^p` as a
quotient of the "absolute" cocycle module, which agrees with the Stacks
subquotient-of-`gr^p` definition by the modular law):

* `K.Z r p = F^p ∩ d⁻¹(F^{p+r})`, the `r`-cocycles;
* `K.B r p = (F^{p+1} ∩ d⁻¹(F^{p+r})) + (F^p ∩ d(F^{p-r+1}))`, the `r`-boundaries;
* `K.page r p = Z_r^p / B_r^p`, the `p`-th piece of the `r`-th page `E_r^p`;
* `K.dPage r p : E_r^p → E_r^{p+r}`, the differential `d_r`, induced by `d`.

## Main results

* `dPageAux_comp`: `d_r ∘ d_r = 0`.
* `pageSuccEquiv`: the main theorem, `E_{r+1}^p ≅ ker(d_r^p) / im(d_r^{p-r})`,
  i.e. each page is the homology of the previous one.
* `Z_zero`, `B_zero`: identification of the `0`-th page with the associated
  graded `gr^p M = F^p/F^{p+1}` (so `E_1 = H(gr M)` is the case `r = 0` of the
  main theorem).

## Convergence

We define the limit term `pageInf` from the intersection of the normalised
cycle submodules and the union of the normalised boundary submodules in `E₀`.
We separately define `associatedGradedHomology`, the canonical abutment candidate
`(F^p ∩ ker d)/((F^{p+1} ∩ ker d) + (F^p ∩ im d))`, and the induced
filtration `FH` on `H = ker d / im d`.

* `pageEquivAssociatedGradedHomology` identifies a bounded finite page with the
  associated-graded target, while `pageInfEquivAssociatedGradedHomology`
  identifies the actual limit term with the same target under those bounds;
* `dPage_eq_zero`, `dPageFrom_eq_zero` : the differentials at position `p` vanish
  in the same range, so the spectral sequence degenerates there;
* `associatedGradedHomologyEquivGrHomology` identifies that target with `gr^p H`,
  and `pageInfEquivGrHomology` gives the resulting bounded identification of
  `E_∞^p`;
* `pageEquivGrHomologyOfBounded` : **convergence** — for an exhaustive
  (`F^a = ⊤`) and bounded (`F^b = ⊥`) filtration, `E_r^p ≅ gr^p H` for all
  sufficiently large `r` (explicitly `b ≤ p + r` and `p - r + 1 ≤ a`), and in
  particular the pages stabilize (`pageSuccEquivPageOfBounded`).

For *unbounded* filtrations we prove standard convergence ingredients:
`iInf_Z_eq_abutmentZ` (cocycle convergence, assuming only separatedness
`⨅ q, F^q = ⊥`), `iSup_B_eq_abutmentB` (boundary convergence, assuming
exhaustiveness `⨆ q, F^q = ⊤` and a one-sided bound), and — under
`F^{p+r} = ⊥` and exhaustiveness only, with the filtration possibly unbounded
below — the natural surjections `pageTransition : E_r^p ↠ E_{r'}^p` and
`pageToAssociatedGradedHomology`, together with the elementwise eventual-kernel
statement `exists_pageTransition_eq_zero`.
-/

@[expose] public section

open Submodule LinearMap

variable (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]

/-- A **filtered differential module**: a module together with a differential squaring
to zero and a decreasing `ℤ`-indexed filtration compatible with the differential.
This is (the module version of) a *filtered differential object* in the sense of the
Stacks Project, tag 012A. -/
structure FilteredDifferentialModule where
  /-- The differential. -/
  d : M →ₗ[R] M
  /-- The differential squares to zero. -/
  d_squared : ∀ x : M, d (d x) = 0
  /-- The filtration. -/
  F : ℤ → Submodule R M
  /-- The filtration is decreasing. -/
  F_le : ∀ p : ℤ, F (p + 1) ≤ F p
  /-- The differential preserves the filtration. -/
  d_mem_F : ∀ (p : ℤ), ∀ x ∈ F p, d x ∈ F p

namespace FilteredDifferentialModule

variable {R M} (K : FilteredDifferentialModule R M)

lemma F_mono {p q : ℤ} (h : p ≤ q) : K.F q ≤ K.F p := by
  obtain ⟨n, rfl⟩ := Int.le.dest h
  clear h
  induction n with
  | zero => simp
  | succ m ih =>
    refine le_trans ?_ ih
    have e : (p + (m + 1 : ℕ) : ℤ) = (p + m) + 1 := by push_cast; ring
    rw [e]
    exact K.F_le (p + m)

/-! ## Cocycles, boundaries, and the pages -/

/-- The `r`-cocycles in filtration degree `p`:  `Z_r^p = F^p ∩ d⁻¹(F^{p+r})`. -/
def Z (r p : ℤ) : Submodule R M := K.F p ⊓ (K.F (p + r)).comap K.d

/-- The `r`-boundaries in filtration degree `p`:
`B_r^p = (F^{p+1} ∩ d⁻¹(F^{p+r})) + (F^p ∩ d(F^{p-r+1}))`. -/
def B (r p : ℤ) : Submodule R M :=
  (K.F (p + 1) ⊓ (K.F (p + r)).comap K.d) ⊔ (K.F p ⊓ (K.F (p - r + 1)).map K.d)

lemma mem_Z {r p : ℤ} {x : M} :
    x ∈ K.Z r p ↔ x ∈ K.F p ∧ K.d x ∈ K.F (p + r) := by
  simp only [Z, Submodule.mem_inf, Submodule.mem_comap]

lemma mem_B_left {r p : ℤ} {u : M} (h1 : u ∈ K.F (p + 1)) (h2 : K.d u ∈ K.F (p + r)) :
    u ∈ K.B r p :=
  Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨h1, Submodule.mem_comap.mpr h2⟩)

lemma mem_B_right {r p : ℤ} {v : M} (hv : v ∈ K.F (p - r + 1)) (h : K.d v ∈ K.F p) :
    K.d v ∈ K.B r p :=
  Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨h, Submodule.mem_map_of_mem hv⟩)

lemma B_cases {r p : ℤ} {x : M} (hx : x ∈ K.B r p) :
    ∃ u v, u ∈ K.F (p + 1) ∧ K.d u ∈ K.F (p + r) ∧ v ∈ K.F (p - r + 1) ∧
      K.d v ∈ K.F p ∧ x = u + K.d v := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw2
  exact ⟨u, v, hu1, Submodule.mem_comap.mp hu2, hv, hw1, rfl⟩

lemma B_le_Z (r p : ℤ) : K.B r p ≤ K.Z r p := by
  intro x hx
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (K.mem_Z.mpr ⟨K.F_le p hu1, hu2⟩) (K.mem_Z.mpr ⟨hdv, ?_⟩)
  rw [K.d_squared v]
  exact zero_mem _

lemma Z_succ_le (r p : ℤ) : K.Z (r + 1) p ≤ K.Z r p := by
  intro x hx
  obtain ⟨h1, h2⟩ := K.mem_Z.mp hx
  exact K.mem_Z.mpr ⟨h1, K.F_le (p + r) (by rwa [show p + r + 1 = p + (r + 1) by ring])⟩

/-- The `p`-th piece `E_r^p = Z_r^p / B_r^p` of the `r`-th page of the spectral sequence. -/
abbrev page (r p : ℤ) := ↥(K.Z r p) ⧸ (K.B r p).comap (K.Z r p).subtype

/-! ## The differentials on the pages -/

lemma d_mem_Z {r p q : ℤ} (hq : q = p + r) {x : M} (hx : x ∈ K.Z r p) :
    K.d x ∈ K.Z r q := by
  subst hq
  obtain ⟨h1, h2⟩ := K.mem_Z.mp hx
  refine K.mem_Z.mpr ⟨h2, ?_⟩
  rw [K.d_squared x]
  exact zero_mem _

lemma d_mem_B {r p q : ℤ} (hq : q = p + r) {x : M} (hx : x ∈ K.B r p) :
    K.d x ∈ K.B r q := by
  subst hq
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hx
  rw [map_add]
  refine add_mem ?_ ?_
  · refine K.mem_B_right ?_ hu2
    rwa [show p + r - r + 1 = p + 1 by ring]
  · rw [K.d_squared v]
    exact zero_mem _

/-- The differential restricted to the `r`-cocycles, with flexible target degree. -/
def dZ (r p q : ℤ) (hq : q = p + r) : ↥(K.Z r p) →ₗ[R] ↥(K.Z r q) :=
  K.d.restrict fun _ hx ↦ K.d_mem_Z hq hx

@[simp] lemma dZ_coe (r p q : ℤ) (hq : q = p + r) (x : ↥(K.Z r p)) :
    (K.dZ r p q hq x : M) = K.d x := rfl

/-- The differential on the `r`-th page, with flexible target degree. -/
def dPageAux (r p q : ℤ) (hq : q = p + r) : K.page r p →ₗ[R] K.page r q :=
  Submodule.mapQ _ _ (K.dZ r p q hq) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe] at hx ⊢
    exact K.d_mem_B hq hx)

@[simp] lemma dPageAux_mk (r p q : ℤ) (hq : q = p + r) (x : ↥(K.Z r p)) :
    K.dPageAux r p q hq (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.dZ r p q hq x) :=
  Submodule.mapQ_apply _ _ _ x

/-- The differential `d_r : E_r^p → E_r^{p+r}` of the `r`-th page. -/
abbrev dPage (r p : ℤ) : K.page r p →ₗ[R] K.page r (p + r) :=
  K.dPageAux r p (p + r) rfl

/-- The differential `d_r : E_r^{p-r} → E_r^p` of the `r`-th page, arriving at
filtration degree `p`. -/
abbrev dPageFrom (r p : ℤ) : K.page r (p - r) →ₗ[R] K.page r p :=
  K.dPageAux r (p - r) p (by ring)

/-- The composite of two consecutive differentials on a page vanishes. -/
theorem dPageAux_comp (r p q s : ℤ) (hq : q = p + r) (hs : s = q + r) :
    (K.dPageAux r q s hs).comp (K.dPageAux r p q hq) = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  have h0 : K.dZ r q s hs (K.dZ r p q hq ζ) = 0 := by
    apply Subtype.ext
    simp [K.d_squared]
  simp [h0]

theorem dPage_comp_dPageFrom (r p : ℤ) :
    (K.dPage r p).comp (K.dPageFrom r p) = 0 :=
  K.dPageAux_comp r (p - r) p (p + r) (by ring) rfl

lemma range_dPageFrom_le_ker_dPage (r p : ℤ) :
    range (K.dPageFrom r p) ≤ ker (K.dPage r p) := by
  rintro _ ⟨η, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, K.dPage_comp_dPageFrom, LinearMap.zero_apply]

/-! ## The zeroth page is the associated graded -/

lemma Z_zero (p : ℤ) : K.Z 0 p = K.F p := by
  refine le_antisymm inf_le_left fun x hx ↦ ?_
  refine K.mem_Z.mpr ⟨hx, ?_⟩
  rw [show p + (0 : ℤ) = p by ring]
  exact K.d_mem_F p x hx

lemma B_zero (p : ℤ) : K.B 0 p = K.F (p + 1) := by
  apply le_antisymm
  · refine sup_le inf_le_left (le_trans inf_le_right ?_)
    rw [show p - 0 + 1 = p + 1 by ring]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact K.d_mem_F _ y hy
  · intro x hx
    refine K.mem_B_left hx ?_
    rw [show p + (0 : ℤ) = p by ring]
    exact K.d_mem_F p x (K.F_le p hx)

/-! ## The main theorem: each page is the homology of the previous one

We construct a surjection `Z_{r+1}^p → ker(d_r^p)/im(d_r^{p-r})` and compute its
kernel to be `B_{r+1}^p`, yielding the isomorphism
`E_{r+1}^p ≅ ker(d_r^p)/im(d_r^{p-r})`. -/

section MainTheorem

variable (r p : ℤ)

/-- The natural map `Z_{r+1}^p → ker(d_r : E_r^p → E_r^{p+r})`. -/
def toKer : ↥(K.Z (r + 1) p) →ₗ[R] ↥(ker (K.dPage r p)) :=
  LinearMap.codRestrict _
    (((K.B r p).comap (K.Z r p).subtype).mkQ.comp (Submodule.inclusion (K.Z_succ_le r p)))
    fun z ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, K.dPageAux_mk,
        Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe, Submodule.coe_inclusion]
      have hz := K.mem_Z.mp z.2
      refine K.mem_B_left ?_ ?_
      · rw [show p + r + 1 = p + (r + 1) by ring]
        exact hz.2
      · rw [K.d_squared]
        exact zero_mem _

@[simp] lemma toKer_coe (z : ↥(K.Z (r + 1) p)) :
    (K.toKer r p z : K.page r p) =
      Submodule.Quotient.mk (Submodule.inclusion (K.Z_succ_le r p) z) := rfl

lemma toKer_surjective : Function.Surjective (K.toKer r p) := by
  rintro ⟨c, hc⟩
  obtain ⟨⟨z, hzZ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.mem_ker, K.dPageAux_mk, Submodule.Quotient.mk_eq_zero] at hc
  simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe] at hc
  -- `hc : K.d z ∈ K.B r (p + r)`; decompose `d z = u + d v`.
  obtain ⟨u, v, hu1, hu2, hv, hdv, hsum⟩ := K.B_cases hc
  rw [show p + r - r + 1 = p + 1 by ring] at hv
  have hzF : z ∈ K.F p := (K.mem_Z.mp hzZ).1
  have hz' : z - v ∈ K.Z (r + 1) p := by
    refine K.mem_Z.mpr ⟨sub_mem hzF (K.F_le p hv), ?_⟩
    have hdz' : K.d (z - v) = u := by
      rw [map_sub, hsum]
      abel
    rw [hdz', show p + (r + 1) = p + r + 1 by ring]
    exact hu1
  refine ⟨⟨z - v, hz'⟩, ?_⟩
  apply Subtype.ext
  rw [toKer_coe, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
    Submodule.coe_inclusion]
  have : z - v - z = -v := by abel
  rw [this]
  exact neg_mem (K.mem_B_left hv hdv)

/-- The composite `Z_{r+1}^p → ker(d_r^p) → ker(d_r^p)/im(d_r^{p-r})`. -/
def toHomology : ↥(K.Z (r + 1) p) →ₗ[R]
    ↥(ker (K.dPage r p)) ⧸ (range (K.dPageFrom r p)).comap (ker (K.dPage r p)).subtype :=
  ((range (K.dPageFrom r p)).comap (ker (K.dPage r p)).subtype).mkQ.comp (K.toKer r p)

lemma toHomology_surjective : Function.Surjective (K.toHomology r p) := by
  have h := (Submodule.mkQ_surjective
    ((range (K.dPageFrom r p)).comap (ker (K.dPage r p)).subtype)).comp
      (K.toKer_surjective r p)
  simpa [toHomology, LinearMap.coe_comp] using h

/-- Membership in the image of `d_r^{p-r}`, in concrete terms. -/
lemma mk_mem_range_dPageFrom_iff (z : ↥(K.Z r p)) :
    Submodule.Quotient.mk z ∈ range (K.dPageFrom r p) ↔
      ∃ y ∈ K.Z r (p - r), K.d y - ↑z ∈ K.B r p := by
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ η
    refine ⟨↑y, y.2, ?_⟩
    rw [K.dPageAux_mk, Submodule.Quotient.eq] at hη
    simpa only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      dZ_coe] using hη
  · rintro ⟨y, hyZ, hy⟩
    refine ⟨Submodule.Quotient.mk ⟨y, hyZ⟩, ?_⟩
    rw [K.dPageAux_mk, Submodule.Quotient.eq]
    simpa only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      dZ_coe] using hy

/-- Key computation, "⊇" direction: an element of `B_{r+1}^p` becomes, on the `r`-th
page, a boundary for `d_r`. -/
lemma exists_of_mem_B_succ {z : M} (hzB : z ∈ K.B (r + 1) p) :
    ∃ y ∈ K.Z r (p - r), K.d y - z ∈ K.B r p := by
  obtain ⟨u, v, hu1, hu2, hv, hdv, hsum⟩ := K.B_cases hzB
  rw [show p - (r + 1) + 1 = p - r by ring] at hv
  refine ⟨v, K.mem_Z.mpr ⟨hv, by rw [show p - r + r = p by ring]; exact hdv⟩, ?_⟩
  have : K.d v - z = -u := by
    rw [hsum]
    abel
  rw [this]
  refine neg_mem (K.mem_B_left hu1 (K.F_le (p + r) ?_))
  rw [show p + r + 1 = p + (r + 1) by ring]
  exact hu2

/-- Key computation, "⊆" direction: an `(r+1)`-cocycle which is a `d_r`-boundary on
the `r`-th page lies in `B_{r+1}^p`. -/
lemma mem_B_succ_of {z : M} (hz : z ∈ K.Z (r + 1) p)
    (h : ∃ y ∈ K.Z r (p - r), K.d y - z ∈ K.B r p) : z ∈ K.B (r + 1) p := by
  obtain ⟨y, hyZ, hy⟩ := h
  obtain ⟨hy1, hy2⟩ := K.mem_Z.mp hyZ
  rw [show p - r + r = p by ring] at hy2
  obtain ⟨u, t, hu1, hu2, ht, hdt, hsum⟩ := K.B_cases hy
  -- `hsum : d y - z = u + d t`.  Set `y' := y - t`; then `z = d y' - u`.
  have hy' : y - t ∈ K.F (p - r) := sub_mem hy1 (K.F_le (p - r) ht)
  have hdy' : K.d (y - t) ∈ K.F p := by
    rw [map_sub]
    exact sub_mem hy2 hdt
  have hu_eq : K.d (y - t) - z = u := by
    calc K.d (y - t) - z = K.d y - K.d t - z := by rw [map_sub]
      _ = K.d y - z - K.d t := by abel
      _ = u := by rw [hsum]; abel
  have hz_eq : z = K.d (y - t) - u := by
    rw [← hu_eq]
    abel
  have hdu : K.d u ∈ K.F (p + (r + 1)) := by
    have hdu_eq : K.d u = -K.d z := by
      rw [← hu_eq, map_sub, K.d_squared (y - t), zero_sub]
    rw [hdu_eq]
    exact neg_mem (K.mem_Z.mp hz).2
  rw [hz_eq]
  refine sub_mem ?_ (K.mem_B_left hu1 hdu)
  refine K.mem_B_right ?_ hdy'
  rw [show p - (r + 1) + 1 = p - r by ring]
  exact hy'

lemma ker_toHomology :
    ker (K.toHomology r p) = (K.B (r + 1) p).comap (K.Z (r + 1) p).subtype := by
  ext ζ
  obtain ⟨z, hz⟩ := ζ
  simp only [LinearMap.mem_ker, toHomology, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, toKer_coe]
  rw [K.mk_mem_range_dPageFrom_iff]
  simp only [Submodule.coe_inclusion]
  exact ⟨fun h ↦ K.mem_B_succ_of r p hz h, fun h ↦ K.exists_of_mem_B_succ r p h⟩

/-- **The spectral sequence of a filtered differential module** (Stacks Project,
tag 012A): the `(r+1)`-st page is canonically isomorphic to the homology of the
`r`-th page with respect to the differential `d_r`. -/
noncomputable def pageSuccEquiv :
    K.page (r + 1) p ≃ₗ[R]
      (↥(ker (K.dPage r p)) ⧸
        (range (K.dPageFrom r p)).comap (ker (K.dPage r p)).subtype) :=
  (Submodule.quotEquivOfEq _ _ (K.ker_toHomology r p).symm).trans
    ((K.toHomology r p).quotKerEquivOfSurjective (K.toHomology_surjective r p))

end MainTheorem

/-! ## Convergence

The limit term is defined from the stable subquotient of `E₀`:

`Z_∞^p = ⋂_r (Z_r^p + F^{p+1})`,
`B_∞^p = ⋃_r (B_r^p + F^{p+1})`, and
`E_∞^p = Z_∞^p / B_∞^p`.

The sums with `F^{p+1}` are essential: the cycles and boundaries defining the
limit are subobjects of `E₀^p = F^p/F^{p+1}`, not generally nested submodules
of the ambient module `M`.

Separately, we define the associated-graded homology target
`(F^p ∩ ker d) / ((F^{p+1} ∩ ker d) + (F^p ∩ im d))` and prove the two
halves of the convergence theorem for suitably bounded filtrations, following
the Stacks Project (tag 012A):

* **Stabilization**: if `F^{p+r} = ⊥` and `F^{p-r+1} = ⊤` (which happens for all
  sufficiently large `r` when the filtration is exhaustive and bounded), then
  both `E_r^p` and the limit term `E_∞^p` identify with the associated-graded
  target (`pageEquivAssociatedGradedHomology`,
  `pageInfEquivAssociatedGradedHomology`), and
  the differentials into and out of position `p` vanish (`dPage_eq_zero`,
  `dPageFrom_eq_zero`).
* **Identification of the target**: the associated-graded target is canonically
  isomorphic to `gr^p H(M, d)`, where the homology
  `H = ker d / im d` carries the filtration `F^p H = im(F^p ∩ ker d → H)`
  (`associatedGradedHomologyEquivGrHomology`).

Combining the two (`pageEquivGrHomologyOfBounded`) gives the classical
convergence statement `E_r^p ⇒ gr^p H` for bounded filtrations: the pages at
each `p` are eventually constant, equal to the associated graded of homology. -/

section Convergence

lemma range_d_le_ker_d : range K.d ≤ ker K.d := by
  rintro _ ⟨x, rfl⟩
  exact LinearMap.mem_ker.mpr (K.d_squared x)

/-- The cycle submodule used to present the associated-graded homology target:
`F^p ∩ ker d`.  It agrees with the unnormalised intersection of the `Z_r^p`
under separatedness, but is not the limit-cycle submodule in general. -/
def abutmentZ (p : ℤ) : Submodule R M := K.F p ⊓ ker K.d

/-- The boundary submodule used to present the associated-graded homology target:
`(F^{p+1} ∩ ker d) + (F^p ∩ im d)`. -/
def abutmentB (p : ℤ) : Submodule R M :=
  (K.F (p + 1) ⊓ ker K.d) ⊔ (K.F p ⊓ range K.d)

lemma abutmentZ_le_ker (p : ℤ) : K.abutmentZ p ≤ ker K.d := inf_le_right

lemma abutmentB_le_abutmentZ (p : ℤ) : K.abutmentB p ≤ K.abutmentZ p :=
  sup_le (inf_le_inf_right _ (K.F_le p))
    (inf_le_inf_left _ (K.range_d_le_ker_d))

/-- The associated-graded homology target, presented inside the filtered module. -/
abbrev associatedGradedHomology (p : ℤ) :=
  ↥(K.abutmentZ p) ⧸ (K.abutmentB p).comap (K.abutmentZ p).subtype

/-- The numerator of the limit term, represented in `F^p` before quotienting
by `F^{p+1}`: `⋂_{r ≥ 0} (Z_r^p + F^{p+1})`. -/
def limitZ (p : ℤ) : Submodule R M :=
  ⨅ r : ℕ, K.Z (r : ℤ) p ⊔ K.F (p + 1)

/-- The denominator of the limit term, represented in `F^p` before quotienting
by `F^{p+1}`: `⋃_{r ≥ 0} (B_r^p + F^{p+1})`. -/
def limitB (p : ℤ) : Submodule R M :=
  ⨆ r : ℕ, K.B (r : ℤ) p ⊔ K.F (p + 1)

lemma Z_mono {r s p : ℤ} (h : r ≤ s) : K.Z s p ≤ K.Z r p := by
  intro x hx
  obtain ⟨hxF, hdx⟩ := K.mem_Z.mp hx
  exact K.mem_Z.mpr ⟨hxF, K.F_mono (by omega) hdx⟩

lemma normalizedZ_antitone (p : ℤ) :
    Antitone fun r : ℕ ↦ K.Z (r : ℤ) p ⊔ K.F (p + 1) := by
  intro r s h
  exact sup_le_sup (K.Z_mono (by exact_mod_cast h)) le_rfl

lemma normalizedB_monotone (p : ℤ) :
    Monotone fun r : ℕ ↦ K.B (r : ℤ) p ⊔ K.F (p + 1) := by
  intro r s h
  refine sup_le ?_ le_sup_right
  intro x hx
  obtain ⟨u, v, hu1, -, hv, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
  exact K.mem_B_right (K.F_mono (by omega) hv) hdv

lemma B_sup_F_le_Z_sup_F (r s p : ℤ) :
    K.B r p ⊔ K.F (p + 1) ≤ K.Z s p ⊔ K.F (p + 1) := by
  refine sup_le ?_ le_sup_right
  intro x hx
  obtain ⟨u, v, hu1, -, -, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
  exact K.mem_Z.mpr ⟨hdv, by rw [K.d_squared]; exact zero_mem _⟩

lemma limitB_le_limitZ (p : ℤ) : K.limitB p ≤ K.limitZ p := by
  refine iSup_le fun r ↦ le_iInf fun s ↦ ?_
  exact K.B_sup_F_le_Z_sup_F (r : ℤ) (s : ℤ) p

lemma limitZ_le_F (p : ℤ) : K.limitZ p ≤ K.F p := by
  refine le_trans (iInf_le (fun r : ℕ ↦ K.Z (r : ℤ) p ⊔ K.F (p + 1)) 0) ?_
  exact sup_le inf_le_left (K.F_le p)

lemma F_le_limitB (p : ℤ) : K.F (p + 1) ≤ K.limitB p :=
  le_trans le_sup_right (le_iSup (fun r : ℕ ↦ K.B (r : ℤ) p ⊔ K.F (p + 1)) 0)

/-- The limit term `E_∞^p`: the quotient of the intersection of the normalised
cycle submodules by the union of the normalised boundary submodules.  It need
not be equal to any finite page without a stabilization hypothesis. -/
abbrev pageInf (p : ℤ) :=
  ↥(K.limitZ p) ⧸ (K.limitB p).comap (K.limitZ p).subtype

/-! ### Stabilization -/

lemma Z_eq_abutmentZ {r p : ℤ} (hbot : K.F (p + r) = ⊥) : K.Z r p = K.abutmentZ p := by
  unfold Z abutmentZ
  rw [hbot, Submodule.comap_bot]

lemma B_eq_abutmentB {r p : ℤ} (hbot : K.F (p + r) = ⊥) (htop : K.F (p - r + 1) = ⊤) :
    K.B r p = K.abutmentB p := by
  unfold B abutmentB
  rw [hbot, htop, Submodule.comap_bot, Submodule.map_top]

/-- Once the cocycles have stabilized, the numerator of the limit term is the
cycle numerator of the associated-graded target, together with the copy of
`F^{p+1}` used to represent submodules of `E₀^p`. -/
lemma limitZ_eq_abutmentZ_sup_F {r p : ℤ} (hbot : K.F (p + r) = ⊥) :
    K.limitZ p = K.abutmentZ p ⊔ K.F (p + 1) := by
  let N := r.toNat
  have hrN : r ≤ (N : ℤ) := Int.self_le_toNat r
  have hbotN : K.F (p + (N : ℤ)) = ⊥ :=
    le_bot_iff.mp (hbot ▸ K.F_mono (by omega))
  apply le_antisymm
  · refine le_trans (iInf_le (fun s : ℕ ↦ K.Z (s : ℤ) p ⊔ K.F (p + 1)) N) ?_
    rw [K.Z_eq_abutmentZ hbotN]
  · refine le_iInf fun s ↦ sup_le ?_ le_sup_right
    intro x hx
    exact Submodule.mem_sup_left (K.mem_Z.mpr ⟨hx.1, by
      rw [LinearMap.mem_ker.mp hx.2]
      exact zero_mem _⟩)

/-- Once both sides have stabilized, the denominator of the limit term is the
boundary denominator of the associated-graded target, together with the copy
of `F^{p+1}` used to represent submodules of `E₀^p`. -/
lemma limitB_eq_abutmentB_sup_F {r p : ℤ} (hbot : K.F (p + r) = ⊥)
    (htop : K.F (p - r + 1) = ⊤) :
    K.limitB p = K.abutmentB p ⊔ K.F (p + 1) := by
  let N := r.toNat
  have hrN : r ≤ (N : ℤ) := Int.self_le_toNat r
  have hbotN : K.F (p + (N : ℤ)) = ⊥ :=
    le_bot_iff.mp (hbot ▸ K.F_mono (by omega))
  have htopN : K.F (p - (N : ℤ) + 1) = ⊤ :=
    top_le_iff.mp (htop ▸ K.F_mono (by omega))
  apply le_antisymm
  · refine iSup_le fun s ↦ sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨u, v, hu1, -, -, hdv, rfl⟩ := K.B_cases hx
    refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
    exact Submodule.mem_sup_right ⟨hdv, ⟨v, rfl⟩⟩
  · refine le_trans ?_ (le_iSup (fun s : ℕ ↦ K.B (s : ℤ) p ⊔ K.F (p + 1)) N)
    rw [K.B_eq_abutmentB hbotN htopN]

/-- Intersecting the associated-graded cycle numerator with the normalized
boundary denominator recovers the unnormalized boundary denominator. -/
lemma abutmentZ_inf_abutmentB_sup_F_eq_abutmentB (p : ℤ) :
    K.abutmentZ p ⊓ (K.abutmentB p ⊔ K.F (p + 1)) = K.abutmentB p := by
  apply le_antisymm
  · rintro x ⟨hxZ, hx⟩
    obtain ⟨b, hb, f, hf, rfl⟩ := Submodule.mem_sup.mp hx
    refine add_mem hb ?_
    have hfker : f ∈ ker K.d := by
      have hbker : b ∈ ker K.d := (K.abutmentB_le_abutmentZ p hb).2
      simpa using sub_mem hxZ.2 hbker
    exact Submodule.mem_sup_left ⟨hf, hfker⟩
  · exact le_inf (K.abutmentB_le_abutmentZ p) le_sup_left

/-- The associated-graded homology target in its normalized presentation inside
`E₀^p`: adjoining `F^{p+1}` to both numerator and denominator does not change
the quotient. -/
noncomputable def associatedGradedHomologyEquivNormalized (p : ℤ) :
    K.associatedGradedHomology p ≃ₗ[R]
      (↥(K.abutmentZ p ⊔ K.F (p + 1)) ⧸
        ((K.abutmentB p ⊔ K.F (p + 1)).comap (K.abutmentZ p ⊔ K.F (p + 1)).subtype)) := by
  let e := LinearMap.quotientInfEquivSupQuotient
    (K.abutmentZ p) (K.abutmentB p ⊔ K.F (p + 1))
  have hdom :
      (K.abutmentB p).comap (K.abutmentZ p).subtype =
        (K.abutmentZ p).comap (K.abutmentZ p).subtype ⊓
          (K.abutmentB p ⊔ K.F (p + 1)).comap (K.abutmentZ p).subtype := by
    ext x
    change (x : M) ∈ K.abutmentB p ↔
      (x : M) ∈ K.abutmentZ p ∧ (x : M) ∈ K.abutmentB p ⊔ K.F (p + 1)
    rw [← Submodule.mem_inf, K.abutmentZ_inf_abutmentB_sup_F_eq_abutmentB]
  have hnum : K.abutmentZ p ⊔ (K.abutmentB p ⊔ K.F (p + 1)) =
      K.abutmentZ p ⊔ K.F (p + 1) := by
    rw [← sup_assoc, sup_eq_left.mpr (K.abutmentB_le_abutmentZ p)]
  rw [hnum] at e
  exact (Submodule.quotEquivOfEq _ _ hdom).trans e

/-- Under two-sided local bounds, the actual limit term is canonically
isomorphic to the associated-graded homology target. -/
noncomputable def pageInfEquivAssociatedGradedHomology {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) (htop : K.F (p - r + 1) = ⊤) :
    K.pageInf p ≃ₗ[R] K.associatedGradedHomology p := by
  let e₁ : K.pageInf p ≃ₗ[R]
      (↥(K.abutmentZ p ⊔ K.F (p + 1)) ⧸
        ((K.abutmentB p ⊔ K.F (p + 1)).comap (K.abutmentZ p ⊔ K.F (p + 1)).subtype)) :=
    Submodule.Quotient.equiv _ _
      (LinearEquiv.ofEq _ _ (K.limitZ_eq_abutmentZ_sup_F hbot)) (by
        have hB := K.limitB_eq_abutmentB_sup_F hbot htop
        ext x
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa [hB] using hy
        · intro hx
          refine ⟨(LinearEquiv.ofEq _ _ (K.limitZ_eq_abutmentZ_sup_F hbot)).symm x, ?_,
            (LinearEquiv.ofEq _ _ (K.limitZ_eq_abutmentZ_sup_F hbot)).apply_symm_apply x⟩
          simpa [hB] using hx)
  exact e₁.trans (K.associatedGradedHomologyEquivNormalized p).symm

/-- Once `r` is large enough that `F^{p+r} = ⊥` and `F^{p-r+1} = ⊤`, the `r`-th
page at `p` is canonically isomorphic to the associated-graded homology target. -/
noncomputable def pageEquivAssociatedGradedHomology {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) (htop : K.F (p - r + 1) = ⊤) :
    K.page r p ≃ₗ[R] K.associatedGradedHomology p :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)) (by
    have hB := K.B_eq_abutmentB hbot htop
    ext ξ
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨η, hη, rfl⟩
      rw [← hB]
      simpa using hη
    · intro hξ
      refine ⟨(LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)).symm ξ, ?_,
        (LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)).apply_symm_apply ξ⟩
      rw [hB]
      simpa using hξ)

/-- Under two-sided local bounds, the finite `r`-th page has stabilized to the
limit term. -/
noncomputable def pageEquivPageInf {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) (htop : K.F (p - r + 1) = ⊤) :
    K.page r p ≃ₗ[R] K.pageInf p :=
  (K.pageEquivAssociatedGradedHomology hbot htop).trans
    (K.pageInfEquivAssociatedGradedHomology hbot htop).symm

/-- Beyond the bound of the filtration, the differential leaving position `p` vanishes. -/
theorem dPage_eq_zero {r p : ℤ} (hbot : K.F (p + r) = ⊥) : K.dPage r p = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  have h0 : K.dZ r p (p + r) rfl ζ = 0 := by
    apply Subtype.ext
    have h := (K.mem_Z.mp ζ.2).2
    rw [hbot] at h
    simpa using h
  simp [h0]

/-- Beyond the bound of the filtration, the differential arriving at position `p` vanishes. -/
theorem dPageFrom_eq_zero {r p : ℤ} (htop : K.F (p - r + 1) = ⊤) :
    K.dPageFrom r p = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, K.dPageAux_mk, LinearMap.zero_comp,
    LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, dZ_coe]
  have h2 : K.d (ζ : M) ∈ K.F p := by
    have h := (K.mem_Z.mp ζ.2).2
    rwa [show p - r + r = p by ring] at h
  refine K.mem_B_right ?_ h2
  rw [htop]
  exact Submodule.mem_top

/-! ### The associated-graded target -/

/-- The homology `H = ker d / im d` of the underlying differential module. -/
abbrev homology := ↥(ker K.d) ⧸ (range K.d).comap (ker K.d).subtype

/-- The filtration induced on homology: `F^p H` is the image of `F^p ∩ ker d` in `H`. -/
def FH (p : ℤ) : Submodule R K.homology :=
  ((K.abutmentZ p).comap (ker K.d).subtype).map ((range K.d).comap (ker K.d).subtype).mkQ

lemma mem_FH_iff {p : ℤ} {h : K.homology} :
    h ∈ K.FH p ↔ ∃ z : ↥(ker K.d), (z : M) ∈ K.F p ∧ Submodule.Quotient.mk z = h := by
  constructor
  · intro hh
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hh
    have := Submodule.mem_comap.mp hζ
    exact ⟨ζ, (Submodule.mem_inf.mp this).1, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨z, Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨hz, z.2⟩), rfl⟩

/-- The natural map from the filtered cycle submodule `F^p ∩ ker d` to `F^p H`. -/
def toFH (p : ℤ) : ↥(K.abutmentZ p) →ₗ[R] ↥(K.FH p) :=
  LinearMap.codRestrict _
    (((range K.d).comap (ker K.d).subtype).mkQ.comp (Submodule.inclusion (K.abutmentZ_le_ker p)))
    fun x ↦ Submodule.mem_map_of_mem (Submodule.mem_comap.mpr x.2)

@[simp] lemma toFH_coe (p : ℤ) (x : ↥(K.abutmentZ p)) :
    (K.toFH p x : K.homology) =
      Submodule.Quotient.mk (Submodule.inclusion (K.abutmentZ_le_ker p) x) := rfl

lemma toFH_surjective (p : ℤ) : Function.Surjective (K.toFH p) := by
  rintro ⟨h, hmem⟩
  obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hmem
  refine ⟨⟨↑ζ, Submodule.mem_comap.mp hζ⟩, ?_⟩
  apply Subtype.ext
  rw [toFH_coe]
  exact congrArg _ (Subtype.ext rfl)

/-- The composite from filtered cycles to
`F^p H → F^p H / F^{p+1} H = gr^p H`. -/
def toGrH (p : ℤ) : ↥(K.abutmentZ p) →ₗ[R]
    (↥(K.FH p) ⧸ (K.FH (p + 1)).comap (K.FH p).subtype) :=
  ((K.FH (p + 1)).comap (K.FH p).subtype).mkQ.comp (K.toFH p)

lemma toGrH_surjective (p : ℤ) : Function.Surjective (K.toGrH p) := by
  have h := (Submodule.mkQ_surjective
    ((K.FH (p + 1)).comap (K.FH p).subtype)).comp (K.toFH_surjective p)
  simpa [toGrH, LinearMap.coe_comp] using h

lemma ker_toGrH (p : ℤ) :
    ker (K.toGrH p) = (K.abutmentB p).comap (K.abutmentZ p).subtype := by
  ext ξ
  obtain ⟨x, hx⟩ := ξ
  have hxF : x ∈ K.F p := (Submodule.mem_inf.mp hx).1
  simp only [LinearMap.mem_ker, toGrH, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, toFH_coe]
  rw [K.mem_FH_iff]
  constructor
  · rintro ⟨z, hzF, hzeq⟩
    rw [Submodule.Quotient.eq] at hzeq
    have hd : (z : M) - x ∈ range K.d := by
      simpa using hzeq
    have h1 : (z : M) ∈ K.abutmentB p :=
      Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hzF, z.2⟩)
    have h2 : -((z : M) - x) ∈ K.abutmentB p :=
      neg_mem (Submodule.mem_sup_right
        (Submodule.mem_inf.mpr ⟨sub_mem (K.F_le p hzF) hxF, hd⟩))
    have h3 := add_mem h1 h2
    have heq : (z : M) + -((z : M) - x) = x := by abel
    rwa [heq] at h3
  · intro hxB
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hxB
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
    refine ⟨⟨u, hu2⟩, hu1, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have heq : u - x = -w := by
      rw [← hsum]
      abel
    rw [heq]
    exact neg_mem hw2

/-- **Identification of the associated-graded target** with `gr^p H`, the associated
graded of homology with respect to the induced filtration.  This is not an
unconditional identification of the limit term `pageInf`. -/
noncomputable def associatedGradedHomologyEquivGrHomology (p : ℤ) :
    K.associatedGradedHomology p ≃ₗ[R]
      (↥(K.FH p) ⧸ (K.FH (p + 1)).comap (K.FH p).subtype) :=
  (Submodule.quotEquivOfEq _ _ (K.ker_toGrH p).symm).trans
    ((K.toGrH p).quotKerEquivOfSurjective (K.toGrH_surjective p))

/-- Under two-sided local bounds, the limit term is the associated graded of
the induced filtration on homology. -/
noncomputable def pageInfEquivGrHomology {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) (htop : K.F (p - r + 1) = ⊤) :
    K.pageInf p ≃ₗ[R]
      (↥(K.FH p) ⧸ (K.FH (p + 1)).comap (K.FH p).subtype) :=
  (K.pageInfEquivAssociatedGradedHomology hbot htop).trans
    (K.associatedGradedHomologyEquivGrHomology p)

/-! ### Convergence for bounded filtrations -/

/-- **Convergence of the spectral sequence of a filtered differential module**
(Stacks Project, tag 012A): if the filtration is exhaustive (`F^a = ⊤`) and bounded
(`F^b = ⊥`), then for every `r` large enough (explicitly, `b ≤ p + r` and
`p - r + 1 ≤ a`) the `r`-th page at `p` is canonically isomorphic to `gr^p H` of
homology.  In particular the pages at each `p` are eventually constant. -/
noncomputable def pageEquivGrHomologyOfBounded {a b r p : ℤ}
    (ha : K.F a = ⊤) (hb : K.F b = ⊥) (hr1 : b ≤ p + r) (hr2 : p - r + 1 ≤ a) :
    K.page r p ≃ₗ[R] (↥(K.FH p) ⧸ (K.FH (p + 1)).comap (K.FH p).subtype) :=
  (K.pageEquivAssociatedGradedHomology (le_bot_iff.mp (hb ▸ K.F_mono hr1))
    (top_le_iff.mp (ha ▸ K.F_mono hr2))).trans
      (K.associatedGradedHomologyEquivGrHomology p)

/-- For bounded filtrations, consecutive large pages at `p` are isomorphic:
the spectral sequence stabilizes. -/
noncomputable def pageSuccEquivPageOfBounded {a b r p : ℤ}
    (ha : K.F a = ⊤) (hb : K.F b = ⊥) (hr1 : b ≤ p + r) (hr2 : p - r + 1 ≤ a) :
    K.page (r + 1) p ≃ₗ[R] K.page r p :=
  (K.pageEquivGrHomologyOfBounded ha hb (by omega) (by omega)).trans
    (K.pageEquivGrHomologyOfBounded ha hb hr1 hr2).symm

/-! ### Convergence for unbounded filtrations

Useful convergence ingredients do not require the filtration to be two-sided
bounded. We prove the standard unbounded convergence ingredients:

* If the filtration is **separated** (`⨅ q, F^q = ⊥`) then the raw cocycles
  converge: `⨅ r, Z_r^p = abutmentZ p` (`iInf_Z_eq_abutmentZ`).  No other hypothesis is
  needed.
* If the filtration is **exhaustive** (`⨆ q, F^q = ⊤`) and `F^{p+r₀} = ⊥` for some
  `r₀` (boundedness on the *cocycle* side only — the filtration may well be
  unbounded below, so this covers e.g. exhaustive filtrations indexed by all of
  `ℤ`), then the raw boundaries converge: `⨆_{r ≥ r₀}, B_r^p = abutmentB p`
  (`iSup_B_eq_abutmentB`).
* Under the same one-sided hypothesis `F^{p+r} = ⊥` there are natural
  surjections from `E_r^p` to later pages and to the associated-graded homology
  target (`pageTransition`, `pageToAssociatedGradedHomology`).  Assuming
  exhaustiveness, every element in the kernel of the latter map dies on some
  finite page (`exists_pageTransition_eq_zero`).  These are the elementwise
  ingredients for the usual convergence/colimit statement; no categorical
  colimit universal property is asserted here.

Without such hypotheses convergence genuinely fails (Boardman); the missing
ingredient in general is completeness of the filtration. -/

lemma F_add_bot_of_le {r r' p : ℤ} (hbot : K.F (p + r) = ⊥) (h : r ≤ r') :
    K.F (p + r') = ⊥ :=
  le_bot_iff.mp (hbot ▸ K.F_mono (by omega))

/-- **Cocycle convergence for separated filtrations**: if `⨅ q, F^q = ⊥`, then
`abutmentZ p = F^p ∩ ker d` is exactly the intersection of the raw `Z_r^p`, with no
boundedness hypothesis. -/
theorem iInf_Z_eq_abutmentZ (hsep : ⨅ q, K.F q = ⊥) (p : ℤ) :
    ⨅ r : ℤ, K.Z r p = K.abutmentZ p := by
  ext x
  simp only [Submodule.mem_iInf, mem_Z, abutmentZ, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · intro h
    refine ⟨(h 0).1, ?_⟩
    have hmem : K.d x ∈ ⨅ q, K.F q := by
      refine Submodule.mem_iInf _ |>.mpr fun q ↦ ?_
      have h2 := (h (q - p)).2
      rwa [show p + (q - p) = q by ring] at h2
    rw [hsep] at hmem
    simpa using hmem
  · rintro ⟨h1, h2⟩ r
    exact ⟨h1, by rw [h2]; exact zero_mem _⟩

lemma directed_F : Directed (· ≤ ·) K.F :=
  fun i j ↦ ⟨min i j, K.F_mono (min_le_left i j), K.F_mono (min_le_right i j)⟩

lemma B_le_abutmentB {r p : ℤ} (hbot : K.F (p + r) = ⊥) : K.B r p ≤ K.abutmentB p := by
  refine sup_le ?_ ?_
  · rw [hbot, Submodule.comap_bot]
    exact le_sup_left
  · refine le_trans (inf_le_inf_left _ ?_) le_sup_right
    rintro x hx
    obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨y, rfl⟩

lemma B_mono_of_bot {r r' p : ℤ} (hbot : K.F (p + r) = ⊥) (h : r ≤ r') :
    K.B r p ≤ K.B r' p := by
  refine sup_le ?_ ?_
  · rw [hbot, Submodule.comap_bot]
    refine le_trans (inf_le_inf_left _ ?_) le_sup_left
    intro x hx
    exact Submodule.mem_comap.mpr (by rw [LinearMap.mem_ker.mp hx]; exact zero_mem _)
  · exact le_trans (inf_le_inf_left _ (Submodule.map_mono (K.F_mono (by omega)))) le_sup_right

/-- **Boundary convergence for exhaustive filtrations**: if `⨆ q, F^q = ⊤` and
`F^{p+r₀} = ⊥`, then `abutmentB p` is exactly the directed union of the raw `B_r^p`
for `r ≥ r₀`, even when the filtration is unbounded below. -/
theorem iSup_B_eq_abutmentB {r₀ p : ℤ} (hbot : K.F (p + r₀) = ⊥) (hexh : ⨆ q, K.F q = ⊤) :
    ⨆ r, ⨆ (_ : r₀ ≤ r), K.B r p = K.abutmentB p := by
  apply le_antisymm
  · exact iSup₂_le fun r hr ↦ K.B_le_abutmentB (K.F_add_bot_of_le hbot hr)
  · refine sup_le ?_ ?_
    · refine le_trans ?_ (le_iSup₂ (f := fun r _ ↦ K.B r p) r₀ le_rfl)
      refine le_trans (inf_le_inf_left _ ?_) le_sup_left
      intro x hx
      exact Submodule.mem_comap.mpr (by rw [LinearMap.mem_ker.mp hx]; exact zero_mem _)
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx2
      have hy : y ∈ ⨆ q, K.F q := hexh.symm ▸ Submodule.mem_top
      obtain ⟨q, hq⟩ := (Submodule.mem_iSup_of_directed _ K.directed_F).mp hy
      have hmem : K.d y ∈ K.B (max r₀ (p + 1 - q)) p :=
        K.mem_B_right
          (K.F_mono (by have := le_max_right r₀ (p + 1 - q); omega) hq) hx1
      exact le_iSup₂ (f := fun r _ ↦ K.B r p) (max r₀ (p + 1 - q)) (le_max_left _ _) hmem

/-- Once `F^{p+r} = ⊥`, the natural surjection from the `r`-th page onto the
associated-graded homology target.  This is a map to the abutment candidate,
not an unconditional map to the limit term `pageInf`. -/
def pageToAssociatedGradedHomology {r p : ℤ} (hbot : K.F (p + r) = ⊥) :
    K.page r p →ₗ[R] K.associatedGradedHomology p :=
  Submodule.mapQ _ _ (LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)).toLinearMap (by
    intro ζ hζ
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearEquiv.coe_ofEq_apply] at hζ ⊢
    exact K.B_le_abutmentB hbot hζ)

@[simp] lemma pageToAssociatedGradedHomology_mk {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) (ζ : ↥(K.Z r p)) :
    K.pageToAssociatedGradedHomology hbot (Submodule.Quotient.mk ζ) =
      Submodule.Quotient.mk (LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot) ζ) :=
  Submodule.mapQ_apply _ _ _ ζ

lemma pageToAssociatedGradedHomology_surjective {r p : ℤ}
    (hbot : K.F (p + r) = ⊥) :
    Function.Surjective (K.pageToAssociatedGradedHomology hbot) := by
  intro ξ
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  refine ⟨Submodule.Quotient.mk ((LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)).symm ζ), ?_⟩
  rw [K.pageToAssociatedGradedHomology_mk hbot]
  exact congrArg _ ((LinearEquiv.ofEq _ _ (K.Z_eq_abutmentZ hbot)).apply_symm_apply ζ)

/-- The natural surjection `E_r^p ↠ E_{r'}^p` for `r ≤ r'`, in the range where the
cocycles have stabilized. -/
def pageTransition {r r' p : ℤ} (hbot : K.F (p + r) = ⊥) (h : r ≤ r') :
    K.page r p →ₗ[R] K.page r' p :=
  Submodule.mapQ _ _ (LinearEquiv.ofEq _ _ (by
      rw [K.Z_eq_abutmentZ hbot, K.Z_eq_abutmentZ (K.F_add_bot_of_le hbot h)])).toLinearMap (by
    intro ζ hζ
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearEquiv.coe_ofEq_apply] at hζ ⊢
    exact K.B_mono_of_bot hbot h hζ)

@[simp] lemma pageTransition_mk {r r' p : ℤ} (hbot : K.F (p + r) = ⊥) (h : r ≤ r')
    (ζ : ↥(K.Z r p)) :
    K.pageTransition hbot h (Submodule.Quotient.mk ζ) =
      Submodule.Quotient.mk ((LinearEquiv.ofEq _ _ (by
        rw [K.Z_eq_abutmentZ hbot, K.Z_eq_abutmentZ (K.F_add_bot_of_le hbot h)])) ζ) :=
  Submodule.mapQ_apply _ _ _ ζ

/-- The surjections onto later pages are compatible with the map to the
associated-graded homology target. -/
theorem pageToAssociatedGradedHomology_comp_pageTransition {r r' p : ℤ}
    (hbot : K.F (p + r) = ⊥)
    (h : r ≤ r') :
    (K.pageToAssociatedGradedHomology (K.F_add_bot_of_le hbot h)).comp
      (K.pageTransition hbot h) = K.pageToAssociatedGradedHomology hbot := by
  apply Submodule.linearMap_qext
  ext ζ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, pageTransition_mk,
    pageToAssociatedGradedHomology_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- **Eventual-kernel statement for an unbounded filtration**: suppose `F^{p+r} = ⊥`
(one-sided bound) and the filtration is exhaustive (`⨆ q, F^q = ⊤`), but otherwise
arbitrary — in particular possibly unbounded below.  Then every element of the
kernel of the map from `E_r^p` to the associated-graded homology target already
vanishes on some finite page `E_{r'}^p`. -/
theorem exists_pageTransition_eq_zero {r p : ℤ} (hbot : K.F (p + r) = ⊥)
    (hexh : ⨆ q, K.F q = ⊤) (ξ : K.page r p)
    (hξ : K.pageToAssociatedGradedHomology hbot ξ = 0) :
    ∃ (r' : ℤ) (h : r ≤ r'), K.pageTransition hbot h ξ = 0 := by
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [K.pageToAssociatedGradedHomology_mk hbot, Submodule.Quotient.mk_eq_zero] at hξ
  have hζB : (ζ : M) ∈ K.abutmentB p := by
    simpa using hξ
  obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hζB
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw2
  have hy : y ∈ ⨆ q, K.F q := hexh.symm ▸ Submodule.mem_top
  obtain ⟨q, hq⟩ := (Submodule.mem_iSup_of_directed _ K.directed_F).mp hy
  refine ⟨max r (p + 1 - q), le_max_left _ _, ?_⟩
  rw [K.pageTransition_mk, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_ofEq_apply]
  rw [← hsum]
  refine add_mem (K.mem_B_left hu1 ?_) ?_
  · rw [LinearMap.mem_ker.mp hu2]
    exact zero_mem _
  · exact K.mem_B_right
      (K.F_mono (by have := le_max_right r (p + 1 - q); omega) hq) hw1

end Convergence

/-! ## Functoriality and the mapping lemma

A morphism of filtered differential modules induces morphisms on all pages,
commuting with the differentials (`mapPage`, `mapPage_dPageAux`).  The
**mapping lemma** (`Hom.bijective_mapPage_succ`, `Hom.bijective_mapPage_of_le`):
if the induced map is bijective on every spot of the `r`-th page, it is
bijective on all later pages. -/

section Functoriality

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- A **morphism of filtered differential modules**: a linear map commuting with
the differentials and preserving the filtrations. -/
structure Hom (K : FilteredDifferentialModule R M) (K' : FilteredDifferentialModule R M') where
  /-- The underlying linear map. -/
  toLinearMap : M →ₗ[R] M'
  /-- The map commutes with the differentials. -/
  comm_d : ∀ x : M, toLinearMap (K.d x) = K'.d (toLinearMap x)
  /-- The map preserves the filtrations. -/
  map_F : ∀ (p : ℤ), ∀ x ∈ K.F p, toLinearMap x ∈ K'.F p

namespace Hom

variable {M'' : Type*} [AddCommGroup M''] [Module R M'']
variable {K : FilteredDifferentialModule R M} {K' : FilteredDifferentialModule R M'}
  {K'' : FilteredDifferentialModule R M''}

@[ext]
lemma ext {φ ψ : Hom K K'} (h : φ.toLinearMap = ψ.toLinearMap) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- The identity morphism of a filtered differential module. -/
def id (K : FilteredDifferentialModule R M) : Hom K K where
  toLinearMap := LinearMap.id
  comm_d := fun _ ↦ rfl
  map_F := fun _ _ hx ↦ hx

/-- Composition of morphisms of filtered differential modules. -/
def comp (ψ : Hom K' K'') (φ : Hom K K') : Hom K K'' where
  toLinearMap := ψ.toLinearMap.comp φ.toLinearMap
  comm_d := fun x ↦ by rw [LinearMap.comp_apply, φ.comm_d, ψ.comm_d, LinearMap.comp_apply]
  map_F := fun p x hx ↦ ψ.map_F p _ (φ.map_F p x hx)

@[simp] lemma id_toLinearMap (K : FilteredDifferentialModule R M) :
    (id K).toLinearMap = LinearMap.id := rfl

@[simp] lemma comp_toLinearMap (ψ : Hom K' K'') (φ : Hom K K') :
    (ψ.comp φ).toLinearMap = ψ.toLinearMap.comp φ.toLinearMap := rfl

@[simp] lemma id_comp (φ : Hom K K') : (id K').comp φ = φ := by
  apply ext
  ext x
  rfl

@[simp] lemma comp_id (φ : Hom K K') : φ.comp (id K) = φ := by
  apply ext
  ext x
  rfl

lemma comp_assoc {M''' : Type*} [AddCommGroup M'''] [Module R M''']
    {K''' : FilteredDifferentialModule R M'''} (χ : Hom K'' K''')
    (ψ : Hom K' K'') (φ : Hom K K') : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by
  apply ext
  ext x
  rfl

end Hom

/-- `B_r ∩ Z_{r+1} ⊆ B_{r+1}`: an `(r+1)`-cocycle which is an `r`-boundary is an
`(r+1)`-boundary. -/
lemma mem_B_succ_of_mem_B {r p : ℤ} {z : M} (hz : z ∈ K.Z (r + 1) p)
    (hzB : z ∈ K.B r p) : z ∈ K.B (r + 1) p := by
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hzB
  have hdu : K.d u ∈ K.F (p + (r + 1)) := by
    have h2 := (K.mem_Z.mp hz).2
    rw [map_add, K.d_squared v, add_zero] at h2
    exact h2
  refine add_mem (K.mem_B_left hu1 hdu) (K.mem_B_right ?_ hdv)
  rw [show p - (r + 1) + 1 = p - r by ring]
  exact K.F_le (p - r) hv

namespace Hom

variable {K : FilteredDifferentialModule R M} {K' : FilteredDifferentialModule R M'}
variable (φ : Hom K K')

lemma map_Z {r p : ℤ} {x : M} (hx : x ∈ K.Z r p) : φ.toLinearMap x ∈ K'.Z r p := by
  obtain ⟨h1, h2⟩ := K.mem_Z.mp hx
  refine K'.mem_Z.mpr ⟨φ.map_F p x h1, ?_⟩
  rw [← φ.comm_d]
  exact φ.map_F _ _ h2

lemma map_B {r p : ℤ} {x : M} (hx : x ∈ K.B r p) : φ.toLinearMap x ∈ K'.B r p := by
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hx
  rw [map_add]
  refine add_mem (K'.mem_B_left (φ.map_F _ _ hu1) ?_) ?_
  · rw [← φ.comm_d]
    exact φ.map_F _ _ hu2
  · rw [φ.comm_d]
    refine K'.mem_B_right (φ.map_F _ _ hv) ?_
    rw [← φ.comm_d]
    exact φ.map_F _ _ hdv

/-- The induced map on the cocycles. -/
def mapZ (r p : ℤ) : ↥(K.Z r p) →ₗ[R] ↥(K'.Z r p) :=
  φ.toLinearMap.restrict fun _ hx ↦ φ.map_Z hx

@[simp] lemma mapZ_coe (r p : ℤ) (x : ↥(K.Z r p)) :
    (φ.mapZ r p x : M') = φ.toLinearMap x := rfl

/-- The induced map on the pages. -/
def mapPage (r p : ℤ) : K.page r p →ₗ[R] K'.page r p :=
  Submodule.mapQ _ _ (φ.mapZ r p) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, mapZ_coe] at hx ⊢
    exact φ.map_B hx)

@[simp] lemma mapPage_mk (r p : ℤ) (x : ↥(K.Z r p)) :
    φ.mapPage r p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (φ.mapZ r p x) :=
  Submodule.mapQ_apply _ _ _ x

@[simp] lemma mapZ_id (K : FilteredDifferentialModule R M) (r p : ℤ) :
    (Hom.id K).mapZ r p = LinearMap.id := by
  ext x
  rfl

@[simp] lemma mapZ_comp {M'' : Type*} [AddCommGroup M''] [Module R M'']
    {K'' : FilteredDifferentialModule R M''} (ψ : Hom K' K'') (φ : Hom K K')
    (r p : ℤ) : (ψ.comp φ).mapZ r p = (ψ.mapZ r p).comp (φ.mapZ r p) := by
  ext x
  rfl

@[simp] lemma mapPage_id (K : FilteredDifferentialModule R M) (r p : ℤ) :
    (Hom.id K).mapPage r p = LinearMap.id := by
  apply Submodule.linearMap_qext
  ext x
  rfl

@[simp] lemma mapPage_comp {M'' : Type*} [AddCommGroup M''] [Module R M'']
    {K'' : FilteredDifferentialModule R M''} (ψ : Hom K' K'') (φ : Hom K K')
    (r p : ℤ) :
    (ψ.comp φ).mapPage r p = (ψ.mapPage r p).comp (φ.mapPage r p) := by
  apply Submodule.linearMap_qext
  ext x
  rfl

/-- Naturality: the induced maps on pages commute with the differentials. -/
theorem mapPage_dPageAux (r p q : ℤ) (hq : q = p + r) :
    (φ.mapPage r q).comp (K.dPageAux r p q hq)
      = (K'.dPageAux r p q hq).comp (φ.mapPage r p) := by
  apply Submodule.linearMap_qext
  ext ζ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, dPageAux_mk, mapPage_mk]
  congr 1
  apply Subtype.ext
  simp [φ.comm_d]

/-- **Mapping lemma, surjectivity half.** -/
lemma surjective_mapPage_succ (r p : ℤ)
    (hsurj : ∀ p', Function.Surjective (φ.mapPage r p'))
    (hinj : ∀ p', Function.Injective (φ.mapPage r p')) :
    Function.Surjective (φ.mapPage (r + 1) p) := by
  intro c'
  obtain ⟨⟨z', hz'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  -- lift the class of `z'` on the `r`-th page
  obtain ⟨c, hc⟩ := hsurj p (Submodule.Quotient.mk ⟨z', K'.Z_succ_le r p hz'⟩)
  obtain ⟨⟨ζ, hζ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [mapPage_mk, Submodule.Quotient.eq] at hc
  have hb' : φ.toLinearMap ζ - z' ∈ K'.B r p := by
    simpa using hc
  -- the class of `d ζ` on the `r`-th page dies, by injectivity
  have hfz : φ.toLinearMap (K.d ζ) ∈ K'.B r (p + r) := by
    rw [φ.comm_d]
    have heq : K'.d (φ.toLinearMap ζ)
        = K'.d z' + K'.d (φ.toLinearMap ζ - z') := by
      rw [← map_add]
      congr 1
      abel
    rw [heq]
    refine add_mem (K'.mem_B_left ?_ ?_) (K'.d_mem_B rfl hb')
    · have h2 := (K'.mem_Z.mp hz').2
      rwa [show p + r + 1 = p + (r + 1) by ring]
    · rw [K'.d_squared]
      exact zero_mem _
  have hdz : K.d ζ ∈ K.B r (p + r) := by
    have h0 : φ.mapPage r (p + r) (Submodule.Quotient.mk ⟨K.d ζ, K.d_mem_Z rfl hζ⟩) = 0 := by
      rw [mapPage_mk, Submodule.Quotient.mk_eq_zero]
      simpa using hfz
    have h1 := hinj (p + r) (by rw [h0, map_zero] :
      φ.mapPage r (p + r) (Submodule.Quotient.mk ⟨K.d ζ, K.d_mem_Z rfl hζ⟩)
        = φ.mapPage r (p + r) 0)
    rw [Submodule.Quotient.mk_eq_zero] at h1
    simpa using h1
  -- correct `ζ` to an `(r+1)`-cocycle, as in the surjectivity chase of the main theorem
  obtain ⟨u, v, hu1, hu2, hv, hdv, hsum⟩ := K.B_cases hdz
  rw [show p + r - r + 1 = p + 1 by ring] at hv
  have hζF : ζ ∈ K.F p := (K.mem_Z.mp hζ).1
  have hz'' : ζ - v ∈ K.Z (r + 1) p := by
    refine K.mem_Z.mpr ⟨sub_mem hζF (K.F_le p hv), ?_⟩
    have hd : K.d (ζ - v) = u := by
      rw [map_sub, hsum]
      abel
    rw [hd, show p + (r + 1) = p + r + 1 by ring]
    exact hu1
  refine ⟨Submodule.Quotient.mk ⟨ζ - v, hz''⟩, ?_⟩
  rw [mapPage_mk, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub, mapZ_coe]
  refine K'.mem_B_succ_of_mem_B (sub_mem (φ.map_Z hz'') hz') ?_
  have heq2 : φ.toLinearMap (ζ - v) - z'
      = (φ.toLinearMap ζ - z') - φ.toLinearMap v := by
    rw [map_sub]
    abel
  rw [heq2]
  exact sub_mem hb' (φ.map_B (K.mem_B_left hv hdv))

/-- **Mapping lemma, injectivity half.** -/
lemma injective_mapPage_succ (r p : ℤ)
    (hsurj : ∀ p', Function.Surjective (φ.mapPage r p'))
    (hinj : ∀ p', Function.Injective (φ.mapPage r p')) :
    Function.Injective (φ.mapPage (r + 1) p) := by
  rw [← LinearMap.ker_eq_bot]
  refine le_antisymm (fun c hc ↦ ?_) bot_le
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.mem_ker, mapPage_mk, Submodule.Quotient.mk_eq_zero] at hc
  have hfz : φ.toLinearMap z ∈ K'.B (r + 1) p := by
    simpa using hc
  -- decompose and lift the `v'`-part through the previous spot
  obtain ⟨u', v', hu1', hu2', hv', hdv', hsum'⟩ := K'.B_cases hfz
  rw [show p - (r + 1) + 1 = p - r by ring] at hv'
  have hv'Z : v' ∈ K'.Z r (p - r) :=
    K'.mem_Z.mpr ⟨hv', by rw [show p - r + r = p by ring]; exact hdv'⟩
  obtain ⟨c₂, hc₂⟩ := hsurj (p - r) (Submodule.Quotient.mk ⟨v', hv'Z⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c₂
  rw [mapPage_mk, Submodule.Quotient.eq] at hc₂
  have hb : φ.toLinearMap w - v' ∈ K'.B r (p - r) := by
    simpa using hc₂
  -- `z - d w` dies on the `r`-th page after mapping
  have hzw : z - K.d w ∈ K.Z r p :=
    sub_mem (K.Z_succ_le r p hz) (K.d_mem_Z (by ring) hw)
  have hmap0 : φ.toLinearMap (z - K.d w) ∈ K'.B r p := by
    have heq : φ.toLinearMap (z - K.d w)
        = u' - K'.d (φ.toLinearMap w - v') := by
      rw [map_sub, φ.comm_d, map_sub, hsum']
      abel
    rw [heq]
    refine sub_mem (K'.mem_B_left hu1' ?_) (K'.d_mem_B (by ring) hb)
    refine K'.F_le (p + r) ?_
    rwa [show p + r + 1 = p + (r + 1) by ring]
  have h0 : φ.mapPage r p (Submodule.Quotient.mk ⟨z - K.d w, hzw⟩) = 0 := by
    rw [mapPage_mk, Submodule.Quotient.mk_eq_zero]
    simpa using hmap0
  have h1 := hinj p (by rw [h0, map_zero] :
    φ.mapPage r p (Submodule.Quotient.mk ⟨z - K.d w, hzw⟩) = φ.mapPage r p 0)
  rw [Submodule.Quotient.mk_eq_zero] at h1
  have hzB : z - K.d w ∈ K.B r p := by
    simpa using h1
  -- conclude via the kernel identity of the main theorem
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have hmem : z ∈ K.B (r + 1) p := by
    refine K.mem_B_succ_of r p hz ⟨w, hw, ?_⟩
    have heq3 : K.d w - z = -(z - K.d w) := by abel
    rw [heq3]
    exact neg_mem hzB
  exact Submodule.mem_comap.mpr hmem

/-- **The mapping lemma**: a morphism of filtered differential modules that is
bijective on every spot of the `r`-th page is bijective on every spot of the
`(r+1)`-st page. -/
theorem bijective_mapPage_succ (r : ℤ)
    (hbij : ∀ p', Function.Bijective (φ.mapPage r p')) (p : ℤ) :
    Function.Bijective (φ.mapPage (r + 1) p) :=
  ⟨φ.injective_mapPage_succ r p (fun p' ↦ (hbij p').2) (fun p' ↦ (hbij p').1),
    φ.surjective_mapPage_succ r p (fun p' ↦ (hbij p').2) (fun p' ↦ (hbij p').1)⟩

/-- **The mapping lemma, iterated**: bijectivity on the `r`-th page propagates to
all later pages. -/
theorem bijective_mapPage_of_le {r r' : ℤ} (h : r ≤ r')
    (hbij : ∀ p', Function.Bijective (φ.mapPage r p')) :
    ∀ p, Function.Bijective (φ.mapPage r' p) := by
  induction r', h using Int.leInduction with
  | base => exact hbij
  | succ n hn ih => exact φ.bijective_mapPage_succ n ih

end Hom

end Functoriality

/-! ## The spectral sequence of a filtered complex

Following the Stacks Project (tag 012K), a filtered cochain complex
`(X n, d n, F p n)` gives rise to a filtered differential module on the total
module `⨁ n, X n`, and *the spectral sequence of the filtered complex* is the
spectral sequence of this filtered differential module.  (The classical bigraded
pages `E_r^{p,q}` decompose each of our pages `E_r^p` according to the grading
`q = n - p`; the grading plays no role in the construction of the pages, the
differentials, or the homology isomorphism.) -/

section FilteredComplex

open DirectSum

variable (R)
variable (X : ℤ → Type*) [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
variable (d : ∀ n : ℤ, X n →ₗ[R] X (n + 1))
variable (F : ℤ → ∀ n : ℤ, Submodule R (X n))

/-- The total differential on `⨁ n, X n` induced by the differentials of a complex. -/
noncomputable def totalD : (⨁ n, X n) →ₗ[R] ⨁ n, X n :=
  DirectSum.toModule R ℤ _ fun n ↦ (DirectSum.lof R ℤ X (n + 1)).comp (d n)

@[simp] lemma totalD_lof (n : ℤ) (x : X n) :
    totalD R X d (DirectSum.lof R ℤ X n x) = DirectSum.lof R ℤ X (n + 1) (d n x) := by
  simp [totalD]

/-- The total filtration on `⨁ n, X n` induced by a filtration of a complex. -/
def totalF (p : ℤ) : Submodule R (⨁ n, X n) :=
  ⨆ n, (F p n).map (DirectSum.lof R ℤ X n)

/-- **The filtered differential module associated to raw cochain-complex data**
(Stacks Project, tag 012K).  Here `X` is a `ℤ`-indexed family with
differentials `d n : X n → X (n+1)` squaring to zero, and `F` is a decreasing
filtration preserved by the differential.  The primary graded API for a
filtered complex is `FilteredComplex`; this constructor is useful when an
ungraded total differential module is specifically desired. -/
noncomputable def ofComplex
    (hd : ∀ (n : ℤ) (x : X n), d (n + 1) (d n x) = 0)
    (hF : ∀ p n, F (p + 1) n ≤ F p n)
    (hdF : ∀ p n, (F p n).map (d n) ≤ F p (n + 1)) :
    FilteredDifferentialModule R (⨁ n, X n) where
  d := totalD R X d
  d_squared := by
    intro ξ
    induction ξ using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      rw [← DirectSum.lof_eq_of R, totalD_lof, totalD_lof, hd]
      simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  F := totalF R X F
  F_le := fun p ↦
    iSup_le fun n ↦ le_trans (Submodule.map_mono (hF p n))
      (le_iSup (fun n ↦ (F p n).map (DirectSum.lof R ℤ X n)) n)
  d_mem_F := by
    intro p x hx
    have hcomp : ∀ n, (totalD R X d).comp (DirectSum.lof R ℤ X n) =
        (DirectSum.lof R ℤ X (n + 1)).comp (d n) := by
      intro n
      ext y
      simp
    have hmap : (totalF R X F p).map (totalD R X d) ≤ totalF R X F p := by
      rw [totalF, Submodule.map_iSup]
      refine iSup_le fun n ↦ ?_
      rw [← Submodule.map_comp, hcomp n, Submodule.map_comp]
      exact le_trans (Submodule.map_mono (hdF p n))
        (le_iSup (fun m ↦ (F p m).map (DirectSum.lof R ℤ X m)) (n + 1))
    exact hmap (Submodule.mem_map_of_mem hx)

end FilteredComplex

end FilteredDifferentialModule
