/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The graded spectral sequence of a filtered cochain complex

`FLT.Slop.SpectralSequence.FilteredModule` constructs the spectral sequence of a filtered
differential *module*, which is the total, ungraded object.  This file refines the
construction for a filtered cochain **complex** `(X n, d, F)`: the pages are now
graded, `E_r^{p, n}` sitting at filtration degree `p` and total degree `n`
(classically one writes `E_r^{p,q}` with `q = n - p`; see `pageBigraded`), and the
differential has bidegree `(r, 1)` in `(p, n)` — that is, `(r, 1-r)` in `(p, q)`.

The grading is what makes convergence usable in practice: for a first-quadrant-type
complex the filtration is bounded *at each degree `n`* but unbounded globally, so
the ungraded convergence theorems do not apply, while the graded ones
(`pageEquivGrHOfBounded` below) do — with bounds depending on the spot `(p, n)`.
This is exactly what the spectral sequences of a double complex require.

## Design

The underlying complex is a standard
`CochainComplex (ModuleCat R) ℤ`.  We use its all-pairs differential API, whose
shape axiom makes every nonconsecutive component zero and whose square-zero
axiom supplies all differential identities.  Flexible auxiliary indices keep
the submodule calculations independent of transports such as
`(n - 1) + 1 = n`: the cocycles and boundaries

* `Z r p n m = F^p_n ⊓ (d n m)⁻¹(F^{p+r}_m)`   (intended `m = n + 1`),
* `B r p l n m = (F^{p+1}_n ⊓ (d n m)⁻¹(F^{p+r}_m)) + d l n (F^{p-r+1}_l ⊓ (d l n)⁻¹(F^p_n))`
  (intended `l = n - 1`, `m = n + 1`)

are `Submodule R (X n)`-valued functions of the auxiliary indices `l, m`, so
mismatches like `(n+1) - 1` vs `n` are repaired by rewriting the index — the
ambient module never changes.

## Main results

* `page r p n` (`= E_r^{p,n}`), `dPageAux` and `dPageAux_comp` (`d_r² = 0`);
* `pageSuccEquiv` : `E_{r+1}^{p,n} ≅ ker(d_r)/im(d_r)` — the main theorem;
* `pageEquivGrHOfBounded` : **graded convergence** — if `F^{p+r}_{n+1} = ⊥` and
  `F^{p-r+1}_{n-1} = ⊤` (one spot at a time!), then `E_r^{p,n} ≅ gr^p H^n`, the
  associated graded of the cohomology of the complex at degree `n`;
* `pageInfEquivGrH` : under the same local bounds, the actual limit term
  `E_∞^{p,n}` is also isomorphic to `gr^p H^n`.
-/

@[expose] public section

namespace Slop

open CategoryTheory Submodule LinearMap

namespace FilteredComplex

section HomologyEquiv

variable {R M M' Nout Nout' Nin Nin' : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup Nout] [Module R Nout] [AddCommGroup Nout'] [Module R Nout']
  [AddCommGroup Nin] [Module R Nin] [AddCommGroup Nin'] [Module R Nin']

/-- **Transport of a homology object along a linear isomorphism.**  Suppose
`e : M ≃ M'` fits into a commuting square with the outgoing differentials —
`eout (fout x) = gout (e x)` for an iso `eout`— and carries `range fin` onto
`range gin`.  Then the two homologies `ker fout / im fin` and `ker gout / im gin`
are isomorphic.  This packages a differential-level identification (a commuting
square) into a homology-level one. -/
noncomputable def homologyEquivOfSquares
    (e : M ≃ₗ[R] M')
    (fout : M →ₗ[R] Nout) (gout : M' →ₗ[R] Nout')
    (eout : Nout ≃ₗ[R] Nout')
    (hout : ∀ x, eout (fout x) = gout (e x))
    (fin_ : Nin →ₗ[R] M) (gin : Nin' →ₗ[R] M')
    (hin : (range fin_).map (e : M →ₗ[R] M') = range gin) :
    (↥(ker fout) ⧸ (range fin_).comap (ker fout).subtype) ≃ₗ[R]
      (↥(ker gout) ⧸ (range gin).comap (ker gout).subtype) := by
  have hker : (ker fout).map (e : M →ₗ[R] M') = ker gout := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h := hout x
      rw [hx, map_zero] at h
      exact h.symm
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply eout.injective
      rw [hout, e.apply_symm_apply, hy, map_zero]
  refine Submodule.Quotient.equiv _ _
    ((e.submoduleMap (ker fout)).trans (LinearEquiv.ofEq _ _ hker)) ?_
  have hEcoe : ∀ z : ↥(ker fout),
      (((e.submoduleMap (ker fout)).trans (LinearEquiv.ofEq _ _ hker) z :
          ↥(ker gout)) : M') = e (z : M) := by
    intro z
    rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply]
  ext w
  obtain ⟨y, hyk⟩ := w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, hz1, hz2⟩
    have hz3 : e (z : M) = y := by rw [← hEcoe z, hz2]
    rw [← hz3, ← hin]
    exact ⟨(z : M), hz1, rfl⟩
  · intro hy
    rw [← hin] at hy
    obtain ⟨x, hxr, hxy⟩ := hy
    rw [LinearEquiv.coe_coe] at hxy
    have hxk : x ∈ ker fout := by
      rw [LinearMap.mem_ker]
      apply eout.injective
      rw [map_zero, hout, hxy]
      exact LinearMap.mem_ker.mp hyk
    refine ⟨⟨x, hxk⟩, hxr, ?_⟩
    apply Subtype.ext
    rw [hEcoe]
    exact hxy

end HomologyEquiv

end FilteredComplex

universe u v

/-- A **filtered cochain complex** of modules: a standard mathlib cochain complex
with a decreasing filtration by subcomplexes. -/
structure FilteredComplex (R : Type u) [Ring R] where
  /-- The underlying cochain complex. -/
  toCochainComplex : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The filtration. -/
  F : ℤ → ∀ n : ℤ, Submodule R (toCochainComplex.X n)
  /-- The filtration is decreasing. -/
  antitone_F : ∀ n, Antitone fun p ↦ F p n
  /-- The differential preserves the filtration. -/
  map_d_le : ∀ (p i j : ℤ), (F p i).map (toCochainComplex.d i j).hom ≤ F p j

namespace FilteredComplex

variable {R : Type u} [Ring R] (K : FilteredComplex.{u, v} R)

/-- The module in cohomological degree `n`. -/
abbrev X (n : ℤ) : Type _ := K.toCochainComplex.X n

/-- The underlying linear map of the differential from degree `i` to degree `j`.
It is zero unless `j = i + 1`, by the shape axiom of the cochain complex. -/
abbrev d (i j : ℤ) : K.X i →ₗ[R] K.X j := (K.toCochainComplex.d i j).hom

/-- Any two differential components compose to zero; the shape axiom makes this
automatic when either component is nonconsecutive. -/
@[simp] lemma d_comp_d (i j k : ℤ) (x : K.X i) :
    K.d j k (K.d i j x) = 0 := by
  have h := DFunLike.congr_fun
    (ModuleCat.hom_ext_iff.mp (K.toCochainComplex.d_comp_d i j k)) x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The successor step of the decreasing filtration. -/
lemma F_le (p n : ℤ) : K.F (p + 1) n ≤ K.F p n :=
  K.antitone_F n (by omega)

/-- Every differential component carries each filtration step into itself. -/
lemma d_mem_F (p i j : ℤ) (x : K.X i) (hx : x ∈ K.F p i) :
    K.d i j x ∈ K.F p j :=
  K.map_d_le p i j (Submodule.mem_map_of_mem hx)

lemma F_mono {p q : ℤ} (h : p ≤ q) (n : ℤ) : K.F q n ≤ K.F p n := by
  exact K.antitone_F n h

/-! ## Cocycles, boundaries, and the graded pages -/

/-- The graded cocycles `Z_r^{p,n} = F^p_n ∩ d⁻¹(F^{p+r}_{n+1})`; the auxiliary
index `m` is intended to be `n + 1`. -/
def Z (r p n m : ℤ) : Submodule R (K.X n) :=
  K.F p n ⊓ (K.F (p + r) m).comap (K.d n m)

lemma mem_Z {r p n m : ℤ} {x : K.X n} :
    x ∈ K.Z r p n m ↔ x ∈ K.F p n ∧ K.d n m x ∈ K.F (p + r) m := by
  simp only [Z, Submodule.mem_inf, Submodule.mem_comap]

/-- The graded boundaries
`B_r^{p,n} = (F^{p+1}_n ∩ d⁻¹F^{p+r}_{n+1}) + d(F^{p-r+1}_{n-1} ∩ d⁻¹F^p_n)`;
the auxiliary indices `l, m` are intended to be `n - 1, n + 1`. -/
def B (r p l n m : ℤ) : Submodule R (K.X n) :=
  (K.F (p + 1) n ⊓ (K.F (p + r) m).comap (K.d n m)) ⊔
    ((K.F (p - r + 1) l ⊓ (K.F p n).comap (K.d l n)).map (K.d l n))

lemma mem_B_left {r p l n m : ℤ} {u : K.X n} (h1 : u ∈ K.F (p + 1) n)
    (h2 : K.d n m u ∈ K.F (p + r) m) : u ∈ K.B r p l n m :=
  Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨h1, Submodule.mem_comap.mpr h2⟩)

lemma mem_B_right {r p l n m : ℤ} {v : K.X l} (hv : v ∈ K.F (p - r + 1) l)
    (hdv : K.d l n v ∈ K.F p n) : K.d l n v ∈ K.B r p l n m :=
  Submodule.mem_sup_right (Submodule.mem_map_of_mem
    (Submodule.mem_inf.mpr ⟨hv, Submodule.mem_comap.mpr hdv⟩))

lemma B_cases {r p l n m : ℤ} {x : K.X n} (hx : x ∈ K.B r p l n m) :
    ∃ (u : K.X n) (v : K.X l), u ∈ K.F (p + 1) n ∧ K.d n m u ∈ K.F (p + r) m ∧
      v ∈ K.F (p - r + 1) l ∧ K.d l n v ∈ K.F p n ∧ x = u + K.d l n v := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  exact ⟨u, v, hu1, Submodule.mem_comap.mp hu2, hv1, Submodule.mem_comap.mp hv2, rfl⟩

lemma B_le_Z {r p l n m : ℤ} : K.B r p l n m ≤ K.Z r p n m := by
  intro x hx
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (K.mem_Z.mpr ⟨K.F_le p n hu1, hu2⟩) (K.mem_Z.mpr ⟨hdv, ?_⟩)
  rw [K.d_comp_d l n m v]
  exact zero_mem _

lemma Z_succ_le (r p n m : ℤ) : K.Z (r + 1) p n m ≤ K.Z r p n m := by
  intro x hx
  obtain ⟨h1, h2⟩ := K.mem_Z.mp hx
  exact K.mem_Z.mpr ⟨h1, K.F_le (p + r) m (by rwa [show p + r + 1 = p + (r + 1) by ring])⟩

/-- The graded page `E_r^{p,n} = Z_r^{p,n} / B_r^{p,n}`. -/
abbrev page (r p n : ℤ) :=
  ↥(K.Z r p n (n + 1)) ⧸ (K.B r p (n - 1) n (n + 1)).comap (K.Z r p n (n + 1)).subtype

/-- The classical bigraded page `E_r^{p,q}` with `q` the complementary degree:
`E_r^{p,q} = E_r^{p, p+q}`. -/
abbrev pageBigraded (r p q : ℤ) := K.page r p (p + q)

/-! ## The differentials -/

lemma d_mem_Z {r p n : ℤ} {x : K.X n} (hx : x ∈ K.Z r p n (n + 1)) :
    K.d n (n + 1) x ∈ K.Z r (p + r) (n + 1) (n + 1 + 1) := by
  obtain ⟨h1, h2⟩ := K.mem_Z.mp hx
  refine K.mem_Z.mpr ⟨h2, ?_⟩
  rw [K.d_comp_d n (n + 1) (n + 1 + 1) x]
  exact zero_mem _

lemma d_mem_B {r p n : ℤ} {x : K.X n} (hx : x ∈ K.B r p (n - 1) n (n + 1)) :
    K.d n (n + 1) x ∈ K.B r (p + r) n (n + 1) (n + 1 + 1) := by
  obtain ⟨u, v, hu1, hu2, hv, hdv, rfl⟩ := K.B_cases hx
  rw [map_add]
  refine add_mem ?_ ?_
  · refine K.mem_B_right ?_ hu2
    rwa [show p + r - r + 1 = p + 1 by ring]
  · rw [K.d_comp_d (n - 1) n (n + 1) v]
    exact zero_mem _

/-- The differential restricted to the cocycles, with flexible indices
(`q = p + r`, `m = n + 1`). -/
def dZ (r p q n m : ℤ) (hq : q = p + r) (hm : m = n + 1) :
    ↥(K.Z r p n (n + 1)) →ₗ[R] ↥(K.Z r q m (m + 1)) :=
  (K.d n m).restrict fun x hx ↦ by subst hq hm; exact K.d_mem_Z hx

@[simp] lemma dZ_coe (r p q n m : ℤ) (hq : q = p + r) (hm : m = n + 1)
    (x : ↥(K.Z r p n (n + 1))) :
    (K.dZ r p q n m hq hm x : K.X m) = K.d n m x := rfl

/-- The differential `d_r : E_r^{p,n} ⟶ E_r^{p+r, n+1}`, with flexible indices. -/
def dPageAux (r p q n m : ℤ) (hq : q = p + r) (hm : m = n + 1) :
    K.page r p n →ₗ[R] K.page r q m :=
  Submodule.mapQ _ _ (K.dZ r p q n m hq hm) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe] at hx ⊢
    subst hq hm
    have h := K.d_mem_B hx
    rw [show n + 1 - 1 = n by ring]
    exact h)

@[simp] lemma dPageAux_mk (r p q n m : ℤ) (hq : q = p + r) (hm : m = n + 1)
    (x : ↥(K.Z r p n (n + 1))) :
    K.dPageAux r p q n m hq hm (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (K.dZ r p q n m hq hm x) :=
  Submodule.mapQ_apply _ _ _ x

lemma dZ_comp_dZ (r p q s n m t : ℤ) (hq : q = p + r) (hs : s = q + r)
    (hm : m = n + 1) (ht : t = m + 1) :
    (K.dZ r q s m t hs ht).comp (K.dZ r p q n m hq hm) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, dZ_coe, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  subst hm ht
  exact K.d_comp_d n (n + 1) (n + 1 + 1) x

/-- The composite of two consecutive graded page differentials vanishes. -/
theorem dPageAux_comp (r p q s n m t : ℤ) (hq : q = p + r) (hs : s = q + r)
    (hm : m = n + 1) (ht : t = m + 1) :
    (K.dPageAux r q s m t hs ht).comp (K.dPageAux r p q n m hq hm) = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  have h0 : K.dZ r q s m t hs ht (K.dZ r p q n m hq hm ζ) = 0 := by
    have := K.dZ_comp_dZ r p q s n m t hq hs hm ht
    exact congrFun (congrArg (fun f ↦ f.toFun) this) ζ
  simp [h0]

/-- Two elements of the cocycles agree in the page iff their difference lies in
the boundaries. -/
lemma pageπ_eq_iff {r p n : ℤ} (a b : ↥(K.Z r p n (n + 1))) :
    (Submodule.Quotient.mk a : K.page r p n) = Submodule.Quotient.mk b ↔
      ((a : K.X n) - b) ∈ K.B r p (n - 1) n (n + 1) := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.mem_comap]

/-! ## The main theorem: each page is the homology of the previous one -/

section MainTheorem

variable (r p n : ℤ)

/-- The differential `d_r : E_r^{p,n} ⟶ E_r^{p+r, n+1}`. -/
abbrev dPage : K.page r p n →ₗ[R] K.page r (p + r) (n + 1) :=
  K.dPageAux r p (p + r) n (n + 1) rfl rfl

/-- The differential `d_r : E_r^{p-r, n-1} ⟶ E_r^{p,n}` arriving at `(p, n)`. -/
abbrev dPageFrom : K.page r (p - r) (n - 1) →ₗ[R] K.page r p n :=
  K.dPageAux r (p - r) p (n - 1) n (by ring) (by ring)

/-- The natural map `Z_{r+1}^{p,n} ⟶ ker(d_r)`. -/
def toKer : ↥(K.Z (r + 1) p n (n + 1)) →ₗ[R] ↥(ker (K.dPage r p n)) :=
  LinearMap.codRestrict _
    (((K.B r p (n - 1) n (n + 1)).comap (K.Z r p n (n + 1)).subtype).mkQ.comp
      (Submodule.inclusion (K.Z_succ_le r p n (n + 1))))
    fun z ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, K.dPageAux_mk,
        Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe, Submodule.coe_inclusion]
      rw [show n + 1 - 1 = n by ring]
      have hz := K.mem_Z.mp z.2
      refine K.mem_B_left ?_ ?_
      · rw [show p + r + 1 = p + (r + 1) by ring]
        exact hz.2
      · rw [K.d_comp_d n (n + 1) (n + 1 + 1)]
        exact zero_mem _

@[simp] lemma toKer_coe (z : ↥(K.Z (r + 1) p n (n + 1))) :
    (K.toKer r p n z : K.page r p n) =
      Submodule.Quotient.mk (Submodule.inclusion (K.Z_succ_le r p n (n + 1)) z) := rfl

lemma toKer_surjective : Function.Surjective (K.toKer r p n) := by
  rintro ⟨c, hc⟩
  obtain ⟨⟨z, hzZ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.mem_ker, K.dPageAux_mk, Submodule.Quotient.mk_eq_zero] at hc
  simp only [Submodule.mem_comap, Submodule.coe_subtype, dZ_coe] at hc
  rw [show n + 1 - 1 = n by ring] at hc
  obtain ⟨u, v, hu1, hu2, hv, hdv, hsum⟩ := K.B_cases hc
  rw [show p + r - r + 1 = p + 1 by ring] at hv
  have hzF : z ∈ K.F p n := (K.mem_Z.mp hzZ).1
  have hz' : z - v ∈ K.Z (r + 1) p n (n + 1) := by
    refine K.mem_Z.mpr ⟨sub_mem hzF (K.F_le p n hv), ?_⟩
    have hdz' : K.d n (n + 1) (z - v) = u := by
      rw [map_sub, hsum]
      abel
    rw [hdz', show p + (r + 1) = p + r + 1 by ring]
    exact hu1
  refine ⟨⟨z - v, hz'⟩, ?_⟩
  apply Subtype.ext
  rw [toKer_coe, Submodule.Quotient.eq]
  simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
    Submodule.coe_inclusion]
  have heq : z - v - z = -v := by abel
  rw [heq]
  exact neg_mem (K.mem_B_left hv hdv)

/-- The composite `Z_{r+1}^{p,n} ⟶ ker(d_r) ⟶ ker(d_r)/im(d_r)`. -/
def toHomology : ↥(K.Z (r + 1) p n (n + 1)) →ₗ[R]
    ↥(ker (K.dPage r p n)) ⧸
      (range (K.dPageFrom r p n)).comap (ker (K.dPage r p n)).subtype :=
  ((range (K.dPageFrom r p n)).comap (ker (K.dPage r p n)).subtype).mkQ.comp (K.toKer r p n)

lemma toHomology_surjective : Function.Surjective (K.toHomology r p n) := by
  have h := (Submodule.mkQ_surjective
    ((range (K.dPageFrom r p n)).comap (ker (K.dPage r p n)).subtype)).comp
      (K.toKer_surjective r p n)
  simpa [toHomology, LinearMap.coe_comp] using h

/-- Membership in the image of `d_r` arriving at `(p, n)`, concretely. -/
lemma mk_mem_range_dPageFrom_iff (z : ↥(K.Z r p n (n + 1))) :
    Submodule.Quotient.mk z ∈ range (K.dPageFrom r p n) ↔
      ∃ y : K.X (n - 1), y ∈ K.Z r (p - r) (n - 1) n ∧
        K.d (n - 1) n y - ↑z ∈ K.B r p (n - 1) n (n + 1) := by
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ η
    obtain ⟨y, hy2⟩ := y
    refine ⟨y, ?_, ?_⟩
    · have h := hy2
      rwa [show n - 1 + 1 = n by ring] at h
    · rw [K.dPageAux_mk, Submodule.Quotient.eq] at hη
      simpa only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
        dZ_coe] using hη
  · rintro ⟨y, hyZ, hy⟩
    have hyZ' : y ∈ K.Z r (p - r) (n - 1) (n - 1 + 1) := by
      rw [show n - 1 + 1 = n by ring]
      exact hyZ
    refine ⟨Submodule.Quotient.mk ⟨y, hyZ'⟩, ?_⟩
    rw [K.dPageAux_mk, Submodule.Quotient.eq]
    simpa only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      dZ_coe] using hy

/-- An element of `B_{r+1}^{p,n}` is a `d_r`-boundary on the `r`-th page. -/
lemma exists_of_mem_B_succ {z : K.X n} (hzB : z ∈ K.B (r + 1) p (n - 1) n (n + 1)) :
    ∃ y : K.X (n - 1), y ∈ K.Z r (p - r) (n - 1) n ∧
      K.d (n - 1) n y - z ∈ K.B r p (n - 1) n (n + 1) := by
  obtain ⟨u, v, hu1, hu2, hv, hdv, hsum⟩ := K.B_cases hzB
  rw [show p - (r + 1) + 1 = p - r by ring] at hv
  refine ⟨v, K.mem_Z.mpr ⟨hv, by rw [show p - r + r = p by ring]; exact hdv⟩, ?_⟩
  have heq : K.d (n - 1) n v - z = -u := by
    rw [hsum]
    abel
  rw [heq]
  refine neg_mem (K.mem_B_left hu1 (K.F_le (p + r) (n + 1) ?_))
  rwa [show p + r + 1 = p + (r + 1) by ring]

/-- An `(r+1)`-cocycle which is a `d_r`-boundary lies in `B_{r+1}^{p,n}`. -/
lemma mem_B_succ_of {z : K.X n} (hz : z ∈ K.Z (r + 1) p n (n + 1))
    (h : ∃ y : K.X (n - 1), y ∈ K.Z r (p - r) (n - 1) n ∧
      K.d (n - 1) n y - z ∈ K.B r p (n - 1) n (n + 1)) :
    z ∈ K.B (r + 1) p (n - 1) n (n + 1) := by
  obtain ⟨y, hyZ, hy⟩ := h
  obtain ⟨hy1, hy2⟩ := K.mem_Z.mp hyZ
  rw [show p - r + r = p by ring] at hy2
  obtain ⟨u, t, hu1, hu2, ht, hdt, hsum⟩ := K.B_cases hy
  have hy' : y - t ∈ K.F (p - r) (n - 1) := sub_mem hy1 (K.F_le (p - r) (n - 1) ht)
  have hdy' : K.d (n - 1) n (y - t) ∈ K.F p n := by
    rw [map_sub]
    exact sub_mem hy2 hdt
  have hu_eq : K.d (n - 1) n (y - t) - z = u := by
    calc K.d (n - 1) n (y - t) - z
        = K.d (n - 1) n y - K.d (n - 1) n t - z := by rw [map_sub]
      _ = K.d (n - 1) n y - z - K.d (n - 1) n t := by abel
      _ = u := by rw [hsum]; abel
  have hz_eq : z = K.d (n - 1) n (y - t) - u := by
    rw [← hu_eq]
    abel
  have hdu : K.d n (n + 1) u ∈ K.F (p + (r + 1)) (n + 1) := by
    have hdu_eq : K.d n (n + 1) u = -K.d n (n + 1) z := by
      rw [← hu_eq, map_sub, K.d_comp_d (n - 1) n (n + 1) (y - t), zero_sub]
    rw [hdu_eq]
    exact neg_mem (K.mem_Z.mp hz).2
  rw [hz_eq]
  refine sub_mem ?_ (K.mem_B_left hu1 hdu)
  refine K.mem_B_right ?_ hdy'
  rwa [show p - (r + 1) + 1 = p - r by ring]

lemma ker_toHomology :
    ker (K.toHomology r p n)
      = (K.B (r + 1) p (n - 1) n (n + 1)).comap (K.Z (r + 1) p n (n + 1)).subtype := by
  ext ζ
  obtain ⟨z, hz⟩ := ζ
  simp only [LinearMap.mem_ker, toHomology, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, toKer_coe]
  rw [K.mk_mem_range_dPageFrom_iff]
  simp only [Submodule.coe_inclusion]
  exact ⟨fun h ↦ K.mem_B_succ_of r p n hz h, fun h ↦ K.exists_of_mem_B_succ r p n h⟩

/-- **The graded main theorem**: `E_{r+1}^{p,n} ≅ ker(d_r^{p,n})/im(d_r^{p-r,n-1})`. -/
noncomputable def pageSuccEquiv :
    K.page (r + 1) p n ≃ₗ[R]
      (↥(ker (K.dPage r p n)) ⧸
        (range (K.dPageFrom r p n)).comap (ker (K.dPage r p n)).subtype) :=
  (Submodule.quotEquivOfEq _ _ (K.ker_toHomology r p n).symm).trans
    ((K.toHomology r p n).quotKerEquivOfSurjective (K.toHomology_surjective r p n))

/-- **Flexible-index form of the main theorem.**  Identical to `pageSuccEquiv`
but with the source/target filtration degrees of the differentials supplied as
free variables `p' = p + r`, `p'' = p - r`.  This lets downstream identifications
(e.g. `r = 0`, where `p + 0` is *not* definitionally `p`) name the differentials
with clean indices `dPageAux _ p p _ _` rather than `dPageAux _ p (p + 0) _ _`.
Proved by `subst` (the two differ only by proof-irrelevant index equalities). -/
noncomputable def pageSuccEquiv' (r p p' p'' n : ℤ) (hp' : p' = p + r) (hp'' : p'' = p - r) :
    K.page (r + 1) p n ≃ₗ[R]
      (↥(ker (K.dPageAux r p p' n (n + 1) hp' rfl)) ⧸
        (range (K.dPageAux r p'' p (n - 1) n (by rw [hp'']; ring) (by ring))).comap
          (ker (K.dPageAux r p p' n (n + 1) hp' rfl)).subtype) := by
  subst hp' hp''
  exact K.pageSuccEquiv r p n

end MainTheorem

/-! ## Graded convergence

The convergence theory of `FilteredModule.lean`, refined by degree: the boundedness
hypotheses are now *per spot* — `F^{p+r}_{n+1} = ⊥` and `F^{p-r+1}_{n-1} = ⊤` —
which is what first-quadrant-type double complexes satisfy even though their
total filtration is globally unbounded.

The limit term is formed in `E₀`: its numerator is the intersection of
`Z_r^{p,n} + F^{p+1}_n`, and its denominator is the union of
`B_r^{p,n} + F^{p+1}_n`.  The sums with `F^{p+1}_n` are necessary because the
raw ambient `Z_r` and `B_r` are not nested across arbitrary pages. -/

section Convergence

/-- The cycle submodule used to present the associated-graded cohomology target,
`F^p_n ⊓ ker d`.  This is not the limit-cycle submodule without convergence
hypotheses. -/
def abutmentZ (p n : ℤ) : Submodule R (K.X n) := K.F p n ⊓ ker (K.d n (n + 1))

/-- The boundary submodule used to present the associated-graded cohomology target,
`(F^{p+1}_n ⊓ ker d) + d(d⁻¹ F^p_n)`; `l` is intended to be `n - 1`. -/
def abutmentB (p l n : ℤ) : Submodule R (K.X n) :=
  (K.F (p + 1) n ⊓ ker (K.d n (n + 1))) ⊔ ((K.F p n).comap (K.d l n)).map (K.d l n)

lemma mem_abutmentB_left {p l n : ℤ} {u : K.X n} (h1 : u ∈ K.F (p + 1) n)
    (h2 : K.d n (n + 1) u = 0) : u ∈ K.abutmentB p l n :=
  Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨h1, LinearMap.mem_ker.mpr h2⟩)

lemma mem_abutmentB_right {p l n : ℤ} {w : K.X l} (hdw : K.d l n w ∈ K.F p n) :
    K.d l n w ∈ K.abutmentB p l n :=
  Submodule.mem_sup_right (Submodule.mem_map_of_mem (Submodule.mem_comap.mpr hdw))

lemma abutmentB_cases {p l n : ℤ} {x : K.X n} (hx : x ∈ K.abutmentB p l n) :
    ∃ (u : K.X n) (w : K.X l), u ∈ K.F (p + 1) n ∧ K.d n (n + 1) u = 0 ∧
      K.d l n w ∈ K.F p n ∧ x = u + K.d l n w := by
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
  exact ⟨u, w, hu1, LinearMap.mem_ker.mp hu2, Submodule.mem_comap.mp hw, rfl⟩

lemma abutmentB_le_abutmentZ {p l n : ℤ} : K.abutmentB p l n ≤ K.abutmentZ p n := by
  intro x hx
  obtain ⟨u, w, hu1, hu2, hdw, rfl⟩ := K.abutmentB_cases hx
  refine add_mem (Submodule.mem_inf.mpr ⟨K.F_le p n hu1, LinearMap.mem_ker.mpr hu2⟩) ?_
  refine Submodule.mem_inf.mpr ⟨hdw, LinearMap.mem_ker.mpr ?_⟩
  exact K.d_comp_d l n (n + 1) w

/-- The associated-graded cohomology target, presented inside `X n`. -/
abbrev associatedGradedHomology (p n : ℤ) :=
  ↥(K.abutmentZ p n) ⧸ (K.abutmentB p (n - 1) n).comap (K.abutmentZ p n).subtype

/-- The numerator of the limit term, represented before quotienting by
`F^{p+1}_n`: `⋂_{r ≥ 0} (Z_r^{p,n} + F^{p+1}_n)`. -/
def limitZ (p n : ℤ) : Submodule R (K.X n) :=
  ⨅ r : ℕ, K.Z (r : ℤ) p n (n + 1) ⊔ K.F (p + 1) n

/-- The denominator of the limit term, represented before quotienting by
`F^{p+1}_n`: `⋃_{r ≥ 0} (B_r^{p,n} + F^{p+1}_n)`. -/
def limitB (p n : ℤ) : Submodule R (K.X n) :=
  ⨆ r : ℕ, K.B (r : ℤ) p (n - 1) n (n + 1) ⊔ K.F (p + 1) n

lemma Z_mono {r s p n : ℤ} (h : r ≤ s) :
    K.Z s p n (n + 1) ≤ K.Z r p n (n + 1) := by
  intro x hx
  obtain ⟨hxF, hdx⟩ := K.mem_Z.mp hx
  exact K.mem_Z.mpr ⟨hxF, K.F_mono (by omega) (n + 1) hdx⟩

lemma normalizedZ_antitone (p n : ℤ) :
    Antitone fun r : ℕ ↦ K.Z (r : ℤ) p n (n + 1) ⊔ K.F (p + 1) n := by
  intro r s h
  exact sup_le_sup (K.Z_mono (by exact_mod_cast h)) le_rfl

lemma normalizedB_monotone (p n : ℤ) :
    Monotone fun r : ℕ ↦
      K.B (r : ℤ) p (n - 1) n (n + 1) ⊔ K.F (p + 1) n := by
  intro r s h
  refine sup_le ?_ le_sup_right
  intro x hx
  obtain ⟨u, v, hu1, -, hv, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
  exact K.mem_B_right (K.F_mono (by omega) (n - 1) hv) hdv

lemma B_sup_F_le_Z_sup_F (r s p n : ℤ) :
    K.B r p (n - 1) n (n + 1) ⊔ K.F (p + 1) n ≤
      K.Z s p n (n + 1) ⊔ K.F (p + 1) n := by
  refine sup_le ?_ le_sup_right
  intro x hx
  obtain ⟨u, v, hu1, -, -, hdv, rfl⟩ := K.B_cases hx
  refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
  refine K.mem_Z.mpr ⟨hdv, ?_⟩
  rw [K.d_comp_d (n - 1) n (n + 1) v]
  exact zero_mem _

lemma limitB_le_limitZ (p n : ℤ) : K.limitB p n ≤ K.limitZ p n := by
  refine iSup_le fun r ↦ le_iInf fun s ↦ ?_
  exact K.B_sup_F_le_Z_sup_F (r : ℤ) (s : ℤ) p n

lemma limitZ_le_F (p n : ℤ) : K.limitZ p n ≤ K.F p n := by
  refine le_trans
    (iInf_le (fun r : ℕ ↦ K.Z (r : ℤ) p n (n + 1) ⊔ K.F (p + 1) n) 0) ?_
  exact sup_le inf_le_left (K.F_le p n)

lemma F_le_limitB (p n : ℤ) : K.F (p + 1) n ≤ K.limitB p n :=
  le_trans le_sup_right
    (le_iSup (fun r : ℕ ↦
      K.B (r : ℤ) p (n - 1) n (n + 1) ⊔ K.F (p + 1) n) 0)

/-- The limit term `E_∞^{p,n}`.  It need not be equal to any finite page
without a stabilization hypothesis. -/
abbrev pageInf (p n : ℤ) :=
  ↥(K.limitZ p n) ⧸ (K.limitB p n).comap (K.limitZ p n).subtype

lemma Z_eq_abutmentZ {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥) :
    K.Z r p n (n + 1) = K.abutmentZ p n := by
  unfold Z abutmentZ
  rw [hbot, Submodule.comap_bot]

lemma B_eq_abutmentB {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.B r p (n - 1) n (n + 1) = K.abutmentB p (n - 1) n := by
  unfold B abutmentB
  rw [hbot, htop, Submodule.comap_bot, top_inf_eq]

/-- Once the cocycles have stabilized at `(p,n)`, the numerator of the limit
term is the cycle numerator of the associated-graded target, together with the
copy of `F^{p+1}_n` used to represent submodules of `E₀^{p,n}`. -/
lemma limitZ_eq_abutmentZ_sup_F {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥) :
    K.limitZ p n = K.abutmentZ p n ⊔ K.F (p + 1) n := by
  let N := r.toNat
  have hrN : r ≤ (N : ℤ) := Int.self_le_toNat r
  have hbotN : K.F (p + (N : ℤ)) (n + 1) = ⊥ :=
    le_bot_iff.mp (hbot ▸ K.F_mono (by omega) (n + 1))
  apply le_antisymm
  · refine le_trans
      (iInf_le (fun s : ℕ ↦ K.Z (s : ℤ) p n (n + 1) ⊔ K.F (p + 1) n) N) ?_
    rw [K.Z_eq_abutmentZ hbotN]
  · refine le_iInf fun s ↦ sup_le ?_ le_sup_right
    intro x hx
    exact Submodule.mem_sup_left (K.mem_Z.mpr ⟨hx.1, by
      rw [LinearMap.mem_ker.mp hx.2]
      exact zero_mem _⟩)

/-- Once both sides have stabilized at `(p,n)`, the denominator of the limit
term is the boundary denominator of the associated-graded target, together
with the copy of `F^{p+1}_n` used to represent submodules of `E₀^{p,n}`. -/
lemma limitB_eq_abutmentB_sup_F {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.limitB p n = K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n := by
  let N := r.toNat
  have hrN : r ≤ (N : ℤ) := Int.self_le_toNat r
  have hbotN : K.F (p + (N : ℤ)) (n + 1) = ⊥ :=
    le_bot_iff.mp (hbot ▸ K.F_mono (by omega) (n + 1))
  have htopN : K.F (p - (N : ℤ) + 1) (n - 1) = ⊤ :=
    top_le_iff.mp (htop ▸ K.F_mono (by omega) (n - 1))
  apply le_antisymm
  · refine iSup_le fun s ↦ sup_le ?_ le_sup_right
    intro x hx
    obtain ⟨u, w, hu1, -, -, hdw, rfl⟩ := K.B_cases hx
    refine add_mem (Submodule.mem_sup_right hu1) (Submodule.mem_sup_left ?_)
    exact K.mem_abutmentB_right hdw
  · refine le_trans ?_
      (le_iSup (fun s : ℕ ↦
        K.B (s : ℤ) p (n - 1) n (n + 1) ⊔ K.F (p + 1) n) N)
    rw [K.B_eq_abutmentB hbotN htopN]

/-- Intersecting the associated-graded cycle numerator with the normalized
boundary denominator recovers the unnormalized boundary denominator. -/
lemma abutmentZ_inf_abutmentB_sup_F_eq_abutmentB (p n : ℤ) :
    K.abutmentZ p n ⊓ (K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n) =
      K.abutmentB p (n - 1) n := by
  have hBZ : K.abutmentB p (n - 1) n ≤ K.abutmentZ p n := K.abutmentB_le_abutmentZ
  apply le_antisymm
  · rintro x ⟨hxZ, hx⟩
    obtain ⟨b, hb, f, hf, rfl⟩ := Submodule.mem_sup.mp hx
    refine add_mem hb ?_
    have hfker : K.d n (n + 1) f = 0 := by
      have hbker : K.d n (n + 1) b = 0 := LinearMap.mem_ker.mp (hBZ hb).2
      have hxker : K.d n (n + 1) (b + f) = 0 := LinearMap.mem_ker.mp hxZ.2
      simpa [map_add, hbker] using hxker
    exact K.mem_abutmentB_left hf hfker
  · exact le_inf hBZ le_sup_left

/-- The associated-graded cohomology target in its normalized presentation
inside `E₀^{p,n}`: adjoining `F^{p+1}_n` to both numerator and denominator
does not change the quotient. -/
noncomputable def associatedGradedHomologyEquivNormalized (p n : ℤ) :
    K.associatedGradedHomology p n ≃ₗ[R]
      (↥(K.abutmentZ p n ⊔ K.F (p + 1) n) ⧸
        ((K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n).comap
          (K.abutmentZ p n ⊔ K.F (p + 1) n).subtype)) := by
  let e := LinearMap.quotientInfEquivSupQuotient (K.abutmentZ p n)
    (K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n)
  have hdom :
      (K.abutmentB p (n - 1) n).comap (K.abutmentZ p n).subtype =
        (K.abutmentZ p n).comap (K.abutmentZ p n).subtype ⊓
          (K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n).comap (K.abutmentZ p n).subtype := by
    ext x
    change (x : K.X n) ∈ K.abutmentB p (n - 1) n ↔
      (x : K.X n) ∈ K.abutmentZ p n ∧
        (x : K.X n) ∈ K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n
    rw [← Submodule.mem_inf, K.abutmentZ_inf_abutmentB_sup_F_eq_abutmentB]
  have hnum : K.abutmentZ p n ⊔ (K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n) =
      K.abutmentZ p n ⊔ K.F (p + 1) n := by
    rw [← sup_assoc, sup_eq_left.mpr K.abutmentB_le_abutmentZ]
  rw [hnum] at e
  exact (Submodule.quotEquivOfEq _ _ hdom).trans e

/-- Under two-sided local bounds at `(p,n)`, the actual limit term is
canonically isomorphic to the associated-graded cohomology target. -/
noncomputable def pageInfEquivAssociatedGradedHomology {r p n : ℤ}
    (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.pageInf p n ≃ₗ[R] K.associatedGradedHomology p n := by
  let e₁ : K.pageInf p n ≃ₗ[R]
      (↥(K.abutmentZ p n ⊔ K.F (p + 1) n) ⧸
        ((K.abutmentB p (n - 1) n ⊔ K.F (p + 1) n).comap
          (K.abutmentZ p n ⊔ K.F (p + 1) n).subtype)) :=
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
  exact e₁.trans (K.associatedGradedHomologyEquivNormalized p n).symm

/-- Once `F^{p+r}_{n+1} = ⊥` and `F^{p-r+1}_{n-1} = ⊤`, the `r`-th page
at `(p,n)` is the associated-graded cohomology target. -/
noncomputable def pageEquivAssociatedGradedHomology {r p n : ℤ}
    (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.page r p n ≃ₗ[R] K.associatedGradedHomology p n :=
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

/-- Under two-sided local bounds at `(p,n)`, the finite `r`-th page has
stabilized to the limit term. -/
noncomputable def pageEquivPageInf {r p n : ℤ}
    (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.page r p n ≃ₗ[R] K.pageInf p n :=
  (K.pageEquivAssociatedGradedHomology hbot htop).trans
    (K.pageInfEquivAssociatedGradedHomology hbot htop).symm

/-- Beyond the bound of the filtration, the graded differential leaving `(p, n)`
vanishes. -/
theorem dPage_eq_zero {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥) :
    K.dPage r p n = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  have h0 : K.dZ r p (p + r) n (n + 1) rfl rfl ζ = 0 := by
    apply Subtype.ext
    have h := (K.mem_Z.mp ζ.2).2
    rw [hbot] at h
    simpa using h
  simp [h0]

/-- Beyond the bound of the filtration, the graded differential arriving at `(p, n)`
vanishes. -/
theorem dPageFrom_eq_zero {r p n : ℤ} (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.dPageFrom r p n = 0 := by
  apply Submodule.linearMap_qext
  ext ζ
  obtain ⟨zv, hzv⟩ := ζ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, K.dPageAux_mk, LinearMap.zero_comp,
    LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, dZ_coe]
  have h2 : K.d (n - 1) n zv ∈ K.F p n := by
    have h := (K.mem_Z.mp hzv).2
    rw [show n - 1 + 1 = n by ring] at h
    rwa [show p - r + r = p by ring] at h
  refine K.mem_B_right ?_ h2
  rw [htop]
  exact Submodule.mem_top

/-! ### The associated-graded cohomology target -/

/-- The cohomology of the complex at degree `n`, `H^n = ker(d^n)/im(d^{n-1})`. -/
abbrev homology (n : ℤ) :=
  ↥(ker (K.d n (n + 1))) ⧸ (range (K.d (n - 1) n)).comap (ker (K.d n (n + 1))).subtype

/-- The canonical isomorphism from mathlib's categorical cohomology object to
the explicit quotient `ker(d n (n + 1)) / range(d (n - 1) n)`. -/
noncomputable def categoricalHomologyIso (n : ℤ) :
    K.toCochainComplex.homology n ≅ ModuleCat.of R (K.homology n) := by
  let a := n - 1
  let b := n
  let c := n + 1
  let shape := ComplexShape.up ℤ
  have hab : shape.Rel a b := by
    change n - 1 + 1 = n
    omega
  have hbc : shape.Rel b c := by
    change n + 1 = n + 1
    rfl
  let S := K.toCochainComplex.sc' a b c
  refine K.toCochainComplex.homologyIsoSc' a b c
      (shape.prev_eq' hab) (shape.next_eq' hbc) ≪≫
    S.moduleCatHomologyIso ≪≫ ?_
  refine eqToIso ?_
  change ModuleCat.of R
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
    ModuleCat.of R
      (↥(ker (K.d n (n + 1))) ⧸
        (range (K.d (n - 1) n)).comap (ker (K.d n (n + 1))).subtype)
  rw [LinearMap.range_codRestrict]
  rfl

/-- The filtration induced on the cohomology: `F^p H^n = im(F^p_n ⊓ ker d → H^n)`. -/
def FH (p n : ℤ) : Submodule R (K.homology n) :=
  ((K.abutmentZ p n).comap (ker (K.d n (n + 1))).subtype).map
    ((range (K.d (n - 1) n)).comap (ker (K.d n (n + 1))).subtype).mkQ

lemma mem_FH_iff {p n : ℤ} {h : K.homology n} :
    h ∈ K.FH p n ↔ ∃ z : ↥(ker (K.d n (n + 1))), (z : K.X n) ∈ K.F p n ∧
      Submodule.Quotient.mk z = h := by
  constructor
  · intro hh
    obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hh
    have h1 := Submodule.mem_comap.mp hζ
    exact ⟨ζ, (Submodule.mem_inf.mp h1).1, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact Submodule.mem_map.mpr
      ⟨z, Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨hz, z.2⟩), rfl⟩

lemma abutmentZ_le_ker (p n : ℤ) : K.abutmentZ p n ≤ ker (K.d n (n + 1)) := inf_le_right

/-- The natural map from filtered cocycles `F^p_n ∩ ker d` to `F^p H^n`. -/
def toFH (p n : ℤ) : ↥(K.abutmentZ p n) →ₗ[R] ↥(K.FH p n) :=
  LinearMap.codRestrict _
    (((range (K.d (n - 1) n)).comap (ker (K.d n (n + 1))).subtype).mkQ.comp
      (Submodule.inclusion (K.abutmentZ_le_ker p n)))
    fun x ↦ Submodule.mem_map_of_mem (Submodule.mem_comap.mpr x.2)

@[simp] lemma toFH_coe (p n : ℤ) (x : ↥(K.abutmentZ p n)) :
    (K.toFH p n x : K.homology n) =
      Submodule.Quotient.mk (Submodule.inclusion (K.abutmentZ_le_ker p n) x) := rfl

lemma toFH_surjective (p n : ℤ) : Function.Surjective (K.toFH p n) := by
  rintro ⟨h, hmem⟩
  obtain ⟨ζ, hζ, rfl⟩ := Submodule.mem_map.mp hmem
  refine ⟨⟨↑ζ, Submodule.mem_comap.mp hζ⟩, ?_⟩
  apply Subtype.ext
  rw [toFH_coe]
  exact congrArg _ (Subtype.ext rfl)

/-- The associated graded piece `gr^p H^n = F^p H^n / F^{p+1} H^n` of the cohomology.
This is the object the spectral sequence abuts to: the convergence theorems below
identify `E_r^{p,n}` with `K.grH p n`. -/
abbrev grH (p n : ℤ) : Type _ :=
  ↥(K.FH p n) ⧸ (K.FH (p + 1) n).comap (K.FH p n).subtype

/-- The composite from filtered cocycles to `F^p H^n ⟶ gr^p H^n`. -/
def toGrH (p n : ℤ) : ↥(K.abutmentZ p n) →ₗ[R] K.grH p n :=
  ((K.FH (p + 1) n).comap (K.FH p n).subtype).mkQ.comp (K.toFH p n)

lemma toGrH_surjective (p n : ℤ) : Function.Surjective (K.toGrH p n) := by
  have h := (Submodule.mkQ_surjective
    ((K.FH (p + 1) n).comap (K.FH p n).subtype)).comp (K.toFH_surjective p n)
  simpa [toGrH, LinearMap.coe_comp] using h

lemma ker_toGrH (p n : ℤ) :
    ker (K.toGrH p n) = (K.abutmentB p (n - 1) n).comap (K.abutmentZ p n).subtype := by
  ext ξ
  obtain ⟨x, hx⟩ := ξ
  have hxF : x ∈ K.F p n := (Submodule.mem_inf.mp hx).1
  simp only [LinearMap.mem_ker, toGrH, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, toFH_coe]
  rw [K.mem_FH_iff]
  constructor
  · rintro ⟨z, hzF, hzeq⟩
    rw [Submodule.Quotient.eq] at hzeq
    have hd : (z : K.X n) - x ∈ range (K.d (n - 1) n) := by
      simpa using hzeq
    obtain ⟨m, hm⟩ := hd
    have h1 : (z : K.X n) ∈ K.abutmentB p (n - 1) n :=
      K.mem_abutmentB_left hzF (LinearMap.mem_ker.mp z.2)
    have h2 : -((z : K.X n) - x) ∈ K.abutmentB p (n - 1) n := by
      refine neg_mem ?_
      rw [← hm]
      refine K.mem_abutmentB_right ?_
      rw [hm]
      exact sub_mem (K.F_le p n hzF) hxF
    have h3 := add_mem h1 h2
    have heq : (z : K.X n) + -((z : K.X n) - x) = x := by abel
    rwa [heq] at h3
  · intro hxB
    obtain ⟨u, w, hu1, hu2, hdw, hsum⟩ := K.abutmentB_cases hxB
    refine ⟨⟨u, LinearMap.mem_ker.mpr hu2⟩, hu1, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
      Submodule.coe_inclusion]
    have heq : u - x = -(K.d (n - 1) n w) := by
      rw [hsum]
      abel
    rw [heq]
    exact neg_mem ⟨w, rfl⟩

/-- Identification of the associated-graded target with `gr^p H^n`.  This does
not identify the limit term `pageInf` without convergence hypotheses. -/
noncomputable def associatedGradedHomologyEquivGrH (p n : ℤ) :
    K.associatedGradedHomology p n ≃ₗ[R] K.grH p n :=
  (Submodule.quotEquivOfEq _ _ (K.ker_toGrH p n).symm).trans
    ((K.toGrH p n).quotKerEquivOfSurjective (K.toGrH_surjective p n))

/-- Under two-sided local bounds at `(p,n)`, the limit term is the associated
graded of the induced filtration on cohomology. -/
noncomputable def pageInfEquivGrH {r p n : ℤ}
    (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.pageInf p n ≃ₗ[R] K.grH p n :=
  (K.pageInfEquivAssociatedGradedHomology hbot htop).trans
    (K.associatedGradedHomologyEquivGrH p n)

/-- **Graded convergence** (the statement consumed by the double-complex spectral
sequences): if `F^{p+r}_{n+1} = ⊥` and `F^{p-r+1}_{n-1} = ⊤` — bounds required only
at the spot `(p, n)` — then `E_r^{p,n} ≅ gr^p H^n`. -/
noncomputable def pageEquivGrHOfBounded {r p n : ℤ} (hbot : K.F (p + r) (n + 1) = ⊥)
    (htop : K.F (p - r + 1) (n - 1) = ⊤) :
    K.page r p n ≃ₗ[R] K.grH p n :=
  (K.pageEquivAssociatedGradedHomology hbot htop).trans
    (K.associatedGradedHomologyEquivGrH p n)

end Convergence

/-! ## The zeroth page is the associated graded -/

section PageZero

lemma Z_zero (p n : ℤ) : K.Z 0 p n (n + 1) = K.F p n := by
  refine le_antisymm inf_le_left fun x hx ↦ ?_
  refine K.mem_Z.mpr ⟨hx, ?_⟩
  rw [show p + (0 : ℤ) = p by ring]
  exact K.d_mem_F p n (n + 1) x hx

lemma B_zero (p n : ℤ) : K.B 0 p (n - 1) n (n + 1) = K.F (p + 1) n := by
  apply le_antisymm
  · refine sup_le inf_le_left ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨hv1, _⟩ := Submodule.mem_inf.mp hv
    rw [show p - 0 + 1 = p + 1 by ring] at hv1
    exact K.d_mem_F (p + 1) (n - 1) n v hv1
  · intro x hx
    refine K.mem_B_left hx ?_
    rw [show p + (0 : ℤ) = p by ring]
    exact K.d_mem_F p n (n + 1) x (K.F_le p n hx)

/-- **The zeroth page is the associated graded of the filtration**:
`E_0^{p,n} ≅ F^p_n / F^{p+1}_n`.  (Consequently `E_1 = H(gr)` by the main
theorem `pageSuccEquiv` at `r = 0`.) -/
noncomputable def pageZeroEquiv (p n : ℤ) :
    K.page 0 p n ≃ₗ[R] (↥(K.F p n) ⧸ (K.F (p + 1) n).comap (K.F p n).subtype) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (K.Z_zero p n)) (by
    ext ξ
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨η, hη, rfl⟩
      rw [← K.B_zero p n]
      simpa using hη
    · intro hξ
      refine ⟨(LinearEquiv.ofEq _ _ (K.Z_zero p n)).symm ξ, ?_,
        (LinearEquiv.ofEq _ _ (K.Z_zero p n)).apply_symm_apply ξ⟩
      rw [K.B_zero p n]
      simpa using hξ)

end PageZero

/-! ## Functoriality

A morphism of filtered complexes is a cochain map which preserves every step of
the filtration.  Such a morphism induces maps on cocycles, boundaries, and all
pages, compatible with the page differentials. -/

section Functoriality

open CategoryTheory

variable {K K' K'' : FilteredComplex.{u, v} R}

/-- A morphism of filtered cochain complexes: a cochain map which preserves the
filtration. -/
@[ext]
structure Hom (K K' : FilteredComplex.{u, v} R) where
  /-- The underlying morphism of cochain complexes. -/
  toHom : K.toCochainComplex ⟶ K'.toCochainComplex
  /-- Each component of the cochain map preserves the filtration. -/
  map_F : ∀ (p n : ℤ), (K.F p n).map (toHom.f n).hom ≤ K'.F p n

namespace Hom

/-- The identity morphism of a filtered complex. -/
def id (K : FilteredComplex.{u, v} R) : Hom K K where
  toHom := 𝟙 K.toCochainComplex
  map_F p n := by simp

/-- The composite of two morphisms of filtered complexes. -/
def comp (f : Hom K K') (g : Hom K' K'') : Hom K K'' where
  toHom := f.toHom ≫ g.toHom
  map_F p n := by
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, Submodule.map_comp]
    exact le_trans (Submodule.map_mono (f.map_F p n)) (g.map_F p n)

end Hom

instance : Category (FilteredComplex.{u, v} R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp] lemma id_toHom (K : FilteredComplex.{u, v} R) :
    (Hom.toHom (𝟙 K : K ⟶ K)) = 𝟙 K.toCochainComplex := rfl

@[simp] lemma comp_toHom (f : K ⟶ K') (g : K' ⟶ K'') :
    (f ≫ g).toHom = f.toHom ≫ g.toHom := rfl

/-- Two filtered cochain maps are equal if their underlying cochain maps are
equal. -/
@[ext]
lemma Hom.hom_ext (f g : K ⟶ K') (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The component of a filtered cochain map commutes with every differential. -/
lemma Hom.comm_d (f : K ⟶ K') (i j : ℤ) (x : K.X i) :
    K'.d i j ((f.toHom.f i).hom x) = (f.toHom.f j).hom (K.d i j x) := by
  have h := DFunLike.congr_fun
    (ModuleCat.hom_ext_iff.mp (f.toHom.comm i j)) x
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- A filtered cochain map carries each filtration step into the corresponding
filtration step. -/
lemma Hom.map_mem_F (f : K ⟶ K') (p n : ℤ) {x : K.X n} (hx : x ∈ K.F p n) :
    (f.toHom.f n).hom x ∈ K'.F p n :=
  f.map_F p n (Submodule.mem_map_of_mem hx)

lemma Hom.map_Z (f : K ⟶ K') {r p n m : ℤ} {x : K.X n}
    (hx : x ∈ K.Z r p n m) : (f.toHom.f n).hom x ∈ K'.Z r p n m := by
  obtain ⟨hxF, hdx⟩ := K.mem_Z.mp hx
  refine K'.mem_Z.mpr ⟨f.map_mem_F p n hxF, ?_⟩
  rw [f.comm_d]
  exact f.map_mem_F (p + r) m hdx

lemma Hom.map_B (f : K ⟶ K') {r p l n m : ℤ} {x : K.X n}
    (hx : x ∈ K.B r p l n m) : (f.toHom.f n).hom x ∈ K'.B r p l n m := by
  obtain ⟨a, b, haF, hda, hbF, hdb, rfl⟩ := K.B_cases hx
  rw [map_add, ← f.comm_d l n b]
  refine add_mem (K'.mem_B_left (f.map_mem_F (p + 1) n haF) ?_) ?_
  · rw [f.comm_d]
    exact f.map_mem_F (p + r) m hda
  · refine K'.mem_B_right (f.map_mem_F (p - r + 1) l hbF) ?_
    rw [f.comm_d]
    exact f.map_mem_F p n hdb

/-- The map on boundary submodules induced by a filtered cochain map. -/
def Hom.mapB (f : K ⟶ K') (r p l n m : ℤ) :
    ↥(K.B r p l n m) →ₗ[R] ↥(K'.B r p l n m) :=
  (f.toHom.f n).hom.restrict fun _ hx ↦ f.map_B hx

@[simp] lemma Hom.mapB_coe (f : K ⟶ K') (r p l n m : ℤ)
    (x : ↥(K.B r p l n m)) :
    (f.mapB r p l n m x : K'.X n) = (f.toHom.f n).hom x := rfl

/-- The map on cocycles induced by a filtered cochain map. -/
def Hom.mapZ (f : K ⟶ K') (r p n m : ℤ) :
    ↥(K.Z r p n m) →ₗ[R] ↥(K'.Z r p n m) :=
  (f.toHom.f n).hom.restrict fun _ hx ↦ f.map_Z hx

@[simp] lemma Hom.mapZ_coe (f : K ⟶ K') (r p n m : ℤ) (x : ↥(K.Z r p n m)) :
    (f.mapZ r p n m x : K'.X n) = (f.toHom.f n).hom x := rfl

/-- The map on an `r`-page induced by a filtered cochain map. -/
def Hom.mapPage (f : K ⟶ K') (r p n : ℤ) : K.page r p n →ₗ[R] K'.page r p n :=
  Submodule.mapQ _ _ (f.mapZ r p n (n + 1)) (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Hom.mapZ_coe] at hx ⊢
    exact f.map_B hx)

@[simp] lemma Hom.mapPage_mk (f : K ⟶ K') (r p n : ℤ)
    (x : ↥(K.Z r p n (n + 1))) :
    f.mapPage r p n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.mapZ r p n (n + 1) x) :=
  Submodule.mapQ_apply _ _ _ x

@[simp] lemma Hom.mapPage_id (K : FilteredComplex.{u, v} R) (r p n : ℤ) :
    (𝟙 K : K ⟶ K).mapPage r p n = LinearMap.id := by
  apply Submodule.linearMap_qext
  ext x
  rfl

@[simp] lemma Hom.mapPage_comp (f : K ⟶ K') (g : K' ⟶ K'') (r p n : ℤ) :
    (f ≫ g).mapPage r p n = (g.mapPage r p n).comp (f.mapPage r p n) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [Hom.mapPage_mk, LinearMap.comp_apply, Submodule.mkQ_apply]
  congr 1

/-- Naturality of page differentials with respect to filtered cochain maps. -/
theorem Hom.mapPage_dPageAux (f : K ⟶ K') (r p q n m : ℤ)
    (hq : q = p + r) (hm : m = n + 1) :
    (f.mapPage r q m).comp (K.dPageAux r p q n m hq hm) =
      (K'.dPageAux r p q n m hq hm).comp (f.mapPage r p n) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, dPageAux_mk, Hom.mapPage_mk]
  congr 1
  apply Subtype.ext
  simpa only [Hom.mapZ_coe, dZ_coe] using (f.comm_d n m x).symm

end Functoriality

end FilteredComplex

end Slop
