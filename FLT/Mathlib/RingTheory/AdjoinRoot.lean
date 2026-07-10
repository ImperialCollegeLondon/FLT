/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# Complements on `AdjoinRoot`

Material for `Mathlib.RingTheory.AdjoinRoot`: reduction of `A[X]/(P)` along ring maps, and
degrees and generators of the simple extension `F[X]/(q)`.
-/

@[expose] public section

open IsLocalRing Polynomial

universe u

/-- Reduction along `f : A →+* B` descends to `AdjoinRoot`: the square
`A[X] → B[X] → B[X]/(q)` = `A[X] → A[X]/(p) → B[X]/(q)` commutes when `q = p.map f`. -/
theorem AdjoinRoot.map_comp_mk {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {p : A[X]}
    {q : B[X]} (h : q = p.map f) :
    (map f p q h.dvd).comp (mk p)
      = (mk q).comp (Polynomial.mapRingHom f) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, mk_C, map_of,
      Polynomial.coe_mapRingHom, Polynomial.map_C, mk_C]
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← root, map_root,
      Polynomial.coe_mapRingHom, Polynomial.map_X, ← root]


/-- The simple extension `F[X]/(q)` by a root of an irreducible `q` has degree `natDegree q`. -/
theorem AdjoinRoot.finrank_eq_natDegree {F : Type*} [Field F] {q : F[X]}
    [Fact (Irreducible q)] : Module.finrank F (AdjoinRoot q) = q.natDegree := by
  rw [PowerBasis.finrank (powerBasis (Fact.out (p := Irreducible q)).ne_zero),
    powerBasis_dim]



/-- The minimal polynomial of `root q` has the same degree as the irreducible `q`. -/
theorem AdjoinRoot.natDegree_minpoly_root {F : Type*} [Field F] {q : F[X]}
    [Fact (Irreducible q)] : (minpoly F (root q)).natDegree = q.natDegree := by
  have hq0 : q ≠ 0 := (Fact.out (p := Irreducible q)).ne_zero
  rw [minpoly_root hq0, natDegree_mul hq0
    (C_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0))), natDegree_C, add_zero]

/-- In `F[X]/(q)` with `q` irreducible of degree at least `2`, the elements `1` and `root q` are
linearly independent over `F`: a linear relation `a · root q + b = 0` forces `a = b = 0`. -/
theorem AdjoinRoot.eq_zero_of_mul_root_add_eq_zero {F : Type*} [Field F] {q : F[X]}
    [Fact (Irreducible q)] (hdeg : 2 ≤ q.natDegree) {a b : F}
    (hab : algebraMap F (AdjoinRoot q) a * root q
      + algebraMap F (AdjoinRoot q) b = 0) : a = 0 ∧ b = 0 := by
  have hpoly : Polynomial.aeval (root q) (C a * X + C b) = 0 := by
    simpa only [map_add, map_mul, aeval_C, aeval_X] using hab
  have h0 : C a * X + C b = 0 := by
    by_contra h0
    have hle := natDegree_le_of_dvd (minpoly.dvd F (root q) hpoly) h0
    rw [natDegree_minpoly_root] at hle
    exact absurd (hle.trans natDegree_linear_le) (by lia)
  exact ⟨by simpa using congrArg (fun p ↦ coeff p 1) h0,
    by simpa using congrArg (fun p ↦ coeff p 0) h0⟩

/-- The root of an irreducible polynomial of degree at least `2` does not lie in the base
field. -/
theorem AdjoinRoot.root_notMem_range_algebraMap {F : Type*} [Field F] {q : F[X]}
    [Fact (Irreducible q)] (hdeg : 2 ≤ q.natDegree) :
    root q ∉ Set.range (algebraMap F (AdjoinRoot q)) := by
  rintro ⟨c, hc⟩
  have h := natDegree_minpoly_root (q := q)
  rw [← hc, minpoly.eq_X_sub_C, natDegree_X_sub_C] at h
  lia

end
