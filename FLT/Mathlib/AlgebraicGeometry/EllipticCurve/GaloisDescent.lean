/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Michael Stoll, Claude
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import FLT.Mathlib.FieldTheory.Galois.Basic

/-!
# Galois descent for Weierstrass curve data

Proposed new Mathlib file `Mathlib.AlgebraicGeometry.EllipticCurve.GaloisDescent`: a change of
variables (or a point) over a separable quadratic extension `L/K` fixed by `Gal(L/K)` descends
to `K`.
-/

@[expose] public section

open Algebra.IsQuadraticExtension

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

/-- **Galois descent for changes of variables.** A change of variables over `L` fixed by the
nontrivial `σ ∈ Gal(L/K)` has all its coefficients in `K`, so it is the base change of a change of
variables over `K`. -/
lemma exists_baseChange_eq_of_map_eq {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {C : VariableChange L}
    (hCinv : C.map σ.toAlgHom.toRingHom = C) : ∃ CK : VariableChange K, CK.baseChange L = C := by
  have hap : ⇑σ.toAlgHom.toRingHom = ⇑σ := rfl
  have mem : ∀ x : L, σ x = x → x ∈ Set.range (algebraMap K L) :=
    fun x hx ↦ mem_range_algebraMap_of_apply_eq K L hσ hx
  have hu : σ (C.u : L) = (C.u : L) := by
    simpa [VariableChange.map, Units.coe_map, hap] using congrArg (fun D ↦ (D.u : L)) hCinv
  have hr : σ C.r = C.r := by
    simpa [VariableChange.map, hap] using congrArg VariableChange.r hCinv
  have hs : σ C.s = C.s := by
    simpa [VariableChange.map, hap] using congrArg VariableChange.s hCinv
  have ht : σ C.t = C.t := by
    simpa [VariableChange.map, hap] using congrArg VariableChange.t hCinv
  obtain ⟨uK, huK⟩ := mem _ hu
  obtain ⟨rK, hrK⟩ := mem _ hr
  obtain ⟨sK, hsK⟩ := mem _ hs
  obtain ⟨tK, htK⟩ := mem _ ht
  have huK' : uK ≠ 0 := by rintro rfl; rw [map_zero] at huK; exact C.u.ne_zero huK.symm
  refine ⟨⟨Units.mk0 uK huK', rK, sK, tK⟩, VariableChange.ext (Units.ext ?_) hrK hsK htK⟩
  simpa [VariableChange.baseChange, VariableChange.map] using huK

/-- **Galois descent for points.** A point of `W(L)` fixed by the nontrivial `σ ∈ Gal(L/K)` (hence,
as `[L : K] = 2`, by all of `Gal(L/K)`) is the base change of a point of `W(K)`: its coordinates,
being fixed by `σ`, lie in `K`. -/
theorem exists_baseChange_point_eq_of_map_eq [DecidableEq K] [DecidableEq L]
    {W : WeierstrassCurve K} {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) {R : (W⁄L).Point}
    (hR : Affine.Point.map σ.toAlgHom R = R) :
    ∃ Q : (W⁄K).Point, Affine.Point.baseChange K L Q = R := by
  rcases R with _ | ⟨x, y, h⟩
  · exact ⟨0, rfl⟩
  · rw [Affine.Point.map_some] at hR
    injection hR with hx hy
    obtain ⟨x₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hx
    obtain ⟨y₀, rfl⟩ := mem_range_algebraMap_of_apply_eq K L hσ hy
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular W
      (f := Algebra.ofId K L) (FaithfulSMul.algebraMap_injective K L) x₀ y₀).mp h), rfl⟩

end WeierstrassCurve

end
