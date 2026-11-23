/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Complex conjugation as an element of the absolute Galois group of `ℚ`

We produce an element `c` of `Gal(ℚ̄/ℚ)` with `c² = 1` which inverts every root of unity
(`exists_conj_absoluteGaloisGroup`): choose an embedding `j : ℚ̄ ↪ ℂ` (via
`IsAlgClosed.lift`), and restrict complex conjugation along `j` to the normal extension
`ℚ̄/ℚ` using `AlgHom.restrictNormal'`.  Since `j` maps roots of unity to complex numbers of
norm one, where conjugation agrees with inversion, `c` inverts every root of unity.

This discharges assumption S3 of `abs_irred_v2.tex` (see
`CyclotomicAbsIrred.exists_complex_conjugation` in `FLT.Slop.CyclotomicAbsIrred.Assumed`).
-/

@[expose] public section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

namespace CyclotomicAbsIrred

/-- There is an element of `Gal(ℚ̄/ℚ)` of square one inverting all roots of unity, namely
(the restriction of) complex conjugation. -/
theorem exists_conj_absoluteGaloisGroup :
    ∃ c : Γ ℚ, c ^ 2 = 1 ∧ ∀ (t : (ℚᵃˡᵍ)) (n : ℕ), 0 < n → t ^ n = 1 → c t = t⁻¹ := by
  -- instance-diamond workaround: with the analysis instances in scope, these fail to be
  -- found by synthesis for the concrete field `ℚ`, so we provide them by hand
  haveI : Algebra.IsAlgebraic ℚ (ℚᵃˡᵍ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (ℚᵃˡᵍ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (ℚᵃˡᵍ) := IsAlgClosure.normal ℚ (ℚᵃˡᵍ)
  letI : Algebra (ℚᵃˡᵍ) ℂ := (IsAlgClosed.lift : (ℚᵃˡᵍ) →ₐ[ℚ] ℂ).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (ℚᵃˡᵍ) ℂ := IsScalarTower.of_algebraMap_eq'
    ((IsAlgClosed.lift : (ℚᵃˡᵍ) →ₐ[ℚ] ℂ).comp_algebraMap).symm
  set j : (ℚᵃˡᵍ) →+* ℂ := algebraMap (ℚᵃˡᵍ) ℂ with hjdef
  have hjinj : Function.Injective j := j.injective
  set φ : ℂ →ₐ[ℚ] ℂ := ((RCLike.conjAe (K := ℂ)).restrictScalars ℚ).toAlgHom with hφdef
  have hφ_apply : ∀ z : ℂ, φ z = starRingEnd ℂ z := fun z =>
    congrFun (RCLike.conjAe_coe (K := ℂ)) z
  set c : Γ ℚ := φ.restrictNormal' (ℚᵃˡᵍ) with hcdef
  have hcomm : ∀ x : (ℚᵃˡᵍ), j (c x) = φ (j x) := fun x =>
    φ.restrictNormal_commutes (ℚᵃˡᵍ) x
  refine ⟨c, ?_, ?_⟩
  · -- `c ^ 2 = 1`, since conjugation is an involution
    apply AlgEquiv.ext
    intro x
    have h2 : (c ^ 2) x = c (c x) := by rw [pow_two]; rfl
    apply hjinj
    rw [h2, hcomm, hcomm, hφ_apply, hφ_apply, Complex.conj_conj]
    rfl
  · -- `c` inverts roots of unity
    intro t n hn htn
    have hjt_pow : (j t) ^ n = 1 := by rw [← map_pow, htn, map_one]
    have hnorm : ‖j t‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hjt_pow hn.ne'
    apply hjinj
    rw [hcomm, hφ_apply, ← Complex.inv_eq_conj hnorm, map_inv₀]

end CyclotomicAbsIrred

end
