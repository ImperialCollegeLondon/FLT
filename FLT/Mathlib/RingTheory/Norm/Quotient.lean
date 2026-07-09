/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Norm and the residue field

Material for a new `Mathlib.RingTheory.Norm.Quotient` (the norm analogue of
`Mathlib.RingTheory.Trace.Quotient`): the norm commutes with reduction to the residue field.
-/

@[expose] public section

/-- **Rank-2 Cayley–Hamilton.** Every element `θ` of a free rank-2 `A`-algebra `B` satisfies its
characteristic polynomial `X² - (trace θ) X + (norm θ)`: this is Cayley–Hamilton
(`Algebra.aeval_self_charpoly_lmul`) applied to left multiplication by `θ`, whose characteristic
polynomial is `X² - trace X + norm` in rank two (`Matrix.charpoly_fin_two`). -/
theorem sq_sub_trace_mul_self_add_norm {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] (h2 : Module.finrank A B = 2) (θ : B) :
    θ ^ 2 - algebraMap A B (Algebra.trace A B θ) * θ + algebraMap A B (Algebra.norm A θ) = 0 := by
  classical
  set b : Module.Basis (Fin 2) A B := Module.finBasisOfFinrankEq A B h2 with hb
  have hcp : (Algebra.lmul A B θ).charpoly
      = Polynomial.X ^ 2 - Polynomial.C (Algebra.trace A B θ) * Polynomial.X
        + Polynomial.C (Algebra.norm A θ) := by
    rw [← LinearMap.charpoly_toMatrix (Algebra.lmul A B θ) b, ← Algebra.leftMulMatrix_apply,
      Matrix.charpoly_fin_two, ← Algebra.trace_eq_matrix_trace b, ← Algebra.norm_eq_matrix_det b]
  have hCH := Algebra.aeval_self_charpoly_lmul (R := A) (M := B) θ
  rw [hcp] at hCH
  simpa only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    using hCH

open IsLocalRing in
/-- **Norm and the residue field.** For a finite free algebra `B` over a local ring `A`, the norm of
the reduction of `x` is the reduction of the norm. This is the norm analogue of
`Algebra.trace_quotient_mk`; the proof is identical, using `RingHom.map_det` in place of the matrix
trace map. -/
theorem norm_quotient_mk {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [Module.Free A B] [Module.Finite A B] (x : B) :
    Algebra.norm (A ⧸ maximalIdeal A)
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (maximalIdeal A)) x)
      = Ideal.Quotient.mk (maximalIdeal A) (Algebra.norm A x) := by
  classical
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let b : Module.Basis (Module.Free.ChooseBasisIndex A B) A B := Module.Free.chooseBasis A B
  rw [Algebra.norm_eq_matrix_det (basisQuotient b), Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply,
    ← map_mul, basisQuotient_repr]

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

open IsLocalRing in
/-- Transport of the rank-2 Cayley–Hamilton identity `θ² - t·θ + n = 0` (`t`, `n` the trace and
norm of `θ`, `sq_sub_trace_mul_self_add_norm`) through an isomorphism of residue fields: the image
of the residue of `θ` satisfies the corresponding relation in the residues of `t` and `n`. -/
theorem sq_sub_trace_mul_self_add_norm_residue {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Free R S] [Module.Finite R S]
    (hSrank : Module.finrank R S = 2) {k' : Type u} [CommRing k']
    [Algebra (ResidueField R) k'] (resIso : ResidueField S ≃ₐ[ResidueField R] k') (θ : S) :
    resIso (residue S θ) ^ 2
      - algebraMap (ResidueField R) k' (residue R (Algebra.trace R S θ)) * resIso (residue S θ)
      + algebraMap (ResidueField R) k' (residue R (Algebra.norm R θ)) = 0 := by
  have htower : ∀ r : R, algebraMap (ResidueField R) (ResidueField S) (residue R r)
      = residue S (algebraMap R S r) := fun r ↦ by
    simp only [← ResidueField.algebraMap_residue]
  simpa only [map_sub, map_add, map_mul, map_pow, map_zero, ← htower, resIso.commutes]
    using congrArg (fun x ↦ resIso (residue S x)) (sq_sub_trace_mul_self_add_norm hSrank θ)

end
