/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# An involution of determinant -1 on a 2-dimensional space has a 1-dimensional fixed space

If `A` is a linear endomorphism of a two-dimensional vector space `V` over a field `k` with
`2 ≠ 0`, satisfying `A ^ 2 = 1` and `det A = -1`, then the fixed space of `A` (the eigenspace
for the eigenvalue `1`) is one-dimensional.

This is Step 1 of the proof of the main theorem of `FLT.Slop.CyclotomicAbsIrred.Main`: it is
applied to the image of a complex conjugation under a two-dimensional mod-`ℓ` Galois
representation with cyclotomic determinant, and feeds into
`OddRep.isIrreducible_iff_isAbsolutelyIrreducible`.
-/

@[expose] public section

open Module

namespace CyclotomicAbsIrred

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- An involution with determinant `-1` of a two-dimensional vector space over a field of
characteristic different from `2` has a one-dimensional fixed space. -/
theorem finrank_eigenspace_one_eq_one_of_involution
    (A : Module.End k V) (hdim : finrank k V = 2) (h2 : (2 : k) ≠ 0)
    (hinv : A * A = 1) (hdet : LinearMap.det (A : V →ₗ[k] V) = -1) :
    finrank k (Module.End.eigenspace A 1) = 1 := by
  have : FiniteDimensional k V := .of_finrank_pos (by omega)
  have hneg : (-1 : k) ≠ 1 := by
    intro h
    apply h2
    have h0 : (-1 : k) + 1 = 0 := neg_add_cancel 1
    rw [h] at h0
    rw [show (2 : k) = 1 + 1 by norm_num]
    exact h0
  set E := Module.End.eigenspace A 1 with hE
  have hle : finrank k E ≤ 2 := hdim ▸ Submodule.finrank_le E
  have hAA : ∀ v : V, A (A v) = v := by
    intro v
    have := congrArg (fun f : Module.End k V => f v) hinv
    simpa using this
  interval_cases h : finrank k E
  · -- fixed space is zero: then `A = -1`, of determinant `1`, contradiction
    exfalso
    have hEbot : E = ⊥ := Submodule.finrank_eq_zero.mp h
    have hAv : ∀ v : V, A v = -v := by
      intro v
      have hmem : v + A v ∈ E := by
        rw [hE, Module.End.mem_eigenspace_iff]
        simp [map_add, hAA v, add_comm]
      rw [hEbot, Submodule.mem_bot] at hmem
      exact eq_neg_of_add_eq_zero_right hmem
    have hA : A = -LinearMap.id (R := k) (M := V) := by
      ext v
      simp [hAv v]
    rw [hA, show -LinearMap.id (R := k) (M := V) = (-1 : k) • LinearMap.id by simp,
      LinearMap.det_smul, hdim, LinearMap.det_id] at hdet
    apply hneg
    rw [← hdet]
    norm_num
  · rfl
  · -- fixed space is everything: then `A = 1`, of determinant `1`, contradiction
    exfalso
    have hEtop : E = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h, hdim])
    have hA : A = LinearMap.id (R := k) (M := V) := by
      ext v
      have hmem : v ∈ E := hEtop ▸ Submodule.mem_top
      rw [hE, Module.End.mem_eigenspace_iff] at hmem
      simpa using hmem
    rw [hA, LinearMap.det_id] at hdet
    exact hneg hdet.symm

end CyclotomicAbsIrred

end
