/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Complements on admissible changes of variables

Material for `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`: decidable equality,
the negation automorphism `[-1]`, compatibility of changes of variables with base change,
and Galois descent for changes of variables.
-/

@[expose] public section

namespace WeierstrassCurve

universe u

/-- Two admissible changes of variables agree iff their four coefficients do; this makes equality
of changes of variables decidable over a commutative ring with decidable equality. -/
instance {R : Type*} [CommRing R] [DecidableEq R] : DecidableEq (VariableChange R) :=
  fun _ _ ↦ decidable_of_iff _ VariableChange.ext_iff.symm

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-- The automorphism `[-1] : (x, y) ↦ (x, -y - a₁x - a₃)` of a Weierstrass curve, as an admissible
change of variables `⟨-1, 0, -a₁, -a₃⟩`. It fixes `E` (`negVariableChange_smul_self`) and is an
involution (`negVariableChange_mul_self`). -/
def negVariableChange : VariableChange K :=
  ⟨-1, 0, -E.a₁, -E.a₃⟩

@[simp] lemma negVariableChange_u : E.negVariableChange.u = -1 := rfl

lemma negVariableChange_smul_self : E.negVariableChange • E = E := by
  simp [variableChange_def, negVariableChange]
  ring_nf

lemma negVariableChange_mul_self : E.negVariableChange * E.negVariableChange = 1 := by
  simp [VariableChange.mul_def, VariableChange.one_def, negVariableChange,
    Odd.neg_one_pow (by decide : Odd 3)]

lemma negVariableChange_inv : E.negVariableChange⁻¹ = E.negVariableChange :=
  inv_eq_of_mul_eq_one_right E.negVariableChange_mul_self

/-- Base change commutes with the negation automorphism: mapping `[-1]` on `W` through a ring
homomorphism `φ` gives `[-1]` on `W.map φ`. -/
lemma negVariableChange_map {A B : Type*} [Field A] [Field B] (W : WeierstrassCurve A)
    (φ : A →+* B) : W.negVariableChange.map φ = (W.map φ).negVariableChange := by
  ext <;> simp [negVariableChange]

/-- The negation automorphism is nontrivial for an elliptic curve: in characteristic `≠ 2` it
has `u = -1 ≠ 1`, and in characteristic `2` it has `(s, t) = (-a₁, -a₃) ≠ (0, 0)`, since an
elliptic curve in characteristic `2` cannot have `a₁ = a₃ = 0`. -/
lemma negVariableChange_ne_one [E.IsElliptic] : E.negVariableChange ≠ 1 := by
  intro h
  rcases eq_or_ne (2 : K) 0 with h2 | h2
  · have hs := congrArg VariableChange.s h
    have ht := congrArg VariableChange.t h
    simp [negVariableChange, VariableChange.one_def] at hs ht
    grind [a₁_ne_zero_or_a₃_ne_zero_of_two_eq_zero]
  · contrapose h2
    have hv : (-1 : K) = 1 := by
      simpa [VariableChange.one_def] using congrArg (fun C : VariableChange K ↦ (C.u : K)) h
    linear_combination -hv

section

variable (L : Type*) [Field L] [Algebra K L]

/-- The automorphism `[-1]` of `E` over `L` is defined over `K`, hence fixed by the Galois action:
its components `-1, 0, -a₁, -a₃` all lie in `K`. -/
lemma negVariableChange_baseChange_map (σ : L ≃ₐ[K] L) :
    (E.baseChange L).negVariableChange.map σ.toAlgHom.toRingHom
      = (E.baseChange L).negVariableChange := by
  ext <;>
    simp [VariableChange.map, negVariableChange, map_neg, baseChange, AlgEquiv.commutes]

/-- Base change commutes with the action of changes of variables. -/
lemma baseChange_smul_baseChange (C : VariableChange K) (V : WeierstrassCurve K) :
    (C.baseChange L) • V.baseChange L = (C • V).baseChange L :=
  map_variableChange (W := V) (C := C) (φ := algebraMap K L)

/-- A relation `Cᴸ • Vᴸ = Wᴸ` between base changes, with `C` defined over `K`, descends to
`C • V = W` over `K`. -/
lemma smul_eq_of_baseChange_smul_eq (C : VariableChange K) {V W : WeierstrassCurve K}
    (h : (C.baseChange L) • V.baseChange L = W.baseChange L) : C • V = W := by
  apply map_injective (FaithfulSMul.algebraMap_injective K L)
  exact (baseChange_smul_baseChange L C V).symm.trans h

/-- The Galois conjugate of an `L`-isomorphism between base-changed curves is again one. -/
lemma map_smul_baseChange_eq (σ : L ≃ₐ[K] L) {V W : WeierstrassCurve K} {ρ : VariableChange L}
    (hρ : ρ • V.baseChange L = W.baseChange L) :
    (ρ.map σ.toAlgHom.toRingHom) • V.baseChange L = W.baseChange L := by
  have hVinv : (V.baseChange L).map σ.toAlgHom.toRingHom = V.baseChange L :=
    map_baseChange (W := V) σ.toAlgHom
  have hWinv : (W.baseChange L).map σ.toAlgHom.toRingHom = W.baseChange L :=
    map_baseChange (W := W) σ.toAlgHom
  have hmv := map_variableChange (W := V.baseChange L) (C := ρ) (φ := σ.toAlgHom.toRingHom)
  rw [hρ, hVinv, hWinv] at hmv
  exact hmv

end

end WeierstrassCurve

end
