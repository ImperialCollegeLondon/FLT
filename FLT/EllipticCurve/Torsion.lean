/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RepresentationTheory.Basic

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

abbrev WeierstrassCurve.n_torsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E ⟮k⟯) n

--variable (n : ℕ) in
--#synth AddCommGroup (E.n_torsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.n_torsion n) :=
  AddCommGroup.zmodModule sorry -- shouldn't be too hard

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.n_torsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.n_torsion n) = n^2 := sorry

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    ∃ φ : (Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n)), True := sorry

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)

/- Start of proof attempt -/
lemma round1_h1 (k : Type u) [Field k] (E : WeierstrassCurve k) (n : ℕ) (hn : (n : k) ≠ 0) : 0 < n := by
  by_contra h2
  push_neg at h2
  have h21 : n = 0 := by linarith
  have h22 : (n : k) = 0 := by
    rw [h21]
    <;> simp
  contradiction

lemma round1_h6 (k : Type u) [Field k] (E : WeierstrassCurve k) (n : ℕ) (hn : (n : k) ≠ 0) (h1 : 0 < n) : ∀ (d : ℕ), d ∣ n → (d : k) ≠ 0 := by
  intro d hd
  intro h9
  have h91 : ∃ c, n = d * c := by
    exact?
  rcases h91 with ⟨c, hc⟩
  have h92 : (n : k) = (d : k) * (c : k) := by
    rw [hc]
    simp [mul_comm]
    <;> ring
  have h93 : (n : k) = 0 := by
    rw [h9] at h92
    ring_nf at h92 ⊢
    <;> simpa using h92
  contradiction

lemma round1_h11 (k : Type u) [Field k] [IsSepClosed k] [DecidableEq k] (E : WeierstrassCurve k) [E.IsElliptic] (n : ℕ) (hn : (n : k) ≠ 0) (h1 : 0 < n) (h6 : ∀ (d : ℕ), d ∣ n → (d : k) ≠ 0) : ∀ d : ℕ, d ∣ n → Nat.card (E.n_torsion d) = d ^ 2 := by
  intro d hd
  have h12 : (d : k) ≠ 0 := h6 d hd
  have h121 : Nat.card (E.n_torsion d) = d ^ 2 := by
    exact E.n_torsion_card h12
  exact h121

lemma round1_h13 (k : Type u) [Field k] [DecidableEq k] (E : WeierstrassCurve k) (n : ℕ) (h1 : 0 < n) (h11 : ∀ d : ℕ, d ∣ n → Nat.card (E.n_torsion d) = d ^ 2) : ∃ φ : (E.n_torsion n) ≃+ (Fin 2 → (ZMod n)), True := by
  exact group_theory_lemma h1 2 h11

lemma round1_h15 (k : Type u) [Field k] (E : WeierstrassCurve k) (n : ℕ) : ∃ (φ2 : (Fin 2 → (ZMod n)) ≃+ ((ZMod n) × (ZMod n))), True := by
  have h152 : ∃ (φ2 : (Fin 2 → (ZMod n)) ≃+ ((ZMod n) × (ZMod n))), True := by
    refine ⟨{ toFun := fun f => (f 0, f 1),
              invFun := fun p => fun i => if i = 0 then p.1 else p.2,
              left_inv := by
                intro f
                ext i
                fin_cases i <;> simp
              ,
              right_inv := by
                intro p
                ext
                <;> simp
              ,
              map_add' := by
                intro f g
                simp [Prod.ext_iff]
                <;> aesop
            }, by trivial⟩
  exact h152

theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    ∃ φ : E.n_torsion n ≃+ (ZMod n) × (ZMod n), True  := by

  have h1 : 0 < n := by
    exact round1_h1 k E n hn

  have h6 : ∀ (d : ℕ), d ∣ n → (d : k) ≠ 0 := by
    exact round1_h6 k E n hn h1

  have h11 : ∀ d : ℕ, d ∣ n → Nat.card (E.n_torsion d) = d ^ 2 := by
    exact round1_h11 k E n hn h1 h6

  have h13 : ∃ φ : (E.n_torsion n) ≃+ (Fin 2 → (ZMod n)), True := by
    exact round1_h13 k E n h1 h11

  have h15 : ∃ (φ2 : (Fin 2 → (ZMod n)) ≃+ ((ZMod n) × (ZMod n))), True := by
    exact round1_h15 k E n

  obtain ⟨φ1, _⟩ := h13
  obtain ⟨φ2, _⟩ := h15
  refine ⟨φ1.trans φ2, by trivial⟩

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : E ⟮K⟯ →+ E ⟮L⟯ := sorry

lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := sorry

lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Points.map E g).comp (WeierstrassCurve.Points.map E f) =
    WeierstrassCurve.Points.map E (g.comp f) := sorry

/-- The Galois action on the points of an elliptic curve. -/
def WeierstrassCurve.galoisRepresentation (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E ⟮K⟯) := sorry

/-- The Galois action on the n-torsion points of an elliptic curve. -/
def WeierstrassCurve.torsionGaloisRepresentation (n : ℕ) (K : Type u) [Field K] [Algebra k K] :
    Representation (ZMod n) (K ≃ₐ[k] K) (E.n_torsion n) := sorry
