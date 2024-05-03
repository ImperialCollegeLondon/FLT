/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
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

variable {k : Type u} [Field k] (E : EllipticCurve k)

open WeierstrassCurve

abbrev EllipticCurve.n_torsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E.toWeierstrassCurve ⟮k⟯) n

--variable (n : ℕ) in
--#synth AddCommGroup (E.n_torsion n)

def ZMod.module (A : Type*) [AddCommGroup A] (n : ℕ) (hn : ∀ a : A, n • a = 0) :
    Module (ZMod n) A :=
  sorry

-- not sure if this instance will cause more trouble than it's worth
instance (n : ℕ) : Module (ZMod n) (E.n_torsion n) := sorry -- shouldn't be too hard

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem EllipticCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.n_torsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem EllipticCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.n_torsion n) = n^2 := sorry

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    ∃ φ :(Submodule.torsionBy ℤ A n) ≃+ Fin d → (ZMod n), True := sorry

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem EllipticCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    ∃ φ : E.n_torsion n ≃+ (ZMod n) × (ZMod n), True := sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
def EllipticCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K] [Algebra k L]
    (f : K →ₐ[k] L) : E.toWeierstrassCurve ⟮K⟯ →+ E.toWeierstrassCurve ⟮L⟯ := sorry

lemma EllipticCurve.Points.map_id (K : Type u) [Field K] [Algebra k K] :
    EllipticCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := sorry

lemma EllipticCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M] (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (EllipticCurve.Points.map E g).comp (EllipticCurve.Points.map E f) =
    EllipticCurve.Points.map E (g.comp f) := sorry

/-- The Galois action on the points of an elliptic curve. -/
def EllipticCurve.galoisRepresentation (K : Type u) [Field K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E.toWeierstrassCurve ⟮K⟯) := sorry

/-- The Galois action on the n-torsion points of an elliptic curve. -/
def EllipticCurve.torsionGaloisRepresentation (n : ℕ) (K : Type u) [Field K] [Algebra k K] :
    Representation (ZMod n) (K ≃ₐ[k] K) (E.n_torsion n) := sorry
