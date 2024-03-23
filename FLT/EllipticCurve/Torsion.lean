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

variable {K : Type u} [Field K] (E : EllipticCurve K)

open WeierstrassCurve

abbrev EllipticCurve.n_torsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E.toWeierstrassCurve ⟮K⟯) n

--variable (n : ℕ) in
--#synth AddCommGroup (E.n_torsion n)

-- not sure if this instance will cause more trouble than it's worth
instance (n : ℕ) : Module (ZMod n) (E.n_torsion n) := sorry -- shouldn't be too hard

-- The next two theorems need e.g. a theory of division polynomials. They are ongoing work of David Angdinata
theorem EllipticCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.n_torsion n) := sorry

theorem EllipticCurve.n_torsion_card [IsSepClosed K] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (E.n_torsion n) = n^2 := sorry

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
theorem EllipticCurve.n_torsion_dimension [IsSepClosed K] {n : ℕ} (hn : (n : K) ≠ 0) :
    FiniteDimensional.finrank (ZMod n) (E.n_torsion n) = 2 := sorry

-- We need this -- ask David?
example (L M : Type u) [Field L] [Field M] [Algebra K L] [Algebra K M] (f : L →ₐ[K] M) :
    E.toWeierstrassCurve ⟮L⟯ →+ E.toWeierstrassCurve ⟮M⟯ := sorry

-- Once we have it, plus the id and comp lemmas for it, we can get an action of Gal(K-bar/K) on E(K-bar)[n]
def EllipticCurve.mod_p_Galois_representation (n : ℕ) (L : Type u) [Field L] [Algebra K L] :
    Representation (ZMod n) (L ≃ₐ[K] L) (E.n_torsion n) := sorry
