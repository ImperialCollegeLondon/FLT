/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Coprimality of polynomials over a Jacobson-radical quotient

Two small coprimality facts used throughout the theory of Henselian pairs.

## Main results

* `isCoprime_X_sub_C_of_isUnit_eval` — if `p.eval a` is a unit then `X - C a` and `p`
  are coprime, i.e. `a` is a *simple* root of `(X - C a) * p`.
* `isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson` — coprimality of monic
  polynomials descends from `R ⧸ J` to `R` when `J ≤ Jac(R)`.

## References

* [Stacks Project, Tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Polynomial

/-- If `p.eval a` is a unit then `X - C a` is coprime to `p`. This packages the
fact that `a` is a *simple* root of `(X - C a) * p`. -/
theorem isCoprime_X_sub_C_of_isUnit_eval {a : R} {p : R[X]} (h : IsUnit (p.eval a)) :
    IsCoprime (X - C a) p := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  obtain ⟨k, hk⟩ : (X - C a) ∣ (p - C (p.eval a)) := X_sub_C_dvd_sub_C_eval
  rw [show p = C (p.eval a) + (X - C a) * k by rw [← hk]; ring,
    IsCoprime.add_mul_left_right_iff]
  exact ⟨0, C v, by rw [zero_mul, zero_add, ← C_mul, mul_comm, hv, C_1]⟩

/-- **Coprimality lifts along Jacobson-radical quotients for monic polynomials.**
If `J ≤ Jac(R)` and two monic polynomials become coprime modulo `J`, then they
were already coprime over `R`.

The proof uses the resultant: for a monic polynomial, being coprime is equivalent
to the resultant being a unit.  The resultant is a unit modulo `J`; since the
quotient map is local when `J ≤ Jac(R)`, it was already a unit in `R`. -/
theorem isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson {J : Ideal R}
    (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R)) {g h : R[X]} (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk J)) (h.map (Ideal.Quotient.mk J))) :
    IsCoprime g h := by
  rcases subsingleton_or_nontrivial R with _ | hR
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  have hJtop : J ≠ ⊤ :=
    (hJ.trans_lt (Ideal.jacobson_bot (R := R) ▸ Ring.jacobson_lt_top R)).ne
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hJ
  rw [← Polynomial.isUnit_resultant_iff_isCoprime hg]
  refine IsUnit.of_map (Ideal.Quotient.mk J) _ ?_
  simpa [hg.natDegree_map, hh.natDegree_map, Polynomial.resultant_map_map]
    using (Polynomial.isUnit_resultant_iff_isCoprime (hg.map _)).mpr hcop

end Polynomial
