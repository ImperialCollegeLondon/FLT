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
theorem isCoprime_X_sub_C_of_isUnit_eval {a : R} {p : R[X]}
    (h : IsUnit (p.eval a)) : IsCoprime (X - C a) p := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  have hdvd : (X - C a) ∣ (p - C (p.eval a)) := X_sub_C_dvd_sub_C_eval
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨-(C v * k), C v, ?_⟩
  have hk2 : p - (X - C a) * k = C (p.eval a) := by rw [← hk]; ring
  calc -(C v * k) * (X - C a) + C v * p
      = C v * (p - (X - C a) * k) := by ring
    _ = C v * C (p.eval a) := by rw [hk2]
    _ = C (p.eval a * v) := by rw [← C_mul, mul_comm]
    _ = C 1 := by rw [hv]
    _ = 1 := C_1

/-- **Coprimality lifts along Jacobson-radical quotients for monic polynomials.**
If `J ≤ Jac(R)` and two monic polynomials become coprime modulo `J`, then they
were already coprime over `R`.

The proof uses the resultant: for a monic polynomial, being coprime is equivalent
to the resultant being a unit.  The resultant is a unit modulo `J`; since the
quotient map is local when `J ≤ Jac(R)`, it was already a unit in `R`. -/
theorem isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson {J : Ideal R}
    (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R)) {g h : R[X]} (hg : g.Monic)
    (hh : h.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk J)) (h.map (Ideal.Quotient.mk J))) :
    IsCoprime g h := by
  rcases subsingleton_or_nontrivial R with _ | hR
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  have hJtop : J ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ Ideal.jacobson (⊥ : Ideal R) :=
      hJ (htop ▸ Submodule.mem_top)
    rw [Ideal.mem_jacobson_bot] at h1
    have h0 := h1 (-1)
    rw [one_mul, neg_add_cancel] at h0
    exact not_isUnit_zero h0
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hJ
  rw [← Polynomial.isUnit_resultant_iff_isCoprime hg]
  refine IsUnit.of_map (Ideal.Quotient.mk J) _ ?_
  have hres :
      IsUnit (Polynomial.resultant (g.map (Ideal.Quotient.mk J))
        (h.map (Ideal.Quotient.mk J))) :=
    (Polynomial.isUnit_resultant_iff_isCoprime (hg.map _)).mpr hcop
  rwa [show (g.map (Ideal.Quotient.mk J)).natDegree = g.natDegree
        from hg.natDegree_map _,
      show (h.map (Ideal.Quotient.mk J)).natDegree = h.natDegree
        from hh.natDegree_map _,
      Polynomial.resultant_map_map] at hres

end Polynomial
