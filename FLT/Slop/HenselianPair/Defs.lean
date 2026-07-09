/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Coprime
public import FLT.Slop.HenselianPair.HenselianRing

/-!
# Henselian pairs

A pair `(R, I)` is a **Henselian pair** if `I` is contained in the Jacobson radical of `R` and
every monic polynomial whose reduction modulo `I` factors as a product of two monic *coprime*
polynomials lifts to a matching factorisation over `R` (Stacks Tag 09XE).

This file gives the definition, the bridge to mathlib's simple-root-lifting predicate
`HenselianRing`, and the two basic examples `(R, ⊥)` and a Henselian local ring.

## Main definitions

* `IsHenselianPair R I` — the factorisation-lifting definition of a Henselian pair.

## Main results

* `IsHenselianPair.henselianRing` — a Henselian pair satisfies mathlib's `HenselianRing`.
* `IsHenselianPair.henselianLocalRing` — a local ring Henselian at its maximal ideal is a
  `HenselianLocalRing`.
* `IsHenselianPair.existsUnique_root_lift_of_isUnit_derivative` — the simple-root lift is unique
  in its congruence class.
* `IsHenselianPair.bot` — `(R, ⊥)` is a Henselian pair.

## References

* [Stacks Project, Tag 09XE](https://stacks.math.columbia.edu/tag/09XE)
* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

/-- A pair `(R, I)` is a **Henselian pair** if `I` is contained in the Jacobson
radical and every monic polynomial whose reduction modulo `I` factors as a
product of two monic *coprime* polynomials lifts to a matching factorisation
over `R` (Stacks Tag 09XE). -/
@[stacks 09XE]
class IsHenselianPair (R : Type*) [CommRing R] (I : Ideal R) : Prop where
  /-- `I` is contained in the Jacobson radical of `R`. -/
  le_jacobson : I ≤ Ideal.jacobson ⊥
  /-- Coprime monic factorisations lift from `R/I` to `R`. -/
  exists_lift_factorization : ∀ (f : R[X]), f.Monic →
    ∀ {g₀ h₀ : (R ⧸ I)[X]}, g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ f = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

namespace IsHenselianPair

/-- A Henselian pair is Henselian in the simple-root-lifting sense of mathlib's
`HenselianRing`: a simple root of a monic polynomial over `R/I` lifts to a root
over `R`. (Stacks Tag 09XE; the factorisation definition implies the
root-lifting property.) -/
@[stacks 09XI "(1) => (5), root-lifting form"]
theorem henselianRing {I : Ideal R} (h : IsHenselianPair R I) : HenselianRing R I where
  jac := h.le_jacobson
  is_henselian := by
    intro f hf a₀ h₁ h₂
    rcases subsingleton_or_nontrivial R with _ | _
    · exact ⟨a₀, Subsingleton.elim _ _, by rw [sub_self]; exact I.zero_mem⟩
    -- `I ≠ ⊤`, hence `R/I` is nontrivial.
    have hItop : I ≠ ⊤ := by
      intro hI
      have h1 : (1 : R) ∈ Ideal.jacobson ⊥ := h.le_jacobson (hI ▸ Submodule.mem_top)
      rw [Ideal.mem_jacobson_bot] at h1
      have h0 := h1 (-1)
      rw [one_mul, neg_add_cancel] at h0
      exact not_isUnit_zero h0
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    -- `a₀` reduces to a simple root of `f.map (mk I)`.
    have hroot : (f.map (Ideal.Quotient.mk I)).IsRoot (Ideal.Quotient.mk I a₀) := by
      change (f.map (Ideal.Quotient.mk I)).eval (Ideal.Quotient.mk I a₀) = 0
      rw [eval_map_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact h₁
    -- factor out the linear factor over `R/I`.
    obtain ⟨h₀, hfact⟩ := dvd_iff_isRoot.mpr hroot
    have hfb_monic : (f.map (Ideal.Quotient.mk I)).Monic := hf.map _
    have hg0_monic : (X - C (Ideal.Quotient.mk I a₀)).Monic := monic_X_sub_C _
    have hh0_monic : h₀.Monic := by
      apply hg0_monic.of_mul_monic_left
      rwa [← hfact]
    -- the cofactor `h₀` does not vanish at `a₀`, i.e. the root is simple.
    have hh0_eval : IsUnit (h₀.eval (Ideal.Quotient.mk I a₀)) := by
      have hd : (derivative (f.map (Ideal.Quotient.mk I))).eval (Ideal.Quotient.mk I a₀)
          = h₀.eval (Ideal.Quotient.mk I a₀) := by
        rw [hfact]
        simp [derivative_mul, eval_mul, eval_add, eval_sub, eval_X, eval_C]
      have he : (derivative (f.map (Ideal.Quotient.mk I))).eval (Ideal.Quotient.mk I a₀)
          = Ideal.Quotient.mk I (f.derivative.eval a₀) := by
        rw [derivative_map, eval_map_apply]
      rw [hd] at he
      rw [he]; exact h₂
    have hcop : IsCoprime (X - C (Ideal.Quotient.mk I a₀)) h₀ :=
      isCoprime_X_sub_C_of_isUnit_eval hh0_eval
    -- lift the factorisation to `R`.
    obtain ⟨g, hh, hg_monic, -, hfgh, hgmap, -⟩ :=
      h.exists_lift_factorization f hf (g₀ := X - C (Ideal.Quotient.mk I a₀)) (h₀ := h₀)
        hg0_monic hh0_monic hcop (by rw [hfact])
    -- `g` is monic of degree one, so it is `X - C a` for the lift `a` we seek.
    have hgdeg : g.natDegree = 1 := by
      have hmap := hg_monic.natDegree_map (Ideal.Quotient.mk I)
      rw [hgmap, natDegree_X_sub_C] at hmap
      exact hmap.symm
    have hgeq : g = X + C (g.coeff 0) := hg_monic.eq_X_add_C hgdeg
    refine ⟨-(g.coeff 0), ?_, ?_⟩
    · change f.eval (-(g.coeff 0)) = 0
      rw [hfgh, eval_mul]
      have : g.eval (-(g.coeff 0)) = 0 := by rw [hgeq]; simp
      rw [this, zero_mul]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      have hc0 : Ideal.Quotient.mk I (g.coeff 0) = -(Ideal.Quotient.mk I a₀) := by
        have := congrArg (fun p => Polynomial.coeff p 0) hgmap
        simpa [coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] using this
      rw [map_neg, hc0, neg_neg]

/-- A simple root lift for a Henselian pair is unique in its congruence class.

This is the Jacobson-radical uniqueness argument for simple roots: if two roots
of `f` are congruent to the same `a₀` modulo `I`, and `f' a₀` is a unit modulo
`I`, then the two roots are equal.  No monicity is needed for this uniqueness
statement. -/
theorem root_lift_unique_of_isUnit_derivative {I : Ideal R} (h : IsHenselianPair R I)
    {f : R[X]} {a₀ a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (haI : a - a₀ ∈ I) (hbI : b - a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    a = b := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.root_lift_unique_of_isUnit_derivative ha hb haI hbI hderiv

/-- A Henselian pair has a unique lift of a simple root in the prescribed
congruence class.  This is the `∃!` form of `IsHenselianPair.henselianRing`. -/
theorem existsUnique_root_lift_of_isUnit_derivative {I : Ideal R}
    (h : IsHenselianPair R I) {f : R[X]} (hf : f.Monic) (a₀ : R)
    (hroot : f.eval a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃! a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.existsUnique_root_lift_of_isUnit_derivative hf a₀ hroot hderiv

/-- Uniqueness in the quotient form of the Stacks Tag 09XI root condition for
a Henselian pair.

This uniqueness statement needs only the Jacobson-radical condition, but this
pair-level spelling is convenient when working from `IsHenselianPair R I`. -/
theorem root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one {I : Ideal R}
    (h : IsHenselianPair R I) {f : R[X]} (n : ℕ)
    (hmod : f.map (Ideal.Quotient.mk I) = X ^ n * (X - C (1 : R ⧸ I)))
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one n hmod
    ha hb haI hbI

/-- Uniqueness in the coefficientwise-congruence form of the Stacks Tag 09XI
root condition for a Henselian pair. -/
theorem root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) {f : R[X]} (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I)
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one
    n hcoeff ha hb haI hbI

/-- Uniqueness in the perturbation form of the Stacks Tag 09XI root condition
for a Henselian pair. -/
theorem root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) (n : ℕ) {p : R[X]}
    (hp : ∀ k, p.coeff k ∈ I) {a b : R}
    (ha : (X ^ n * (X - C (1 : R)) + p).IsRoot a)
    (hb : (X ^ n * (X - C (1 : R)) + p).IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one
    n hp ha hb haI hbI

/-- Uniqueness in the literal finite-coefficient form of the Stacks Tag 09XI
root condition for a Henselian pair. -/
theorem root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) (n : ℕ) (a : ℕ → R)
    (ha_coeff : ∀ i ≤ n, a i ∈ I) {x y : R}
    (hx : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot x)
    (hy : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot y)
    (hxI : x - 1 ∈ I) (hyI : y - 1 ∈ I) :
    x = y := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one
    n a ha_coeff hx hy hxI hyI

/-- **The root condition for a Henselian pair**, in the direction supplied by
factorisation lifting (Stacks Tag 09XI, `(1) ⇒ (5)`).

If `f` is monic and `f` reduces modulo `I` to `X ^ n * (X - 1)`, then `f` has a
unique root congruent to `1` modulo `I`. -/
theorem existsUnique_root_one_mod_of_map_eq_X_pow_mul_X_sub_C_one {I : Ideal R}
    (h : IsHenselianPair R I) {f : R[X]} (hf : f.Monic) (n : ℕ)
    (hmod : f.map (Ideal.Quotient.mk I) =
      X ^ n * (X - C (1 : R ⧸ I))) :
    ∃! a : R, f.IsRoot a ∧ a - 1 ∈ I := by
  letI : HenselianRing R I := h.henselianRing
  exact HenselianRing.existsUnique_root_one_mod_of_map_eq_X_pow_mul_X_sub_C_one
    hf n hmod

/-- Coefficientwise-congruence form of the Stacks Tag 09XI root condition.

If the coefficients of `f - X ^ n * (X - 1)` all lie in `I`, then `f` has a
unique root congruent to `1` modulo `I`. -/
theorem existsUnique_root_one_mod_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) {f : R[X]} (hf : f.Monic) (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I) :
    ∃! a : R, f.IsRoot a ∧ a - 1 ∈ I := by
  apply h.existsUnique_root_one_mod_of_map_eq_X_pow_mul_X_sub_C_one hf n
  exact Polynomial.map_eq_X_pow_mul_X_sub_C_one_of_forall_coeff_sub_mem n hcoeff

/-- Stacks-style perturbation form of the Tag 09XI root condition.

If `p` has all coefficients in `I`, then every monic polynomial of the form
`X ^ n * (X - 1) + p` has a unique root congruent to `1` modulo `I`. -/
theorem existsUnique_root_one_mod_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) (n : ℕ) {p : R[X]}
    (hp : ∀ k, p.coeff k ∈ I) (hf : (X ^ n * (X - C (1 : R)) + p).Monic) :
    ∃! a : R, (X ^ n * (X - C (1 : R)) + p).IsRoot a ∧ a - 1 ∈ I := by
  apply h.existsUnique_root_one_mod_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one hf n
  intro k
  simpa [coeff_sub, coeff_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp k

/-- Finite-coefficient form of the Stacks Tag 09XI root condition.

If `a₀, ..., aₙ` lie in `I`, then the Stacks polynomial
`X ^ n * (X - 1) + aₙ X ^ n + ... + a₀` has a unique root congruent to `1`
modulo `I`. This is condition (5) in Tag 09XI in its literal finite-sum shape,
for the direction supplied by a Henselian pair. -/
@[stacks 09XI "(5)"]
theorem existsUnique_root_one_mod_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} (h : IsHenselianPair R I) (n : ℕ) (a : ℕ → R)
    (ha : ∀ i ≤ n, a i ∈ I) :
    ∃! x : R,
      (X ^ n * (X - C (1 : R)) +
        ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot x ∧ x - 1 ∈ I := by
  have hf :
      (X ^ n * (X - C (1 : R)) +
        ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).Monic :=
    Polynomial.monic_X_pow_mul_X_sub_C_one_add_sum_range_C_mul_X_pow n a
  apply h.existsUnique_root_one_mod_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one n ?_ hf
  intro k
  rw [Polynomial.coeff_sum_range_C_mul_X_pow n a k]
  split_ifs with hk
  · exact ha k hk
  · exact I.zero_mem

/-- **Local-ring bridge, easy direction** (Stacks Tag 04GH / 0DYD, `←`).
If `(R, 𝔪)` is a Henselian pair at the maximal ideal of a local ring, then `R`
is a Henselian local ring. (The converse is the coprime-factorisation lift, which
is the hard direction and a mathlib TODO.) -/
@[stacks 04GH]
theorem henselianLocalRing [IsLocalRing R]
    (h : IsHenselianPair R (IsLocalRing.maximalIdeal R)) : HenselianLocalRing R where
  is_henselian f hf a₀ h₁ h₂ :=
    h.henselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk _))

/-- The pair `(R, ⊥)` is a Henselian pair for any commutative ring `R`: reduction
modulo `⊥` is an isomorphism, so any coprime monic factorisation of the reduction
transports back to `R`. In particular a field `K` gives the Henselian pair `(K, ⊥)`. -/
theorem bot : IsHenselianPair R (⊥ : Ideal R) where
  le_jacobson := bot_le
  exists_lift_factorization := by
    intro f _ g₀ h₀ hg₀ hh₀ _ hfact
    -- `e : R ⧸ ⊥ ≃+* R` is the canonical isomorphism.
    set e := RingEquiv.quotientBot R with he
    set mk₀ := Ideal.Quotient.mk (⊥ : Ideal R) with hmk₀
    -- `e ∘ mk₀ = id` and `mk₀ ∘ e = id`, as ring homomorphisms.
    have h1 : e.toRingHom.comp mk₀ = RingHom.id R :=
      RingHom.ext fun r => RingEquiv.quotientBot_mk r
    have h2 : (mk₀ : R →+* R ⧸ (⊥ : Ideal R)).comp e.toRingHom = RingHom.id _ :=
      RingHom.ext fun x => by
        rw [RingHom.comp_apply, RingHom.id_apply, hmk₀, ← RingEquiv.quotientBot_symm_mk]
        exact e.symm_apply_apply x
    refine ⟨g₀.map e.toRingHom, h₀.map e.toRingHom, hg₀.map _, hh₀.map _, ?_, ?_, ?_⟩
    · rw [← Polynomial.map_mul, ← hfact, Polynomial.map_map, h1, Polynomial.map_id]
    · rw [Polynomial.map_map, h2, Polynomial.map_id]
    · rw [Polynomial.map_map, h2, Polynomial.map_id]

end IsHenselianPair
