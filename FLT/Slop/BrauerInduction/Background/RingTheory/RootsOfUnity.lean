/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Sums of powers of roots of unity

This file provides finiteness helpers for the `rootsOfUnity` submonoid and the
vanishing of a sum of powers of a nontrivial root of unity.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

namespace rootsOfUnity

/-- In Mathlib v4.32 the `rootsOfUnity` submonoid only carries a `Finite` instance, not a
`Fintype` one; we supply the missing `Fintype` locally so that finite sums over
`rootsOfUnity m k` elaborate. -/
noncomputable local instance instFintypeRootsOfUnity
    (m : ℕ) (k : Type u) [CommRing k] [IsDomain k] [NeZero m] :
    Fintype (rootsOfUnity m k) :=
  Fintype.ofFinite _

/--
The sum of the `n`-th powers of all `m`-th roots of unity is zero when `m` does
not divide `n`.
-/
lemma sum_zpow_eq_zero_of_not_dvd
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (m : ℕ) [NeZero m] :
    ∀ (n : ℤ), (¬ (m : ℤ) ∣ n) →
      (∑ ζ : rootsOfUnity m k, (((ζ : kˣ) ^ n : kˣ) : k)) = 0 := by
  intro n h_div
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity m k)
  let ω : k := (((g : kˣ) ^ n : kˣ) : k)
  have h_ω_ne_one : ω ≠ 1 := by
    intro h_eq
    change (((g : kˣ) ^ n : kˣ) : k) = 1 at h_eq
    have h1 : (g : kˣ) ^ n = 1 := by
      obtain ⟨val, property⟩ := g
      ext : 1
      simp_all only [Units.val_zpow_eq_zpow_val, Units.val_one]
    have h2 : g ^ n = 1 := by
      obtain ⟨val, property⟩ := g
      ext : 2
      simp_all only [SubgroupClass.coe_zpow, Units.val_one, OneMemClass.coe_one]
    have h_ord : (orderOf g : ℤ) = m := by
      have h_card1 : orderOf g = Nat.card (rootsOfUnity m k) :=
          orderOf_eq_card_of_forall_mem_zpowers hg
      have h_card2 : Nat.card (rootsOfUnity m k) = m :=
        HasEnoughRootsOfUnity.natCard_rootsOfUnity k m
      rw [h_card1, h_card2]
    have h_dvd : (orderOf g : ℤ) ∣ n := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [h_ord] at h_dvd
    exact h_div h_dvd
  set S := ∑ ζ : rootsOfUnity m k, (((ζ : kˣ) ^ n : kˣ) : k)
  have h_shift : ω * S = S := by
    dsimp [S, ω]
    rw [Finset.mul_sum]
    apply Finset.sum_bij (fun ζ _ => g * ζ)
    case hi =>
      intro ζ _
      exact Finset.mem_univ _
    case h =>
      intro ζ _
      have h_kUnits : ((g * ζ : rootsOfUnity m k) : kˣ)^n = (g : kˣ)^n * (ζ : kˣ)^n := by
        push_cast
        exact mul_zpow _ _ _
      rw [h_kUnits]
      push_cast
      rfl
    case i_inj =>
      intro a _ b _ h_eq
      exact mul_left_cancel h_eq
    case i_surj =>
      intro b _
      use g⁻¹ * b
      refine ⟨Finset.mem_univ _, ?_⟩
      exact mul_inv_cancel_left g b
  have h_zero : (ω - 1) * S = 0 := by
    calc (ω - 1) * S
      _ = ω * S - S := by exact sub_one_mul ω S
      _ = S - S := by rw [h_shift]
      _ = 0 := sub_self _
  cases mul_eq_zero.mp h_zero with
  | inl h =>
    exfalso
    exact h_ω_ne_one (sub_eq_zero.mp h)
  | inr h =>
    exact h

/-- A nonzero-order root of unity is integral over `ℤ`. -/
lemma isIntegral_of_ne_zero
    (k : Type u) [CommRing k]
    (n : ℕ) (hn : n ≠ 0)
    (ζ : rootsOfUnity n k) :
    IsIntegral ℤ (ζ.val : k) := by
  have hpow_units : (ζ.1 : kˣ) ^ n = 1 := by
    have hzmem : (ζ.1 : kˣ) ∈ rootsOfUnity n k := ζ.property
    dsimp [rootsOfUnity] at hzmem
    exact hzmem
  have hpow : (ζ.val : k) ^ n = 1 := by
    simpa using congrArg (fun u : kˣ => (u : k)) hpow_units
  refine ⟨(Polynomial.X ^ n - Polynomial.C (1 : ℤ) : Polynomial ℤ), ?_, ?_⟩
  · simpa using
      (Polynomial.monic_X_pow_sub_C (R := ℤ) (a := (1 : ℤ)) (n := n) hn)
  · simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, Polynomial.eval₂_sub,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
    simp only [← hpow, sub_self]

/-- A `|G|`-th root of unity is integral over `ℤ` -/
lemma isIntegral
    (k : Type u) [CommRing k]
    (G : Type v) [Group G] [NeZero (Nat.card G)]
    (ζ : rootsOfUnity (Nat.card G) k) :
    IsIntegral ℤ (ζ.val : k) := by
  refine isIntegral_of_ne_zero k (Nat.card G) ?_ ζ
  exact Ne.symm (NeZero.ne' (Nat.card G))

end rootsOfUnity

end Slop
