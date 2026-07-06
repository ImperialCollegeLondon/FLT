/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Maps
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Integral
public import Mathlib.RingTheory.Localization.Defs

@[expose] public section

/-!
# The localization of the integers at a prime

For a prime number `p`, `Zlocal p` is the localization of `ℤ` obtained by
inverting all integers coprime to `p`. This file constructs its canonical map
to a field of characteristic zero and proves basic results about units and
clearing denominators.

The file also defines pointwise casting of integer-valued class functions and
the induced action of `Zlocal p` on class functions over a characteristic-zero
field.
-/

universe u v

/-- Integers coprime to `p` (via `natAbs`) as a submonoid of `ℤ`. -/
def Zlocal.intCoprimeSubmonoid (p : ℕ) : Submonoid ℤ where
  carrier := { z : ℤ | Nat.Coprime z.natAbs p }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simpa [Int.natAbs_mul] using (Nat.Coprime.mul_left ha hb)

/--
The `p`-local integers `ℤ_(p)`.

This is the localization of `ℤ` obtained by inverting all integers coprime to `p`.
Equivalently, for prime `p`, its elements can be viewed as rational numbers
`a / b` whose denominator `b` is not divisible by `p`.
-/
abbrev Zlocal (p : ℕ) := Localization (Zlocal.intCoprimeSubmonoid p)

namespace Zlocal

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

lemma intCoprimeSubmonoid.not_dvd
    {p : ℕ} [Fact p.Prime] (m : intCoprimeSubmonoid p) :
    ¬ (p : ℤ) ∣ (m : ℤ) := by
  intro h_dvd
  have h_coprime : Nat.Coprime (Int.natAbs (m : ℤ)) p := m.property
  have h_dvd_nat : p ∣ Int.natAbs (m : ℤ) := by
    exact Int.ofNat_dvd_left.mp h_dvd
  have h_not_dvd :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h_coprime.symm
  exact h_not_dvd h_dvd_nat

section CanonicalMap

variable {k : Type u} [Field k] [CharZero k]

/--
The canonical ring homomorphism from `Zlocal p` to a field of characteristic
zero.
-/
noncomputable def toK (p : ℕ) [Fact p.Prime] :
    Zlocal p →+* k := by
  -- Use the universal property of the localization
  refine IsLocalization.lift
    (R := ℤ)
    (M := intCoprimeSubmonoid p)
    (S := Zlocal p)
    (P := k)
    (g := Int.castRingHom k)
    ?_
  intro y
  refine (isUnit_iff_ne_zero).2 ?_
  have hy0 : (y : ℤ) ≠ 0 := by
    intro hy
    have hycop : Nat.Coprime ((y : ℤ).natAbs) p := y.property
    have : Nat.Coprime 0 p := by simpa [hy] using hycop
    have hp1 : p = 1 := (Nat.coprime_zero_left p).1 this
    exact (Fact.out : Nat.Prime p).ne_one hp1
  change ((y : ℤ) : k) ≠ 0
  exact Int.cast_ne_zero.mpr hy0

/--
The `p`-local integers are nontrivial, as witnessed by their canonical map to
any characteristic-zero field.
-/
lemma nontrivial
    {k : Type u} [Field k] [CharZero k]
    (p : ℕ) [Fact p.Prime] :
    Nontrivial (Zlocal p) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h01
  have h01k : (0 : k) = 1 := by
    simpa using congrArg (Zlocal.toK (k := k) p) h01
  exact zero_ne_one h01k

end CanonicalMap

section Units
/--
A natural number not divisible by `p` is a unit in `Zlocal p`.
-/
lemma isUnit_natCast (p : ℕ) [Fact p.Prime] (m : ℕ) (h : ¬ (m : ZMod p) = 0) :
  IsUnit (m : Zlocal p) := by
  rw [← Int.cast_natCast (R := ZMod p) m] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  norm_cast at h
  have h_coprime : Nat.Coprime m p :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr h |>.symm
  let u : intCoprimeSubmonoid p := ⟨(m : ℤ), by simpa [intCoprimeSubmonoid] using h_coprime⟩
  have h_eq : ((m : ℤ) : Zlocal p) = algebraMap ℤ (Zlocal p) u := by
    exact Eq.symm (eq_intCast (algebraMap ℤ (Zlocal p)) ↑u)
  rw [← Int.cast_natCast (R := Zlocal p) m]
  rw [h_eq]
  exact IsLocalization.map_units (Zlocal p) u

/--
Every element congruent to `1` modulo `p` is a unit in `Zlocal p`.
-/
lemma isUnit_one_add_p_mul {p : ℕ} [Fact p.Prime] (z : Zlocal p) :
    IsUnit (1 + (p : Zlocal p) * z) := by
  obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.surj (intCoprimeSubmonoid p) z
  dsimp only at hz
  have hz_cast : z * (m.val : Zlocal p) = (a : Zlocal p) := by
    have h_tmp := hz
    simp only [eq_intCast] at h_tmp
    exact h_tmp
  have h_alg : (1 + (p : Zlocal p) * z) * (m : Zlocal p)
      = (((m : ℤ) + (p : ℤ) * a) : Zlocal p) := by
    calc (1 + (p : Zlocal p) * z) * (m : Zlocal p)
      _ = (m : Zlocal p) + (p : Zlocal p) * (z * (m : Zlocal p)) := by ring
      _ = (m : Zlocal p) + (p : Zlocal p) * (a : Zlocal p) := by rw [hz_cast]
      _ = (((m : ℤ) + (p : ℤ) * a) : Zlocal p) := by push_cast; ring
  have h_num_coprime : ((m : ℤ) + (p : ℤ) * a) ∈ intCoprimeSubmonoid p := by
    simp only [intCoprimeSubmonoid, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
    change Int.gcd ((m : ℤ) + (p : ℤ) * a) (p : ℤ) = 1
    rw [Int.gcd_add_mul_left_left]
    exact m.property
  have h_num_unit : IsUnit (((m : ℤ) + (p : ℤ) * a) : Zlocal p) := by
    have h_raw := IsLocalization.map_units (Zlocal p) (⟨(m : ℤ) + (p : ℤ) * a, h_num_coprime⟩
      : intCoprimeSubmonoid p)
    simp only [eq_intCast] at h_raw
    push_cast at h_raw
    exact h_raw
  rw [← h_alg] at h_num_unit
  exact (IsUnit.mul_iff.mp h_num_unit).1

end Units

section CanonicalMap

variable {k : Type u} [Field k] [CharZero k]

/--
The canonical map `Zlocal p →+* k` sends the inverse of a unit represented by
a natural number to the inverse of its image in `k`.
-/
lemma toK_unit_inv_eq_inv_natCast
    (p : ℕ) [Fact p.Prime]
    (m : ℕ)
    (hunit : IsUnit (m : Zlocal p)) :
    toK (k := k) (p := p) (↑(hunit.unit⁻¹) : Zlocal p) =
      (m : k)⁻¹ := by
  have hu : (↑hunit.unit : Zlocal p) = (m : Zlocal p) := by
    simp only [IsUnit.unit_spec]
  calc
    Zlocal.toK (k := k) (p := p) (↑(hunit.unit⁻¹) : Zlocal p)
        = (Zlocal.toK (k := k) (p := p) (↑hunit.unit : Zlocal p))⁻¹ := by
            simp
    _   = (Zlocal.toK (k := k) (p := p) (m : Zlocal p))⁻¹ := by
            simp only [IsUnit.unit_spec, map_natCast]
    _   = ((m : k))⁻¹ := by
            simp [Zlocal.toK, map_natCast]

/--
The characteristic-zero field `k` as an algebra over `Zlocal p`, through the
canonical map `Zlocal.toK`.
-/
noncomputable instance instAlgebra
    (p : ℕ) [Fact p.Prime] :
    Algebra (Zlocal p) k :=
  (toK (k := k) (p := p)).toAlgebra

end Zlocal.CanonicalMap

namespace ClassFun
namespace Zlocal

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type v} [Group G]

lemma smul_apply
    (p : ℕ) [Fact p.Prime]
    (c : Zlocal p) (f : ClassFun k G) (g : G) :
    (c • f) g = Zlocal.toK (k := k) (p := p) c * f g := by
  apply ClassFun.smul_apply

@[simp]
lemma smul_eq_int_smul
  (p : ℕ) [Fact p.Prime]
  (n : ℤ) (f : ClassFun k G) :
  (((n : Zlocal p) • f) : ClassFun k G) = ((n : k) • f) := by
  ext g
  change (Zlocal.toK (k := k) (p := p) (n : Zlocal p)) * f g = (n : k) * f g
  have : Zlocal.toK (k := k) (p := p) (n : Zlocal p) = (n : k) := by
    simp only [Zlocal.toK, map_intCast]
  simp only [this]

open Classical in
/--
Multiplying the action of the localized element `a / m ∈ ℤ_(p)` by its
denominator `m` gives the integral action by `a`.
-/
lemma clear_denom
    (p : ℕ) [Fact p.Prime]
    (a : ℤ) (m : Zlocal.intCoprimeSubmonoid p) (y : ClassFun k G) :
    ((m : ℤ) •
        (Zlocal.toK (k := k) (p := p)
          (IsLocalization.mk' (Zlocal p) a m) • y))
      =
    (a : ℤ) • y := by
  ext g
  simp only [zsmul_eq_mul, Algebra.mul_smul_comm, ClassFun.smul_apply, mul_apply, intCast_apply,
    smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [mul_comm]
  have h_spec := IsLocalization.mk'_spec (Zlocal p) a m
  have h_apply :=
    congrArg (Zlocal.toK (k := k) (p := p)) h_spec
  rw [map_mul] at h_apply
  simp only [eq_intCast, map_intCast] at h_apply
  rw [← h_apply]
  exact Int.cast_comm
    (m : ℤ)
    (Zlocal.toK (k := k) (p := p)
      (IsLocalization.mk' (Zlocal p) a m))


end Zlocal

end ClassFun
