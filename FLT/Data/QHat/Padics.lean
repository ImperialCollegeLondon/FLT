/-
Copyright (c) 2026 Pedro Paulo Marques do Nascimento. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pedro Paulo Marques do Nascimento
-/
module

public import FLT.Data.QHat
public import FLT.NumberField.Padics.RestrictedProduct
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The profinite integers and the finite rational adeles

This file identifies the explicit inverse-limit model `ZHat` with the product of the rings of
`p`-adic integers. Extending scalars from `ℤ` to `ℚ` then identifies `QHat` with the restricted
product of the fields `ℚ_[p]` with respect to `ℤ_[p]`.

## Main definitions

* `ZHat.padicIntEquiv`: the ring equivalence `ZHat ≃+* (p : Nat.Primes) → ℤ_[p]`.
* `Rat.PadicRestrictedProduct`: the restricted product of the `p`-adic fields with respect to
  their rings of integers.
* `QHat.padicRestrictedProductEquiv`: the `ℚ`-algebra equivalence between `QHat` and
  `Rat.PadicRestrictedProduct`.
-/

@[expose] public section

open scoped RestrictedProduct TensorProduct

namespace ZHat

local instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

/-- The projection from the profinite integers to the `p`-adic integers. -/
noncomputable def toPadicInt (p : Nat.Primes) : ZHat →+* ℤ_[p] :=
  PadicInt.lift (f := fun n => ZHat.toZMod
    ⟨(p : ℕ) ^ n, pow_pos p.2.pos n⟩) (by
      intro k₁ k₂ hk
      ext z
      exact z.prop
        ⟨(p : ℕ) ^ k₁, pow_pos p.2.pos k₁⟩
        ⟨(p : ℕ) ^ k₂, pow_pos p.2.pos k₂⟩
        (pow_dvd_pow (p : ℕ) hk))

theorem toPadicInt_spec (p : Nat.Primes) (n : ℕ) :
    (PadicInt.toZModPow n).comp (toPadicInt p) =
      ZHat.toZMod ⟨(p : ℕ) ^ n, pow_pos p.2.pos n⟩ := by
  apply PadicInt.lift_spec

/-- The map from the profinite integers to the product of the `p`-adic integers. -/
noncomputable def toPadicInts : ZHat →+* ((p : Nat.Primes) → ℤ_[p]) :=
  RingHom.pi fun p => toPadicInt p

theorem toPadicInts_injective : Function.Injective toPadicInts := by
  intro x y hxy
  apply ZHat.ext
  intro N
  apply (ZMod.equivPi (n := N) N.ne_zero).injective
  funext p
  let p' : Nat.Primes := ⟨p, Nat.prime_of_mem_primeFactors p.2⟩
  have hp := congrFun hxy p'
  have hpmod := congrArg
    (fun t : ℤ_[p'] => PadicInt.toZModPow ((N : ℕ).factorization p) t) hp
  have hx : PadicInt.toZModPow ((N : ℕ).factorization p) (toPadicInt p' x) =
      x ⟨p ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ := by
    change ((PadicInt.toZModPow ((N : ℕ).factorization p)).comp (toPadicInt p')) x = _
    rw [toPadicInt_spec]
    rfl
  have hy : PadicInt.toZModPow ((N : ℕ).factorization p) (toPadicInt p' y) =
      y ⟨p ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ := by
    change ((PadicInt.toZModPow ((N : ℕ).factorization p)).comp (toPadicInt p')) y = _
    rw [toPadicInt_spec]
    rfl
  change PadicInt.toZModPow ((N : ℕ).factorization p) (toPadicInt p' x) =
    PadicInt.toZModPow ((N : ℕ).factorization p) (toPadicInt p' y) at hpmod
  rw [hx, hy] at hpmod
  have hdiv : (p : ℕ) ^ (N : ℕ).factorization p ∣ (N : ℕ) :=
    (p'.2.pow_dvd_iff_le_factorization N.ne_zero).2 le_rfl
  have hprod : (p : ℕ) ^ (N : ℕ).factorization p ∣
      ∏ q : (N : ℕ).primeFactors, (q : ℕ) ^ (N : ℕ).factorization q :=
    Finset.dvd_prod_of_mem
      (fun q : (N : ℕ).primeFactors => (q : ℕ) ^ (N : ℕ).factorization q)
      (Finset.mem_univ p)
  let left : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (N : ℕ).factorization p) :=
    (ZMod.castHom hprod _).comp
      (ZMod.ringEquivCongr (Nat.prod_primeFactors_coe_pow_factorization N.ne_zero)).toRingHom
  let right : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (N : ℕ).factorization p) :=
    ZMod.castHom hdiv _
  have hmaps : left = right := Subsingleton.elim _ _
  have hxcrt : (ZMod.equivPi (n := N) N.ne_zero) (x N) p =
      x ⟨p ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ := by
    rw [ZMod.equivPi, RingEquiv.trans_apply, ZMod.prodEquivPi_apply]
    rw [← x.prop ⟨(p : ℕ) ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ N hdiv]
    change left (x N) = right (x N)
    exact RingHom.congr_fun hmaps (x N)
  have hycrt : (ZMod.equivPi (n := N) N.ne_zero) (y N) p =
      y ⟨p ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ := by
    rw [ZMod.equivPi, RingEquiv.trans_apply, ZMod.prodEquivPi_apply]
    rw [← y.prop ⟨(p : ℕ) ^ (N : ℕ).factorization p, pow_pos p'.2.pos _⟩ N hdiv]
    change left (y N) = right (y N)
    exact RingHom.congr_fun hmaps (y N)
  rw [hxcrt, hycrt]
  exact hpmod

/-- The residue modulo `N` assembled from the `p`-adic components using the Chinese remainder
theorem. -/
noncomputable def crtResidue
    (x : (p : Nat.Primes) → ℤ_[p]) (N : ℕ+) : ZMod N :=
  (ZMod.equivPi (n := N) N.ne_zero).symm fun p =>
    @PadicInt.toZModPow p ⟨Nat.prime_of_mem_primeFactors p.2⟩ ((N : ℕ).factorization p)
      (x ⟨p, Nat.prime_of_mem_primeFactors p.2⟩)

theorem crtResidue_spec
    (x : (p : Nat.Primes) → ℤ_[p]) (N : ℕ+) (p : (N : ℕ).primeFactors) :
    (ZMod.equivPi (n := N) N.ne_zero) (crtResidue x N) p =
      @PadicInt.toZModPow p ⟨Nat.prime_of_mem_primeFactors p.2⟩ ((N : ℕ).factorization p)
        (x ⟨p, Nat.prime_of_mem_primeFactors p.2⟩) := by
  simp [crtResidue]

theorem equivPi_apply_eq_cast
    (N : ℕ+) (p : (N : ℕ).primeFactors)
    (hdiv : (p : ℕ) ^ (N : ℕ).factorization p ∣ (N : ℕ)) (z : ZMod N) :
    (ZMod.equivPi (n := N) N.ne_zero) z p =
      ZMod.castHom hdiv (ZMod ((p : ℕ) ^ (N : ℕ).factorization p)) z := by
  rw [ZMod.equivPi, RingEquiv.trans_apply, ZMod.prodEquivPi_apply]
  have hprod : (p : ℕ) ^ (N : ℕ).factorization p ∣
      ∏ q : (N : ℕ).primeFactors, (q : ℕ) ^ (N : ℕ).factorization q :=
    Finset.dvd_prod_of_mem
      (fun q : (N : ℕ).primeFactors => (q : ℕ) ^ (N : ℕ).factorization q)
      (Finset.mem_univ p)
  let left : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (N : ℕ).factorization p) :=
    (ZMod.castHom hprod _).comp
      (ZMod.ringEquivCongr (Nat.prod_primeFactors_coe_pow_factorization N.ne_zero)).toRingHom
  let right : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (N : ℕ).factorization p) :=
    ZMod.castHom hdiv _
  change left z = right z
  exact RingHom.congr_fun (Subsingleton.elim _ _) z

/-- The profinite integer whose residue modulo each `N` is assembled from its `p`-adic
components. -/
noncomputable def fromPadicInts
    (x : (p : Nat.Primes) → ℤ_[p]) : ZHat :=
  ⟨fun N => crtResidue x N, by
    intro D N hDN
    apply (ZMod.equivPi (n := D) D.ne_zero).injective
    funext p
    let p' : Nat.Primes := ⟨p, Nat.prime_of_mem_primeFactors p.2⟩
    have hpD : (p : ℕ) ^ (D : ℕ).factorization p ∣ (D : ℕ) :=
      (p'.2.pow_dvd_iff_le_factorization D.ne_zero).2 le_rfl
    have hp_dvd_N : (p : ℕ) ∣ (N : ℕ) :=
      (Nat.dvd_of_mem_primeFactors p.2).trans hDN
    let pN : (N : ℕ).primeFactors :=
      ⟨p, p'.2.mem_primeFactors hp_dvd_N N.ne_zero⟩
    have hpN : (p : ℕ) ^ (N : ℕ).factorization p ∣ (N : ℕ) :=
      (p'.2.pow_dvd_iff_le_factorization N.ne_zero).2 le_rfl
    have he : (D : ℕ).factorization p ≤ (N : ℕ).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right hDN D.ne_zero N.ne_zero
    have hpow : (p : ℕ) ^ (D : ℕ).factorization p ∣
        (p : ℕ) ^ (N : ℕ).factorization p := pow_dvd_pow (p : ℕ) he
    calc
      (ZMod.equivPi (n := D) D.ne_zero)
          (ZMod.castHom hDN (ZMod D) (crtResidue x N)) p =
          ZMod.castHom hpD _ (ZMod.castHom hDN (ZMod D) (crtResidue x N)) :=
        equivPi_apply_eq_cast D p hpD _
      _ = ZMod.castHom hpow _
          (ZMod.castHom hpN _ (crtResidue x N)) := by
        let left : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (D : ℕ).factorization p) :=
          (ZMod.castHom hpD _).comp (ZMod.castHom hDN _)
        let right : ZMod (N : ℕ) →+* ZMod ((p : ℕ) ^ (D : ℕ).factorization p) :=
          (ZMod.castHom hpow _).comp (ZMod.castHom hpN _)
        change left (crtResidue x N) = right (crtResidue x N)
        exact RingHom.congr_fun (Subsingleton.elim _ _) (crtResidue x N)
      _ = ZMod.castHom hpow _
          ((ZMod.equivPi (n := N) N.ne_zero) (crtResidue x N) pN) := by
        exact congrArg (ZMod.castHom hpow _)
          (equivPi_apply_eq_cast N pN hpN _).symm
      _ = ZMod.castHom hpow _
          (@PadicInt.toZModPow p ⟨p'.2⟩ ((N : ℕ).factorization p) (x p')) := by
        rw [crtResidue_spec]
      _ = @PadicInt.toZModPow p ⟨p'.2⟩ ((D : ℕ).factorization p) (x p') := by
        exact RingHom.congr_fun
          (PadicInt.zmod_cast_comp_toZModPow _ _ he) (x p')
      _ = (ZMod.equivPi (n := D) D.ne_zero) (crtResidue x D) p := by
        exact (crtResidue_spec x D p).symm⟩

theorem crtResidue_prime_pow
    (x : (p : Nat.Primes) → ℤ_[p]) (p : Nat.Primes) (n : ℕ) :
    crtResidue x ⟨(p : ℕ) ^ n, pow_pos p.2.pos n⟩ =
      @PadicInt.toZModPow p ⟨p.2⟩ n (x p) := by
  let P : ℕ+ := ⟨(p : ℕ) ^ n, pow_pos p.2.pos n⟩
  change crtResidue x P = _
  cases n with
  | zero =>
      change (crtResidue x 1 : ZMod 1) = _
      letI : Subsingleton (ZMod (1 : ℕ+)) := ZMod.subsingleton_iff.mpr rfl
      exact Subsingleton.elim _ _
  | succ n =>
      apply (ZMod.equivPi (n := P) P.ne_zero).injective
      funext q
      let q' : Nat.Primes := ⟨q, Nat.prime_of_mem_primeFactors q.2⟩
      have hq_dvd_pow : (q : ℕ) ∣ (p : ℕ) ^ (n + 1) :=
        Nat.dvd_of_mem_primeFactors q.2
      have hq_dvd_p : (q : ℕ) ∣ (p : ℕ) := q'.2.dvd_of_dvd_pow hq_dvd_pow
      have hqp : (q : ℕ) = (p : ℕ) :=
        (Nat.prime_dvd_prime_iff_eq q'.2 p.2).mp hq_dvd_p
      have hq'p : q' = p := Subtype.ext hqp
      have hp_mem : (p : ℕ) ∈ (P : ℕ).primeFactors := by
        simpa [hqp] using q.2
      let pP : (P : ℕ).primeFactors := ⟨p, hp_mem⟩
      have hqeq : q = pP := Subtype.ext hqp
      subst q
      have hfactor : (P : ℕ).factorization pP = n + 1 := by
        simpa [P, pP] using Nat.factorization_pow_self (n := n + 1) p.2
      have hdiv : (pP : ℕ) ^ (P : ℕ).factorization pP ∣ (P : ℕ) :=
        (q'.2.pow_dvd_iff_le_factorization P.ne_zero).2 le_rfl
      rw [crtResidue_spec, equivPi_apply_eq_cast P pP hdiv]
      change @PadicInt.toZModPow q' ⟨q'.2⟩ ((P : ℕ).factorization pP) (x q') = _
      subst q'
      have he : (P : ℕ).factorization pP ≤ n + 1 := hfactor.le
      have hz := RingHom.congr_fun
        (PadicInt.zmod_cast_comp_toZModPow ((P : ℕ).factorization pP) (n + 1) he) (x p)
      convert hz.symm using 1
      · have hp' : (⟨p, Nat.prime_of_mem_primeFactors pP.2⟩ : Nat.Primes) = p :=
          Subtype.ext rfl
        cases hp'
        rfl
      · let left : ℤ_[p] →+* ZMod ((p : ℕ) ^ (P : ℕ).factorization pP) :=
          (ZMod.castHom hdiv _).comp (PadicInt.toZModPow (n + 1))
        let right : ℤ_[p] →+* ZMod ((p : ℕ) ^ (P : ℕ).factorization pP) :=
          (ZMod.castHom (pow_dvd_pow (p : ℕ) he) _).comp (PadicInt.toZModPow (n + 1))
        change left (x p) = right (x p)
        rfl

theorem toPadicInts_fromPadicInts (x : (p : Nat.Primes) → ℤ_[p]) :
    toPadicInts (fromPadicInts x) = x := by
  funext p
  change toPadicInt p (fromPadicInts x) = x p
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  change ((PadicInt.toZModPow n).comp (toPadicInt p)) (fromPadicInts x) = _
  rw [toPadicInt_spec]
  change crtResidue x ⟨(p : ℕ) ^ n, pow_pos p.2.pos n⟩ = _
  exact crtResidue_prime_pow x p n

theorem toPadicInts_surjective : Function.Surjective toPadicInts :=
  fun x => ⟨fromPadicInts x, toPadicInts_fromPadicInts x⟩

/-- The profinite integers are the product of the rings of `p`-adic integers. -/
noncomputable def padicIntEquiv : ZHat ≃+* ((p : Nat.Primes) → ℤ_[p]) :=
  RingEquiv.ofBijective toPadicInts ⟨toPadicInts_injective, toPadicInts_surjective⟩

end ZHat

local instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

namespace Rat

/-- The restricted product of the `p`-adic fields with respect to their rings of integers. -/
abbrev PadicRestrictedProduct :=
  Πʳ (p : Nat.Primes), [ℚ_[p], PadicInt.subring p]

end Rat

private theorem cast_one_div_nat_mul (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    (↑(1 / (n : ℚ)) : ℚ_[p]) * (n : ℚ_[p]) = 1 := by
  have hn' : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [one_div, Rat.cast_inv, Rat.cast_natCast, inv_mul_cancel₀ hn']

namespace ZHat

local instance {p : Nat.Primes} : Fact p.1.Prime := ⟨p.2⟩

/-- The inclusion of the profinite integers into the restricted product of the `p`-adics. -/
noncomputable def toPadicRestrictedProduct : ZHat →+* Rat.PadicRestrictedProduct where
  toFun z := ⟨fun p => (toPadicInt p z : ℚ_[p]),
    Filter.Eventually.of_forall fun p => (toPadicInt p z).2⟩
  map_one' := by ext p; simp
  map_mul' x y := by ext p; simp
  map_zero' := by ext p; simp
  map_add' x y := by ext p; simp

theorem toPadicRestrictedProduct_injective :
    Function.Injective toPadicRestrictedProduct := by
  intro x y h
  apply toPadicInts_injective
  funext p
  apply Subtype.val_injective
  exact congrFun (congrArg Subtype.val h) p

end ZHat

namespace QHat

/-- The `ℤ`-algebra map from `QHat` to the restricted product, obtained from the tensor product
universal property. -/
noncomputable def toPadicRestrictedProductIntAlgHom :
    QHat →ₐ[ℤ] Rat.PadicRestrictedProduct :=
  Algebra.TensorProduct.lift
    (algebraMap ℚ Rat.PadicRestrictedProduct).toIntAlgHom
    ZHat.toPadicRestrictedProduct.toIntAlgHom
    (fun _ _ => .all _ _)

/-- The `ℚ`-algebra map from `QHat` to the restricted product of the `p`-adic fields. -/
noncomputable def toPadicRestrictedProduct :
    QHat →ₐ[ℚ] Rat.PadicRestrictedProduct where
  __ := toPadicRestrictedProductIntAlgHom.toRingHom
  commutes' q := by
    change toPadicRestrictedProductIntAlgHom (q ⊗ₜ[ℤ] (1 : ZHat)) =
      algebraMap ℚ Rat.PadicRestrictedProduct q
    simp [toPadicRestrictedProductIntAlgHom]

@[simp]
theorem toPadicRestrictedProduct_tmul_apply (q : ℚ) (z : ZHat) (p : Nat.Primes) :
    toPadicRestrictedProduct (q ⊗ₜ[ℤ] z) p =
      (q : ℚ_[p]) * (ZHat.toPadicInt p z : ℚ_[p]) := by
  rfl

theorem toPadicRestrictedProduct_injective :
    Function.Injective toPadicRestrictedProduct := by
  intro x y hxy
  apply sub_eq_zero.mp
  suffices hker : ∀ u, toPadicRestrictedProduct u = 0 → u = 0 by
    apply hker (x - y)
    rw [map_sub, hxy, sub_self]
  intro u hu
  obtain ⟨N, z, huform⟩ := canonicalForm u
  rw [huform] at hu
  rw [huform]
  have hz : ZHat.toPadicRestrictedProduct z = 0 := by
    ext p
    have hp0 := congrFun (congrArg Subtype.val hu) p
    change toPadicRestrictedProduct ((1 / (N : ℚ)) ⊗ₜ[ℤ] z) p = (0 : ℚ_[p]) at hp0
    rw [toPadicRestrictedProduct_tmul_apply] at hp0
    have hp : (↑(1 / (N : ℚ)) : ℚ_[p]) * (ZHat.toPadicInt p z : ℚ_[p]) = 0 := by
      exact hp0
    have hN : (↑(1 / (N : ℚ)) : ℚ_[p]) ≠ 0 := by
      have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
      exact Rat.cast_ne_zero.mpr (one_div_ne_zero hNQ)
    exact (mul_eq_zero.mp hp).resolve_left hN
  have hz0 : z = 0 := ZHat.toPadicRestrictedProduct_injective (by simpa using hz)
  simp [hz0]

theorem toPadicRestrictedProduct_surjective :
    Function.Surjective toPadicRestrictedProduct := by
  intro a
  let N : ℕ := a.padicNatDen
  let nums : (p : Nat.Primes) → ℤ_[p] := RestrictedProduct.padicNum a
  let z : ZHat := ZHat.padicIntEquiv.symm nums
  refine ⟨(1 / (N : ℚ)) ⊗ₜ[ℤ] z, ?_⟩
  ext p
  rw [toPadicRestrictedProduct_tmul_apply]
  change (↑(1 / (N : ℚ)) : ℚ_[p]) * (ZHat.toPadicInt p z : ℚ_[p]) = a p
  have hzAll := ZHat.padicIntEquiv.apply_symm_apply nums
  change ZHat.toPadicInts z = nums at hzAll
  have hz := congrFun hzAll p
  have hzval : (ZHat.toPadicInt p z : ℚ_[p]) = (nums p : ℚ_[p]) :=
    congrArg Subtype.val hz
  rw [hzval]
  dsimp only [nums]
  change (↑(1 / (N : ℚ)) : ℚ_[p]) * ((N : ℚ_[p]) * a p) = a p
  have hcancel : (↑(1 / (N : ℚ)) : ℚ_[p]) * (N : ℚ_[p]) = 1 := by
    apply cast_one_div_nat_mul
    exact a.padicNatDen_ne_zero
  rw [← mul_assoc, hcancel, one_mul]

/-- The rational finite adeles are isomorphic to the restricted product of the `p`-adic fields. -/
noncomputable def padicRestrictedProductEquiv : QHat ≃ₐ[ℚ] Rat.PadicRestrictedProduct :=
  AlgEquiv.ofBijective toPadicRestrictedProduct
    ⟨toPadicRestrictedProduct_injective, toPadicRestrictedProduct_surjective⟩

theorem toPadicRestrictedProduct_i₂ (z : ZHat) :
    toPadicRestrictedProduct (QHat.i₂ z) = ZHat.toPadicRestrictedProduct z := by
  change toPadicRestrictedProductIntAlgHom (QHat.i₂ z) = _
  simp [toPadicRestrictedProductIntAlgHom]

end QHat

theorem ZHat.range_toPadicRestrictedProduct :
    Set.range ZHat.toPadicRestrictedProduct =
      (RestrictedProduct.structureSubring
        (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite :
          Set Rat.PadicRestrictedProduct) := by
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    apply RestrictedProduct.mem_structureSubring_iff.2
    exact fun p ↦ (ZHat.toPadicInt p z).2
  · intro ha
    have ha' := RestrictedProduct.mem_structureSubring_iff.1 ha
    let x : (p : Nat.Primes) → ℤ_[p] := fun p ↦ ⟨a p, ha' p⟩
    obtain ⟨z, hz⟩ := ZHat.toPadicInts_surjective x
    refine ⟨z, ?_⟩
    ext p
    exact congrArg Subtype.val (congrFun hz p)

theorem QHat.image_zHatsub :
    QHat.toPadicRestrictedProduct '' (QHat.zHatsub : Set QHat) =
      (RestrictedProduct.structureSubring
        (fun p : Nat.Primes ↦ ℚ_[p]) (fun p ↦ PadicInt.subring p) Filter.cofinite :
          Set Rat.PadicRestrictedProduct) := by
  ext a
  constructor
  · rintro ⟨q, ⟨z, rfl⟩, rfl⟩
    change QHat.toPadicRestrictedProduct (QHat.i₂ z) ∈ _
    rw [QHat.toPadicRestrictedProduct_i₂]
    rw [← ZHat.range_toPadicRestrictedProduct]
    exact ⟨z, rfl⟩
  · intro ha
    rw [← ZHat.range_toPadicRestrictedProduct] at ha
    obtain ⟨z, rfl⟩ := ha
    refine ⟨QHat.i₂ z, ⟨z, rfl⟩, ?_⟩
    exact QHat.toPadicRestrictedProduct_i₂ z
