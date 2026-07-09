/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Idempotents

/-!
# Quotients, subideals and enlargement of Henselian pairs

Stability of the Henselian-pair condition under passing to quotients `R ⧸ J` for `J ≤ I`,
under shrinking the ideal, and the converse gluing statement: `(R, I)` is Henselian as soon as
`(R, K)` and `(R ⧸ K, I ⧸ K)` are, for `K ≤ I`.

## Main results

* `IsHenselianPair.quotient` — `(R ⧸ J, I · (R ⧸ J))` is Henselian for `J ≤ I` (Tag 09XG).
* `IsHenselianPair.of_le` — `(R, I)` is Henselian whenever `(R, J)` is and `I ≤ J`.
* `IsHenselianPair.of_quotient` — the converse gluing statement (Tag 0DYD).
* `IsHenselianPair.iff_of_le_quotient` — the resulting characterisation.
* `IsHenselianPair.factorization_unique_of_le_jacobson` — uniqueness of the lifted
  coprime factorisation.

## References

* [Stacks Project, Tag 09XG](https://stacks.math.columbia.edu/tag/09XG)
* [Stacks Project, Tag 0DYD](https://stacks.math.columbia.edu/tag/0DYD)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace IsHenselianPair

/-- **Quotient stability** (Stacks Tag 09XG). If `(R, I)` is a Henselian pair and
`J ≤ I`, then `(R ⧸ J, I·(R ⧸ J))` is again a Henselian pair. -/
@[stacks 09XG]
theorem quotient {I J : Ideal R} (h : IsHenselianPair R I) (hJI : J ≤ I) :
    IsHenselianPair (R ⧸ J) (I.map (Ideal.Quotient.mk J)) where
  le_jacobson := by
    have h1 : I ≤ J.jacobson := le_trans h.le_jacobson (Ideal.jacobson_mono bot_le)
    calc I.map (Ideal.Quotient.mk J)
        ≤ J.jacobson.map (Ideal.Quotient.mk J) := Ideal.map_mono h1
      _ = (J.map (Ideal.Quotient.mk J)).jacobson :=
            Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective
              (le_of_eq Ideal.mk_ker)
      _ = Ideal.jacobson ⊥ := by rw [Ideal.map_quotient_self]
  exists_lift_factorization := by
    intro F hF g₀ h₀ hg₀ hh₀ hcop hFfact
    -- `e : (R ⧸ J) ⧸ I' ≃+* R ⧸ I`, where `I' = I·(R ⧸ J)`.
    set e := DoubleQuot.quotQuotEquivQuotOfLE hJI with he
    -- the composite `(R ⧸ J) ⧸ I' ≃ R ⧸ I` identifies the two projections of `R`.
    have hcomp :
        (e.toRingHom.comp
          (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk J)))).comp (Ideal.Quotient.mk J)
          = Ideal.Quotient.mk I := by
      ext r; exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hJI
    -- lift the monic `F` over `R ⧸ J` to a monic `f` over `R`.
    obtain ⟨f, hfmap, -, hfmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic
        (Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective F) hF
    -- transport the factorisation of `F mod I'` to a factorisation of `f mod I`.
    have hcop' : IsCoprime (g₀.map e.toRingHom) (h₀.map e.toRingHom) := by
      simpa using hcop.map (Polynomial.mapRingHom e.toRingHom)
    have ha : f.map (Ideal.Quotient.mk I) = g₀.map e.toRingHom * h₀.map e.toRingHom := by
      rw [← hcomp, ← Polynomial.map_map, ← Polynomial.map_map, hfmap, hFfact,
        Polynomial.map_mul]
    obtain ⟨g, hh, hgm, hhm, hfgh, hgmap, hhmap⟩ :=
      h.exists_lift_factorization f hfmonic (hg₀.map _) (hh₀.map _) hcop' ha
    -- push the lifted factorisation down to `R ⧸ J`.
    refine ⟨g.map (Ideal.Quotient.mk J), hh.map (Ideal.Quotient.mk J), hgm.map _, hhm.map _,
      ?_, ?_, ?_⟩
    · rw [← Polynomial.map_mul, ← hfgh, hfmap]
    · apply Polynomial.map_injective e.toRingHom e.injective
      rw [Polynomial.map_map, Polynomial.map_map, hcomp, hgmap]
    · apply Polynomial.map_injective e.toRingHom e.injective
      rw [Polynomial.map_map, Polynomial.map_map, hcomp, hhmap]

/-- If `K ≤ Jac(R)` and `I/K ≤ Jac(R/K)`, then `I ≤ Jac(R)`. -/
theorem le_jacobson_bot_of_map_le_jacobson {K I : Ideal R}
    (hK : K ≤ Ideal.jacobson (⊥ : Ideal R))
    (hI : I.map (Ideal.Quotient.mk K) ≤ Ideal.jacobson (⊥ : Ideal (R ⧸ K))) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  haveI : IsLocalHom (Ideal.Quotient.mk K) := isLocalHom_of_le_jacobson_bot K hK
  refine IsUnit.of_map (Ideal.Quotient.mk K) _ ?_
  have hxq : Ideal.Quotient.mk K x ∈ I.map (Ideal.Quotient.mk K) :=
    Ideal.mem_map_of_mem _ hx
  have hunit := (Ideal.mem_jacobson_bot.mp (hI hxq)) (Ideal.Quotient.mk K y)
  simpa [map_mul] using hunit

/-- **Dévissage for Henselian pairs along a quotient ideal** (Stacks Tag 0DYD,
hard direction).  Suppose `K ≤ I`, `(R, K)` is a Henselian pair, and
`(R ⧸ K, I·(R ⧸ K))` is a Henselian pair.  Then `(R, I)` is a Henselian pair.

Given a coprime monic factorisation of `f mod I`, first lift it to `R ⧸ K`
using the quotient pair.  The intermediate factors are coprime over `R ⧸ K`
because their reductions are coprime modulo an ideal in the Jacobson radical
and both factors are monic; this is where the resultant/Jacobson lemma enters.
Then lift the factorisation from `R ⧸ K` to `R` using `(R, K)`. -/
@[stacks 0DYD]
theorem of_quotient {K I : Ideal R} (hKI : K ≤ I)
    (hRK : IsHenselianPair R K)
    (hquot : IsHenselianPair (R ⧸ K) (I.map (Ideal.Quotient.mk K))) :
    IsHenselianPair R I where
  le_jacobson := le_jacobson_bot_of_map_le_jacobson hRK.le_jacobson hquot.le_jacobson
  exists_lift_factorization := by
    intro f hf g₀ h₀ hg₀ hh₀ hcop hfact
    set e := DoubleQuot.quotQuotEquivQuotOfLE hKI with he
    -- `e : (R ⧸ K) ⧸ (I·(R ⧸ K)) ≃+* R ⧸ I` identifies the two projections of `R`.
    have hcomp : (e.toRingHom.comp (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk K)))).comp
        (Ideal.Quotient.mk K) = Ideal.Quotient.mk I := by
      ext r; exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hKI
    have hee : e.toRingHom.comp e.symm.toRingHom = RingHom.id (R ⧸ I) :=
      RingHom.ext fun x => by
        rw [RingHom.comp_apply, RingHom.id_apply]; exact e.apply_symm_apply x
    have hmap3 : ∀ p : R[X],
        ((p.map (Ideal.Quotient.mk K)).map
          (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk K)))).map e.toRingHom
          = p.map (Ideal.Quotient.mk I) := fun p => by
      rw [Polynomial.map_map, Polynomial.map_map, hcomp]
    -- Pull the given factorisation of `f mod I` back along `e` to `(R ⧸ K) ⧸ (I·)`.
    have hcop' : IsCoprime (g₀.map e.symm.toRingHom) (h₀.map e.symm.toRingHom) := by
      obtain ⟨a, b, hab⟩ := hcop
      exact ⟨a.map e.symm.toRingHom, b.map e.symm.toRingHom, by
        rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
          Polynomial.map_one]⟩
    have hf1fact : (f.map (Ideal.Quotient.mk K)).map
        (Ideal.Quotient.mk (I.map (Ideal.Quotient.mk K)))
        = g₀.map e.symm.toRingHom * h₀.map e.symm.toRingHom := by
      apply Polynomial.map_injective e.toRingHom e.injective
      rw [hmap3 f, hfact, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hee]
      simp only [Polynomial.map_id]
    -- Step 1: lift the factorisation to `R ⧸ K` using the henselian quotient pair.
    obtain ⟨g₁, h₁, hg₁mon, hh₁mon, hf1, hg₁map, hh₁map⟩ :=
      hquot.exists_lift_factorization (f.map (Ideal.Quotient.mk K)) (hf.map _)
        (hg₀.map _) (hh₀.map _) hcop' hf1fact
    -- Coprimality of `g₁, h₁` over `R ⧸ K`, lifted across the Jacobson quotient.
    have hcop1 : IsCoprime g₁ h₁ :=
      isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson hquot.le_jacobson
        hg₁mon hh₁mon (by rw [hg₁map, hh₁map]; exact hcop')
    -- Step 2: lift from `R ⧸ K` to `R` using the Henselian pair `(R, K)`.
    obtain ⟨g, q, hgmon, hqmon, hfgh, hgmapK, hqmapK⟩ :=
      hRK.exists_lift_factorization f hf hg₁mon hh₁mon hcop1 hf1
    refine ⟨g, q, hgmon, hqmon, hfgh, ?_, ?_⟩
    · rw [← hmap3 g, hgmapK, hg₁map, Polynomial.map_map, hee, Polynomial.map_id]
    · rw [← hmap3 q, hqmapK, hh₁map, Polynomial.map_map, hee, Polynomial.map_id]

/-- **Uniqueness of a Henselian coprime monic factorisation lift across a
Jacobson-radical quotient.**  This is the uniqueness half used to shrink the
ideal of a Henselian pair.

If `I ≤ Jac(R)`, two monic factorisations with the same product and the same
coprime reductions modulo `I` are equal. -/
theorem factorization_unique_of_le_jacobson {I : Ideal R}
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    {g h g' h' : R[X]} (hgmon : g.Monic) (hhmon : h.Monic)
    (hg'mon : g'.Monic) (hh'mon : h'.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)))
    (hg' : g.map (Ideal.Quotient.mk I) = g'.map (Ideal.Quotient.mk I))
    (hhh' : h.map (Ideal.Quotient.mk I) = h'.map (Ideal.Quotient.mk I))
    (hgh : g * h = g' * h') : g = g' ∧ h = h' := by
  have hcop_gh' : IsCoprime g h' :=
    isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson hI hgmon hh'mon
      (by rw [← hhh']; exact hcop)
  have hcop_g'h : IsCoprime g' h :=
    isCoprime_of_monic_of_isCoprime_map_quotient_of_le_jacobson hI hg'mon hhmon
      (show IsCoprime (g'.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)) by
        rw [← hg']; exact hcop)
  -- `g ∣ g'` and `g' ∣ g`, hence (both monic) `g = g'`.
  have hdvd1 : g ∣ g' := hcop_gh'.dvd_of_dvd_mul_right ⟨h, hgh.symm⟩
  have hdvd2 : g' ∣ g := hcop_g'h.dvd_of_dvd_mul_right ⟨h', hgh⟩
  obtain ⟨c, hc⟩ := hdvd1
  obtain ⟨d, hd⟩ := hdvd2
  have cmon : c.Monic := hgmon.of_mul_monic_left (hc ▸ hg'mon)
  have hg_cd : g * (c * d) = g := by rw [← mul_assoc, ← hc, ← hd]
  have hcd1 : c * d = 1 :=
    sub_eq_zero.mp (hgmon.mul_right_eq_zero_iff.mp (by rw [mul_sub, mul_one, hg_cd, sub_self]))
  have hcunit : IsUnit c := ⟨⟨c, d, hcd1, by rw [mul_comm]; exact hcd1⟩, rfl⟩
  have hgeq : g = g' := by
    rw [hc, cmon.eq_one_of_isUnit hcunit, mul_one]
  -- Monic cancellation of `g` gives `h = h'`.
  have hheq : h = h' :=
    sub_eq_zero.mp (hgmon.mul_right_eq_zero_iff.mp (by rw [mul_sub, hgh, hgeq, sub_self]))
  exact ⟨hgeq, hheq⟩

/-- **Shrinking the ideal of a Henselian pair** (one direction of Stacks Tag
0DYD).  If `(R, J)` is a Henselian pair and `I ≤ J`, then `(R, I)` is a
Henselian pair. -/
theorem of_le {I J : Ideal R} (h : IsHenselianPair R J) (hIJ : I ≤ J) :
    IsHenselianPair R I where
  le_jacobson := le_trans hIJ h.le_jacobson
  exists_lift_factorization := by
    intro f hf g₀ h₀ hg₀ hh₀ hcop hfact
    set K : Ideal (R ⧸ I) := J.map (Ideal.Quotient.mk I) with hK
    set e := DoubleQuot.quotQuotEquivQuotOfLE hIJ with he
    set q : R ⧸ I →+* R ⧸ J := e.toRingHom.comp (Ideal.Quotient.mk K) with hq
    have hcomp : q.comp (Ideal.Quotient.mk I) = Ideal.Quotient.mk J := by
      ext r
      exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r hIJ
    have hKjac : K ≤ Ideal.jacobson (⊥ : Ideal (R ⧸ I)) := by
      rw [hK]
      exact (h.quotient hIJ).le_jacobson
    have hcopJ : IsCoprime (g₀.map q) (h₀.map q) :=
      hcop.map (Polynomial.mapRingHom q)
    have hfactJ : f.map (Ideal.Quotient.mk J) = g₀.map q * h₀.map q := by
      rw [← hcomp, ← Polynomial.map_map, hfact, Polynomial.map_mul]
    obtain ⟨g, h', hgmon, hhmon, hfgh, hgJ, hhJ⟩ :=
      h.exists_lift_factorization f hf (hg₀.map _) (hh₀.map _) hcopJ hfactJ
    have hprodI : g₀ * h₀ =
        g.map (Ideal.Quotient.mk I) * h'.map (Ideal.Quotient.mk I) := by
      rw [← hfact, hfgh, Polynomial.map_mul]
    have hcopK :
        IsCoprime (g₀.map (Ideal.Quotient.mk K)) (h₀.map (Ideal.Quotient.mk K)) := by
      obtain ⟨a, b, hab⟩ := hcop
      exact ⟨a.map (Ideal.Quotient.mk K), b.map (Ideal.Quotient.mk K), by
        rw [← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
          Polynomial.map_one]⟩
    have hgK : g₀.map (Ideal.Quotient.mk K) =
        (g.map (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk K) := by
      apply Polynomial.map_injective e.toRingHom e.injective
      rw [Polynomial.map_map, Polynomial.map_map, ← hq, Polynomial.map_map, hcomp, hgJ]
    have hhK : h₀.map (Ideal.Quotient.mk K) =
        (h'.map (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk K) := by
      apply Polynomial.map_injective e.toRingHom e.injective
      rw [Polynomial.map_map, Polynomial.map_map, ← hq, Polynomial.map_map, hcomp, hhJ]
    obtain ⟨hgI, hhI⟩ :=
      factorization_unique_of_le_jacobson hKjac hg₀ hh₀ (hgmon.map _) (hhmon.map _)
        hcopK hgK hhK hprodI
    exact ⟨g, h', hgmon, hhmon, hfgh, hgI.symm, hhI.symm⟩

/-- **Two-step criterion for Henselian pairs** (Stacks Tag 0DYD).  For `I ≤ J`,
if `(R, I)` and `(R ⧸ I, J·(R ⧸ I))` are Henselian pairs, then `(R, J)` is a
Henselian pair. -/
theorem of_le_of_quotient {I J : Ideal R} (hIJ : I ≤ J)
    (hI : IsHenselianPair R I)
    (hquot : IsHenselianPair (R ⧸ I) (J.map (Ideal.Quotient.mk I))) :
    IsHenselianPair R J :=
  of_quotient hIJ hI hquot

/-- **Stacks Tag 0DYD.**  For `I ≤ J`, the pair `(R, J)` is Henselian iff
`(R, I)` is Henselian and the quotient pair
`(R ⧸ I, J·(R ⧸ I))` is Henselian. -/
@[stacks 0DYD]
theorem iff_of_le_quotient {I J : Ideal R} (hIJ : I ≤ J) :
    IsHenselianPair R J ↔
      IsHenselianPair R I ∧ IsHenselianPair (R ⧸ I) (J.map (Ideal.Quotient.mk I)) :=
  ⟨fun h => ⟨h.of_le hIJ, h.quotient hIJ⟩,
    fun h => of_le_of_quotient hIJ h.1 h.2⟩

end IsHenselianPair
