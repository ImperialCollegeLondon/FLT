/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Regular
public import FLT.Slop.DimensionTheorem.Defs

/-!
# `dim R ≤ d(R)`

The Krull dimension of a Noetherian local ring is at most the growth degree
of its Hilbert–Samuel function — the hardest inequality of the dimension
theorem (Stacks Project, tag 00KQ), following the classical Artin–Rees
induction of Atiyah–Macdonald, Ch. 11, adapted to the growth-order
formulation of `d(R)`.

## Strategy: induction on `d` (`ringKrullDim_le_of_growthLE`)

* **Base case `d = 0`** (`ringKrullDim_le_zero_of_growthLE_zero`): if
  `ℓ(R/𝔪ⁿ)` is bounded, it stabilizes, so `𝔪ⁿ = 𝔪ⁿ⁺¹` for some `n`; Nakayama
  (`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) gives `𝔪ⁿ = ⊥`, so every
  prime equals `𝔪` and `dim R ≤ 0`.
* **Inductive step**: it suffices to bound `dim (R ⧸ p)` for each minimal
  prime `p` (`ringKrullDim_le_of_forall_minimalPrimes`, proved by transporting
  prime chains to the quotient). `R ⧸ p` is a Noetherian local domain whose
  Hilbert–Samuel function is dominated by that of `R`
  (`hilbertSamuel_quotient_le`). If its maximal ideal is `⊥` it is a field of
  dimension `0`; otherwise pick `x ≠ 0` in the maximal ideal. The
  **Artin–Rees lemma** (Mathlib's `Ideal.exists_pow_inf_eq_pow_smul`) yields
  `c > 0` with `hs_{R/(x)}(n) + hs_R(n - c) ≤ hs_R(n)` for `n ≥ c`
  (`exists_hilbertSamuel_quotient_span_singleton_add_le`); the key point is
  the colon-ideal bound `(𝔪ⁿ : x) ≤ 𝔪^(n-c)`, using that `x` is a
  nonzerodivisor. The telescoping lemma `GrowthLE.of_le_sub`
  (`FLT/Slop/DimensionTheorem/Numeric.lean`) then drops the growth degree by one, and
  Mathlib's
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  (`dim (R/(x)) + 1 = dim R` for a nonzerodivisor `x ∈ 𝔪`) closes the
  induction.

The comparison of the Samuel functions of `R` and `R/(x)` via Artin–Rees is
the standard textbook argument. The telescoping lemma replaces the classical
"a difference of a polynomial has strictly smaller degree" step, which is not
available in the growth-order formulation of `d(R)`.

## Main result

* `DimensionTheorem.ringKrullDim_le_of_growthLE` :
  `GrowthLE (hilbertSamuel R) d → ringKrullDim R ≤ d`.
-/

/- Some lemmas below do not use all the section variables; keep the statements
exactly as in the interface rather than `omit`-ting hypotheses. -/
set_option linter.unusedSectionVars false

@[expose] public section

namespace DimensionTheorem

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-! ### Auxiliary lemmas -/

private lemma hilbertSamuel_zero : hilbertSamuel R 0 = 0 := by
  haveI : Subsingleton (R ⧸ (maximalIdeal R ^ 0)) := by
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mpr rfl
  unfold hilbertSamuel colength
  rw [Module.length_eq_zero]
  rfl

private lemma hilbertSamuel_coe (n : ℕ) :
    (hilbertSamuel R n : ℕ∞) = Module.length R (R ⧸ maximalIdeal R ^ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (R ⧸ (maximalIdeal R ^ 0)) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [hilbertSamuel_zero, Module.length_eq_zero, Nat.cast_zero]
  · exact colength_coe (radical_pow_eq_of_radical_eq
      (maximalIdeal.isMaximal R).isPrime.radical hn.ne')

/-- The image of the maximal ideal in a proper quotient is the maximal ideal. -/
private lemma map_mk_maximalIdeal (I : Ideal R) [Nontrivial (R ⧸ I)] :
    (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
  haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI)]

/-- The length of a double quotient over `R ⧸ I` equals the length of the
corresponding single quotient over `R`. -/
private lemma length_quotient_map_quotient (I J : Ideal R) :
    Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) =
      Module.length R (R ⧸ (I ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
      (M := (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv.length_eq

/-- The Hilbert–Samuel function of `R ⧸ I` as a colength in `R`. -/
private lemma hilbertSamuel_quotient_eq (I : Ideal R) [Nontrivial (R ⧸ I)] (n : ℕ) :
    hilbertSamuel (R ⧸ I) n = colength R (I ⊔ maximalIdeal R ^ n) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
  have hmax : maximalIdeal (R ⧸ I) ^ n = (maximalIdeal R ^ n).map (Ideal.Quotient.mk I) := by
    rw [← map_mk_maximalIdeal I, Ideal.map_pow]
  unfold hilbertSamuel colength
  rw [hmax, length_quotient_map_quotient]

/-! ### The five main lemmas -/

/-- The Hilbert–Samuel function decreases when passing to a proper quotient ring. -/
lemma hilbertSamuel_quotient_le (I : Ideal R) [Nontrivial (R ⧸ I)] (n : ℕ) :
    hilbertSamuel (R ⧸ I) n ≤ hilbertSamuel R n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hilbertSamuel_zero]
    exact Nat.zero_le _
  · have hrad : (maximalIdeal R ^ n).radical = maximalIdeal R :=
      radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical hn.ne'
    rw [hilbertSamuel_quotient_eq I n]
    exact colength_le_colength le_sup_right hrad

/-- **Artin–Rees difference bound.** In a Noetherian local domain, quotienting by
`0 ≠ x ∈ 𝔪` drops the Hilbert–Samuel function by at least a shifted copy of
itself: there is `c > 0` with
`hs_{R/(x)}(n) + hs_R(n - c) ≤ hs_R(n)` for all `n ≥ c`. -/
lemma exists_hilbertSamuel_quotient_span_singleton_add_le [IsDomain R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    [Nontrivial (R ⧸ Ideal.span {x})] :
    ∃ c, 0 < c ∧ ∀ n, c ≤ n →
      hilbertSamuel (R ⧸ Ideal.span {x}) n + hilbertSamuel R (n - c) ≤
        hilbertSamuel R n := by
  -- Artin–Rees, applied to `N = (x)` inside `M = R`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R)
    ((Ideal.span {x} : Ideal R) : Submodule R R)
  have htop : ∀ J : Ideal R, J • (⊤ : Submodule R R) = J := fun J => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨k + 1, Nat.succ_pos k, fun n hn => ?_⟩
  -- Step 1: the colon ideal `(𝔪ⁿ : x)` is contained in `𝔪^(n - (k+1))`.
  have hcolon : ∀ r : R, r * x ∈ maximalIdeal R ^ n →
      r ∈ maximalIdeal R ^ (n - (k + 1)) := by
    intro r hr
    have h1 : r * x ∈ (maximalIdeal R ^ n • (⊤ : Submodule R R)) ⊓
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
      rw [htop]
      exact Submodule.mem_inf.mpr ⟨hr, Ideal.mem_span_singleton.mpr (dvd_mul_left x r)⟩
    rw [hk n (le_trans (Nat.le_succ k) hn)] at h1
    have h2 : r * x ∈ (maximalIdeal R ^ (n - k)) •
        ((Ideal.span {x} : Ideal R) : Submodule R R) :=
      Submodule.smul_mono le_rfl inf_le_right h1
    obtain ⟨t, ht, hteq⟩ := Submodule.mem_smul_span_singleton.mp h2
    have htr : t = r := mul_right_cancel₀ hx0 (by rwa [smul_eq_mul] at hteq)
    exact Ideal.pow_le_pow_right (Nat.sub_le_sub_left (Nat.le_succ k) n) (htr ▸ ht)
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 k) hn
  -- Step 2: length bookkeeping over `R`.
  -- The map `r ↦ r x mod 𝔪ⁿ`.
  set φ : R →ₗ[R] R ⧸ ((maximalIdeal R ^ n : Ideal R) : Submodule R R) :=
    (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R)) ∘ₗ
      LinearMap.toSpanSingleton R R x with hφ
  have hφapply : ∀ r : R, φ r = Submodule.Quotient.mk (r * x) := fun r => by
    simp [hφ, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hkerle : LinearMap.ker φ ≤ ((maximalIdeal R ^ (n - (k + 1)) : Ideal R) : Submodule R R) := by
    intro r hr
    rw [LinearMap.mem_ker, hφapply, Submodule.Quotient.mk_eq_zero] at hr
    exact hcolon r hr
  have hrange : LinearMap.range φ =
      Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
    rw [hφ, LinearMap.range_comp, LinearMap.range_toSpanSingleton]
  -- The middle term of the additivity formula equals `ℓ(R ⧸ ker φ)`.
  have hmapJ : Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        (((Ideal.span {x} ⊔ maximalIdeal R ^ n : Ideal R)) : Submodule R R) =
      Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
    rw [Submodule.map_sup]
    have hbot : Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((maximalIdeal R ^ n : Ideal R) : Submodule R R) = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨z, hz, rfl⟩
      simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hz
    rw [hbot, sup_bot_eq]
  have hquot : Module.length R
      (Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R)) =
      Module.length R (R ⧸ LinearMap.ker φ) :=
    ((φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).length_eq).symm
  -- Surjection `R ⧸ ker φ ↠ R ⧸ 𝔪^(n-(k+1))`.
  have hsurj : Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1))) ≤
      Module.length R (R ⧸ LinearMap.ker φ) := by
    have hle : LinearMap.ker φ ≤
        Submodule.comap LinearMap.id
          ((maximalIdeal R ^ (n - (k + 1)) : Ideal R) : Submodule R R) := by
      simpa using hkerle
    refine Module.length_le_of_surjective
      (Submodule.mapQ (LinearMap.ker φ) _ LinearMap.id hle) ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  -- Additivity of length: `ℓ(R/𝔪ⁿ) = ℓ(R ⧸ ker φ) + ℓ(R/((x) ⊔ 𝔪ⁿ))`.
  have hadd := length_quotient_eq_add (maximalIdeal R ^ n)
    (Ideal.span {x} ⊔ maximalIdeal R ^ n) le_sup_right
  rw [hmapJ, hquot] at hadd
  -- Assemble the `ℕ∞` inequality.
  have hmain : Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
      Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1))) ≤
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
    calc Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
        Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1)))
        ≤ Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
          Module.length R (R ⧸ LinearMap.ker φ) := add_le_add le_rfl hsurj
      _ = Module.length R (R ⧸ LinearMap.ker φ) +
          Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) := add_comm _ _
      _ = Module.length R (R ⧸ maximalIdeal R ^ n) := hadd.symm
  -- Convert to `ℕ`.
  have hradJ : (Ideal.span {x} ⊔ maximalIdeal R ^ n).radical = maximalIdeal R := by
    refine le_antisymm ?_ ?_
    · have hJm : Ideal.span {x} ⊔ maximalIdeal R ^ n ≤ maximalIdeal R :=
        sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hx)
          (Ideal.pow_le_self (by omega : n ≠ 0))
      exact (Ideal.radical_mono hJm).trans_eq (maximalIdeal.isMaximal R).isPrime.radical
    · calc maximalIdeal R
          = (maximalIdeal R ^ n).radical :=
            (radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical
              (by omega : n ≠ 0)).symm
        _ ≤ (Ideal.span {x} ⊔ maximalIdeal R ^ n).radical := Ideal.radical_mono le_sup_right
  have hcoeq : (hilbertSamuel (R ⧸ Ideal.span {x}) n : ℕ∞) =
      Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) := by
    rw [hilbertSamuel_quotient_eq (Ideal.span {x}) n, colength_coe hradJ]
  have hfinal : ((hilbertSamuel (R ⧸ Ideal.span {x}) n +
      hilbertSamuel R (n - (k + 1)) : ℕ) : ℕ∞) ≤ ((hilbertSamuel R n : ℕ) : ℕ∞) := by
    push_cast
    rw [hcoeq, hilbertSamuel_coe, hilbertSamuel_coe]
    exact hmain
  exact_mod_cast hfinal

/-- **Base case**: bounded Hilbert–Samuel function forces dimension `≤ 0`. -/
lemma ringKrullDim_le_zero_of_growthLE_zero
    (h : GrowthLE (hilbertSamuel R) 0) : ringKrullDim R ≤ 0 := by
  obtain ⟨C, hC⟩ := h
  simp only [pow_zero, mul_one] at hC
  -- Step 1: the Hilbert–Samuel function stabilizes.
  obtain ⟨n, hn1, heq⟩ : ∃ n, 1 ≤ n ∧ hilbertSamuel R (n + 1) = hilbertSamuel R n := by
    by_contra hcon
    have hlt : ∀ m, 1 ≤ m → hilbertSamuel R m < hilbertSamuel R (m + 1) := by
      intro m hm
      rcases lt_or_eq_of_le (hilbertSamuel_monotone (R := R) (Nat.le_succ m)) with hlt | heq
      · exact hlt
      · exact absurd ⟨m, hm, heq.symm⟩ hcon
    have key : ∀ m : ℕ, m + hilbertSamuel R 1 ≤ hilbertSamuel R (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ j ih =>
        have h2 := hlt (j + 1) (by omega)
        omega
    have h3 := key (C + 1)
    have h4 := hC (C + 1 + 1)
    omega
  -- Step 2: hence `𝔪ⁿ ≤ 𝔪ⁿ⁺¹`.
  have hfin : Module.length R (R ⧸ maximalIdeal R ^ n) ≠ ⊤ :=
    length_quotient_ne_top_of_radical_eq
      (radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical (by omega : n ≠ 0))
  have hlen : Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) =
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
    rw [← hilbertSamuel_coe, ← hilbertSamuel_coe, heq]
  have hbot : maximalIdeal R ^ n ≤ maximalIdeal R ^ (n + 1) := by
    have hadd := length_quotient_eq_add (maximalIdeal R ^ (n + 1)) (maximalIdeal R ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [hlen] at hadd
    have hmid0 : Module.length R
        (Submodule.map (Submodule.mkQ ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R))
          ((maximalIdeal R ^ n : Ideal R) : Submodule R R)) = 0 :=
      WithTop.add_right_cancel hfin (hadd.symm.trans (zero_add _).symm)
    haveI := Module.length_eq_zero_iff.mp hmid0
    have hbot' :
        Submodule.map
          (Submodule.mkQ ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R))
          ((maximalIdeal R ^ n : Ideal R) : Submodule R R) = ⊥ :=
      Submodule.eq_bot_of_subsingleton
    intro y hy
    have hmem := hbot' ▸ Submodule.mem_map_of_mem (f := Submodule.mkQ _) hy
    rw [Submodule.mem_bot] at hmem
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  -- Step 3: Nakayama gives `𝔪ⁿ = ⊥`.
  have hpow : maximalIdeal R ^ n = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    rw [Ideal.smul_eq_mul, mul_comm, ← pow_succ]
    exact hbot
  -- Step 4: every prime is the maximal ideal, so the dimension is `0`.
  have hprime : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
    intro p
    haveI := p.2
    refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
    have hle : maximalIdeal R ^ n ≤ p.asIdeal := hpow ▸ bot_le
    exact (Ideal.IsPrime.pow_le_iff (by omega : n ≠ 0)).mp hle
  rw [ringKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
  intro q r _
  have : q = r := PrimeSpectrum.ext ((hprime q).trans (hprime r).symm)
  exact this ▸ le_rfl

/-- Reduction to domain quotients: to bound `dim R` it suffices to bound
`dim (R ⧸ p)` for every minimal prime `p`. -/
@[nolint unusedArguments]
lemma ringKrullDim_le_of_forall_minimalPrimes {n : ℕ}
    (h : ∀ p ∈ minimalPrimes R, ringKrullDim (R ⧸ p) ≤ (n : WithBot ℕ∞)) :
    ringKrullDim R ≤ (n : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim, iSup_le_iff]
  intro c
  haveI : c.head.asIdeal.IsPrime := c.head.2
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := c.head.asIdeal))
  haveI hpprime : p.IsPrime := hp.1.1
  have hmono : ∀ i : Fin (c.length + 1), p ≤ (c i).asIdeal := fun i =>
    le_trans hple (c.monotone (Fin.zero_le i) : c.head.asIdeal ≤ (c i).asIdeal)
  have hcomap : ∀ I : Ideal R, p ≤ I →
      (I.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = I := by
    intro I hpI
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpI]
  have hprime' : ∀ i : Fin (c.length + 1),
      (((c i).asIdeal).map (Ideal.Quotient.mk p)).IsPrime := by
    intro i
    haveI := (c i).2
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hmono i)
  let c' : LTSeries (PrimeSpectrum (R ⧸ p)) :=
    { length := c.length
      toFun := fun i => ⟨((c i).asIdeal).map (Ideal.Quotient.mk p), hprime' i⟩
      step := fun i => by
        change (((c i.castSucc).asIdeal).map (Ideal.Quotient.mk p)) <
          (((c i.succ).asIdeal).map (Ideal.Quotient.mk p))
        have hlt : (c i.castSucc).asIdeal < (c i.succ).asIdeal := c.step i
        refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun he => hlt.ne ?_
        rw [← hcomap _ (hmono i.castSucc), he, hcomap _ (hmono i.succ)] }
  calc ((c.length : ℕ∞) : WithBot ℕ∞) = ((c'.length : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ Order.krullDim (PrimeSpectrum (R ⧸ p)) := Order.LTSeries.length_le_krullDim c'
    _ = ringKrullDim (R ⧸ p) := by rw [ringKrullDim]
    _ ≤ (n : WithBot ℕ∞) := h p hp

/-- **`dim R ≤ d(R)`, inductive form**: any bound on the growth of the
Hilbert–Samuel function bounds the Krull dimension. -/
theorem ringKrullDim_le_of_growthLE :
    ∀ (d : ℕ) (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      GrowthLE (hilbertSamuel R) d → ringKrullDim R ≤ (d : WithBot ℕ∞) := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ h
    simpa using ringKrullDim_le_zero_of_growthLE_zero h
  | succ d ih =>
    intro R _ _ _ h
    apply ringKrullDim_le_of_forall_minimalPrimes
    intro p hp
    haveI hpp : p.IsPrime := hp.1.1
    haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hpp.ne_top
    haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
    have hS : GrowthLE (hilbertSamuel (R ⧸ p)) (d + 1) :=
      h.of_le fun m => hilbertSamuel_quotient_le p m
    by_cases hm : maximalIdeal (R ⧸ p) = ⊥
    · have hfield : IsField (R ⧸ p) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
      rw [ringKrullDim_eq_zero_of_isField hfield]
      exact_mod_cast Nat.zero_le (d + 1)
    · obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).mp hm
      have hxle : Ideal.span {x} ≤ maximalIdeal (R ⧸ p) :=
        (Ideal.span_singleton_le_iff_mem _).mpr hxmem
      haveI : Nontrivial ((R ⧸ p) ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hxle)
      obtain ⟨c, hc, hAR⟩ := exists_hilbertSamuel_quotient_span_singleton_add_le hxmem hx0
      have hdrop : GrowthLE (hilbertSamuel ((R ⧸ p) ⧸ Ideal.span {x})) d :=
        GrowthLE.of_le_sub hc hS hilbertSamuel_monotone hAR
      have hdim := ih _ hdrop
      have heq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hx0) hxmem
      rw [← heq, show ((d + 1 : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) + 1 by push_cast; ring]
      exact add_le_add hdim le_rfl

end DimensionTheorem
