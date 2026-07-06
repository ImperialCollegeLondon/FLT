import FLT.Slop.DimensionTheorem.Defs

/-!
# `d(R) ≤ δ(R)`

The growth degree of the Hilbert–Samuel function is at most the number of
generators of any ideal of definition — one inequality of the dimension
theorem (Stacks Project, tag 00KQ).

## Strategy: monomial counting

If `q = (x₁, …, xₖ)` has radical `𝔪`, then `qⁿ/qⁿ⁺¹` is generated over `R/q`
by the images of the degree-`n` monomials in the `xᵢ`
(`span_pow_eq_span_monomial`), of which there are at most `(n+1)^(k-1)`
(`card_sym_le` from `FLT/Slop/DimensionTheorem/Numeric.lean`). A module with `N`
generators each killed by `q` has length at most `N · ℓ(R/q)`
(`length_span_range_le`), so summing along the filtration via
`length_quotient_eq_add` gives `ℓ(R/qⁿ) ≤ ℓ(R/q) · (n+1)^k`
(`colength_pow_le`). Since `qⁿ ≤ 𝔪ⁿ`, also `ℓ(R/𝔪ⁿ) ≤ ℓ(R/qⁿ)`, whence
`GrowthLE (hilbertSamuel R) k` (`growthLE_hilbertSamuel_spanFinrank`).

Classically this inequality is deduced from the Hilbert–Serre theorem applied
to the associated graded ring `gr_q(R)`, a quotient of a polynomial ring in
`k` variables over `R/q` (Atiyah–Macdonald, Ch. 11). The counting argument
here uses the same underlying idea — the associated graded ring is generated
in degree one by `k` elements — without any graded-ring machinery.

## Main results

* `DimensionTheorem.growthLE_hilbertSamuel_spanFinrank` — the growth bound.
* `DimensionTheorem.growthLE_hilbertSamuel_growthDeg` — the defining set of
  `growthDeg` is nonempty, so `growthDeg` is an attained minimum.
* `DimensionTheorem.growthDeg_le_minGenPrimary` — `d(R) ≤ δ(R)`.
-/

namespace DimensionTheorem

open IsLocalRing Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

-- Several helper lemmas below do not use the local/Noetherian hypotheses.
set_option linter.unusedSectionVars false

/-- A product of a multiset of elements of an ideal lies in the corresponding
power of the ideal. -/
private lemma multiset_prod_mem_pow {q : Ideal R} {t : Multiset R}
    (h : ∀ x ∈ t, x ∈ q) : t.prod ∈ q ^ Multiset.card t := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (h a (Multiset.mem_cons_self a t))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

/-- The degree-`n` monomial in the elements of `s` indexed by a symmetric power. -/
private def monomial (s : Finset R) {n : ℕ} (a : Sym {x // x ∈ s} n) : R :=
  (Multiset.map Subtype.val (a : Multiset {x // x ∈ s})).prod

private lemma monomial_mem (s : Finset R) {n : ℕ} (a : Sym {x // x ∈ s} n) :
    monomial s a ∈ Ideal.span (s : Set R) ^ n := by
  have hmem : ∀ x ∈ Multiset.map Subtype.val (a : Multiset {x // x ∈ s}),
      x ∈ Ideal.span (s : Set R) := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Ideal.subset_span (Finset.mem_coe.mpr y.2)
  have h := multiset_prod_mem_pow hmem
  rwa [Multiset.card_map, Sym.card_coe] at h

/-- `qⁿ` is spanned by the degree-`n` monomials in a generating set of `q`. -/
private lemma span_pow_eq_span_monomial (s : Finset R) (n : ℕ) :
    Ideal.span (s : Set R) ^ n = Ideal.span (Set.range (monomial s (n := n))) := by
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · induction n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      refine Ideal.subset_span ⟨(Sym.nil : Sym {x // x ∈ s} 0), ?_⟩
      simp [monomial]
    | succ n ih =>
      rw [pow_succ']
      calc Ideal.span (s : Set R) * Ideal.span (s : Set R) ^ n
          ≤ Ideal.span (s : Set R) * Ideal.span (Set.range (monomial s (n := n))) :=
            Ideal.mul_mono le_rfl ih
        _ = Ideal.span ((s : Set R) * Set.range (monomial s (n := n))) :=
            Ideal.span_mul_span' _ _
        _ ≤ Ideal.span (Set.range (monomial s (n := n + 1))) := by
            refine Ideal.span_mono ?_
            rintro x ⟨y, hy, _, ⟨a, rfl⟩, rfl⟩
            refine ⟨(⟨y, Finset.mem_coe.mp hy⟩ : {x // x ∈ s}) ::ₛ a, ?_⟩
            simp [monomial, Sym.coe_cons]
  · rintro x ⟨a, rfl⟩
    exact monomial_mem s a

/-- A module spanned by finitely many elements each killed by `q` has length at
most `(number of generators) * length (R ⧸ q)`. -/
private lemma length_span_range_le {M : Type*} [AddCommGroup M] [Module R M]
    (q : Ideal R) {ι : Type*} [Fintype ι] (w : ι → M)
    (hw : ∀ r ∈ q, ∀ i, r • w i = 0) :
    Module.length R (Submodule.span R (Set.range w)) ≤
      (Fintype.card ι : ℕ∞) * Module.length R (R ⧸ q) := by
  classical
  have hmem : ∀ c : ι → R,
      Fintype.linearCombination R w c ∈ Submodule.span R (Set.range w) := by
    intro c
    rw [← Fintype.range_linearCombination R w]
    exact LinearMap.mem_range_self _ c
  let f : (ι → R) →ₗ[R] Submodule.span R (Set.range w) :=
    (Fintype.linearCombination R w).codRestrict _ hmem
  have hker : Submodule.pi Set.univ (fun _ : ι => q) ≤ LinearMap.ker f := by
    intro c hc
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp only [f, LinearMap.codRestrict_apply, Fintype.linearCombination_apply,
      ZeroMemClass.coe_zero]
    exact Finset.sum_eq_zero fun i _ => hw (c i) (hc i (Set.mem_univ i)) i
  have hfsurj : Function.Surjective f := by
    intro y
    have hy : (y : M) ∈ LinearMap.range (Fintype.linearCombination R w) := by
      rw [Fintype.range_linearCombination R w]; exact y.2
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩
  have hg : Function.Surjective (Submodule.liftQ _ f hker) := by
    intro y
    obtain ⟨c, hc⟩ := hfsurj y
    exact ⟨Submodule.Quotient.mk c, by rw [Submodule.liftQ_apply]; exact hc⟩
  calc Module.length R (Submodule.span R (Set.range w))
      ≤ Module.length R ((ι → R) ⧸ Submodule.pi Set.univ (fun _ : ι => q)) :=
        Module.length_le_of_surjective _ hg
    _ = Module.length R ((_ : ι) → R ⧸ q) :=
        (Submodule.quotientPi (fun _ : ι => q)).length_eq
    _ = ∑ _i : ι, Module.length R (R ⧸ q) :=
        Module.length_pi_of_fintype R (fun _ : ι => R ⧸ q)
    _ = (Fintype.card ι : ℕ∞) * Module.length R (R ⧸ q) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The key counting bound: for an ideal `q` spanned by a finset `s` of size
`k ≥ 1`, the length of `qⁿ/qⁿ⁺¹` is bounded by the length of `R/q` times
`(n+1)^(k-1)`, a bound on the number of degree-`n` monomials in `k` variables. -/
lemma length_pow_quotient_le (s : Finset R) (hs : 1 ≤ s.card) (n : ℕ)
    (q : Ideal R) (hq : q = Ideal.span (s : Set R)) :
    Module.length R
        (Submodule.map (Submodule.mkQ ((q ^ (n + 1) : Ideal R) : Submodule R R))
          ((q ^ n : Ideal R) : Submodule R R)) ≤
      ((n + 1) ^ (s.card - 1) : ℕ) * Module.length R (R ⧸ q) := by
  classical
  have hpow : ((q ^ n : Ideal R) : Submodule R R) =
      Submodule.span R (Set.range (monomial s (n := n))) := by
    rw [hq, span_pow_eq_span_monomial, ← Ideal.submodule_span_eq]
  rw [hpow, Submodule.map_span, ← Set.range_comp]
  have hkill : ∀ r ∈ q, ∀ a : Sym {x // x ∈ s} n,
      r • (Submodule.mkQ ((q ^ (n + 1) : Ideal R) : Submodule R R)) (monomial s a) = 0 := by
    intro r hr a
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      pow_succ']
    refine Ideal.mul_mem_mul hr ?_
    have h := monomial_mem s a
    rwa [← hq] at h
  refine le_trans (length_span_range_le q _ fun r hr a => hkill r hr a) ?_
  refine mul_le_mul_left ?_ _
  rw [Nat.cast_le]
  calc Fintype.card (Sym {x // x ∈ s} n)
      = Fintype.card (Sym (Fin s.card) n) :=
        Fintype.card_congr (Sym.equivCongr (Fintype.equivFinOfCardEq (Fintype.card_coe s)))
    _ ≤ (n + 1) ^ (s.card - 1) := card_sym_le s.card n hs

/-- Summing the filtration bounds: `ℓ(R/qⁿ)` is bounded by
`ℓ(R/q) * (n+1)^k` where `k = s.card ≥ 1`. -/
lemma colength_pow_le (s : Finset R) (hs : 1 ≤ s.card)
    (q : Ideal R) (hq : q = Ideal.span (s : Set R))
    (hrad : q.radical = maximalIdeal R) (n : ℕ) :
    colength R (q ^ n) ≤ colength R q * (n + 1) ^ s.card := by
  have key : ∀ m : ℕ, Module.length R (R ⧸ (q ^ m : Ideal R)) ≤
      ((colength R q * (m + 1) ^ s.card : ℕ) : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      haveI : Subsingleton (R ⧸ (q ^ 0 : Ideal R)) := by
        rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.Quotient.subsingleton_iff.mpr rfl
      rw [Module.length_eq_zero]
      exact zero_le
    | succ m ih =>
      have hle : (q ^ (m + 1) : Ideal R) ≤ q ^ m := Ideal.pow_le_pow_right m.le_succ
      have harith : (m + 1) ^ (s.card - 1) + (m + 1) ^ s.card ≤ (m + 2) ^ s.card := by
        obtain ⟨j, hj⟩ : ∃ j, s.card = j + 1 := ⟨s.card - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
        rw [hj, Nat.add_sub_cancel]
        calc (m + 1) ^ j + (m + 1) ^ (j + 1) = (m + 1) ^ j * (m + 2) := by ring
          _ ≤ (m + 2) ^ j * (m + 2) :=
            mul_le_mul_left (Nat.pow_le_pow_left (by omega) j) _
          _ = (m + 2) ^ (j + 1) := (pow_succ _ _).symm
      have hL : ((colength R q : ℕ) : ℕ∞) = Module.length R (R ⧸ q) := colength_coe hrad
      rw [length_quotient_eq_add (q ^ (m + 1)) (q ^ m) hle]
      calc Module.length R
            (Submodule.map (Submodule.mkQ ((q ^ (m + 1) : Ideal R) : Submodule R R))
              ((q ^ m : Ideal R) : Submodule R R)) +
            Module.length R (R ⧸ (q ^ m : Ideal R))
          ≤ ((m + 1) ^ (s.card - 1) : ℕ) * Module.length R (R ⧸ q) +
              ((colength R q * (m + 1) ^ s.card : ℕ) : ℕ∞) :=
            add_le_add (length_pow_quotient_le s hs m q hq) ih
        _ = ((((m + 1) ^ (s.card - 1) + (m + 1) ^ s.card) * colength R q : ℕ) : ℕ∞) := by
            rw [← hL]; push_cast; ring
        _ ≤ (((m + 2) ^ s.card * colength R q : ℕ) : ℕ∞) := by
            rw [Nat.cast_le]
            exact mul_le_mul_left harith _
        _ = ((colength R q * (m + 1 + 1) ^ s.card : ℕ) : ℕ∞) := by
            push_cast; ring
  have hne : Module.length R (R ⧸ (q ^ n : Ideal R)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (key n)
  rw [colength, ← Nat.cast_le (α := ℕ∞), ENat.coe_toNat hne]
  exact key n

/-- **`d(R) ≤ δ(R)`, main lemma**: the Hilbert–Samuel function grows at most
like `n^k` where `k` is the number of generators of any ideal of definition. -/
theorem growthLE_hilbertSamuel_spanFinrank {I : Ideal R}
    (h : I.radical = maximalIdeal R) :
    GrowthLE (hilbertSamuel R) I.spanFinrank := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian I)
  have hq : I = Ideal.span (s : Set R) := by rw [← Ideal.submodule_span_eq, hspan]
  rw [← hcard]
  by_cases hs : 1 ≤ s.card
  · refine ⟨colength R I, fun n => ?_⟩
    cases n with
    | zero =>
      haveI : Subsingleton (R ⧸ (maximalIdeal R ^ 0 : Ideal R)) := by
        rw [pow_zero, Ideal.one_eq_top]
        exact Submodule.Quotient.subsingleton_iff.mpr rfl
      have h0 : hilbertSamuel R 0 = 0 := by
        rw [hilbertSamuel, colength, Module.length_eq_zero]
        rfl
      simp [h0]
    | succ m =>
      have hIm : I ≤ maximalIdeal R := h ▸ Ideal.le_radical
      have h1 : hilbertSamuel R (m + 1) ≤ colength R (I ^ (m + 1)) :=
        colength_le_colength (Ideal.pow_right_mono hIm (m + 1))
          (radical_pow_eq_of_radical_eq h (Nat.succ_ne_zero m))
      exact h1.trans (colength_pow_le s hs I hq h (m + 1))
  · have hcard0 : s.card = 0 := by omega
    have hbot : I = ⊥ := by
      rw [← hspan, Finset.card_eq_zero.mp hcard0, Finset.coe_empty, Submodule.span_empty]
    rw [hcard0]
    refine GrowthLE.of_bounded (C := colength R I) fun n => ?_
    exact colength_le_colength (hbot.trans_le bot_le) h

variable (R)

/-- The defining set of `growthDeg` is nonempty; `growthDeg` is a true minimum. -/
theorem growthLE_hilbertSamuel_growthDeg :
    GrowthLE (hilbertSamuel R) (growthDeg R) := by
  have h : GrowthLE (hilbertSamuel R) (maximalIdeal R).spanFinrank :=
    growthLE_hilbertSamuel_spanFinrank (by
      exact (maximalIdeal.isMaximal R).isPrime.radical)
  exact Nat.sInf_mem (s := {d | GrowthLE (hilbertSamuel R) d}) ⟨_, h⟩

/-- **`d(R) ≤ δ(R)`**. -/
theorem growthDeg_le_minGenPrimary : growthDeg R ≤ minGenPrimary R := by
  have hne : {k | ∃ I : Ideal R, I.radical = maximalIdeal R ∧ I.spanFinrank = k}.Nonempty :=
    ⟨(maximalIdeal R).spanFinrank, maximalIdeal R,
      (maximalIdeal.isMaximal R).isPrime.radical, rfl⟩
  obtain ⟨I, hI, hIk⟩ :
      ∃ I : Ideal R, I.radical = maximalIdeal R ∧ I.spanFinrank = minGenPrimary R :=
    Nat.sInf_mem hne
  exact Nat.sInf_le (hIk ▸ growthLE_hilbertSamuel_spanFinrank hI)

end DimensionTheorem
