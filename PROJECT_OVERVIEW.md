# Project Overview: Tate curve cluster (`FLT/KnownIn1980s/EllipticCurves/`)

Generated: 2026-07-08.
Scope: the three files worked on in the current session — `TateCurve.lean`, `TateParameter.lean`,
`TateCurveBaseChange.lean`. Run with `--skip-mathlibable` (no per-declaration `/mathlibable` sweep).

## Executive Summary

This cluster formalises the analytic backbone of Tate's uniformisation of elliptic curves with
split multiplicative reduction over nonarchimedean local fields: the Tate parameter power series
(`TateParameter.lean`), the evaluation theory of integral power series on the open unit disc and
its base-change functoriality (`TateCurveBaseChange.lean`), and the Tate curve itself with its
valuation-theoretic properties and the (largely still-sorried) uniformisation statements
(`TateCurve.lean`). The proven layer is in good shape: choice-free definitions, careful ultrametric
arguments, honest hypotheses (`|q| < 1`), and no dead code. The 13 sorries in `TateCurve.lean` are
the genuine mathematical frontier (the uniformisation `tateCurveEquiv`/`tateEquiv`, the two
base-change reduction instances, and the torsion/Weil-pairing layer), not neglect.

The top findings: (1) one clean moral duplication — `summable_evalInt` is a special case of the
more general `summable_of_valuation_le_pow`, each currently carrying its own copy of a 4-line
uniformity/nonarchimedean-instance boilerplate that should be a registered instance; (2) the
adic-valuation ↔ canonical-valuation bridge is re-derived inline in two proofs and will be needed
twice more (in reverse) for the sorried base-change instances — it should be extracted to the
`FLT/Mathlib` valuative-relations file; (3) two genuine mathlib-gap/contribution candidates: the
nonarchimedean geometric-series/Lambert-series layer (mathlib has these only for normed fields,
in `Mathlib.NumberTheory.TsumDivisorsAntidiagonal`), and the fact that `evalInt` deliberately
re-implements power-series evaluation because mathlib's `PowerSeries.eval₂` requires a *linear*
topology, which a field never has — a "valued field" evaluation API is missing upstream.

## Statistics

- Files: 3. Declarations: 69 (19 defs, 45 theorems/lemmas, 5 instances).
- Declarations with `sorry`: 13 (all in `TateCurve.lean`; 3 of them are sorried *data*).
- Moral duplications found: 2 (plus 1 shared-skeleton extraction opportunity).
- Generalization opportunities: 3.
- Missing API items: 5.
- Junk declarations: 0.
- Mathlibable assessment: skipped (`--skip-mathlibable`).

---

## Part 1: Declaration Inventory

Format per entry: **What** / **How** / **Hypotheses** / **Uses (project)** / **Used by (in file)**.
"NALF" abbreviates "nonarchimedean local field" (`[Field k] [ValuativeRel k] [TopologicalSpace k]
[IsNonarchimedeanLocalField k]`).

### `TateParameter.lean` (301 lines; 19 declarations: 7 defs, 11 theorems, 1 instance; 0 sorries)

Constructs the inverse of `q ↦ j(q)` — the Tate parameter series `q = j⁻¹ + 744j⁻² + ⋯`
(Silverman ATAEC V.5.2) — as choice-free data in three steps: formal `1/j ∈ ℤ⟦q⟧`, formal
compositional inversion, evaluation over a topological field.

- **`def TateCurve.sInt (k : ℕ) : ℤ⟦X⟧`** (96–98) — What: the formal series `sₖ(q) = ∑ σₖ(n)qⁿ`
  over ℤ. How: `PowerSeries.mk` of `ArithmeticFunction.sigma`. Hyp: none. Uses: []. Used by:
  `c₄Formal` (and `a₄Formal` in TateCurveBaseChange.lean).
- **`def TateCurve.c₄Formal : ℤ⟦X⟧`** (100–102) — What: `E₄`-series `1 + 240s₃(q)`. How: direct.
  Hyp: none. Uses: [`sInt`]. Used by: `jInv`.
- **`def TateCurve.ΔFormal : ℤ⟦X⟧`** (104–108) — What: `Δ(q) = q∏(1-qⁿ)²⁴`, the `η²⁴` product.
  How: `tprod` in the `X`-adic topology (`WithPiTopology.multipliable_one_sub_X_pow`). Hyp: none.
  Uses: []. Used by: `jInv`, `constantCoeff_jInv`, `coeff_one_jInv`.
- **`def TateCurve.jInv : ℤ⟦X⟧`** (110–114) — What: `1/j = Δ/c₄³ = q - 744q² + ⋯` with integer
  coefficients. How: `ΔFormal * invOfUnit (c₄Formal ^ 3) 1` (constant coefficient of `c₄³` is 1,
  so no denominators). Hyp: none. Uses: [`ΔFormal`, `c₄Formal`]. Used by: 8 declarations (the
  file's hub).
- **`theorem TateCurve.constantCoeff_jInv`** (116–118, `@[simp]`) — What: `jInv(0) = 0`. How: the
  leading `X` factor of `ΔFormal` kills the constant term (simp). Hyp: none. Uses: [`jInv`,
  `ΔFormal`]. Used by: `subst_jInvReverse`, `jInv_subst_jInvReverse`.
- **`theorem TateCurve.coeff_one_jInv`** (120–123) — What: linear coefficient of `jInv` is 1,
  making inversion divide only by 1 (integrality by construction). How: `constantCoeff` is a
  continuous ring map, so commutes with the `tprod` (`Multipliable.map_tprod` +
  `constantCoeff_invOfUnit`). Hyp: none. Uses: [`jInv`, `ΔFormal`]. Used by: the `Invertible`
  instance, `coeff_one_jInvReverse`.
- **`instance : Invertible (coeff 1 jInv)`** (127–129) — What: the hypothesis under which
  `PowerSeries.substInv` applies. How: transport `invertibleOne` along `coeff_one_jInv` via
  `Invertible.copy`. Hyp: none. Uses: [`jInv`, `coeff_one_jInv`]. Used by: `jInvReverse` and its
  lemmas (instance argument).
- **`def TateCurve.jInvReverse : ℤ⟦X⟧`** (131–136) — What: the inverse `j`-series
  `ψ = X + 744X² + 750420X³ + ⋯`; integral coefficients *by construction* (no division by `n`,
  legal in every characteristic). How: `substInv jInv`. Hyp: none. Uses: [`jInv`, the instance].
  Used by: 5 declarations.
- **`theorem TateCurve.subst_jInvReverse`** (138–141) — What: `ψ(jInv(q)) = q` formally. How:
  `subst_substInv_left` + `constantCoeff_jInv`. Hyp: none. Uses: [`jInv`, `jInvReverse`,
  `constantCoeff_jInv`]. Used by: unused in file (reserved for the round-trip identities of
  Silverman V.5.2, explicitly future work).
- **`theorem TateCurve.jInv_subst_jInvReverse`** (143–145) — What: `jInv(ψ(w)) = w` formally.
  How: `subst_substInv_right`. Hyp: none. Uses: [`jInv`, `jInvReverse`, `constantCoeff_jInv`].
  Used by: unused in file (same future work).
- **`theorem TateCurve.constantCoeff_jInvReverse`** (147–148, `@[simp]`) — What: `ψ(0) = 0`. How:
  `constantCoeff_substInv`. Hyp: none. Uses: [`jInv`, `jInvReverse`]. Used by: unused in file
  (consumed by `valuation_tateParameter_eq` in TateCurve.lean).
- **`theorem TateCurve.coeff_one_jInvReverse`** (150–152, `@[simp]`) — What: linear coefficient of
  `ψ` is 1. How: `coeff_one_substInv` + `invOf_eq_right_inv` with `coeff_one_jInv`. Hyp: none.
  Uses: [`jInvReverse`, `coeff_one_jInv`]. Used by: unused in file (same consumer).
- **`def TateCurve.evalInt (q : k) (F : ℤ⟦X⟧) : k`** (168–170) — What: the evaluation
  `∑ₙ Fₙqⁿ ∈ k` of an integral power series at a point of a topological field (junk if
  divergent). How: `tsum` of cast coefficients times powers. Hyp: `k` topological field. Uses:
  []. Used by: 5 in file, plus 22 use sites across the cluster (the cluster's central bridge).
- **`theorem TateCurve.evalInt_X`** (172–174, `@[simp]`) — What: `evalInt q X = q`. How: the term
  family is supported at `n = 1` (simp with `coeff_X`). Hyp: topological field. Uses:
  [`evalInt`]. Used by: `valuation_evalInt_eq`.
- **`theorem TateCurve.evalInt_add`** (180–183) — What: `(F+G)(q) = F(q) + G(q)` given both
  summable. How: coefficientwise `map_add`/`add_mul` then `Summable.tsum_add`. Hyp:
  `[IsTopologicalRing k] [T2Space k]`; two summability hypotheses. Uses: [`evalInt`]. Used by:
  `valuation_evalInt_eq`.
- **`theorem TateCurve.summable_evalInt`** (190–216) — What: every `F ∈ ℤ⟦X⟧` is evaluable on the
  open unit disc of a NALF: terms have valuation `≤ |q|ⁿ → 0`, which suffices by completeness +
  nonarchimedean property. How: equips `k` with its canonical uniformity, transports
  `ValuativeRel.nonarchimedeanRing` along `Valuation.toTopologicalSpace_eq`, applies
  `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; the tail estimate chases the
  valuation-ball basis via `exists_pow_valuation_lt` and `valuation_intCast_le_one`. Hyp: NALF,
  `|q| < 1`. Uses: [`exists_pow_valuation_lt`, `valuation_intCast_le_one`] (both
  `FLT/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`). Used by: `valuation_evalInt_le_pow`,
  `valuation_evalInt_eq` (and 3 sites in TateCurveBaseChange.lean).
- **`theorem TateCurve.valuation_evalInt_le_pow`** (218–257; **32-line proof**) — What: if the
  first `M` coefficients of `F` vanish then `|F(q)| ≤ |q|^M`. How: partial sums satisfy the bound
  termwise (`Valuation.map_sum_le` + `valuation_intCast_le_one`); passes to the limit by the
  ultrametric isosceles principle (a partial sum closer to the limit than `|F(q)|` forces
  `|F(q)| < |F(q)|` via `Valuation.map_sub`). Hyp: NALF, `|q| < 1`, `coeff m F = 0` for `m < M`.
  Uses: [`evalInt`, `summable_evalInt`, `valuation_intCast_le_one`]. Used by:
  `valuation_evalInt_eq` (and `valuation_evalInt_sub_sum_le` in TateCurveBaseChange.lean).
- **`theorem TateCurve.valuation_evalInt_eq`** (259–277) — What: leading-term principle — if
  `F = X + O(X²)` then `|F(q)| = |q|` on the punctured open disc. How: split
  `F(q) = q + (F - X)(q)` via `evalInt_add`/`evalInt_X`; bound the tail by `|q|² < |q|` via
  `valuation_evalInt_le_pow`; conclude by `Valuation.map_add_eq_of_lt_left`. Hyp: NALF, `q ≠ 0`,
  `|q| < 1`, `F(0) = 0`, `coeff 1 F = 1`. Uses: [`evalInt`, `evalInt_add`, `evalInt_X`,
  `summable_evalInt`, `valuation_evalInt_le_pow`; the FLT `T2Space` instance from
  `FLT/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean` implicitly]. Used by: unused
  in file (consumed by `valuation_tateParameter_eq`).
- **`def WeierstrassCurve.tateParameter (j : k) : k`** (287–300) — What: the Tate parameter as a
  function of `j`: `evalInt j⁻¹ jInvReverse`, i.e. `j⁻¹ + 744j⁻² + ⋯` (junk for `|j| ≤ 1`).
  Choice-free by design: the inverse *map* is data, so no `∃!`/`Classical.choose`. How: one-liner.
  Hyp: topological field. Uses: [`evalInt`, `jInvReverse`]. Used by: unused in file (the file's
  end product; 11 use sites in TateCurve.lean).

### `TateCurveBaseChange.lean` (317 lines; 12 declarations: 2 defs, 10 theorems; 0 sorries)

Support for `tateCurve_baseChange`: the Lambert rearrangement expressing the Tate-curve
coefficient series as `evalInt`s, and the theorem that `evalInt` commutes with valuative
extensions. Extracted minimally from FLT PR #1081.

- **`def TateCurve.a₄Formal : ℤ⟦X⟧`** (51–54) — What: formal `a₄`-series `-5s₃(q)`, integral
  avatar of `tateA₄`. How: `-5 * sInt 3`. Hyp: none. Uses: [`sInt`]. Used by: `coeff_a₄Formal`.
- **`def TateCurve.a₆Formal : ℤ⟦X⟧`** (56–60) — What: formal `a₆`-series
  `-(5s₃+7s₅)/12`, exact integer division since `12 ∣ 5d³+7d⁵`. How: coefficientwise
  `PowerSeries.mk` with `ℤ`-division. Hyp: none. Uses: []. Used by: `coeff_a₆Formal`.
- **`theorem TateCurve.coeff_a₄Formal`** (62–66, `@[simp]`) — What: `coeff n a₄Formal = -5σ₃(n)`.
  How: unfold through `coeff_C_mul`/`coeff_mk` after rewriting `5` as `C 5`. Hyp: none. Uses:
  [`a₄Formal`, `sInt`]. Used by: unused in file (consumed by `tateA₄_eq_evalInt`).
- **`theorem TateCurve.coeff_a₆Formal`** (68–71, `@[simp]`) — What: coefficient formula for
  `a₆Formal`. How: `coeff_mk`. Hyp: none. Uses: [`a₆Formal`]. Used by: unused in file (consumed
  by `tateA₆_eq_evalInt`).
- **`theorem TateCurve.evalInt_sub`** (79–85) — What: `(F-G)(q) = F(q) - G(q)` given both
  summable. How: `map_sub`/`sub_mul` + `Summable.tsum_sub`. Hyp: `[IsTopologicalRing k]
  [T2Space k]`. Uses: [`evalInt`]. Used by: `valuation_evalInt_sub_sum_le`.
- **`theorem TateCurve.summable_of_valuation_le_pow`** (99–117) — What: the general
  nonarchimedean convergence criterion: `f : ι → k` is summable if `|f i| ≤ |q|^(e i)` with
  `|q| < 1` and finite sublevel sets `{i | e i < N}`. How: same uniformity/`NonarchimedeanRing`
  setup as `summable_evalInt`, then `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`
  with a cofinite basis chase via `exists_pow_valuation_lt`. Hyp: NALF, `|q| < 1`. Uses:
  [`exists_pow_valuation_lt`]. Used by: `hasSum_geometric_succ`, `tsum_lambert`.
- **`theorem TateCurve.tendsto_pow_nhds_zero`** (120–127) — What: powers of an element of the
  open unit disc tend to 0 (i.e. such elements are topologically nilpotent). How: valuation-ball
  basis chase via `exists_pow_valuation_lt` + `pow_le_pow_right_of_le_one'`. Hyp: NALF,
  `|x| < 1`. Uses: [`exists_pow_valuation_lt`]. Used by: `hasSum_geometric_succ`.
- **`theorem TateCurve.hasSum_geometric_succ`** (133–156) — What: geometric series
  `∑_{j≥1} x^j = x/(1-x)` for `|x| < 1` over a NALF. How: summability by
  `summable_of_valuation_le_pow`; value identified through the closed-form partial sums
  (`geom_sum_eq`) whose limit is computed from `tendsto_pow_nhds_zero`, matched by
  `tendsto_nhds_unique`. Hyp: NALF, `|x| < 1`. Uses: [`summable_of_valuation_le_pow`,
  `tendsto_pow_nhds_zero`]. Used by: `tsum_lambert`.
- **`theorem TateCurve.tsum_lambert`** (164–228; **64-line proof**) — What: Lambert rearrangement
  `∑_{m≥1} c(m)qᵐ/(1-qᵐ) = ∑_{N≥1} (∑_{d∣N} c(d))qᴺ` for arbitrary integer coefficients over a
  NALF. How: expand each row as a geometric series (`hasSum_geometric_succ`); the double series
  over `ℕ+ × ℕ+` is summable by `summable_of_valuation_le_pow` (integer coefficients absorbed by
  `valuation_intCast_le_one`); regroup along fibres of `(m,j) ↦ mj` using mathlib's
  `sigmaAntidiagonalEquivProd` / `HasSum.prod_fiberwise` / `HasSum.sigma` /
  `Nat.sum_divisorsAntidiagonal` / `tsum_pnat_eq_tsum_succ`. Hyp: NALF, `|q| < 1`. Uses:
  [`summable_of_valuation_le_pow`, `hasSum_geometric_succ`, `valuation_intCast_le_one`]. Used by:
  unused in file (consumed by `tateA₄_eq_evalInt`, `tateA₆_eq_evalInt`).
- **`theorem TateCurve.valuation_evalInt_sub_sum_le`** (234–252) — What: quantitative tail bound
  — `evalInt q F` is within `|q|^N` of its `N`-th partial sum. How: the partial sum is
  `evalInt q (F.trunc N)` (`hasSum_sum_of_ne_finset_zero`, `PowerSeries.coeff_trunc`); the
  difference is an evaluation with vanishing low coefficients (`evalInt_sub`), bounded by
  `valuation_evalInt_le_pow`. Hyp: NALF, `|q| < 1`. Uses: [`evalInt`, `evalInt_sub`,
  `summable_evalInt`, `valuation_evalInt_le_pow`]. Used by: `evalInt_map` (twice).
- **`theorem TateCurve.valuation_algebraMap_lt_one`** (264–266) — What: a valuative extension
  maps the open unit disc into the open unit disc. How: one-liner from
  `ValuativeExtension.mapValueGroupWithZero_strictMono` (purely valuation-theoretic; topological
  hypotheses `omit`ted). Hyp: valuative extension of valuative fields. Uses: []. Used by:
  `evalInt_map`.
- **`theorem TateCurve.evalInt_map`** (273–315; **41-line proof**) — What: the file's main
  theorem — `algebraMap k l (evalInt q F) = evalInt (algebraMap k l q) F` for a valuative
  extension of NALFs; no continuity argument needed. How: ultrametric squeeze by contradiction —
  both sides are within `|q_l|^N` of the common `N`-th partial sum (the `k`-side bound transfers
  along `mapValueGroupWithZero` by `mapValueGroupWithZero_valuation` + strict monotonicity), and
  `exists_pow_valuation_lt` picks `N` beating any putative nonzero difference; conclude with
  `Valuation.map_sub` and `lt_irrefl`. Hyp: NALFs, valuative extension, `|q| < 1`. Uses:
  [`evalInt`, `valuation_algebraMap_lt_one`, `valuation_evalInt_sub_sum_le`,
  `exists_pow_valuation_lt`]. Used by: unused in file (consumed by `tateCurve_baseChange`,
  `tateParameter_map`).

### `TateCurve.lean` (535 lines; 38 declarations: 10 defs, 24 theorems/lemmas, 4 instances; 13 sorries)

The Tate curve `E_q`, the Tate parameter of an elliptic curve, valuation-theoretic consequences
of split multiplicative reduction, base-change functoriality, and the (sorried) uniformisation,
torsion and Weil-pairing layer. File-level `set_option linter.overlappingInstances false`
(removable when mathlib#41391 lands). Module docstring carries three explicit TODOs (rank-1
generality, topology on points, sign conventions).

Proven layer:

- **`def WeierstrassCurve.tateA₄ (q : k) : k`** (92–95) — What: `a₄(q) = -5∑ n³qⁿ/(1-qⁿ)` as a
  `tsum` (Silverman ATAEC V.3). How: direct definition. Hyp: any topological field. Uses: [].
  Used by: `tateCurve`, `tateA₄_eq_evalInt`, `tateCurve_baseChange`.
- **`def WeierstrassCurve.tateA₆ (q : k) : k`** (97–102) — What: `a₆(q) = -(5s₃+7s₅)/12` with the
  exact division done in ℤ before casting, so valid in every characteristic. How: direct. Hyp:
  any topological field. Uses: []. Used by: `tateCurve`, `tateA₆_eq_evalInt`,
  `tateCurve_baseChange`.
- **`def WeierstrassCurve.tateCurve (q : k) : WeierstrassCurve k`** (104–106) — What: the Tate
  curve `y² + xy = x³ + a₄(q)x + a₆(q)`. How: constructor literal `⟨1, 0, 0, tateA₄ q, tateA₆ q⟩`.
  Hyp: any topological field. Uses: [`tateA₄`, `tateA₆`]. Used by: `tateCurveEquiv`,
  `exists_variableChange_tateCurve`, `tateCurve_baseChange`.
- **`lemma WeierstrassCurve.tateParameter_eq`** (130–133) — What: unfolding lemma
  `tateParameter j = evalInt j⁻¹ jInvReverse` (abstraction barrier over the TateParameter file).
  How: `rfl`. Hyp: topological field. Uses: [`tateParameter`, `evalInt`, `jInvReverse`]. Used by:
  `valuation_tateParameter_eq`, `tateParameter_map`.
- **`theorem WeierstrassCurve.valuation_tateParameter_eq`** (135–145) — What:
  `|tateParameter j| = |j|⁻¹` for `|j| > 1`: the leading term of the inverse series dominates.
  How: `TateCurve.valuation_evalInt_eq` at `j⁻¹` with `constantCoeff_jInvReverse`,
  `coeff_one_jInvReverse`. Hyp: NALF, `|j| > 1`. Uses: [`valuation_evalInt_eq`,
  `constantCoeff_jInvReverse`, `coeff_one_jInvReverse`, `tateParameter_eq`]. Used by:
  `tateParameter_ne_zero`, `valuation_tateParameter_lt_one`.
- **`theorem WeierstrassCurve.tateParameter_ne_zero`** (147–152) — What: nonvanishing for
  `|j| > 1`. How: zero would have valuation 0, contradicting `valuation_tateParameter_eq`. Hyp:
  NALF, `|j| > 1`. Uses: [`valuation_tateParameter_eq`]. Used by: `q_ne_zero`.
- **`theorem WeierstrassCurve.valuation_tateParameter_lt_one`** (154–156) — What:
  `|tateParameter j| < 1` for `|j| > 1`. How: rewrite to `|j|⁻¹` and `inv_lt_one_of_one_lt₀`.
  Hyp: NALF, `|j| > 1`. Uses: [`valuation_tateParameter_eq`]. Used by: `valuation_q_lt_one`.
- **`theorem WeierstrassCurve.valuation_Δ_lt_one`** (162–175) — What: multiplicative reduction
  gives `|Δ(E)| < 1` in the canonical valuation. How: transfers mathlib's
  `HasMultiplicativeReduction.badReduction` (adic valuation on `𝒪[k]`) via
  `integralModel_Δ_eq`, `HeightOneSpectrum.valuation_lt_one_iff_mem` (maximal-ideal membership),
  and `Valuation.integer.integers`. Hyp: NALF, `E.HasMultiplicativeReduction 𝒪[k]`. Uses: []
  (all mathlib). Used by: `one_lt_valuation_j`.
- **`theorem WeierstrassCurve.valuation_c₄_eq_one`** (177–189) — What: multiplicative reduction
  gives `|c₄(E)| = 1` (integral `c₄` is a unit of `𝒪[k]`). How: mirror of the previous, via
  `valuation_eq_one_iff_notMem` and `Valuation.Integers.isUnit_iff_valuation_eq_one`. Hyp: NALF,
  multiplicative reduction. Uses: []. Used by: `valuation_j_eq`.
- **`theorem WeierstrassCurve.valuation_Δ_ne_zero`** (191–196) — What: `|Δ(E)| ≠ 0` for an
  elliptic curve (Δ is a unit of `k`). How: `(valuation k).ne_zero_iff` + `coe_Δ'` +
  `Units.ne_zero`. Hyp: valuative field only. Uses: []. Used by: `one_lt_valuation_j`.
- **`theorem WeierstrassCurve.valuation_j_eq`** (198–203) — What: `|j| = |Δ|⁻¹` under
  multiplicative reduction (since `|c₄| = 1`). How: unfold `j = Δ'⁻¹c₄³`, multiplicativity,
  `valuation_c₄_eq_one`. Hyp: NALF, elliptic + multiplicative reduction. Uses:
  [`valuation_c₄_eq_one`]. Used by: `one_lt_valuation_j`.
- **`theorem WeierstrassCurve.one_lt_valuation_j`** (205–212) — What: split multiplicative
  reduction forces non-integral `j`, `|j| > 1`. How: `valuation_j_eq` + `valuation_Δ_lt_one` +
  `valuation_Δ_ne_zero` via `one_lt_inv₀`. Hyp: NALF, elliptic + split mult. reduction. Uses:
  [`valuation_j_eq`, `valuation_Δ_lt_one`, `valuation_Δ_ne_zero`]. Used by: `q_ne_zero`,
  `valuation_q_lt_one`, `q_baseChange`.
- **`def WeierstrassCurve.q (E) : k`** (214–223) — What: the Tate parameter of `E`, defined
  choice-freely as `tateParameter E.j` (docstring explains why an abstract isomorphism would not
  pin `q` down). How: one-liner. Hyp: NALF, elliptic. Uses: [`tateParameter`]. Used by: 5+
  declarations.
- **`theorem WeierstrassCurve.q_ne_zero`** (230–231) — What/How: `E.q ≠ 0`, from
  `tateParameter_ne_zero` at `one_lt_valuation_j`. Hyp: split mult. reduction. Uses:
  [`tateParameter_ne_zero`, `one_lt_valuation_j`]. Used by: `qUnit`.
- **`theorem WeierstrassCurve.valuation_q_lt_one`** (233–235) — What/How: `|E.q| < 1`, from
  `valuation_tateParameter_lt_one` at `one_lt_valuation_j`. Hyp: split mult. reduction. Uses:
  [`valuation_tateParameter_lt_one`, `one_lt_valuation_j`]. Used by: unused in file (cited by
  the `tateCurve_baseChange` docstring as making its `|q| < 1` hypothesis free).
- **`def WeierstrassCurve.qUnit : kˣ`** (237–239) — What: `E.q` as a unit. How:
  `Units.mk0 E.q E.q_ne_zero`. Hyp: split mult. reduction. Uses: [`q`, `q_ne_zero`]. Used by:
  `tateEquiv`, `tateEquiv_baseChange`, `qUnitSepClosure`.
- **`theorem WeierstrassCurve.tateA₄_eq_evalInt`** (260–285) — What: Lambert rearrangement
  identifying `tateA₄ q` with `evalInt q a₄Formal` for `|q| < 1`. How: `TateCurve.tsum_lambert`
  with `c(d) = d³`; sides matched via `coeff_a₄Formal` and `ArithmeticFunction.sigma_apply`.
  Hyp: NALF, `|q| < 1`. Uses: [`tateA₄`, `tsum_lambert`, `evalInt`, `a₄Formal`,
  `coeff_a₄Formal`]. Used by: `tateCurve_baseChange`.
- **`theorem WeierstrassCurve.tateA₆_eq_evalInt`** (287–332; **41-line proof**) — What: same for
  `tateA₆`/`a₆Formal`, with the exact-division-by-12 bookkeeping. How: `tsum_lambert` with
  `c(d) = -((5d³+7d⁵)/12)`; `12 ∣ 5d³+7d⁵` by `decide` in `ZMod 12`; the divisor sum commutes
  with the exact division via `Int.ediv_mul_cancel` and `mul_right_cancel₀`. Hyp: NALF,
  `|q| < 1`. Uses: [`tateA₆`, `tsum_lambert`, `evalInt`, `a₆Formal`, `coeff_a₆Formal`]. Used by:
  `tateCurve_baseChange`.
- **`instance : (E.baseChange l).IsElliptic`** (347–351) — What: base change of an elliptic
  curve is elliptic. How: `inferInstanceAs (E.map (algebraMap k l)).IsElliptic` — bridges the
  non-reducible `baseChange`. Hyp: valuative extension of NALFs. Uses: []. Used by: 4+
  declarations implicitly.
- **`theorem WeierstrassCurve.tateCurve_baseChange`** (353–380) — What: the Tate curve commutes
  with any valuative morphism: `(tateCurve q)⁄l = tateCurve (algebraMap k l q)` for `|q| < 1`
  (docstring justifies the hypothesis via the junk-value semantics of `tsum`, including the
  Diophantine subtlety at `|q| = 1`). How: rewrite both sides through
  `tateA₄_eq_evalInt`/`tateA₆_eq_evalInt` (with `valuation_algebraMap_lt_one`), apply
  `evalInt_map`, finish coefficientwise by `ext` + `simp`. Hyp: valuative extension of NALFs,
  `|q| < 1`. Uses: [`tateCurve`, `tateA₄/₆`, `tateA₄/₆_eq_evalInt`,
  `valuation_algebraMap_lt_one`, `evalInt_map`]. Used by: unused in file (equation-level input
  for the future transport of `tateCurveEquiv`).
- **`theorem WeierstrassCurve.tateParameter_map`** (394–402) — What: `tateParameter` commutes
  with valuative extensions for `|j| > 1`. How: direct instance of `evalInt_map` at `j⁻¹` via
  `tateParameter_eq` + `map_inv₀`. Hyp: valuative extension of NALFs, `|j| > 1`. Uses:
  [`tateParameter_eq`, `evalInt_map`, `jInvReverse`]. Used by: `q_baseChange`.
- **`theorem WeierstrassCurve.q_baseChange`** (404–409) — What: `(E.baseChange l).q =
  algebraMap k l E.q`. How: `map_j` (mathlib) + `tateParameter_map` at `one_lt_valuation_j`.
  Hyp: valuative extension, split mult. reduction. Uses: [`q`, `tateParameter_map`,
  `one_lt_valuation_j`, the `IsElliptic` instance]. Used by: unused in file (terminal API).
- **`instance : (E.baseChange Ω).IsElliptic`** (470–472) — What/How: as for `l`, over a separable
  closure `Ω`. Uses: []. Used by: the `Ω`-layer.
- **`def WeierstrassCurve.qUnitSepClosure (Ω) : Ωˣ`** (474–477) — What: image of `qUnit` in a
  separable closure (which is not itself a NALF). How: `Units.map`. Hyp: `Ω` separable closure.
  Uses: [`qUnit`]. Used by: `tateEquivSepClosure`, `tatePoint_mem_torsionBy_of_pow_eq`,
  `weilPairing_tatePoint`.
- **`def WeierstrassCurve.tatePoint (x : Ωˣ)`** (489–491) — What: the point of `E(Ω)` attached to
  `x` under the uniformisation. How: apply `tateEquivSepClosure` to the class of `x`. Hyp: `Ω`
  separable closure, `DecidableEq Ω`. Uses: [`tateEquivSepClosure`]. Used by: 5 declarations.

Sorried layer (13; each is a one-line `sorry` body with substantial documenting comments):

- **`def WeierstrassCurve.tateCurveEquiv`** (115–122; sorried *data*) — the choice-free
  uniformisation `kˣ/qᶻ ≃+ E_q(k)` via the explicit series `X(u,q)`, `Y(u,q)`.
- **`def WeierstrassCurve.tateEquiv`** (241–248; sorried *data*) — the uniformisation for general
  `E`, to be obtained by transporting `tateCurveEquiv` along `exists_variableChange_tateCurve`
  (the one binary sign choice in the theory).
- **`theorem WeierstrassCurve.exists_variableChange_tateCurve`** (256–258) — Silverman ATAEC
  V.5.3: `∃ C, C • tateCurve E.q = E`.
- **`instance : (E.baseChange l).IsMinimal 𝒪[l]`** (382–387) — needs the unit-`c₄` minimality
  criterion; see the Action Plan.
- **`instance : (E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l]`** (389–392) — needs
  valuation transfer + splitness along the residue extension; see the Action Plan.
- **`theorem WeierstrassCurve.tateEquiv_baseChange`** (426–434) — commutativity up to a uniform
  unremovable sign `ε` (15-line comment gives the Frobenius forcing example for `ε = -1`).
- **`theorem WeierstrassCurve.tateEquiv_galois`** (441–447) — sign-free equivariance for
  `k`-algebra automorphisms.
- **`def WeierstrassCurve.tateEquivSepClosure`** (482–487; sorried *data*) — the glued
  uniformisation over `Ω`.
- **`theorem WeierstrassCurve.tatePoint_baseChange`** (497–501) — pins the sign of
  `tateEquivSepClosure` to that of `tateEquiv`.
- **`theorem WeierstrassCurve.tatePoint_galois`** (503–508) — Galois equivariance over `Ω`.
- **`theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_mem_rootsOfUnity`** (510–514) — roots of
  unity give torsion (immediate once `tateEquivSepClosure` is a hom).
- **`theorem WeierstrassCurve.tatePoint_mem_torsionBy_of_pow_eq`** (516–521) — roots of `q` give
  torsion.
- **`theorem WeierstrassCurve.weilPairing_tatePoint`** (529–535) — `e_N(ζ, q^{1/N}) = ζ`: the
  coherence demand pinning the sign conventions of the (also sorried) Weil pairing.

---

## Part 2: Cross-File Dependencies

Import graph (project-internal): `TateCurve.lean` ← imports `TateParameter.lean`,
`TateCurveBaseChange.lean`, `WeilPairing.lean`; `TateCurveBaseChange.lean` ← imports
`TateParameter.lean` (public, so re-exports its API). Both also use
`FLT/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean` (`exists_pow_valuation_lt`,
`valuation_intCast_le_one`) and, implicitly, the `T2Space` instance from
`FLT/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean`.

Cross-file usage (verified by grep):

| Exporter | Declaration | Consumed by |
|---|---|---|
| TateParameter | `evalInt` | TateCurve (8 sites), TateCurveBaseChange (14 sites) — the cluster hub |
| TateParameter | `tateParameter` | TateCurve (11 sites) |
| TateParameter | `jInvReverse`, `constantCoeff_jInvReverse`, `coeff_one_jInvReverse`, `valuation_evalInt_eq` | TateCurve |
| TateParameter | `sInt`, `summable_evalInt`, `valuation_evalInt_le_pow` | TateCurveBaseChange |
| TateParameter | `subst_jInvReverse`, `jInv_subst_jInvReverse` | nobody yet (reserved for the V.5.2 round-trip identities) |
| TateCurveBaseChange | `a₄Formal`, `a₆Formal`, `coeff_a₄Formal`, `coeff_a₆Formal`, `tsum_lambert`, `valuation_algebraMap_lt_one`, `evalInt_map` | TateCurve |
| TateCurveBaseChange | `evalInt_sub`, `summable_of_valuation_le_pow`, `tendsto_pow_nhds_zero`, `hasSum_geometric_succ`, `valuation_evalInt_sub_sum_le` | internal only |

Nothing in the cluster is consumed elsewhere in FLT yet (grep for `tateCurve`, `tateEquiv`,
`tateParameter`, `tatePoint`, `qUnit` outside these files: no hits).

---

## Part 3: Mathlib API Audit (most important)

#### 1. `TateCurve.evalInt` vs `PowerSeries.eval₂` — keep, but know the trade-off

Mathlib has a topological power-series evaluation API
(`Mathlib.RingTheory.PowerSeries.Evaluation`, Chambert-Loir–de Frutos-Fernández): `eval₂ φ a f`
with `eval₂Hom` a *ring homomorphism* when `φ` is continuous and `a` is topologically nilpotent,
plus `eval₂_eq_tsum`, continuity, and `aeval`. **It does not apply here directly**: it requires
`IsLinearTopology S S` (a neighbourhood basis of 0 consisting of *ideals of S*), and a field has
no nontrivial ideals — the valuative topology on `k` is linear over `𝒪[k]`, not over `k`.

- Impact today: none of the proven code is wrong to be hand-rolled.
- Impact tomorrow: PR #1081 goes on to hand-roll `evalInt_mul` (a ~50-line nonarchimedean Mertens
  argument), `evalInt_pow`, and `evalInt_subst` (~70 lines) — exactly what `eval₂Hom.map_mul`
  etc. would give for free. Two escape routes before porting those: (a) define the evaluation
  over `𝒪[k]` (where the topology *is* linear and `|q| < 1` is precisely
  `PowerSeries.HasEval q`) via mathlib's `eval₂Hom` and push into `k` along the (injective)
  coercion — cost: subtype bookkeeping; or (b) PR a valued-field version of `eval₂` to mathlib.
- **Action**: none now; decide (a)/(b) before porting `evalInt_mul`/`evalInt_subst` from PR #1081.

#### 2. `tendsto_pow_nhds_zero` is `IsTopologicallyNilpotent` — align the statement

Mathlib's `IsTopologicallyNilpotent x` *is* `Tendsto (x ^ ·) atTop (𝓝 0)`, and it is the
`PowerSeries.HasEval` condition of the evaluation API. Restating the lemma as
`theorem isTopologicallyNilpotent_of_valuation_lt_one : valuation k x < 1 →
IsTopologicallyNilpotent x` costs nothing and connects to mathlib's API (finding #1).
- **Action**: rename/restate (or add an `abbrev`-level alias); low effort.

#### 3. The `NonarchimedeanRing` boilerplate should be an instance

`summable_evalInt` (TateParameter, lines 197–203) and `summable_of_valuation_le_pow`
(TateCurveBaseChange, lines 105–111) carry verbatim-identical 5-line blocks:
`letI : UniformSpace k := …rightUniformSpace; haveI : IsUniformAddGroup k := …;
haveI : NonarchimedeanRing k := by convert! ValuativeRel.nonarchimedeanRing k; exact
Valuation.toTopologicalSpace_eq _`.
- **Action**: register `instance : NonarchimedeanRing k` for a field with `IsValuativeTopology`
  in `FLT/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean` (next to the existing
  `T2Space` instance) and delete both blocks. Mathlib-ready fixup.

#### 4. Geometric/Lambert series: a genuine mathlib gap, not a misuse

`hasSum_geometric_succ` and `tsum_lambert` duplicate *statements* that mathlib has only for
normed fields: `hasSum_geometric_of_norm_lt_one`, and
`tsum_pow_div_one_sub_eq_tsum_sigma` (`Mathlib.NumberTheory.TsumDivisorsAntidiagonal`, for
`[NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]`, coefficients `n^k` only). A NALF via
`ValuativeRel` carries no `NormedField` instance, so the mathlib versions are unusable here, and
`tsum_lambert` is strictly more general in the coefficients (`c : ℕ → ℤ` arbitrary vs `n^k`).
- **Action**: keep; both are upstream-contribution candidates (see Action Plan Priority 5 note).

#### 5. Adic ↔ canonical valuation bridging is inlined twice (and needed twice more)

`valuation_Δ_lt_one` and `valuation_c₄_eq_one` each re-derive the same two conversion steps
between mathlib's `HeightOneSpectrum` adic valuation on `𝒪[k]` (in which the reduction classes
are phrased) and the `ValuativeRel` canonical valuation on `k`:
"adic `< 1` ↔ maximal-ideal membership ↔ non-unit ↔ canonical `< 1`" and
"adic `= 1` ↔ unit ↔ canonical `= 1`". The two sorried base-change instances will need the same
bridges in the *reverse* direction over `l`.
- **Action**: extract two iff-lemmas (for `x : 𝒪[k]`: `valuation k (x:k) < 1 ↔ x ∈
  IsLocalRing.maximalIdeal 𝒪[k]` and `valuation k (x:k) = 1 ↔ IsUnit x`) into
  `FLT/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`; rewrite both proofs (each drops to
  ~3 lines) and reuse for the instances.

#### 6. Hand-rolled patterns check — clean

No hand-rolled ε–δ/limit/compactness patterns; `Tendsto`, `HasSum`, `Summable`,
`IsValuativeTopology.hasBasis_nhds`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`,
`sigmaAntidiagonalEquivProd`, `mapValueGroupWithZero_*` are all the right mathlib abstractions.

---

## Part 4: Moral Duplications

Pairwise comparison table (pairs with any overlap; all other pairs are clearly distinct):

| Decl A | Decl B | Same statement? | Same proof? | Verdict |
|---|---|---|---|---|
| `summable_evalInt` (TateParameter) | `summable_of_valuation_le_pow` (TateCurveBaseChange) | A is the special case `ι = ℕ`, `e = id`, `f n = Fₙqⁿ` of B | same skeleton (uniformity boilerplate + cofinite criterion + basis chase); A's only extra content is `valuation_intCast_le_one` | **UNIFY**: reprove A as a 4-line application of B (B is the later, more general lemma); ~20 lines and one boilerplate copy deleted |
| `evalInt_add` (TateParameter) | `evalInt_sub` (TateCurveBaseChange) | additive vs subtractive twins | identical shape (`map_add`/`map_sub` + `tsum_add`/`tsum_sub`) | keep both, but **co-locate** in TateParameter's Evaluation section (they are split across files only as a porting accident) |
| `tateA₄_eq_evalInt` | `tateA₆_eq_evalInt` | same shape: `tsum_lambert` + coefficient identification | same skeleton; A₆ adds the division-by-12 bookkeeping | **EXTRACT** a shared bridge lemma (Part 6, item 2); each drops to ~5 lines |
| `valuation_Δ_lt_one` | `valuation_c₄_eq_one` | different facts | same two-step adic↔canonical bridge | **EXTRACT** the bridge iffs (Part 3, item 5) |
| `tendsto_pow_nhds_zero` | tail argument inside `summable_evalInt` | different statements | shared basis-chasing idiom | keep (idiom, not duplication) |
| `hasSum_geometric_succ` | mathlib `hasSum_geometric_of_norm_lt_one` | same mathematics, incomparable typeclasses (valued vs normed) | different | keep (mathlib gap) |
| `tsum_lambert` | mathlib `tsum_pow_div_one_sub_eq_tsum_sigma` | ours strictly more general (arbitrary `c`, valued field) | different | keep; upstream candidate |
| `q_ne_zero` / `valuation_q_lt_one` | `tateParameter_ne_zero` / `valuation_tateParameter_lt_one` | 1-line specialisations to `E.q` | — | keep (intended convenience API) |

---

## Part 5: Generalization Opportunities

1. **The analytic layer: `IsNonarchimedeanLocalField` → complete rank-1 valuative field.**
   Affected: `summable_of_valuation_le_pow`, `tendsto_pow_nhds_zero`, `hasSum_geometric_succ`,
   `tsum_lambert`, `summable_evalInt`, `valuation_evalInt_le_pow`, `valuation_evalInt_eq`,
   `valuation_evalInt_sub_sum_le`, `evalInt_map`, `tateA₄/₆_eq_evalInt`, `tateCurve_baseChange`.
   The proofs use only: rank ≤ 1 (`IsRankLeOne`, via `exists_pow_valuation_lt`), completeness
   (via `summable_of_tendsto_cofinite_zero`), the valuative topology, and T2 — never
   discreteness or finite residue field. Literature: Tate's theory needs exactly "complete with
   respect to a nontrivial rank-1 valuation" (Silverman ATAEC V; Roquette 1970) — this is the
   module docstring's own first TODO (`ℂ_p`, completed maximal unramified extensions).
   **Difficulty: medium** — the blocker is bundling "complete rank-1 valuative field" as
   instances mathlib can synthesise; the reduction-theoretic layer (`valuation_Δ_lt_one` etc.)
   genuinely needs the DVR and stays at local fields. Recommended trigger: whenever the `ℂ_p`
   TODO is attacked, not before.
2. **`tsum_lambert` coefficients: `ℤ` → bounded elements of `k`.** The proof uses integrality
   only through `valuation_intCast_le_one`; the statement holds for any `c : ℕ → k` with
   `|c(n)| ≤ 1` (or even `|c(n)|` polynomially bounded). PR #1081's `hasSum_sum_divisors_mul_pow`
   is that generalisation. **Difficulty: low**, but do it when porting the PR layer that needs
   it, to avoid speculative generality.
3. **`evalInt` beyond fields.** The definition and `evalInt_add/sub/X` need only a topological
   commutative ring. Worth doing only as part of an upstream PR (finding #1 route (b)); inside
   FLT the field case is the only consumer. **Difficulty: trivial, value: only upstream.**

---

## Part 6: API Improvements

1. **`instance NonarchimedeanRing k` for valuative fields** (Part 3, item 3) — deletes duplicated
   boilerplate in 2 proofs; will be needed by every future summability proof in the PR #1081
   port (there are ~6 more such blocks in that branch).
2. **Bridge lemma `tsum_lambert_eq_evalInt`**: from `c : ℕ → ℤ` and `F : ℤ⟦X⟧` with
   `∀ n, coeff n F = ∑ d ∈ n.divisors, c d`, conclude
   `∑' m, c(m+1)q^{m+1}/(1-q^{m+1}) = evalInt q F`. Makes `tateA₄_eq_evalInt` and
   `tateA₆_eq_evalInt` ~5-liners and serves any future coefficient series with divisor-sum
   expansions (the `c₆` and `Δ` series of PR #1081 are next).
3. **Extract `twelve_dvd_sigma`** (`12 ∣ 5σ₃(n) + 7σ₅(n)`): currently an inline `have h12` inside
   `tateA₆_eq_evalInt`; it is the exactness witness for `a₆Formal`'s integer division and
   belongs next to that definition (PR #1081 has it as a standalone lemma — port it).
4. **Adic ↔ canonical valuation iffs** (Part 3, item 5) — two lemmas in
   `FLT/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`; four consumers already known.
5. **Missing `evalInt` companions** for the next port wave: `evalInt_C`, `evalInt_one`,
   `evalInt_C_mul`, `evalInt_mul`, `evalInt_pow` all exist in PR #1081 and will be needed by
   `tateΔ_eq_prod`/`tateCurve_Δ_eq_evalInt`; when porting, land them in TateParameter's
   Evaluation section (single home, cf. Part 4 row 2), and decide finding #1's route (a)/(b)
   first — route (a) makes `evalInt_mul`/`evalInt_pow` free.

Simp coverage is healthy: `evalInt_X`, `constantCoeff_jInv(Reverse)`, `coeff_one_jInvReverse`,
`coeff_a₄Formal`, `coeff_a₆Formal` are tagged; no manual `simp only [foo_def]` unfolding patterns
were found.

---

## Part 7: Junk / Removable

None. Specifically checked:
- Every "unused in file" declaration is either consumed cross-file (verified by grep) or is a
  documented forward-looking export (`subst_jInvReverse`, `jInv_subst_jInvReverse` — reserved
  for the Silverman V.5.2 round-trip identities; keep).
- No wrapper qualifies for inlining: `valuation_algebraMap_lt_one` is a 1-line wrapper over
  `mapValueGroupWithZero_strictMono` but is used from two files and names a real concept; its
  natural *home* is `FLT/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean` (it is not
  Tate-specific) — move, don't delete.
- `tateParameter_eq` is a `rfl` lemma but earns its keep as the cross-file abstraction barrier.
- Tracked debt, not junk: `set_option linter.overlappingInstances false` (remove when
  mathlib#41391 lands); commented-out `[E.IsMinimal 𝒪[k]]` at TateCurve.lean:228 ("caused lake
  lint errors; re-add back later").

## Part 8: Mathlibable Assessment

Skipped (`--skip-mathlibable`). Informal shortlist for a future run: `tsum_lambert`,
`hasSum_geometric_succ`, `summable_of_valuation_le_pow`, `tendsto_pow_nhds_zero` (nonarchimedean
analysis with no elliptic content), the `NonarchimedeanRing` instance, and the adic↔canonical
bridges — plus, from the sorried-instances work, the unit-`c₄` minimality criterion.

---

## Recommended Action Plan

### Priority 1: Quick Wins
1. Reprove `summable_evalInt` from `summable_of_valuation_le_pow` (Part 4, row 1).
2. Register the `NonarchimedeanRing` instance and delete both boilerplate blocks (Part 6, item 1).
3. Move `evalInt_sub` next to `evalInt_add`; move `valuation_algebraMap_lt_one` to the FLT
   ValuativeRel fixup file.
4. Extract `twelve_dvd_sigma` from `tateA₆_eq_evalInt`.

### Priority 2: API Improvements
5. Add the two adic↔canonical valuation iff-lemmas; rewrite `valuation_Δ_lt_one` and
   `valuation_c₄_eq_one` through them (they are also prerequisites for Priority 4).
6. Add `tsum_lambert_eq_evalInt` and shrink `tateA₄/₆_eq_evalInt`.
7. Restate `tendsto_pow_nhds_zero` as `IsTopologicallyNilpotent`.

### Priority 3: Generalizations
8. Defer the rank-1 generalisation until the `ℂ_p` TODO is attacked (Part 5, item 1); when
   porting more of PR #1081, generalise `tsum_lambert`'s coefficients only if the port needs it.

### Priority 4: Structural (the sorried frontier)
9. The two base-change instances (`IsMinimal 𝒪[l]`, `HasSplitMultiplicativeReduction 𝒪[l]`)
   need, in order: the ring map `𝒪[k] →+* 𝒪[l]` with `IsLocalHom` (from
   `mapValueGroupWithZero_strictMono`); the unit-`c₄` minimality criterion (Kraus–Laska,
   Silverman AEC Rem. VII.1.1 — provable from `variableChange_c₄`/`variableChange_Δ` against
   mathlib's `MaximalFor`-based `IsMinimal`); base-change of `integralModel` (uniqueness of
   integral lifts); and splitness transfer along `IsLocalRing.ResidueField.map` via
   `Polynomial.Splits.map`. None of this exists in mathlib yet.
10. The uniformisation layer (`tateCurveEquiv` → `tateEquiv` → `Ω`-glue → torsion → Weil
    pairing) is the long game; PR #1081's `TateUniformisation.lean`/`TateCurveDescent.lean` are
    the source to port, with finding #1's route decision made first.

### Priority 5: Mathlib contributions (informal, no /mathlibable run)
- Nonarchimedean geometric/Lambert series for valuative fields (unifying with
  `Mathlib.NumberTheory.TsumDivisorsAntidiagonal`); the `NonarchimedeanRing` instance; the
  valuation bridges; later, the minimality criterion and a valued-field `PowerSeries.eval`.
