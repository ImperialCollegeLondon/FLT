# Ticket board — flat torsion sorry-elimination (items 1–3)

## PAUSE RECORD (2026-07-10, end of beastmode session 2) — read this first on resume

**Goal**: make `WeierstrassCurve.torsion_flat_of_good_reduction` sorry-free except the Katz–Mazur
hard case `torsion_isFlat_of_good_reduction_residueCharPow` (explicitly out of scope).

**Build state**: FULL `lake build` GREEN (8877 jobs incl. FermatsLastTheorem) with all
session work in the tree; final verification rerun after registering HopfAlgebra/Pi.lean
in FLT.lean. All files individually LSP-clean (no errors/warnings).

**Sorry-dependency tree of the main theorem at pause** (each with a ticket + written plan):
1. `Point.smul_dichotomy_pos` n ≥ 3 core (DivisionPolynomialTorsion.lean) — [T001a] —
   reduces to (A) Ward's addition formula + (B) y-coordinate input; bridges + n ≤ 2 PROVED.
   (A) = `normEDS_addition_formula` (FLT/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean,
   the ONLY sorry there) — [T001a-A2]; `normEDS_isEllipticSequence`/`rel_normEDS` PROVED from it.
   (B) = ω-theory or mathlib's AddSubMap correctness TODO — [T001a-B, open].
2. `exists_reduction_hom_injective_of_good_reduction` (GoodReduction.lean, its only real sorry) —
   [T003a] — NOS theorem itself is PROVED from it. New PointReduction.lean (CLEAN, killed
   worker's partial: integerHom/residueFieldHom/natCast_isUnit/xCoord_mem infrastructure landed).
3. `resultant_Φ_ΨSq_universal_radical` (Flat.lean) — [T002b] — the no-common-root radical step;
   everything above it (∃k-divisibility, isUnit-resultant, isCoprime rewiring) PROVED.
   (Plus off-critical-path `resultant_Φ_ΨSq_universal` full ±Δ^k identity, kept as strengthening.)
4. `IsFlat.of_isUnramifiedExtension` (FiniteFlat.lean, its only sorry) — [T004b] — Tate descent
   core; `of_isUnramified`→`of_finiteGalois_unramified`→(L-shrinking T004a PROVED) chain done.
   Irreducible input = function Hopf algebra: FLT/Mathlib/RingTheory/HopfAlgebra/Pi.lean
   [T004b-i] — structure layer (comulAux/comul/counit/antipode, comul_single, piScalarRight
   route) landed CLEAN with 3 sorries in the coassoc/counit-law/antipode-law proofs.
   Then: universe transport (Type u) + R'-étale-from-unramified + assembly (queued in T004b notes).

**Session-2 fully-proved highlights**: NOS easy direction (modulo packaging lemma);
T004a L-shrinking; T002a ∃k-divisibility + UFD bridge; T001a-A elliptic-sequence relation
(modulo Ward); dictionary bridges bridge_ΨSq/bridge_Φ; n = 2 doubling case; both repair
passes after the mid-session mathlib bump.

**Resume order suggestion**: T001a-A2 (Ward induction — deepest, unblocks dictionary →
finiteness/radical/reduction tickets), T004b-i sorries (mechanical basis computations),
T002b (radical), T003a (reduction map construction; read PointReduction.lean +
ReductionBaseChange.lean first).

**Session note (resume, 2026-07-10 evening)**: user committed all prior work as 37ca7a2e "pause" and merged main with a MATHLIB BUMP (b76f0261) — that bump, not cache corruption, caused the earlier rebuild scare. Post-bump state: FiniteFlat.lean and Flat.lean compile (sorries: Flat.lean:403 residueCharPow + :594 resultant; FiniteFlat.lean:207 T004a + :240 T004b). DivisionPolynomialTorsion.lean and GoodReduction.lean carry killed-worker mid-edit breakage (bridge_Φ type mismatch; universe error at ~128); two proof-repair subagents dispatched to restore them to clean sorried baselines. Queue after repair: T001a, T002, T003, T004a, T004b.

Goal: reduce the transitive sorry-dependency set of
`WeierstrassCurve.torsion_flat_of_good_reduction` to the single hard case
`WeierstrassCurve.torsion_isFlat_of_good_reduction_residueCharPow` (Katz–Mazur;
explicitly out of scope for this board).

### [T001] Division-polynomial dictionary induction (smul_dichotomy)
- **Status**: open (paused 2026-07-10 — parent of T001a chain; see pause record)
- **Title**: The strong induction relating `n • P` to `ΨSq n` and `Φ n` (Silverman Ex. 3.7)
- **File**: FLT/KnownIn1980s/EllipticCurves/DivisionPolynomialTorsion.lean
- **Depends on**: (none)
- **Parent**: (top-level)
- **Type**: lemma
- **Statement**: `WeierstrassCurve.Affine.Point.smul_dichotomy` (already stated in the file, sorried): for `n ≠ 0` and a nonsingular point `P = some x y h`, either `n • P = 0 ∧ (W.ΨSq n).eval x = 0`, or `n • P ≠ 0 ∧ (W.ΨSq n).eval x ≠ 0 ∧ ∀ x' y' h', n • P = some x' y' h' → x' * (W.ΨSq n).eval x = (W.Φ n).eval x`.
- **Proof sketch**: (1) reduce n < 0 to n > 0 via `neg_smul`, x-invariance under negation, `ΨSq_neg`/`Φ_neg`; (2) base cases n = 1 (trivial: 1•P = P, ΨSq 1 = 1, Φ 1 = X) and n = 2 (doubling formula vs `ΨSq 2 = Ψ₂Sq`, `Φ 2`); (3) strong induction: express `(n+1)•P` via addition formula from `n•P` and `P`, use the EDS recurrences for `preΨ`/`ΨSq`/`Φ` (mathlib `preΨ_even`/`preΨ_odd`/`ΨSq_even`/`ΨSq_odd` and the definitional `Φ`), and the affine `addX`/`slope` formulas. Consider strengthening the induction hypothesis to track `y`-coordinates (the `ω` division polynomial) if needed; helpers may be added freely (sorried helpers acceptable if they strictly reduce mathematical content, e.g. pure polynomial identities).
- **Mathlib lemmas needed**: WeierstrassCurve.preΨ/ΨSq/Φ recurrences and parity lemmas (DivisionPolynomial.Basic), normEDS relations (EllipticDivisibilitySequence), Affine.Point.add_some/addX/addY/slope, Point group instance.
- **Sources**: Silverman AEC Ex. 3.7; Ayad, Points S-entiers des courbes elliptiques.
- **Generality decision**: match the existing statement exactly (elliptic W over field F, DecidableEq F). Frozen — consumers exist.

**Progress (T001)**:
- 2026-07-10: subagent pass 1 — `smul_dichotomy` PROVED via negation reduction + n=1 base case; remaining geometric content isolated in private sorried helper `smul_dichotomy_pos` (n ≥ 2 strong-induction step). Spawning T001a for it.
- 2026-07-10: T001a pass 2 — n = 2 doubling case PROVED (equation_iff, ΨSq_two via linear_combination, add_self_of_Y_eq/ne, slope_of_Y_ne, Φ_two). Sorry now covers only n ≥ 3: needs the ψ/φ→ΨSq/Φ evaluation bridge (specialising mk_Ψ_sq/mk_φ) + secant-step EDS induction. Namespace gotcha recorded: call Affine-namespace methods via W.toAffine.*. Dispatching pass 3.
- 2026-07-10 latest: pass 5 — no-edit, CONCLUSIVE analysis. Closing n ≥ 3 needs TWO missing developments, both flagged as open TODOs by mathlib's own authors: (A) normEDS satisfies IsEllipticSequence (EllipticDivisibilitySequence.lean lines 70-71 TODO; only even/odd doubling recurrences are proven) — the Ward/Stange strong induction; AND (B) either a Y-coordinate division polynomial ω theory (absent entirely; the (2yₙ+a₁xₙ+a₃) tracker pins the slope DENOMINATOR not yₙ itself, so the direct route needs ω) or the correctness of Affine/AddSubMap.lean (Stoll 2026, its own line-21 TODO) for a y-free x-recurrence. Spawning T001a-A (elliptic-sequence relation, pure EDS, upstreamable) and T001a-B (AddSubMap correctness / ω). Sequence: A first.

### [T001a-A2] Ward's addition formula for normEDS
- **Status**: open (paused 2026-07-10 — worker killed mid-session; see pause record)
- **Title**: `normEDS_addition_formula`: W(m+n)W(m−n) = W(m+1)W(m−1)W(n)² − W(n+1)W(n−1)W(m)²
- **File**: FLT/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean (~the single sorry)
- **Depends on**: (none)
- **Parent**: T001a-A
- **Type**: theorem
- **Statement**: as stated in the file (public, clean, numerically verified by the previous worker on b,c,d = 2,3,5).
- **Proof sketch**: Ward 1948's strong double induction. The definitional even/odd recurrences ARE the adjacent cases (n = 1 trivial [W(1) = 1], n = 2 relates to the doubling recurrences); induct on m (or m+n) using the proven `rel_normEDS`-reduction machinery in reverse or the classical route: prove the formula for (m, n) from (m−1, n), (m−2, n)-type instances plus the recurrences — the standard trick is proving the four-index relator vanishes for the special families rel(p, q, q, 0)-adjacent first, then a determinant/Plücker-style three-term manipulation. Alternatively: prove it first over ℤ[b,c,d] (MvPolynomial, an integral domain where cancellation by nonzero polynomials is available — normEDS values are nonzero polys for indices ≠ 0? needs care) then specialise. The previous worker ruled out any constant-coefficient linear recurrence shortcut.
- **Mathlib lemmas needed**: preNormEDS'_even/odd, normEDS_even/odd/one/two/neg, the file's own proved `rel_normEDS` reduction (note: careful not to use circularly — rel_normEDS is proved FROM the addition formula; the induction must be independent).
- **Sources**: Ward, Memoir on elliptic divisibility sequences, 1948, §2; Stange, Elliptic nets, Prop 2.4-ish.
- **Generality decision**: arbitrary CommRing (as stated).

### [T001a-A] normEDS is an elliptic sequence (Ward relation)
- **Status**: done-modulo-child (2026-07-10: `normEDS_isEllipticSequence` + `rel_normEDS` PROVED over any CommRing via a ring-checked three-pair cancellation reduction to the single sorried `normEDS_addition_formula` [child T001a-A2]. New module builds; FLT.lean import landed at line 131.)
- **Title**: `IsEllipticSequence (normEDS b c d)` — the general addition relation
- **File**: FLT/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean (new; FLT/Mathlib mirror convention; add to FLT.lean imports)
- **Depends on**: (none — pure EDS, no elliptic curves)
- **Parent**: T001a
- **Type**: theorem
- **Statement**: `IsEllipticSequence (normEDS b c d)` (and/or the instance form mathlib's TODO asks for), over any CommRing. Equivalently the relation ER(p,q,r,s) = 0 / the classical W(m+n)W(m−n)W(1)² = W(m+1)W(m−1)W(n)² − W(n+1)W(n−1)W(m)².
- **Proof sketch**: the Ward/Stange strong induction on max(|indices|): base cases from normEDS_even/odd small values; step reduces ER(p,q,r,s) via the doubling recurrences — see Stange, "Elliptic nets and elliptic curves" (Thm on net relations) or Ward 1948 §2; mathlib's IsEllipticNet.rel/atomRel_eq API gives the target shape. This is a self-contained polynomial-identity development, flagged TODO upstream — proving it here is directly mathlib-upstreamable.
- **Mathlib lemmas needed**: preNormEDS_even/odd, normEDS_even/odd, IsEllipticNet/IsEllipticSequence defs, IsEllipticNet.rel_eq/atomRel_eq.
- **Sources**: Ward 1948; Stange, Elliptic nets.
- **Generality decision**: exactly mathlib's TODO statement (maximally upstreamable).

### [T001a-B] y-free addition input: AddSubMap correctness or ω-theory
- **Status**: open (blocked on preference: attempt after T001a-A)
- **Title**: Either prove Affine/AddSubMap.lean's correctness TODO, or develop ω
- **File**: FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean (new) or DivisionPolynomialTorsion.lean
- **Depends on**: T001a-A
- **Parent**: T001a
- **Type**: theorem
- **Statement**: (route 1) mathlib AddSubMap line-21 TODO: the map sends (x_P·x_Q : x_P+x_Q : 1) to (x_{P+Q}·x_{P−Q} : x_{P+Q}+x_{P−Q} : 1) on points; (route 2) define ω n with recurrences + yₙ·ψₙ³ = ωₙ(x,y).
- **Proof sketch**: route 1 is a direct (heavy) computation with addX/slope + field_simp/linear_combination against the two Weierstrass relations; route 2 is Silverman Ex 3.7's ω-development.
- **Mathlib lemmas needed**: AddSubMap defs (addSubMapCoeff etc.), Affine/Formula y-elimination lemmas.
- **Sources**: Silverman AEC Ex 3.7; Stoll's AddSubMap file header.
- **Generality decision**: match the mathlib TODO (route 1 preferred — upstreamable, y-free).

- 2026-07-10 late: pass 4 — no-edit, decomposition sharpened. The n ≥ 3 step needs exactly: (1) y-coordinate tracker identity `(2y_n + a₁x_n + a₃)·ψ_n(P)⁴ = ψ_{2n}(P)` (evaluated ψ_even form — the missing ω); (2) the general EDS addition identity ψ_{m+n}ψ_{m−n}ψ_1² = ψ_{m+1}ψ_{m−1}ψ_n² − ψ_{n+1}ψ_{n−1}ψ_m² — CHECK mathlib EllipticDivisibilitySequence: `IsEllSequence` is literally this relation; hunt `isEllSequence_normEDS`/`normEDS` relation theorems before building from preNormEDS; (3) strong induction carrying Q(n) ∧ Q(n+1), degenerate branches keyed to ψ_{n±1}(P) = 0. Available: bridges (proved), φ def = C X·ψ n² − ψ(n+1)ψ(n−1), ψ recurrences, y-elimination lemmas addX_eq_addX_negY_sub / cyclic_sum_Y_mul_X_sub_X / addY_sub_negY_addY (Formula.lean). Pass 5 mandate: land (1)+(2) as pure evalEval lemmas (proved or sorried) AND close the induction from them — geometric→algebraic sorry conversion.
- 2026-07-10 evening: repair pass — the killed pass-3 worker's evaluation bridges `bridge_ΨSq`, `bridge_Φ` are now PROVED (fix: CoordinateRing.mk_ψ/mk_Ψ_sq/mk_φ take W explicitly; evaluation via `AdjoinRoot.evalEval`/`evalEval_mk` from Algebra/Polynomial/Bivariate with hxy : polynomial.evalEval x y = 0; omit [DecidableEq F] [W.IsElliptic]). Single sorry at line 143 = the n ≥ 3 induction, with bridges available. Dispatching pass 4.

### [T001a] Positive induction step for smul_dichotomy (n ≥ 2)
- **Status**: open (paused 2026-07-10 — see pause record)
- **Title**: The n ≥ 2 strong induction of Silverman Ex 3.7
- **File**: FLT/KnownIn1980s/EllipticCurves/DivisionPolynomialTorsion.lean
- **Depends on**: (none)
- **Parent**: T001
- **Type**: lemma
- **Statement**: `Point.smul_dichotomy_pos` (private, already stated + sorried at ~line 77): the dichotomy for `0 < n`, base case n = 1 already proved inline.
- **Proof sketch**: (1) either the bivariate route — evaluation bridge ψₙ(P)² = ΨSqₙ(x), φₙ(P) = Φₙ(x) via `mk_Ψ_sq`/`mk_φ` in the coordinate ring, then simultaneous induction computing n•P from ψ/φ(/ω) with `Point.add_some`/`addX`/`slope`; or (2) the y-free Ayad route — symmetric identities for x(A+B) + x(A−B) and x(A+B)·x(A−B) as rational functions of x(A), x(B), applied with A = m•P, B = P, giving a two-step induction only on x-coordinates and the EDS recurrences `preΨ_even/odd`, `ΨSq_even/odd`. Further strictly-smaller sorried helpers (pure polynomial/EDS identities, no Point) are acceptable.
- **Mathlib lemmas needed**: mk_Ψ_sq, mk_φ, Point.add_some, addX/addY/slope, preΨ/ΨSq recurrences, normEDS relations.
- **Sources**: Silverman AEC Ex 3.7; Ayad 1992.
- **Generality decision**: as stated (private helper; may be strengthened to a simultaneous-induction statement if that makes the proof cleaner, since it is private and only `smul_dichotomy` consumes it).

### [T002] Resultant identity for division polynomials
- **Status**: done-modulo-children (T002a done; T002b open — see pause record)
- **Title**: `Res(Φ n, ΨSq n) = ±Δ^((n⁴−n²)/6)`
- **File**: FLT/KnownIn1980s/EllipticCurves/Flat.lean
- **Depends on**: T001
- **Parent**: (top-level)
- **Type**: lemma
- **Statement**: `WeierstrassCurve.resultant_Φ_ΨSq` (already stated, sorried): for any commutative ring R₀, Weierstrass curve W, n ≠ 0: `(W.Φ n).resultant (W.ΨSq n) (n.natAbs^2) (n.natAbs^2 - 1) = ± W.Δ ^ ((n.natAbs^4 - n.natAbs^2)/6)`.
- **Proof sketch**: (1) reduce to the universal Weierstrass curve over ℤ[a₁,…,a₆] by base-change stability of resultants; (2) over a field where Δ is invertible, Φ n and ΨSq n have no common root (a common root would be the x-coordinate of a nonzero point both n-torsion and (n±1)-torsion, via the T001 dictionary and the definitional Φ = X·ΨSq − preΨ·preΨ·(…)); hence the resultant is nonzero mod every prime of the universal ring not containing Δ, forcing resultant = ±c·Δ^k with c = ±1 (run over 𝔽ₗ for all primes ℓ); (3) pin k by isobaric weights. NOTE: this ticket is deep; acceptable outcome is a decomposition with strictly-smaller purely-polynomial sorried helpers, or a B2 report if the stated form (sign/exponent conventions) turns out wrong.
- **Mathlib lemmas needed**: Polynomial.resultant API (Resultant.Basic), MvPolynomial universal-curve machinery, WeierstrassCurve.Δ.
- **Sources**: Ayad 1992, Manuscripta Math. 76, 305–324.
- **Generality decision**: as stated. Frozen — `isCoprime_Φ_ΨSq` consumes it.

**Progress (T002)**:
- 2026-07-10 latest: pass 1 LANDED a critical-path weakening (lake build Flat succeeded, 2553 jobs, all concurrent edits co-compiling): NEW PROVED public lemma `isUnit_resultant_Φ_ΨSq_of_isUnit_Δ` (base-change to WeierstrassCurve.universal via map_Φ/map_ΨSq/map_Δ + resultant_map_map, then map_dvd + isUnit_of_dvd_unit); `isCoprime_Φ_ΨSq` REWIRED onto it. Critical path now: isCoprime → (proved) → NEW private sorry `resultant_Φ_ΨSq_universal_dvd` (Res ∣ Δ^((n⁴−n²)/6) over the universal curve — no sign, no exact exponent). Full ±Δ^k identity kept off-path as documented strengthening (still sorried). Noted for future: `Polynomial.isUnit_resultant_iff_isCoprime`, `resultant_dvd_leadingCoeff_pow`. Spawning T002a for the divisibility.

### [T002b] Radical step: primes dividing Res divide Δ (universal curve)
- **Status**: open (paused 2026-07-10 — worker killed mid-session; see pause record)
- **Title**: `resultant_Φ_ΨSq_universal_radical` — Ayad's no-common-root argument
- **File**: FLT/KnownIn1980s/EllipticCurves/Flat.lean (~line 650)
- **Depends on**: T001 (dictionary — public lemmas stable)
- **Parent**: T002a
- **Type**: lemma
- **Statement**: (stated + sorried, docstring carries the full proof plan): Res ≠ 0 ∧ every prime p of ℤ[a₁..a₆] dividing Res divides Δ.
- **Proof sketch**: in the docstring at the declaration — quotient to domain, fraction field, algebraic closure, IsElliptic ↔ IsUnit Δ by contradiction, resultant vanishing ⇒ common root (mind degree-index semantics + char∣n degeneration), dictionary ⇒ nonzero point n- and (n±1)-torsion ⇒ contradiction.
- **Mathlib lemmas needed**: resultant root criteria over domains, dictionary lemmas, universal curve API, quotient/fraction-field/algebraic-closure plumbing.
- **Sources**: Ayad 1992.
- **Generality decision**: as stated (private; restatable if consumer permits).

### [T002a] Universal divisibility: Res(Φ, ΨSq) ∣ Δ^k
- **Status**: done (finished 2026-07-10 latest — PROVED after ∃k-restatement, via new proved UFD bridge `exists_dvd_pow_of_forall_prime_dvd` [a ∣ b^card(factors a)]; consumer chain rewired and building (lake build Flat exit 0, 2553 jobs); critical path now gated ONLY by T002b radical lemma)
- **Title**: The resultant divides Δ^((n⁴−n²)/6) over the universal Weierstrass curve
- **File**: FLT/KnownIn1980s/EllipticCurves/Flat.lean
- **Depends on**: T001 (dictionary, for the no-common-root argument over fields)
- **Parent**: T002
- **Type**: lemma
- **Statement**: `resultant_Φ_ΨSq_universal_dvd` (private, stated + sorried at Flat.lean ~615).
- **Proof sketch**: over the UFD ℤ[a₁..a₆]: (1) RADICAL step — every irreducible p dividing Res divides Δ: over Frac(ℤ[aᵢ]/(p))'s algebraic closure, Res = 0 ⟹ common root of Φₙ, ΨSqₙ ⟹ (dictionary + Φ definitional identity) a nonzero point both n- and (n±1)-torsion ⟹ contradiction unless Δ = 0 ⟹ p ∣ Δ. (2) MULTIPLICITY step — Res = c·Δ^j with j ≤ k: needs Δ irreducible in ℤ[aᵢ] (classical; may need proving) + weighted-degree bookkeeping (Res isobaric of weight 12k). Acceptable decomposition: prove (1) fully from the dictionary; sorry Δ-irreducibility and the weight computation as separate clean statements.
- **Mathlib lemmas needed**: resultant_eq_prod_eval / resultant root criteria, WeierstrassCurve.universal API, dictionary lemmas (import ok), UFD divisibility.
- **Sources**: Ayad 1992.
- **Generality decision**: private helper; restatable if a cleaner shape serves the consumer. (`resultant_map_map` @140, `resultant_eq_prod_eval` @478, `exists_mul_add_mul_eq_C_resultant` present); Degree.lean still provides `leadingCoeff_ΨSq`, `ΨSq_ne_zero`, `natDegree_Φ_le`, `coeff_ΨSq_ne_zero` (all needing `(n : R) ≠ 0` + NoZeroDivisors). Ready to dispatch once a slot frees.
- 2026-07-10 (recon, pre-dispatch): mathlib `RingTheory/Polynomial/Resultant/Basic.lean` provides: `resultant_map_map` (commutes with ring homs — gives base-change/universal-curve reduction), `resultant_eq_prod_roots_sub`, `resultant_eq_prod_eval` (field/domain root formulas — connects "no common root" to "resultant ≠ 0"), `resultant_mul_left/right`, `resultant_comm`, `resultant_C_mul_left/right`, `resultant_eq_zero_of_lt_lt`, `exists_mul_add_mul_eq_C_resultant` (already consumed by the proved `isCoprime_Φ_ΨSq`). Missing (build if needed): "resultant ≠ 0 ↔ IsCoprime over a field"; MvPolynomial universal-Weierstrass specialisation plumbing; isobaric-weight argument to pin the exponent.

### [T003] Reduction map on points and Néron–Ogg–Shafarevich (easy direction)
- **Status**: open
- **Title**: Inertia acts trivially on prime-to-p torsion under good reduction
- **File**: FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean
- **Depends on**: T001, T002
- **Parent**: (top-level)
- **Type**: theorem
- **Statement**: `WeierstrassCurve.torsion_unramified_of_good_reduction` (already stated, sorried). The proof sketch is written in the file as comments (3 steps: integrality via ΨSq leading coefficient; injectivity of reduction on torsion via isCoprime_Φ_ΨSq; inertia kills the difference).
- **Proof sketch**: as in the file. The missing infrastructure is a reduction map on points: given the valuation subring 𝒪 of ksep above R with residue field κ, a map from the 𝒪-integral points of E(ksep) to Ẽ(κ) compatible with the group law on the relevant subgroup and Galois-equivariant, injective on n-torsion for n invertible in κ. Helpers should be introduced in GoodReduction.lean (or a new auxiliary file only GoodReduction imports); sorried helpers acceptable if strictly smaller.
- **Mathlib lemmas needed**: WeierstrassCurve.HasGoodReduction, WeierstrassCurve.reduction, ValuationSubring residue field API, IsLocalRing.residue, integrality (isIntegral of roots of monic-up-to-unit polynomials).
- **Sources**: Silverman AEC VII.7.1; Serre–Tate Theorem 1.
- **Generality decision**: as stated. Frozen — Flat.lean and FlatImpliesUnramified.lean consume it.

**Progress (T003)**:
- 2026-07-10 (recon, pre-dispatch): mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` (362 lines) provides ONLY curve-level API: `WeierstrassCurve.reduction R W : WeierstrassCurve (ResidueField R)` (= `(integralModel R W).map (residue R)`), `HasGoodReduction` (class, extends `IsMinimal`, `valuation Δ = 1`), `hasGoodReduction_iff_isElliptic_reduction`, plus `integralModel`, `minimal`, `exists_isMinimal`. NO points map, NO reduction on `Affine.Point`. The worker must build: for `𝒪 : ValuationSubring ksep` above `R` with residue field `κ`, a partial reduction map on points with 𝒪-integral coordinates → `((E.reduction R).baseChange κ)`-points (or points of `(integralModel R E).map (𝒪.residueField-map)`), additive on integral points, Galois-to-residue equivariant, injective on n-torsion (n invertible in κ) via `isCoprime_Φ_ΨSq` + T001 dictionary.

**Progress (T003)**:
- 2026-07-10 evening: repair agent completed the killed worker's design — `torsion_unramified_of_good_reduction` is now PROVED from a single sorried packaging lemma `exists_reduction_hom_injective_of_good_reduction` (GoodReduction.lean:86): existence of a reduction map `red` on the n-torsion into some abelian group, injective, Galois-equivariant, with inertia acting trivially on the target. Universe of the target pinned to 0 at the call site. File sorry count: 1. Spawning T003a for the packaging lemma.
- 2026-07-10 (recon): bumped mathlib Reduction.lean provides integralModel + coefficient lemmas (integralModel_a₁_eq …), reduction, hasGoodReduction_iff_isElliptic_reduction — the raw material for T003a's construction.

### [T003a] The reduction packaging lemma
- **Status**: open (paused 2026-07-10 — worker killed mid-session; landed PointReduction.lean infrastructure; see pause record)
- **Title**: Reduction map on n-torsion: existence, injectivity, equivariance, inertia-triviality
- **File**: FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean
- **Depends on**: T001 (dictionary, for integrality), T002 (coprimality, for injectivity)
- **Parent**: T003
- **Type**: lemma
- **Statement**: `WeierstrassCurve.exists_reduction_hom_injective_of_good_reduction` (stated + sorried at GoodReduction.lean:86; read it there).
- **Proof sketch**: steps 1–2 of the file's NOS sketch: (1) torsion points have 𝒪-integral coordinates (dictionary + leadingCoeff_ΨSq unit); (2) define red via IsLocalRing.residue 𝒪 on coordinates into the reduced curve's points over ResidueField 𝒪 (elliptic by good reduction: integralModel/reduction API + h𝒪); additivity/equivariance by construction; injectivity via coprimality of Φ/ΨSq over the residue field (local mirror of isCoprime_Φ_ΨSq — do NOT import Flat.lean, cycle).
- **Mathlib lemmas needed**: integralModel + coefficient lemmas, reduction, hasGoodReduction_iff_isElliptic_reduction, ValuationSubring integral closure/IsLocalRing API, DivisionPolynomialTorsion dictionary (import allowed).
- **Sources**: Silverman AEC VII.7.1.
- **Generality decision**: as stated (frozen — consumed by the now-proved NOS theorem).

**Progress (T003a)**:
- 2026-07-10 late: pass 1 returned stuck-with-roadmap (no edit; file clean, no regression). Blockers identified: (a) A := ((E.reduction R).baseChange κ).Point needs Algebra (ResidueField R) (ResidueField 𝒪) built from h𝒪 via IsLocalRing.ResidueField.map + IsScalarTower; (b) packaging lemma's universe pin .{_,_,_,0} at the call site must be freed to ksep's universe (packaging lemma NOT frozen, only the NOS statement); (c) red is DATA — must be constructed, not sorried: define on torsion via residue of 𝒪-integral coordinates (integrality provable: dictionary + leadingCoeff_ΨSq + ValuationSubring integrally closed); nonsingularity of reduced points provable (isElliptic reduction + base change); the sorry-able Props: additivity of red, injectivity (κ-level coprimality mirror isCoprime_Φ_ΨSq_residue — import cycle blocks reuse), Galois equivariance, inertia-triviality. Pass 2 dispatched with this tranche plan.
- 2026-07-10 evening (recon correction): `ReductionBaseChange.lean` in the working tree came from the MAIN MERGE (PR #1093, TateCurve baseChange instances) — upstream infrastructure, not this ticket's worker. It provides `integerMap : 𝒪[k] →+* 𝒪[l]`, `residueMap` (between residue fields of local fields), `integralModel_baseChange` — likely directly usable for the reduction map over 𝒪 and the residue-field base change of the reduced curve. Future passes should read it (plus FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean) before building from scratch.

### [T004] Galois descent: unramified module prolongs étale-ly
- **Status**: done-modulo-children (of_finiteGalois_unramified proved; T004a done, T004b open)
- **Title**: `IsFlat.of_finiteGalois_unramified` — the descent core
- **File**: FLT/GroupScheme/FiniteFlat.lean
- **Depends on**: (none — independent of T001–T003)
- **Parent**: (top-level)
- **Type**: theorem
- **Statement**: `GroupScheme.GaloisModule.IsFlat.of_finiteGalois_unramified` (already stated, sorried): given finite Galois L/K through which the finite action factors, and IsUnramified R ρ, conclude IsFlat R ρ.
- **Proof sketch**: (B) build the K-Hopf algebra A = (M → L)^{Gal(L/K)} (pointwise mult, comul dual to addition of M) — needs new Pi-functions Hopf API; (C) R' = integral closure of R in L, finite étale over R by unramifiedness (this is where IsUnramified enters: inertia trivial at every 𝒪 above R ⇒ L/K unramified at R); H = (M → R')^{Gal(L/K)}; (D) show K ⊗[R] H ≅ A, points = M equivariantly. Acceptable outcome: proved modulo ≤3 strictly-smaller sorried helpers each purely commutative-algebraic (e.g. "finite étale integral closure from unramified extension of DVR", "Pi Hopf algebra on finite group functions").
- **Mathlib lemmas needed**: FixedPoints/IsGalois descent, IsIntegralClosure, Algebra.Etale/Unramified, Bialgebra API.
- **Sources**: Tate, Finite flat group schemes §1.3–1.4; Waterhouse §6.
- **Generality decision**: as stated. Frozen — `of_isUnramified` consumes it.

### [T004a] L-shrinking: exists_isUnramifiedExtension
- **Status**: done (finished 2026-07-10 late — PROVED, no helper sorries; finite Galois correspondence route: N = ρ-kernel subgroup (normal via hρ), Nbar = image under restrictNormalHom, L' = lift (fixedField Nbar); key mathlib: restrictNormalHom_ker, fixingSubgroup_fixedField, IsGalois.of_fixedField_normal_subgroup, IntermediateField.lift/mem_lift/liftAlgEquiv. FiniteFlat.lean sorries now: 1 (T004b only).)
- **Title**: The action factors through an unramified finite Galois subextension
- **File**: FLT/GroupScheme/FiniteFlat.lean
- **Depends on**: (none)
- **Parent**: T004
- **Type**: lemma
- **Statement**: `GroupScheme.GaloisModule.exists_isUnramifiedExtension` (stated + sorried at ~line 207): from finite Galois L/K carrying ρ and `IsUnramified R ρ`, produce L' finite Galois carrying ρ with `IsUnramifiedExtension R L'` (inertia at every valuation subring above R contained in L'.fixingSubgroup).
- **Proof sketch**: L' := fixed field of the ρ-kernel {σ | ∀ m, ρ σ m = m} (a subgroup ⊇ L.fixingSubgroup by hL, hence open; normal because it is the kernel of a multiplicative action — needs hρ); by Galois correspondence L' ⊆ L is finite Galois; inertia acts trivially on M (IsUnramified) so inertia ⊆ kernel; kernel = L'.fixingSubgroup by the (finite-level) Galois correspondence. Pure Krull-topology/Galois-correspondence work; mathlib: `IntermediateField.fixedField`, `fixingSubgroup_fixedField` (finite-dimensional case), `IsGalois.ofFixedField...`.
- **Sources**: standard Galois theory.
- **Generality decision**: as stated (frozen: consumed by the proved of_finiteGalois_unramified).

### [T004b] Tate descent for an unramified extension
- **Status**: open
- **Title**: `IsFlat.of_isUnramifiedExtension` — invariant functions Hopf algebra
- **File**: FLT/GroupScheme/FiniteFlat.lean
- **Depends on**: (none)
- **Parent**: T004
- **Type**: theorem
- **Statement**: stated + sorried at ~line 240: of_finiteGalois_unramified's conclusion with the extra hypothesis `IsUnramifiedExtension R L`.
- **Proof sketch**: (B) A := Gal(L/K)-invariants of (M → L); (C) R' := integralClosure R L (Algebra R L via `((algebraMap K L).comp (algebraMap R K)).toAlgebra`, IsScalarTower via `of_algebraMap_eq fun _ => rfl` — worker note from T004 pass); H := invariants of (M → R'), finite flat over DVR (torsion-free finite ⇒ free); étale generic fibre via twisted-form splitting L ⊗[K] A ≅ (M → L); points bijection by evaluation; universe transport of H into Type u (H is finite free — transport along a Basis to a Fin-indexed model in Type u). Decomposition into further strictly-smaller pure-commutative-algebra sorried helpers acceptable.
- **Sources**: Tate §1.3–1.4; Waterhouse §6.
- **Generality decision**: as stated (frozen: consumed by proved of_finiteGalois_unramified).

### [T004b-i] Function Hopf algebra on a finite group
- **Status**: open (paused 2026-07-10 — worker killed mid-session; see pause record)
- **Title**: `HopfAlgebra S (M → S)` for finite abelian M — the constant-group-scheme functions
- **File**: FLT/Mathlib/RingTheory/HopfAlgebra/Pi.lean (new; add one import line to FLT.lean)
- **Depends on**: (none — pure Hopf algebra, no Galois, no elliptic curves; mathlib-upstreamable)
- **Parent**: T004b
- **Type**: def + theorems
- **Statement**: for a finite (add) group M and CommRing S: a HopfAlgebra S (M → S) package — counit = evaluation at 0/1, comul dual to the group law (via the algebra iso (M → S) ⊗[S] (M' → S) ≅ (M × M' → S) for finite index types), antipode dual to inversion; plus the points lemma: for a domain/field T over S, AlgHoms (M → S) →ₐ[S] T correspond to elements of M (evaluation at group elements = the indicator-idempotent decomposition), as a convolution-group iso.
- **Proof sketch**: mathlib confirmed to LACK any Pi/function coalgebra; the dual `MonoidAlgebra.instHopfAlgebra` exists; `HopfAlgebra.ofAlgHom` is the assembly entry point. The tensor iso for finite index types: hunt `Algebra.TensorProduct.piRight`/`piScalarRight`/`Finsupp` variants; if absent build via the basis of indicator functions (Pi.single as idempotents; M finite ⟹ free with basis indicators; tensor of frees).
- **Mathlib lemmas needed**: HopfAlgebra.ofAlgHom, Bialgebra constructors, Pi.commRing/algebra, Algebra.TensorProduct API, MonoidAlgebra dual patterns.
- **Sources**: Waterhouse §2.3 (constant group schemes); Tate §1.2.
- **Generality decision**: mathlib generality — arbitrary comm ring S, finite (Add)CommGroup M (or even finite monoid for the bialgebra part); design for upstreaming.

**Progress (T004b)**:
- 2026-07-10 latest: pass 1 no-edit with decisive scoping. Crux confirmed: mathlib has NO function-algebra Hopf structure (loogle/leanfinder empty on HopfAlgebra/Coalgebra/Bialgebra over Pi); only the dual MonoidAlgebra Hopf. Foundations VERIFIED compiling via lean_run_code: Algebra R L towers, R' = integralClosure, Module.Finite R R' (IsIntegralClosure.finite), Module.Free R R' (IsIntegralClosure.module_free), torsion-free via Module.isTorsionFree_iff_algebraMap_injective. Universe obstruction confirmed (H must be Type u; invariants live in Ksep's universe) — needs structure-transport helper. Decomposition queue: T004b-i (function Hopf, dispatched), then universe transport, then R'-étale-from-unramified, then assembly.
- 2026-07-10 evening (post-bump recon): mathlib has a full `RingTheory/Unramified/` suite — Basic, Dedekind (`isDedekindDomainDvr.of_formallyUnramified`), Field, Finite, LocalRing, LocalStructure, Locus, **Pi** (likely the Pi-functions étale/unramified input for the invariant-functions algebra!), plus `IsIntegralClosure.isFractionRing_of_finite_extension`. The T004b worker should read Unramified/Pi.lean and Unramified/Field.lean first — the (M → R') construction may be mostly composable from these.
- DISPATCH PLAN (pre-written; fire when FiniteFlat.lean frees): tranche the same way as T003a p2 — the Hopf algebra H is DATA: (i) build the Gal(L/K)-action on the algebra (M → L) (pointwise ops; action σ·f = σ ∘ f ∘ (ρ σ)⁻¹, needs hρ for action laws); (ii) H := invariant SUBALGEBRA as a Subalgebra of (M → integralClosure R L) — data, constructible; (iii) Hopf structure: comul dual to addition — the finite-group-functions bialgebra (M → A) ⊗ (M → A) ≅ (M × M → A) for finite M: check mathlib Bialgebra instances on Pi/function types and `Algebra.TensorProduct.piRight...`; if absent, isolate as sorried structure-carrying def only as last resort (prefer building); (iv) sorry-able Props: Module.Finite/Flat of invariants over the DVR (torsion-free+finite ⟹ free), étale generic fibre (twisted form splits over L), points-bijection equivariance; (v) universe transport of H into Type u via Basis-indexed Fin model. Read Unramified/Pi.lean + Field.lean + Finite.lean first.

**Progress (T004)**:
- 2026-07-10: subagent pass 1 — `of_finiteGalois_unramified` PROVED; descent sorry split into T004a (L-shrinking, pure Galois) + T004b (Tate descent under IsUnramifiedExtension + universe transport). New public def `IsUnramifiedExtension R L`. File clean. T004 done modulo children.
- 2026-07-10 (recon, pre-dispatch): mathlib `RingTheory/Unramified/` is substantial: `Basic` (FormallyUnramified), `Field`, `Finite`, `Pi` (products!), `LocalRing` (`FormallyUnramified.iff_map_maximalIdeal_eq`, `Algebra.IsUnramifiedAt` with instances giving separable + finite residue extensions, `isUnramifiedAt_iff_map_eq`), `Dedekind` (`isDedekindDomainDvr.of_formallyUnramified`), `Locus` (`IsUnramifiedIn`). `Unramified/Pi.lean` may help the functions-algebra `M → R'` step directly. Étale = FormallyEtale + FinitePresentation (`Etale/Basic`). The descent worker should bridge: Galois-theoretic `IsUnramified R ρ` (inertia triviality at valuation subrings) → `Algebra.IsUnramifiedAt`-style condition for the integral closure R' of R in L → `Algebra.Etale R R'`.
