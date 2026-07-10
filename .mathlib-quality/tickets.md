# Ticket board — flat torsion sorry-elimination (items 1–3)

Goal: reduce the transitive sorry-dependency set of
`WeierstrassCurve.torsion_flat_of_good_reduction` to the single hard case
`WeierstrassCurve.torsion_isFlat_of_good_reduction_residueCharPow` (Katz–Mazur;
explicitly out of scope for this board).

### [T001] Division-polynomial dictionary induction (smul_dichotomy)
- **Status**: in_progress (started 2026-07-10, beastmode; dispatched to lean-lsp subagent)
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

### [T001a] Positive induction step for smul_dichotomy (n ≥ 2)
- **Status**: in_progress (spawned + dispatched 2026-07-10, beastmode)
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
- **Status**: in_progress (dispatched 2026-07-10, beastmode; T001a in flight in a different file — the dictionary statements T002 consumes are stable and proved modulo the private helper)
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

### [T004] Galois descent: unramified module prolongs étale-ly
- **Status**: in_progress (dispatched 2026-07-10, beastmode; independent of T001–T003, distinct file)
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
- **Status**: open
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

**Progress (T004)**:
- 2026-07-10: subagent pass 1 — `of_finiteGalois_unramified` PROVED; descent sorry split into T004a (L-shrinking, pure Galois) + T004b (Tate descent under IsUnramifiedExtension + universe transport). New public def `IsUnramifiedExtension R L`. File clean. T004 done modulo children.
- 2026-07-10 (recon, pre-dispatch): mathlib `RingTheory/Unramified/` is substantial: `Basic` (FormallyUnramified), `Field`, `Finite`, `Pi` (products!), `LocalRing` (`FormallyUnramified.iff_map_maximalIdeal_eq`, `Algebra.IsUnramifiedAt` with instances giving separable + finite residue extensions, `isUnramifiedAt_iff_map_eq`), `Dedekind` (`isDedekindDomainDvr.of_formallyUnramified`), `Locus` (`IsUnramifiedIn`). `Unramified/Pi.lean` may help the functions-algebra `M → R'` step directly. Étale = FormallyEtale + FinitePresentation (`Etale/Basic`). The descent worker should bridge: Galois-theoretic `IsUnramified R ρ` (inertia triviality at valuation subrings) → `Algebra.IsUnramifiedAt`-style condition for the integral closure R' of R in L → `Algebra.Etale R R'`.
