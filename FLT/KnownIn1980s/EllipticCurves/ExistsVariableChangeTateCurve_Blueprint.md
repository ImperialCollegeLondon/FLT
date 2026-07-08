# Blueprint: `WeierstrassCurve.exists_variableChange_tateCurve`

> **Target.** Fill the `sorry` in
> [`TateCurve.lean:246`](TateCurve.lean#L246):
> ```lean
> theorem WeierstrassCurve.exists_variableChange_tateCurve :
>     ∃ C : VariableChange k, C • tateCurve E.q = E
> ```
> where `E/k` is elliptic with split multiplicative reduction over a nonarchimedean local
> field `k`, and `E.q = tateParameter E.j` is its Tate parameter.
>
> This is **Silverman, ATAEC V.5.3** ("every `E` with split multiplicative reduction is
> isomorphic over `k` to the Tate curve `E_q` of its parameter").

## Verdict up front

This is **not** a short proof. It decomposes into **two independent halves**, each of which
is itself a small development, and it rests on **two genuine API gaps** that do not exist in
mathlib or FLT today:

1. **The discriminant product formula** `Δ(tateCurve q) = q·∏(1-qⁿ)²⁴` — the `q`-expansion
   of the modular discriminant. This is the deep classical identity and is the dominant risk.
2. **The split-reduction ⟺ trivial-twist link** — that a nontrivial quadratic twist destroys
   split multiplicative reduction, so equal-`j` + both-split forces isomorphism *over `k`*.

Everything else is routine bookkeeping on top of the substantial infrastructure that already
exists (`TateParameter.lean`, `QuadraticTwists.lean`, mathlib's `VariableChange`/`Reduction`).

Do not expect to land this in one sitting. Build it bottom-up in the order at the end.

---

## Mathematical strategy

Write `E_q := tateCurve E.q`. The proof is Silverman's:

- **Half A — same `j`.** Show `j(E_q) = j(E)`. This is the "`tateParameter` inverts the
  `j`-function of the Tate curve" property, explicitly flagged as *future work* in the
  `TateParameter.lean` module docstring (Step 3). Over `k`, `E.j = j(E)`, and by construction
  `E.q = tateParameter E.j`; the claim is that feeding `E.q` back through `j(tateCurve ·)`
  returns `E.j`.

- **Half B — descent from `k̄` to `k`.** Two elliptic curves over a field with the same
  `j ∉ {0, 1728}` are quadratic twists of one another, hence isomorphic over the separable
  closure. They are isomorphic *over `k`* iff the twisting class in `kˣ/(kˣ)²` is trivial.
  Split multiplicative reduction of **both** `E` and `E_q` forces triviality: a nontrivial
  quadratic twist of a split-multiplicative curve has non-split (unramified twist) or
  additive (ramified twist) reduction.

The exclusion `j ∉ {0, 1728}` is **free** here: `|E.j| > 1` (`one_lt_valuation_j`) while
`|0|, |1728| ≤ 1` (they are integers), so `E.j ≠ 0, 1728`, hence `c₄(E), c₆(E) ≠ 0`.

---

## Half A: `j(tateCurve E.q) = E.j`

### Key fact already in place

`TateParameter.lean` builds the formal series and the *formal* inversion identity:

```lean
TateCurve.jInv        : ℤ⟦X⟧ := ΔFormal * invOfUnit (c₄Formal ^ 3) 1   -- = 1/j  as a q-series
TateCurve.jInvReverse : ℤ⟦X⟧ := substInv jInv                          -- the parameter series
TateCurve.subst_jInvReverse     : subst jInv jInvReverse = X
TateCurve.jInv_subst_jInvReverse: subst jInvReverse jInv = X           -- ← this is the one we use
```
and the evaluation bridge with `evalInt q F = ∑ₙ (coeff n F) qⁿ`, already a ring
homomorphism on the convergent range:
```lean
TateCurve.evalInt_mul : valuation k q < 1 → evalInt q (F*G) = evalInt q F * evalInt q G
TateCurve.evalInt_pow, evalInt_add, evalInt_X, summable_evalInt, valuation_evalInt_eq
```
and `E.q = tateParameter E.j = evalInt (E.j⁻¹) jInvReverse` (`tateParameter_eq`).

### Decomposition

| # | Statement | Status |
|---|-----------|--------|
| **A1** | `(tateCurve q).c₄ = evalInt q c₄Formal` | 🟢 **new, easy** |
| **A2** | `(tateCurve q).Δ = evalInt q ΔFormal` | 🔴 **new, HARD (gap #1)** |
| **A3** | `evalInt (evalInt w G) F = evalInt w (subst G F)` (convergent range, `constantCoeff G = 0`) | 🟡 **new, medium** |
| **A4** | `evalInt q jInv = (j (tateCurve q))⁻¹` for `0 < |q| < 1` | 🟢 new, from A1+A2 |
| **A5** | `j (tateCurve E.q) = E.j` | 🟢 new, from A3+A4 |

**A1 (easy).** `c₄ = b₂² - 24 b₄` with `b₂ = a₁² + 4a₂ = 1`, `b₄ = 2a₄ + a₁a₃ = 2·tateA₄ q`,
so `c₄(tateCurve q) = 1 - 48·tateA₄ q`. Now `tateA₄ q = evalInt q a₄Formal` (already:
`tateA₄_eq_evalInt`) and `a₄Formal = -5·sInt 3`, `c₄Formal = 1 + 240·sInt 3`. Conclude by
`evalInt`-linearity (`evalInt_add`, `evalInt` of an integer constant, `evalInt` scaling).
A finite, mechanical calculation.

**A2 (the hard gap).** Equivalent to the *formal* power-series identity in `ℤ⟦X⟧`:
```
Δ_Weierstrass ⟨1, 0, 0, a₄Formal, a₆Formal⟩  =  ΔFormal  =  X · (∏ₙ (1 - Xⁿ⁺¹))²⁴
```
i.e. the `q`-expansion of the discriminant modular form / Jacobi's product. There is **no
mathlib API** for this. See the "Dominant risks" section for the two realistic routes
(direct formal proof vs. transfer from the complex-analytic `TateCurveConstruction.lean`).
Everything downstream is blocked on A2 (and A2 is also needed by **B0**, so it is the single
most load-bearing lemma in the whole file).

**A3 (evaluation commutes with substitution).** The convergent avatar of
`subst`: for series with integer coefficients and arguments in the open unit disc,
`evalInt (evalInt w G) F = evalInt w (subst G F)`. Proof by the standard formal-to-analytic
bridge (partial sums of `F ∘ G` converge to `evalInt (evalInt w G) F`). This is the
"evaluation of a formal `subst` identity at a convergent point" the docstring refers to.
Mildly technical (double series / summability), but self-contained.

**A4.** `jInv = ΔFormal · invOfUnit (c₄Formal³)`. Evaluate with `evalInt_mul`/`evalInt_pow`
and A1, A2:
`evalInt q jInv = Δ(tateCurve q) · (c₄(tateCurve q)³)⁻¹ = 1 / j(tateCurve q)`
(using `evalInt q (invOfUnit (c₄Formal³)) = (evalInt q c₄Formal³)⁻¹`, valid because
`|evalInt q c₄Formal| = |c₄(tateCurve q)| = 1 ≠ 0`).

**A5.** Put `w := E.j⁻¹`, which satisfies `|w| < 1` (from `one_lt_valuation_j`). Then
`E.q = evalInt w jInvReverse`, so by **A4** and **A3**:
```
1 / j(tateCurve E.q) = evalInt (E.q) jInv
                     = evalInt (evalInt w jInvReverse) jInv
                     = evalInt w (subst jInvReverse jInv)   -- A3
                     = evalInt w X                          -- jInv_subst_jInvReverse
                     = w = E.j⁻¹.
```
Invert both sides (all nonzero) to get `j(tateCurve E.q) = E.j`.

---

## Half B: descent `∃ C : VariableChange k, C • tateCurve E.q = E`

Given `j(E_q) = j(E)` (Half A) and split multiplicative reduction of both curves.

### What's already in place (`QuadraticTwists.lean`)

```lean
WeierstrassCurve.quadraticTwistOf (t n : K) : WeierstrassCurve K   -- all characteristics
c₄_quadraticTwistOf : (E.quadraticTwistOf t n).c₄ = (t²-4n)² · E.c₄
Δ_quadraticTwistOf  : (E.quadraticTwistOf t n).Δ  = (t²-4n)⁶ · E.Δ
j_quadraticTwistOf  : (E.quadraticTwistOf t n).j  = E.j
exists_smul_eq_quadraticTwistOf_quadraticTwistOf, exists_smul_quadraticTwistOf_eq, …
```
and from mathlib `VariableChange.lean`:
```lean
variableChange_c₄ : (C • W).c₄ = C.u⁻¹^4 · W.c₄
variableChange_c₆ : (C • W).c₆ = C.u⁻¹^6 · W.c₆
variableChange_Δ  : (C • W).Δ  = C.u⁻¹^12 · W.Δ
```

### Decomposition

| # | Statement | Status |
|---|-----------|--------|
| **B0** | `(tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[k]` | 🟡 **new, medium** (needs A2) |
| **B1** | Set `d := c₄(E)·c₆(E_q) / (c₄(E_q)·c₆(E))`; then `d² = c₄(E)/c₄(E_q)` and `d³ = c₆(E)/c₆(E_q)` | 🟢 new, algebra from `j(E)=j(E_q)` |
| **B2** | `d ∈ (kˣ)²` — the twist class is trivial | 🔴 **new, HARD (gap #2)** |
| **B3** | matching `c₄, c₆` via a unit `u` (with `u⁴=c₄(E)/c₄(E_q)`, `u⁶=c₆(E)/c₆(E_q)`) ⟹ `∃ C, C • E_q = E` | 🟡 **new, medium** |

**B0.** `HasSplitMultiplicativeReduction` needs: `IsMinimal 𝒪[k]` (the Tate curve is minimal —
its `Δ` has valuation `v(q) < 1` and `c₄` is a unit, so it is already minimal), `v(Δ) < 1`
(from A2: `Δ(E_q) = evalInt q ΔFormal` and `ΔFormal = X·(unit)`, giving `v = v(q) < 1`),
`v(c₄) = 1` (from A1 and `|tateA₄| < 1`), and the *split* condition — the residue quadratic
`c₄T² + a₁c₄T - (…)` splits. For the Tate curve `a₁ = 1`, `a₃ = a₂ = 0` and the reduction is
the nodal cubic `y² + xy = x³`, whose node has tangents `y = 0` and `y = -x`, manifestly
rational — so it splits. This is where "the Tate curve is *the* split model" is discharged.
*Note*: even the valuation part `v(Δ(E_q)) < 1` needs A2 (or at least `constantCoeff ΔFormal = 0`
and `coeff 1 ΔFormal` a unit, which is a weaker fragment of A2 — see risks).

**B1.** Pure field algebra. From `j = c₄³/Δ` and `j - 1728 = c₆²/Δ`, equal `j` gives the two
identities for `d`. Needs `c₄(E), c₄(E_q), c₆(E), c₆(E_q) ≠ 0`, all from `j ∉ {0,1728}`.

**B2 (the hard gap).** `d ∈ (kˣ)²` is exactly "the quadratic twist relating `E` and `E_q` is
trivial". The input is that **both** curves have *split* multiplicative reduction. The clean
statement to isolate and prove:
> For an elliptic curve `W/k` with multiplicative reduction, the reduction is **split** iff a
> canonical square-class `δ(W) ∈ kˣ/(kˣ)²` is trivial; and for two same-`j` curves the twist
> class `d` equals `δ(E)·δ(E_q)`.

Then split + split ⟹ `δ(E) = δ(E_q) = 1` ⟹ `d` square. The residue quadratic in
`HasSplitMultiplicativeReduction` (splitting of `c₄T² + a₁c₄T - (…)`) is the concrete handle
on `δ`. This is real reduction-theory work; see risks.

**B3.** Given `u ∈ kˣ` with `u⁴ = c₄(E)/c₄(E_q)` and `u⁶ = c₆(E)/c₆(E_q)` (take `u` a square
root of `d` from B2; then `u² = d`, and B1 gives the `⁴/⁶` powers), the curves `E_q` and `E`
have `c₄, c₆` related by the scaling of a variable change with parameter `u`. Since `c₄, c₆`
determine an elliptic curve up to variable change over a field (for `Δ ≠ 0`), there is a
`VariableChange k` sending `E_q` to `E`. The generic lemma
> matching `(c₄, c₆)` up to `(u⁴, u⁶)` ⟹ `∃ C : VariableChange k, C • W₁ = W₂`
is the field-generic cousin of mathlib's `exists_variableChange_of_j_eq` (which is stated
only over `[IsSepClosed]`). It may be extractable from the normal-form machinery in
`Mathlib/AlgebraicGeometry/EllipticCurve/NormalForms.lean` + `IsomOfJ.lean`, or need a short
standalone proof (put `E_q`, `E` in short/normal form and solve for `r, s, t`).

### Final glue

```lean
theorem exists_variableChange_tateCurve :
    ∃ C : VariableChange k, C • tateCurve E.q = E := by
  have hj  : (tateCurve E.q).j = E.j := ...      -- A5
  have hEq : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[k] := ...  -- B0
  -- B1: define d, its square/cube identities
  -- B2: d is a square  (uses hEq and E's split reduction)
  -- B3: turn the square root of d into the variable change
  ...
```

---

## Dominant risks (read before starting)

### Gap #1 — the discriminant product formula (A2)

`Δ_Weierstrass ⟨1,0,0,a₄Formal,a₆Formal⟩ = X·∏(1-Xⁿ)²⁴` in `ℤ⟦X⟧`. Two routes:

- **(a) Direct formal proof.** Prove the `q`-expansion of `Δ` as an identity of integer power
  series. This is essentially formalizing `Δ = η²⁴`. Mathlib's modular-forms `q`-expansion API
  is thin; expect this to be a mini-project on its own.
- **(b) Transfer from the analytic side.** `TateCurveConstruction.lean` develops the complex
  Tate curve (`weierstrassP_q_expansion`, Eisenstein series via `riemannZeta_four/six`, …). If
  that file proves `Δ(E_q^{an}) = q∏(1-qⁿ)²⁴` as a **complex** `q`-series with the standard
  coefficients, the `ℤ⟦X⟧` identity follows: both sides have integer coefficients and
  `ℤ → ℂ` is injective, so a coefficientwise identity over `ℂ` transfers to `ℤ⟦X⟧`. **Check
  whether that file already reaches `Δ`, or is one Eisenstein-series step away** — this is
  likely the cheaper route and should be scoped first.

**Weaker fragment that still unblocks B0's valuation part:** you only need
`constantCoeff ΔFormal = 0` and `coeff 1 ΔFormal` a unit to get `v(Δ(E_q)) = v(q) < 1`. Those
two coefficients of `X·∏(1-Xⁿ)²⁴` are `0` and `1`, provable directly from the product without
the full identity. So **B0 can proceed on a fragment**; only A4/A5 need the full A2.

### Gap #2 — split reduction ⟺ trivial twist class (B2)

The arithmetic heart of V.5.3. Needs a clean "reduction type of a quadratic twist" theory:
nontrivial unramified twist swaps split ↔ non-split; ramified twist gives additive. In terms
of the residue quadratic of `HasSplitMultiplicativeReduction`, split ⟺ a square class is
trivial. `QuadraticTwists.lean` gives the twist *models* and their `c₄, Δ`, but **not** their
reduction behaviour — that is the new content. Consider isolating a general lemma
`HasSplitMultiplicativeReduction (W.quadraticTwistOf t n) ↔ (t²-4n) ∈ (kˣ)²` (or the residue
version) and proving `exists_variableChange_tateCurve` as a corollary.

---

## Recommended build order

Bottom-up, each step lake-building before the next:

1. **A1** `tateCurve_c₄` — warm-up, pure `evalInt`-linearity. (low risk)
2. **A3** `evalInt_subst` — reusable bridge lemma, no dependence on A2. (medium)
3. **A2 fragment** `constantCoeff/coeff 1 ΔFormal` → **B0** split reduction of `E_q`. (medium)
4. **B1** the `d`-identities. (low, pure algebra)
5. **B3** matching-`(c₄,c₆)` ⟹ variable change (generic lemma). (medium)
6. **A2 full** discriminant product formula — **scope route (b) first**. (HIGH risk)
7. **A4, A5** finish Half A. (low, once A2 lands)
8. **B2** split ⟹ `d` square. (HIGH risk)
9. **Final glue.**

Steps 1–5 are all doable now and de-risk ~half the file without touching either gap. The two
red items (6, 8) are where the mathematical difficulty is concentrated and each may warrant
its own blueprint/ticket.

---

## Skeleton (drop into a new `.lean`, or grow `TateCurve.lean`)

All signatures below are grounded in existing names. `sorry`ed leaves; the file should
`lake build` with these as stubs (adjust namespaces/opens as needed).

```lean
open TateCurve PowerSeries in
theorem WeierstrassCurve.tateCurve_c₄ (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ = evalInt q c₄Formal := by
  sorry  -- A1: c₄ = 1 - 48·tateA₄ q; evalInt-linearity from a₄Formal, c₄Formal

open TateCurve PowerSeries in
theorem WeierstrassCurve.tateCurve_Δ (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = evalInt q ΔFormal := by
  sorry  -- A2: discriminant product formula — GAP #1

open TateCurve PowerSeries in
theorem TateCurve.evalInt_subst (w : k) (hw : valuation k w < 1) (F G : ℤ⟦X⟧)
    (hG0 : constantCoeff G = 0) :
    evalInt (evalInt w G) F = evalInt w (subst G F) := by
  sorry  -- A3

open TateCurve in
theorem WeierstrassCurve.evalInt_jInv (q : k) (hq0 : q ≠ 0) (hq : valuation k q < 1) :
    evalInt q jInv = (tateCurve q).j⁻¹ := by
  sorry  -- A4, from tateCurve_c₄, tateCurve_Δ, evalInt_mul

theorem WeierstrassCurve.j_tateCurve_q : (tateCurve E.q).j = E.j := by
  sorry  -- A5, from evalInt_jInv + evalInt_subst + jInv_subst_jInvReverse

instance : (tateCurve E.q).HasSplitMultiplicativeReduction 𝒪[k] := by
  sorry  -- B0

theorem WeierstrassCurve.isSquare_twist_of_splitMult
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic]
    [W₁.HasSplitMultiplicativeReduction 𝒪[k]] [W₂.HasSplitMultiplicativeReduction 𝒪[k]]
    (hj : W₁.j = W₂.j) :
    IsSquare (W₁.c₄ * W₂.c₆ / (W₂.c₄ * W₁.c₆)) := by
  sorry  -- B1 + B2 — GAP #2 is the IsSquare part

theorem WeierstrassCurve.exists_variableChange_of_c₄_c₆
    (W₁ W₂ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] (u : kˣ)
    (h4 : W₂.c₄ = (u : k)^4 * W₁.c₄) (h6 : W₂.c₆ = (u : k)^6 * W₁.c₆) :
    ∃ C : VariableChange k, C • W₁ = W₂ := by
  sorry  -- B3 (field-generic cousin of exists_variableChange_of_j_eq)

-- assembled:
theorem WeierstrassCurve.exists_variableChange_tateCurve' :
    ∃ C : VariableChange k, C • tateCurve E.q = E := by
  sorry  -- glue A5 + B0 + isSquare_twist_of_splitMult + exists_variableChange_of_c₄_c₆
```

---

## Appendix: API quick-reference (all verified present)

**Tate parameter / formal series** (`TateParameter.lean`, `TateCurveBaseChange.lean`):
`tateParameter`, `tateParameter_eq`, `jInv`, `ΔFormal`, `c₄Formal`, `sInt`, `jInvReverse`,
`subst_jInvReverse`, `jInv_subst_jInvReverse`, `constantCoeff_jInvReverse`,
`coeff_one_jInvReverse`, `evalInt`, `evalInt_mul`, `evalInt_pow`, `evalInt_add`, `evalInt_X`,
`summable_evalInt`, `valuation_evalInt_eq`, `a₄Formal`, `a₆Formal`, `coeff_a₄Formal`,
`coeff_a₆Formal`.

**This file** (`TateCurve.lean`): `tateCurve`, `tateA₄`, `tateA₆`, `tateA₄_eq_evalInt`,
`tateA₆_eq_evalInt`, `q`, `qUnit`, `q_ne_zero`, `valuation_q_lt_one`, `one_lt_valuation_j`,
`valuation_c₄_eq_one`, `valuation_Δ_lt_one`, `valuation_j_eq`.

**Quadratic twists** (`QuadraticTwists.lean`): `quadraticTwistOf`, `c₄_quadraticTwistOf`,
`Δ_quadraticTwistOf`, `j_quadraticTwistOf`, `isElliptic_quadraticTwistOf`,
`exists_smul_eq_quadraticTwistOf_quadraticTwistOf`, `exists_smul_quadraticTwistOf_eq`,
`quadraticTwistBy`, `quadraticTwist`.

**Mathlib** (`Weierstrass.lean`, `VariableChange.lean`, `Reduction.lean`, `IsomOfJ.lean`):
`b₂ b₄ b₆ b₈ c₄ c₆ Δ j`, `variableChange_c₄/c₆/Δ`, `HasMultiplicativeReduction`,
`HasSplitMultiplicativeReduction` (residue-quadratic-splits form), `exists_variableChange_of_j_eq`
(**`[IsSepClosed]` only** — does not apply over `k`).
