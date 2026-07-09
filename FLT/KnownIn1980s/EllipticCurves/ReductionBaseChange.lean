/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.LocalField.Basic
-- the minimality criterion `WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one` (step 2)
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
-- the valuation-transfer lemmas `ValuativeExtension.valuation_algebraMap_{le,lt,eq}_one`
-- (step 0, used to build `integerMap`) and the adic ↔ canonical bridges
-- `ValuativeRel.adicValuation_{lt,eq}_one_iff` (used throughout the proof sketches)
public import FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!

# Reduction theory under base change

Let `k → l` be a valuative extension of nonarchimedean local fields and let `E/k` be an
elliptic curve with split multiplicative reduction. This file proves that the two reduction
instances currently sorried in `FLT.KnownIn1980s.EllipticCurves.TateCurve` transfer to the
base change (stated for an arbitrary such `E`, not just Tate curves):

* `(E.baseChange l).IsMinimal 𝒪[l]` (`isMinimal_baseChange`, and the
  `HasMultiplicativeReduction` instance which yields it by parent projection)
* `(E.baseChange l).HasSplitMultiplicativeReduction 𝒪[l]`

Neither is provable by assembling existing declarations: mathlib's reduction API
(`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`) has no minimality criterion and no
base-change results at all, and mathlib's `ValuativeExtension` provides only the map of
value groups `mapValueGroupWithZero`, not the induced ring map `𝒪[k] →+* 𝒪[l]` of rings
of integers. FLT PR #1081 (branch `logos2`) also leaves both instances sorried.

## Mathematical route

The whole point is that minimality by itself is *not* preserved by base change —
`y² = x³ + p` is minimal over `ℚ_p` but not over `ℚ_p(p^{1/6})` — so one cannot argue
about minimality abstractly. The multiplicative reduction hypothesis rescues everything
through a single mechanism: it forces `|c₄| = 1`, and "integral with `|c₄| = 1`" is a
property that (i) forces minimality and (ii) is visibly preserved by any valuative
extension.

Mathlib phrases `HasMultiplicativeReduction` at the *field level* — its two non-parent
fields are statements about the adic valuation of `W.Δ` and `W.c₄` as elements of the
field — and this branch already has both halves of the translation apparatus:

* the bridges `ValuativeRel.adicValuation_lt_one_iff` and `adicValuation_eq_one_iff`
  (`FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic`) convert between the adic
  valuation of the DVR `𝒪[k]`, in which mathlib's reduction theory is phrased, and the
  canonical valuation of `k`, on the two distinctions that matter (`< 1` and `= 1`);
* strict monotonicity of `ValuativeExtension.mapValueGroupWithZero` transfers the
  canonical valuation along `k → l`.

So everything except the minimality criterion and the splitness clause is a field-level
valuation chase along the chain *adic over `k` → canonical over `k` → canonical over `l`
→ adic over `l`*. In detail:

0. **Transfer of the canonical valuation**
   (`ValuativeExtension.valuation_algebraMap_le_one`, `_lt_one`, `_eq_one` — proved
   below, not sorried). A valuative extension preserves `|x| ≤ 1`, `|x| < 1` and
   `|x| = 1`, because `mapValueGroupWithZero` is a strictly monotone monoid-with-zero
   homomorphism sending `valuation k x` to `valuation l (algebraMap k l x)`. (The `< 1`
   case duplicates `TateCurve.valuation_algebraMap_lt_one` from `TateCurveBaseChange`;
   when de-blueprinting, consolidate all three next to the bridges in
   `FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic`.)

1. **Functoriality of the integers** (`ValuativeExtension.integerMap`), needed *only*
   for the splitness clause (step 5). By `valuation_algebraMap_le_one`, `algebraMap k l`
   restricts to a map `𝒪[k] →+* 𝒪[l]`; it is a local homomorphism (by
   `valuation_algebraMap_lt_one`) and hence induces a map of residue fields
   (`residueMap`). The `IsMinimal` and `HasMultiplicativeReduction` transfers below do
   not use any of this.

2. **The minimality criterion** (`WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`).
   An integral Weierstrass equation whose `c₄` has adic valuation `1` is minimal — the
   unit-`c₄` case of the Kraus–Laska criterion "`v(c₄) < 4` or `v(Δ) < 12` implies
   minimal" (Silverman AEC, Remark VII.1.1). This is the one genuinely new piece of
   mathematics, and it is mathlib-worthy. It is stated at the field level to match
   mathlib's `HasMultiplicativeReduction.multiplicativeReduction`, which is exactly the
   fact consumers hold.

3. **Base change of the integral model.** Integrality transfers coefficientwise: each
   coefficient of `E.baseChange l` is `algebraMap k l` of the corresponding coefficient
   of `E`, and `valuation_algebraMap_le_one` keeps it integral
   (`isIntegral_of_exists_lift`). For the splitness clause we also record
   `integralModel_baseChange`: the integral model of the base change is the
   `integerMap`-image of the integral model, by uniqueness of lifts along the injective
   map `𝒪[l] → l`.

4. **Multiplicative reduction.** `badReduction` and `multiplicativeReduction` transfer
   along the chain above: adic `|Δ| < 1` over `k` converts to the canonical valuation
   (`adicValuation_lt_one_iff` + `integralModel_Δ_eq`), moves along the extension
   (`valuation_algebraMap_lt_one` + `map_Δ`), and converts back over `l`
   (`adicValuation_lt_one_iff` again); same for `|c₄| = 1` with the `eq_one` lemmas.
   Minimality is step 2 applied to the transferred `|c₄| = 1`. No `integerMap`, no
   `IsLocalHom`. Note multiplicative reduction is preserved by *arbitrary* extensions of
   local fields (Silverman AEC, VII.5.4(b)) — no unramifiedness is needed, in contrast
   to good reduction.

5. **Splitness.** Mathlib's `HasSplitMultiplicativeReduction` demands that the explicit
   quadratic `c₄T² + a₁c₄T - (54b₆ - 3b₂b₄ + a₂c₄)` (tangent directions at the node)
   split over the residue field. By 3 the quadratic of the `l`-model is the image of
   the quadratic of the `k`-model under the induced map of residue fields
   (`IsLocalRing.ResidueField.map (integerMap k l)`), and a split polynomial stays split
   under any ring map (`Polynomial.Splits.map`). Splitness can only be gained, never
   lost, when the residue field grows. This is the only step that uses `integerMap`,
   `residueMap` and `integralModel_baseChange`.

The base-change transfer is packaged as `theorem`s here rather than `instance`s, so that
the consuming instances live in `FLT.KnownIn1980s.EllipticCurves.TateCurve`, where this file
is imported: the two sorried instances there are filled by `isMinimal_baseChange` and
`hasSplitMultiplicativeReduction_baseChange` (which also yields `IsMinimal` and
`HasMultiplicativeReduction` by class-parent projection).

The `k`-side adic → canonical conversions of `valuation_c₄_baseChange_eq_one` and
`valuation_Δ_baseChange_lt_one` duplicate the downstream `WeierstrassCurve.valuation_c₄_eq_one`
and `valuation_Δ_lt_one` of `TateCurve`; they are reduction-theoretic rather than
Tate-theoretic, so consider extracting the `k`-side halves as shared lemmas (or moving those
`TateCurve` lemmas here) when de-blueprinting.

## References

* Silverman, *The arithmetic of elliptic curves*, VII §1 (minimal Weierstrass equations,
  Remark VII.1.1 for the minimality criterion) and VII.5.4 (behaviour of reduction type
  under field extension).
-/

@[expose] public section

open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

namespace ValuativeExtension

/-! ### Step 0: transfer of the canonical valuation

A valuative extension preserves `≤ 1`, `< 1` and `= 1` of the canonical valuation:
`mapValueGroupWithZero` is a strictly monotone monoid-with-zero homomorphism matching
the two valuations. These are proved (for arbitrary valuative extensions of rings) in
`FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic` as
`ValuativeExtension.valuation_algebraMap_le_one`, `_lt_one` and `_eq_one`; they are used
just below to build `integerMap`. (The `< 1` case supersedes
`TateCurve.valuation_algebraMap_lt_one` in `TateCurveBaseChange`.)
-/

/-! ### Step 1: functoriality of the ring of integers

A valuative extension `k → l` restricts to a local homomorphism `𝒪[k] →+* 𝒪[l]` and
hence induces a map of residue fields. Only the valuative structure is needed — no
topology, no local-field hypothesis — so this subsection is stated for arbitrary
valuative fields; it is all mathlib-ready material. In this file it is needed *only* for
the splitness clause of `HasSplitMultiplicativeReduction`: the `IsMinimal` and
`HasMultiplicativeReduction` transfers stay at the field level throughout.
-/

section IntegerMap

variable (k l : Type*) [Field k] [ValuativeRel k] [Field l] [ValuativeRel l]
  [Algebra k l] [ValuativeExtension k l]

/-- The restriction of `algebraMap k l` to the rings of integers: `𝒪[k]` is the subring
`(valuation k).integer` of `k`, and `valuation_algebraMap_le_one` says `algebraMap k l`
maps it into `(valuation l).integer`.

Implementation note: it may be worth defining the `Algebra 𝒪[k] 𝒪[l]` instance directly
instead, so that `WeierstrassCurve.baseChange` (rather than `map`) can be used on
integral models in `integralModel_baseChange` below; whichever is chosen, this is the
underlying ring homomorphism. -/
noncomputable def integerMap : 𝒪[k] →+* 𝒪[l] :=
  (algebraMap k l).restrict 𝒪[k] 𝒪[l] fun _ hx ↦
    (Valuation.mem_integer_iff _ _).mpr <|
      valuation_algebraMap_le_one <| (Valuation.mem_integer_iff _ _).mp hx

/-- `integerMap` is the algebra map on underlying elements. -/
@[simp]
theorem integerMap_coe (x : 𝒪[k]) :
    (integerMap k l x : l) = algebraMap k l (x : k) :=
  rfl

/-- `integerMap` is a local homomorphism: if `integerMap x` is a unit then `x` is a
unit. Non-units of the integer subring are exactly the elements of valuation `< 1`
(`Valuation.Integer.not_isUnit_iff_valuation_lt_one`), and `valuation k x < 1` gives
`valuation l (integerMap k l x) < 1` by `valuation_algebraMap_lt_one`. Needed only to
make `IsLocalRing.ResidueField.map` applicable in `residueMap`. -/
instance : IsLocalHom (integerMap k l) where
  map_nonunit x hx := by
    by_contra h
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at h
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ?_ hx
    rw [integerMap_coe]
    exact valuation_algebraMap_lt_one h

/-- The commuting square `algebraMap 𝒪[l] l ∘ integerMap = algebraMap k l ∘ algebraMap 𝒪[k] k`
underlying `integerMap`: on underlying elements both send `x` to `algebraMap k l x`
(`integerMap_coe`, and `algebraMap 𝒪[·] ·` is the subring inclusion). This is the
functoriality used to transfer integral models along the base change. -/
theorem algebraMap_integerMap (x : 𝒪[k]) :
    algebraMap 𝒪[l] l (integerMap k l x) = algebraMap k l (algebraMap 𝒪[k] k x) :=
  integerMap_coe k l x

end IntegerMap

/-! ### Interlude: nonarchimedean local fields

From here on `k → l` is a valuative extension of nonarchimedean local fields, so that the
rings of integers are discrete valuation rings and mathlib's reduction theory applies.
-/

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

variable (k l) in
/-- The induced map of residue fields `𝒪[k]/𝓂[k] →+* 𝒪[l]/𝓂[l]`, from the local
homomorphism `integerMap`. (An honest definition, not a sorry: it is
`IsLocalRing.ResidueField.map` of `integerMap k l`.) -/
noncomputable def residueMap :
    IsLocalRing.ResidueField 𝒪[k] →+* IsLocalRing.ResidueField 𝒪[l] :=
  IsLocalRing.ResidueField.map (integerMap k l)

end ValuativeExtension

namespace WeierstrassCurve

/-! ### Step 2: the minimality criterion

The unit-`c₄` case of the Kraus–Laska criterion (Silverman AEC, Remark VII.1.1) — an
integral Weierstrass equation whose `c₄` has adic valuation `1` is minimal — is proved
(over an arbitrary discrete valuation ring with fraction field, as in mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`) in
`FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` as
`WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`. Its hypothesis is at the field
level, matching mathlib's phrasing of `HasMultiplicativeReduction.multiplicativeReduction`
— exactly the fact `isMinimal_baseChange` below holds after transferring `c₄`.
-/

/-! ### Steps 3–5: base change of reduction data -/

section BaseChange

open ValuativeExtension

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]
variable (E : WeierstrassCurve k)

/-- Base change along a valuative extension preserves integrality, coefficientwise:
each coefficient of `E.baseChange l` is `algebraMap k l` of the corresponding
coefficient of `E` (`map_a₁`, …), which is integral over `k` (`integralModel_a₁_eq`, …,
and elements of `𝒪[k]` have `valuation k · ≤ 1`), so stays integral over `l` by
`valuation_algebraMap_le_one`; conclude with `isIntegral_of_exists_lift`. (No
functoriality of `map` is needed.) -/
instance [IsIntegral 𝒪[k] E] : IsIntegral 𝒪[l] (E.baseChange l) :=
  isIntegral_of_exists_lift 𝒪[l]
    ⟨integerMap k l (integralModel 𝒪[k] E).a₁, by
      rw [algebraMap_integerMap, integralModel_a₁_eq]; exact (E.map_a₁ _).symm⟩
    ⟨integerMap k l (integralModel 𝒪[k] E).a₂, by
      rw [algebraMap_integerMap, integralModel_a₂_eq]; exact (E.map_a₂ _).symm⟩
    ⟨integerMap k l (integralModel 𝒪[k] E).a₃, by
      rw [algebraMap_integerMap, integralModel_a₃_eq]; exact (E.map_a₃ _).symm⟩
    ⟨integerMap k l (integralModel 𝒪[k] E).a₄, by
      rw [algebraMap_integerMap, integralModel_a₄_eq]; exact (E.map_a₄ _).symm⟩
    ⟨integerMap k l (integralModel 𝒪[k] E).a₆, by
      rw [algebraMap_integerMap, integralModel_a₆_eq]; exact (E.map_a₆ _).symm⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] in
/-- The integral model of the base change is the base change of the integral model.
Both sides are lifts of `E.baseChange l` along the *injective* map `𝒪[l] → l`
(injectivity from `IsFractionRing`), and lifts along an injective map are unique:
compare coefficientwise via `integralModel_a₁_eq` on both sides and the commuting square
`algebraMap_integerMap`. (Only the splitness clause of step 5 consumes this.) -/
theorem integralModel_baseChange [IsIntegral 𝒪[k] E] :
    integralModel 𝒪[l] (E.baseChange l) =
      (integralModel 𝒪[k] E).map (integerMap k l) := by
  -- both sides base change to `E.baseChange l`; `𝒪[l] → l` is injective, so `map` is
  refine map_injective (f := algebraMap 𝒪[l] l) (IsFractionRing.injective 𝒪[l] l) ?_
  change (integralModel 𝒪[l] (E.baseChange l)).map (algebraMap 𝒪[l] l)
    = ((integralModel 𝒪[k] E).map (integerMap k l)).map (algebraMap 𝒪[l] l)
  have hcomp : (algebraMap 𝒪[l] l).comp (integerMap k l)
      = (algebraMap k l).comp (algebraMap 𝒪[k] k) := by
    ext x; simpa using algebraMap_integerMap k l x
  rw [map_map, hcomp, ← map_map,
    show (integralModel 𝒪[k] E).map (algebraMap 𝒪[k] k) = E from baseChange_integralModel_eq 𝒪[k] E]
  exact baseChange_integralModel_eq 𝒪[l] (E.baseChange l)

/-- The `c₄` of the base change has adic valuation `1`. Multiplicative reduction of `E`
makes the canonical valuation `|E.c₄| = 1` (via `adicValuation_eq_one_iff` and
`integralModel_c₄_eq`, as in `WeierstrassCurve.valuation_c₄_eq_one`); this transfers to
`l` by `valuation_algebraMap_eq_one`, and converts back to the adic valuation over
`𝒪[l]`. Shared by `isMinimal_baseChange` and multiplicative reduction of the base change. -/
theorem valuation_c₄_baseChange_eq_one [HasMultiplicativeReduction 𝒪[k] E] :
    (IsDiscreteValuationRing.maximalIdeal 𝒪[l]).valuation l (E.baseChange l).c₄ = 1 := by
  have hk : valuation k E.c₄ = 1 := by
    have hmul := HasMultiplicativeReduction.multiplicativeReduction (R := 𝒪[k]) (W := E)
    rw [← integralModel_c₄_eq 𝒪[k] E] at hmul ⊢
    exact adicValuation_eq_one_iff.mp hmul
  have hl : valuation l (E.baseChange l).c₄ = 1 := by
    rw [show (E.baseChange l).c₄ = algebraMap k l E.c₄ from E.map_c₄ (algebraMap k l)]
    exact valuation_algebraMap_eq_one hk
  rw [← integralModel_c₄_eq 𝒪[l] (E.baseChange l)] at hl ⊢
  exact adicValuation_eq_one_iff.mpr hl

/-- The discriminant of the base change has adic valuation `< 1`. Multiplicative reduction
of `E` makes `|E.Δ| < 1` (via `adicValuation_lt_one_iff` and `integralModel_Δ_eq`, as in
`WeierstrassCurve.valuation_Δ_lt_one`); this transfers to `l` by
`valuation_algebraMap_lt_one`, and converts back to the adic valuation over `𝒪[l]`. -/
theorem valuation_Δ_baseChange_lt_one [HasMultiplicativeReduction 𝒪[k] E] :
    (IsDiscreteValuationRing.maximalIdeal 𝒪[l]).valuation l (E.baseChange l).Δ < 1 := by
  have hk : valuation k E.Δ < 1 := by
    have hbad := HasMultiplicativeReduction.badReduction (R := 𝒪[k]) (W := E)
    rw [← integralModel_Δ_eq 𝒪[k] E] at hbad ⊢
    exact adicValuation_lt_one_iff.mp hbad
  have hl : valuation l (E.baseChange l).Δ < 1 := by
    rw [show (E.baseChange l).Δ = algebraMap k l E.Δ from E.map_Δ (algebraMap k l)]
    exact valuation_algebraMap_lt_one hk
  rw [← integralModel_Δ_eq 𝒪[l] (E.baseChange l)] at hl ⊢
  exact adicValuation_lt_one_iff.mpr hl

/-- Base change along a valuative extension preserves minimality *in the presence of
multiplicative reduction* (minimality alone is not preserved: `y² = x³ + p` is minimal
over `ℚ_p` but not over `ℚ_p(p^{1/6})`): multiplicative reduction makes `|c₄| = 1`
(`valuation_c₄_baseChange_eq_one`), and unit `c₄` forces minimality
(`isMinimal_of_valuation_c₄_eq_one`).

A `theorem` rather than an `instance`: the `HasMultiplicativeReduction` instance below
yields `IsMinimal 𝒪[l] (E.baseChange l)` again by class-parent projection, and a second
instance path to it would overlap (cf. the `overlappingInstances` linter and
mathlib#41391). -/
theorem isMinimal_baseChange [HasMultiplicativeReduction 𝒪[k] E] :
    IsMinimal 𝒪[l] (E.baseChange l) :=
  isMinimal_of_valuation_c₄_eq_one 𝒪[l] (E.baseChange l) (valuation_c₄_baseChange_eq_one E)

/-- Base change along a valuative extension preserves multiplicative reduction
(Silverman AEC, VII.5.4(b); true for arbitrary extensions of local fields — contrast
good reduction, which needs unramifiedness): minimality is `isMinimal_baseChange`, and the
`badReduction`/`multiplicativeReduction` fields are `valuation_Δ_baseChange_lt_one` and
`valuation_c₄_baseChange_eq_one`.

Stated as a `theorem` rather than an `instance` so that the *consuming* instance lives in
`FLT.KnownIn1980s.EllipticCurves.TateCurve`; use it there via
`WeierstrassCurve.hasMultiplicativeReduction_baseChange`. -/
theorem hasMultiplicativeReduction_baseChange [HasMultiplicativeReduction 𝒪[k] E] :
    HasMultiplicativeReduction 𝒪[l] (E.baseChange l) where
  toIsMinimal := isMinimal_baseChange E
  badReduction := valuation_Δ_baseChange_lt_one E
  multiplicativeReduction := valuation_c₄_baseChange_eq_one E

open Polynomial in
/-- The tangent-cone quadratic `c₄T² + a₁c₄T - (54b₆ - 3b₂b₄ + a₂c₄)` whose splitting over
the residue field defines split multiplicative reduction (Silverman AEC, VII, and mathlib's
`HasSplitMultiplicativeReduction.splitMultiplicativeReduction`). Factored out so that its
naturality `splitQuadratic_map` can drive the base-change argument. -/
private noncomputable def splitQuadratic {A : Type*} [CommRing A] (W : WeierstrassCurve A) :
    A[X] :=
  C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X - C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The tangent-cone quadratic is natural in the coefficient ring: it commutes with any
ring homomorphism, since every coefficient is a polynomial in the `aᵢ` and `map` is a ring
homomorphism on each. -/
private lemma splitQuadratic_map {A B : Type*} [CommRing A] [CommRing B]
    (W : WeierstrassCurve A) (ψ : A →+* B) :
    splitQuadratic (W.map ψ) = (splitQuadratic W).map ψ := by
  simp only [splitQuadratic, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_a₂, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat, map_add,
    map_sub, map_mul, map_ofNat]

/-- Base change along a valuative extension preserves *split* multiplicative reduction:
the residue field only grows, and a split quadratic stays split under any ring map.

Proof: multiplicative reduction is `hasMultiplicativeReduction_baseChange`. For splitness, by
`integralModel_baseChange` the integral model over `𝒪[l]` is `integerMap` of the one over
`𝒪[k]`, so the tangent-cone quadratic transfers as `splitQuadratic_map`. The residue square
`residue 𝒪[l] ∘ integerMap = residueMap ∘ residue 𝒪[k]`
(`IsLocalRing.ResidueField.map_residue`) and `Polynomial.map_map` identify the reduced
quadratic over `𝓀[l]` with the `residueMap`-image of the reduced quadratic over `𝓀[k]`,
which splits by hypothesis; conclude with `Polynomial.Splits.map`. This is the only place
`integerMap`, `residueMap` and `integralModel_baseChange` are used.

Stated as a `theorem` rather than an `instance` so that the *consuming* instance lives in
`FLT.KnownIn1980s.EllipticCurves.TateCurve`; use it there via
`WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange`. -/
theorem hasSplitMultiplicativeReduction_baseChange [HasSplitMultiplicativeReduction 𝒪[k] E] :
    HasSplitMultiplicativeReduction 𝒪[l] (E.baseChange l) where
  toHasMultiplicativeReduction := hasMultiplicativeReduction_baseChange E
  splitMultiplicativeReduction := by
    -- the `k`-quadratic splits over `𝓀[k]` by hypothesis
    have hsplit : Polynomial.Splits (Polynomial.map
        (algebraMap 𝒪[k] (IsLocalRing.ResidueField 𝒪[k]))
        (splitQuadratic (integralModel 𝒪[k] E))) :=
      HasSplitMultiplicativeReduction.splitMultiplicativeReduction (R := 𝒪[k]) (W := E)
    -- the residue square `residue 𝒪[l] ∘ integerMap = residueMap ∘ residue 𝒪[k]`
    have hcomp : (IsLocalRing.residue 𝒪[l]).comp (integerMap k l)
        = (residueMap k l).comp (IsLocalRing.residue 𝒪[k]) :=
      RingHom.ext fun x ↦ IsLocalRing.ResidueField.map_residue (integerMap k l) x
    -- push the `l`-quadratic through the square onto the `k`-quadratic and transfer splitting
    change Polynomial.Splits (Polynomial.map (algebraMap 𝒪[l] (IsLocalRing.ResidueField 𝒪[l]))
      (splitQuadratic (integralModel 𝒪[l] (E.baseChange l))))
    rw [integralModel_baseChange E, splitQuadratic_map, Polynomial.map_map,
      IsLocalRing.ResidueField.algebraMap_eq, hcomp, ← IsLocalRing.ResidueField.algebraMap_eq,
      ← Polynomial.map_map]
    exact hsplit.map (residueMap k l)

end BaseChange

end WeierstrassCurve
