/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!

Let E be an elliptic curve over the field of fractions k
of a DVR R, with good reduction. Let n be a positive
integer which is invertible in the residue field of R
(equivalently, prime to the residue characteristic).
Then the Galois representation on the n-torsion points
over k^sep is unramified.

This is the easy direction of the criterion of Néron–Ogg–Shafarevich;
see for example [Silverman, *The Arithmetic of Elliptic Curves*, VII.7.1]
or [Serre–Tate, *Good reduction of abelian varieties*, Theorem 1
for the general abelian variety case].

The correct hypothesis here is that `n` is invertible in the *residue field*,
not merely that `n` is nonzero in `k`. In mixed characteristic (`k` a finite
extension of `ℚ_p`, residue characteristic `p`) every positive `n` is nonzero
in `k`, yet the `p`-torsion of a curve with good reduction, while flat, is in
general ramified at `p`; see the module docstring of
`FLT.KnownIn1980s.EllipticCurves.Flat`. The two hypotheses agree in equal
characteristic. The deduction of this statement from the finite flatness of the
torsion is `FLT.KnownIn1980s.EllipticCurves.FlatImpliesUnramified`.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄K).Point` notation for the group of `K`-points

-- let R be a discrete valuation ring with field of fractions k
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]

-- Let E/k be an elliptic curve with good reduction over R. Note that mathlib's
-- `HasGoodReduction` asks that the given Weierstrass equation for E is a minimal
-- integral equation whose discriminant has valuation 1; this loses no generality
-- because every elliptic curve over k is isomorphic to one given by a minimal
-- equation (`WeierstrassCurve.exists_isMinimal`).
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a positive natural. Its invertibility in the residue field of R is the
-- hypothesis `hn` in the theorem below.
variable (n : ℕ)

-- Let ksep be a separable closure of k (`DecidableEq` is needed for the group law on points)
variable (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] [DecidableEq ksep]

-- Let 𝒪 be a valuation subring of ksep. This is arbitrary here; the hypothesis
-- that it lies above R is `h𝒪` in the theorem below.
variable (𝒪 : ValuationSubring ksep)

/-- If `E` is an elliptic curve over `k` (given by a minimal Weierstrass equation)
with good reduction over `R`, if `n` is invertible in the residue field of `R`, and if
`𝒪` is a valuation subring of `kˢᵉᵖ` lying above `R`, then the inertia subgroup of
`Gal(kˢᵉᵖ/k)` at `𝒪` acts trivially on the `n`-torsion of `E(kˢᵉᵖ)`. In other words, the
Galois representation on the `n`-torsion points is unramified. -/
theorem WeierstrassCurve.torsion_unramified_of_good_reduction
    -- Assume n is invertible in the residue field of R
    (hn : IsUnit (n : IsLocalRing.ResidueField R))
    -- Assume 𝒪 lies above R, i.e. 𝒪 ∩ k = R
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    -- Then every element of the inertia subgroup at 𝒪 fixes every n-torsion point of E(ksep)
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P :=
  -- PROOF SKETCH (the elementary division-polynomial route; Silverman VII.7.1). Let `κ` be
  -- the residue field of `𝒪`.
  --
  -- 1. Integrality: `E[n] ⊆ E(𝒪)`. For a nonzero `n`-torsion point `P = (x, y)`, the
  --    dictionary lemma `WeierstrassCurve.Affine.Point.eval_ΨSq_eq_zero_of_smul_eq_zero`
  --    (in `FLT.KnownIn1980s.EllipticCurves.DivisionPolynomialTorsion`) says `x` is a root
  --    of `ΨSqₙ`. Its leading coefficient `n²` (`leadingCoeff_ΨSq`) is a unit in `R` by
  --    `hn`, so `x` is integral over `R`, hence lies in `𝒪` (which, via `h𝒪`, contains the
  --    integral closure of `R` in `kˢᵉᵖ`); the Weierstrass equation then puts `y ∈ 𝒪` too.
  --
  -- 2. Reduction is injective on `E[n]`. Reducing coordinates mod the maximal ideal of `𝒪`
  --    gives a map to `Ẽ(κ)` (`Ẽ = E.reduction`, elliptic by good reduction). By
  --    `WeierstrassCurve.isCoprime_Φ_ΨSq` (`Δ` is a unit in `κ`), `Φₙ` and `ΨSqₙ` share no
  --    root mod the maximal ideal, so distinct `n`-torsion `x`-coordinates stay distinct
  --    after reduction; hence reduction is injective on `E[n]`.
  --
  -- 3. Inertia kills the difference. `σ ∈ 𝒪.inertiaSubgroup k` acts trivially on `κ` (this
  --    is the *definition* of the inertia subgroup, `ValuationSubring.inertiaSubgroup` being
  --    the kernel of the action on the residue field). Reduction is Galois-equivariant, so
  --    `(σ • P - P)` reduces to `0`; being also in `E[n]`, step 2 forces `σ • P = P`.
  --
  -- REMAINING GAP: steps 1–3 need a *reduction map on points* `E(kˢᵉᵖ) → Ẽ(κ)` compatible
  -- with the group law and Galois action. Mathlib has `WeierstrassCurve.reduction` of the
  -- curve but not this map on `Affine.Point` over an extension; constructing it (and its
  -- equivariance / injectivity-on-torsion lemmas) is the one missing piece. The dictionary
  -- and `isCoprime_Φ_ΨSq` (now proved modulo `resultant_Φ_ΨSq`) are the other inputs.
  sorry
