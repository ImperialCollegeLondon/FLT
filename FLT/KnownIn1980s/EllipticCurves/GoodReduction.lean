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

/-- **Reduction of the torsion points (packaged), the geometric core of
Néron–Ogg–Shafarevich.** Under the standing hypotheses (`E` elliptic with good reduction over
`R`, `n` invertible in the residue field of `R`, `𝒪` lying above `R`), there is a *reduction
map* on the `n`-torsion of `E(kˢᵉᵖ)`: an additive homomorphism to a `Gal`-module `A` — morally
the group `Ẽ(κ)` of points of the reduced curve over the residue field `κ` of `𝒪` — which is

* **injective** on the `n`-torsion (Silverman VII.3: two `n`-torsion points with distinct
  `x`-coordinates, which are roots of `ΨSqₙ`, stay distinct mod `𝔪_𝒪` because `Φₙ` and `ΨSqₙ`
  are coprime over `κ`, `Δ` being a unit there by good reduction), and

* **equivariant** for the action of the decomposition subgroup `Gal(kˢᵉᵖ/k)` at `𝒪` on `A`
  (which acts through its quotient action on `κ`), so that the **inertia subgroup — which by
  definition acts trivially on `κ` — acts trivially on `A`**.

This bundles the three genuinely-elliptic steps (integrality `E[n] ⊆ E(𝒪)`, construction of
the reduction map to `Ẽ(κ)`, and its injectivity/equivariance); the deduction that inertia
fixes the torsion is the elementary group-theoretic `torsion_unramified_of_good_reduction`
below, proved from this by injectivity. The remaining `sorry` is exactly the missing mathlib
infrastructure flagged in the sketch: a reduction map `E(kˢᵉᵖ) → Ẽ(κ)` on `Affine.Point` over
an extension, together with its equivariance and its injectivity on the torsion (the latter
via `WeierstrassCurve.isCoprime_Φ_ΨSq`, restated over `κ`). No inertia, Hopf algebras or flat
group schemes enter here: it is a self-contained statement about reduction of points. -/
theorem WeierstrassCurve.exists_reduction_hom_injective_of_good_reduction
    (hn : IsUnit (n : IsLocalRing.ResidueField R))
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    ∃ (A : Type _) (_ : AddCommGroup A) (_ : DistribMulAction (𝒪.decompositionSubgroup k) A)
        (red : AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ) →+ A),
      -- the reduction map is injective on the `n`-torsion,
      Function.Injective red ∧
      -- it is `Gal`-equivariant (the decomposition group acts on `A` through `κ`),
      (∀ (σ : 𝒪.decompositionSubgroup k)
          (P : AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ)),
          red ⟨Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom (P : (E⁄ksep).Point),
              (Submodule.mem_torsionBy_iff ..).mpr (by
                rw [← map_zsmul, (Submodule.mem_torsionBy_iff ..).mp P.2, map_zero])⟩
            = σ • red P) ∧
      -- and inertia acts trivially on the target `A` (it acts trivially on `κ`).
      (∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ a : A, σ • a = a) :=
  sorry

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
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  -- This is step 3 of the sketch (Silverman VII.7.1), now that the geometric content of
  -- steps 1–2 is packaged as `exists_reduction_hom_injective_of_good_reduction`.
  -- Extract the reduction map: an additive hom `red` to a `Gal`-module `A`, injective on the
  -- `n`-torsion, equivariant, and with inertia acting trivially on `A`.
  obtain ⟨A, _, _, red, hinj, hequiv, htriv⟩ :=
    WeierstrassCurve.exists_reduction_hom_injective_of_good_reduction R k E n ksep 𝒪 hn h𝒪
  intro σ hσ P hP
  -- The point `P`, packaged as an element of the `n`-torsion subgroup.
  set Pt : AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ) := ⟨P, hP⟩ with hPt
  -- Reduction is Galois-equivariant, and `σ`, being in inertia, acts trivially on `A`; hence
  -- `red (σ • P) = σ • red P = red P`. Injectivity of `red` on the torsion forces `σ • P = P`.
  have hfix : red ⟨Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom (Pt : (E⁄ksep).Point),
      (Submodule.mem_torsionBy_iff ..).mpr (by
        rw [← map_zsmul, (Submodule.mem_torsionBy_iff ..).mp Pt.2, map_zero])⟩ = red Pt :=
    (hequiv σ Pt).trans (htriv σ hσ (red Pt))
  exact congrArg Subtype.val (hinj hfix)
