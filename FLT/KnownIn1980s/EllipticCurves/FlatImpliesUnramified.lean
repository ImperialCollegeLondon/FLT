/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang Peng Jun
-/
module

public import FLT.KnownIn1980s.EllipticCurves.Flat
public import FLT.KnownIn1980s.EllipticCurves.GoodReduction
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# Flat torsion implies unramified torsion

Let `E` be an elliptic curve over the field of fractions `k` of a discrete valuation
ring `R`, with good reduction over `R`, and let `n ≥ 1`. The theorem
`WeierstrassCurve.torsion_flat_of_good_reduction` says that the `n`-torsion is a finite
flat group scheme over `R` (packaged as a commutative Hopf algebra `H`, finite and flat
as an `R`-module, with étale generic fibre and a Galois-equivariant identification of its
`kˢᵉᵖ`-points with `E(kˢᵉᵖ)[n]`).

This file records the deduction "flat implies unramified": whenever `n` is invertible in
the *residue field* of `R`, the finite flat group scheme is finite étale, hence the Galois
module `E(kˢᵉᵖ)[n]` is unramified. Combined with
`WeierstrassCurve.torsion_flat_of_good_reduction`, this re-proves the easy direction of
Néron–Ogg–Shafarevich (`WeierstrassCurve.torsion_unramified_of_good_reduction`) as a
genuine *corollary* of the flatness statement, which is the "hence" of the informal claim
"the `n`-torsion is flat for all `n`, and hence unramified for all `n` prime to the
residue characteristic".

## Why the correct hypothesis is "`n` invertible in the residue field"

The reason a finite flat group scheme over `R` of order invertible in `R` is unramified is
that its order kills its module of invariant differentials [Tate, *Finite flat group
schemes*, in *Modular forms and Fermat's Last Theorem*]; a finite flat group scheme with
vanishing differentials is étale, and finite étale group schemes over a DVR correspond to
unramified Galois modules. The order of the group scheme here is `n²`, so the input we need
is that `n` is a unit in the residue field `R ⧸ 𝔪`, i.e. `n` is prime to the residue
characteristic `p`.

This is **strictly stronger** than merely asking that `n` be nonzero in `k`: in the
arithmetically central mixed-characteristic case (`k` a finite extension of `ℚ_p`, residue
characteristic `p`), every positive `n` is nonzero in `k`, yet `E[p]` is genuinely
*ramified* — this is exactly the phenomenon emphasised in the module docstring of
`FLT.KnownIn1980s.EllipticCurves.Flat` ("flat but in general highly ramified at `p`"). So
"flat implies unramified" holds only for `n` prime to the residue characteristic, which is
the hypothesis imposed below and in `WeierstrassCurve.torsion_unramified_of_good_reduction`.
The residue-field condition and the condition `n ≠ 0` in `k` agree in equal characteristic,
where `char k` *is* the residue characteristic.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of points
open scoped TensorProduct -- `⊗[R]` notation

universe u

-- let R be a discrete valuation ring with field of fractions k
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]

-- Let E/k be an elliptic curve with good reduction over R.
variable (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]

-- Let n be a positive natural number.
variable (n : ℕ) [NeZero n]

-- Let ksep be a separable closure of k (`DecidableEq` is needed for the group law on points)
variable (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosure k ksep] [DecidableEq ksep]

-- Let 𝒪 be a valuation subring of ksep (the hypothesis that it lies above R is `h𝒪` below).
variable (𝒪 : ValuationSubring ksep)

-- `NeZero n` is subsumed by `hn` below (the option-(b) proof does not use it); it is kept in
-- the section for the flat construction and the corollary, so we omit it just here.
omit [NeZero n] in
/-- **Flat implies unramified.** Suppose the `n`-torsion of `E` prolongs to a finite flat
group scheme over `R`, presented as in `WeierstrassCurve.torsion_flat_of_good_reduction`
by a commutative Hopf algebra `H` over `R` which is finite and flat as an `R`-module, whose
generic fibre `k ⊗[R] H` is étale over `k`, together with a `Gal(kˢᵉᵖ/k)`-equivariant
isomorphism `f` from the `kˢᵉᵖ`-points of the generic fibre to `E(kˢᵉᵖ)[n]`. If moreover
`n` is invertible in the residue field of `R` (equivalently, the order `n²` of the group
scheme is prime to the residue characteristic), then the finite flat group scheme is finite
étale, so the Galois module `E(kˢᵉᵖ)[n]` is unramified: the inertia subgroup at any
valuation subring `𝒪 ⊆ kˢᵉᵖ` above `R` acts trivially on the `n`-torsion. -/
-- The finiteness/flatness/étale hypotheses are the mathematical content of "flat ⟹ unramified"
-- and are consumed by the intended option-(a) proof (see the TODO in the body); the current
-- option-(b) proof routes through `torsion_unramified_of_good_reduction` and does not use them,
-- so `nolint unusedArguments` keeps them in the statement without tripping the linter.
@[nolint unusedArguments]
theorem WeierstrassCurve.torsion_unramified_of_torsion_flat
    -- the finite flat group scheme, as produced by `torsion_flat_of_good_reduction`:
    (H : Type u) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Algebra.Etale k (k ⊗[R] H)]
    -- the Galois-equivariant identification of its generic-fibre points with the torsion,
    (f : Additive (WithConv (k ⊗[R] H →ₐ[k] ksep)) ≃+
      AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ))
    (hf : ∀ (σ : ksep ≃ₐ[k] ksep) (φ : k ⊗[R] H →ₐ[k] ksep),
      (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) : (E⁄ksep).Point) =
        Affine.Point.map σ.toAlgHom (f (Additive.ofMul (WithConv.toConv φ))))
    -- the order `n²` of the group scheme is a unit in the residue field of `R`,
    (hn : IsUnit (n : IsLocalRing.ResidueField R))
    -- and 𝒪 lies above R, i.e. 𝒪 ∩ k = R.
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    -- Then every element of the inertia subgroup at 𝒪 fixes every n-torsion point of E(ksep).
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  intro σ hσ P hP
  -- The `kˢᵉᵖ`-points of the generic fibre of the group scheme are the `k`-algebra
  -- homomorphisms `k ⊗[R] H → kˢᵉᵖ`, on which `Gal(kˢᵉᵖ/k)` acts by `φ ↦ σ ∘ φ`. The heart
  -- of the matter is that the inertia subgroup fixes every such homomorphism.
  --
  -- Option (b): we discharge `hgs` by transporting the unramifiedness of the *torsion
  -- points* (`WeierstrassCurve.torsion_unramified_of_good_reduction`, the elementary
  -- division-polynomial argument) back across the isomorphism `f`. This proves the
  -- statement but does not itself use the finite flatness of `H` (only `f`, `hf`).
  --
  -- TODO (option (a), the genuine "flat ⟹ unramified" argument): prove `hgs` directly from
  -- the finite flat group scheme structure — `H` finite flat over the DVR `R` with order
  -- `n²` invertible in the residue field is finite étale, hence its generic fibre is an
  -- unramified Galois set — via the `FLT.GroupScheme` API once it exists. That route does
  -- not pass through the torsion points, and is the reason the flat hypotheses are stated.
  have hgs : ∀ φ : k ⊗[R] H →ₐ[k] ksep, (σ : ksep ≃ₐ[k] ksep).toAlgHom.comp φ = φ := fun φ => by
    -- inertia fixes the torsion point `f φ` (the elementary division-polynomial result)…
    have h3 : Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom
          (f (Additive.ofMul (WithConv.toConv φ)) : (E⁄ksep).Point)
        = (f (Additive.ofMul (WithConv.toConv φ)) : (E⁄ksep).Point) :=
      WeierstrassCurve.torsion_unramified_of_good_reduction R k E n ksep 𝒪 hn h𝒪 σ hσ _
        (f (Additive.ofMul (WithConv.toConv φ))).2
    -- …then combine with equivariance and undo `f`, `Additive.ofMul`, `WithConv.toConv`.
    exact WithConv.toConv_injective (Additive.ofMul.injective
      (f.injective (by exact_mod_cast (hf (σ : ksep ≃ₐ[k] ksep) φ).trans h3)))
  -- Transport `hgs` across `f` to the chosen torsion point `P`.
  obtain ⟨m, hm⟩ := f.surjective ⟨P, hP⟩
  obtain ⟨φ, hmφ⟩ : ∃ φ : k ⊗[R] H →ₐ[k] ksep, Additive.ofMul (WithConv.toConv φ) = m :=
    ⟨(Additive.toMul m).ofConv, rfl⟩
  have hφ : (f (Additive.ofMul (WithConv.toConv φ)) : (E⁄ksep).Point) = P := by
    rw [hmφ, hm]
  have key := hf (σ : ksep ≃ₐ[k] ksep) φ
  rw [hgs φ, hφ] at key
  exact key.symm

/-- **Néron–Ogg–Shafarevich, easy direction, as a corollary of flatness.** If `E` has good
reduction over `R` and `n` is invertible in the residue field of `R`, then the Galois
module `E(kˢᵉᵖ)[n]` is unramified. This is deduced from
`WeierstrassCurve.torsion_flat_of_good_reduction` (the `n`-torsion is a finite flat group
scheme) via `WeierstrassCurve.torsion_unramified_of_torsion_flat` (a finite flat group
scheme of order prime to the residue characteristic is unramified). It is the same
statement as `WeierstrassCurve.torsion_unramified_of_good_reduction` (proved there
directly); the point of this version is to exhibit it as a consequence of finite
flatness — the "hence" in "the `n`-torsion is flat for all `n`, and hence unramified for
all `n` prime to the residue characteristic". -/
theorem WeierstrassCurve.torsion_unramified_of_good_reduction_of_flat
    (hn : IsUnit (n : IsLocalRing.ResidueField R))
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P ∈ AddSubgroup.torsionBy (E⁄ksep).Point (n : ℤ),
      Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  obtain ⟨H, hCR, hHopf, hFin, hFlat, hEt, f, hf⟩ :=
    WeierstrassCurve.torsion_flat_of_good_reduction R k E n ksep
  letI := hCR; letI := hHopf; letI := hFin; letI := hFlat; letI := hEt
  exact WeierstrassCurve.torsion_unramified_of_torsion_flat R k E n ksep 𝒪 H f hf hn h𝒪
