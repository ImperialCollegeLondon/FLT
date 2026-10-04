/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# S-minimal Galois representations

Let `F` be a totally real number field, let `ℓ` be a prime and let `S` be a finite
set of finite places of `F` not dividing `ℓ`. We define what it means for a continuous
representation of `Gal(F̄/F)` on a free rank 2 module over a local topological
`ℤ_ℓ`-algebra to be *S-minimal*: cyclotomic determinant, unramified outside `ℓ` and `S`,
flat at the places above `ℓ`, and trace 2 on inertia at the places in `S`.

For `F = ℚ` and `S = {2}` (and `ℓ ≥ 5`) this recovers the notion of a hardly ramified
representation (`GaloisRepresentation.IsHardlyRamified`); the S-minimal condition is
the natural generalisation appearing in the hypotheses of the automorphy lifting
theorem. It corresponds to the deformation-theoretic condition cut out by
`Deformation.narrowSLiftFunctor`.
-/

@[expose] public section

open IsDedekindDomain
open scoped NumberField

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u

/-- Let `F` be a number field, let `ℓ` be a prime, let `S` be a finite set of finite
places of `F` (in applications, not dividing `ℓ`), let `R` be a local topological
`ℤ_ℓ`-algebra and let `ρ : Gal(F̄/F) → GL_2(R)` be a continuous 2-dimensional
representation. We say that `ρ` is *S-minimal* if it has cyclotomic determinant, is
unramified at all finite places away from `ℓ` and `S`, is flat at all places dividing `ℓ`,
and has trace 2 on the inertia subgroup at every place in `S`. -/
structure IsSMinimal (ℓ : ℕ) [Fact ℓ.Prime]
    {F : Type u} [Field F] [NumberField F]
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    -- Rather than GL_2(R) we use the automorphisms of a finite free rank 2 `R`-module `V`.
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    -- Let `ρ` be a continuous action of the absolute Galois group of `F` on `V`.
    (ρ : GaloisRep F R V) : Prop where
  -- We say `ρ` is *S-minimal* if
  -- `det(ρ)` is the `ℓ`-adic cyclotomic character;
  det : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter (F ᵃˡᵍ) ℓ g.toRingEquiv)
  -- `ρ` is unramified at all finite places away from `ℓ` and `S`;
  isUnramified : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → (ℓ : 𝓞 F) ∉ v.asIdeal →
    ρ.IsUnramifiedAt v
  -- `ρ` is flat at all places dividing `ℓ`;
  isFlat : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal → ρ.IsFlatAt v
  -- and `ρ` has trace 2 on inertia at every place in `S`.
  trace_inertia : ∀ v ∈ S, ∀ σ ∈ localInertiaGroup v,
    LinearMap.trace R V ((ρ.toLocal v) σ) = 2

end GaloisRepresentation
