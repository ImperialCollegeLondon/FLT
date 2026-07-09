/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Local-to-global maps for the Poitou–Tate sequence

This file scaffolds §"Restriction Galois Groups" (§1.1) of `PTblueprint.tex`: for a number
field `F`, a finite set `S` of finite places and a place `v ∈ S`, the continuous group
homomorphism
`G_v = Gal(F̄_ṽ/F_v) → G_{F,S} = Gal(F_S/F)`
along which the restriction maps `αᵢ : Hⁱ(G_S, M) → ∏_{v ∈ S} Hⁱ(G_v, M)` are defined.

## Main declarations

* `NumberField.PoitouTate.toGKS` — the restriction map `Gal(F̄/F) →ₜ* G_{F,S}`, using that
  `F_S/F` is Galois (the `Normal` instance is a `sorry` here; per `GKSDefn.lean` it is
  "developed elsewhere").
* `NumberField.PoitouTate.localToGlobal v` — the blueprint's map `G_v → G_{F,S}`, the composite
  of `Field.absoluteGaloisGroup.map (algebraMap F Fᵥ) : Γ Fᵥ →ₜ* Γ F` with `toGKS`. The
  blueprint's "choice of `ṽ` above `v`" is absorbed into `Field.absoluteGaloisGroup.map`, which
  fixes an arbitrary embedding of algebraic closures. The decomposition subgroup `D_v` of the
  blueprint is `(localToGlobal F S v).range`.
* `NumberField.PoitouTate.continuousCohomology_map_conjAux` — the blueprint's remark that the
  choices "have no effect on the `Hⁱ`": conjugating the group homomorphism (and twisting the
  coefficients accordingly) does not change the induced map on continuous cohomology.

All `sorry`s are statements to be proved; no proofs are attempted in this file.
-/

@[expose] public section

universe u v

open CategoryTheory IsDedekindDomain ContRepresentation

namespace NumberField.PoitouTate

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (RingOfIntegers F)))

local notation "Γ" K => Field.absoluteGaloisGroup K

/-- The maximal extension `F_S/F` unramified outside `S` is Galois over `F`
(blueprint §1.1; stated in `GKSDefn.lean` as "developed elsewhere"). -/
instance normal_maximalUnramifiedOutside : Normal F ↥(maximalUnramifiedOutside F S) :=
  sorry

/-- The canonical continuous surjection `Gal(F̄/F) →ₜ* G_{F,S}`, restriction of automorphisms
of the algebraic closure to the maximal extension unramified outside `S`. -/
noncomputable def toGKS : (Γ F) →ₜ* unramifiedOutsideGaloisGroup F S where
  __ := AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F)
    (maximalUnramifiedOutside F S)
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _

/-- `G_{F,S}` is a quotient of the absolute Galois group: the restriction map is surjective. -/
theorem toGKS_surjective : Function.Surjective ⇑(toGKS F S) :=
  sorry

/-- Blueprint §1.1: the local-to-global map `G_v = Gal(F̄_ṽ/F_v) → G_{F,S}` at a finite place
`v`, the composite of `Γ Fᵥ →ₜ* Γ F` (which fixes an arbitrary embedding of algebraic closures,
i.e. a choice of `ṽ` above `v`) with the restriction `Γ F →ₜ* G_{F,S}`.

The decomposition subgroup `D_v ≤ G_{F,S}` of the blueprint is the range of this map. -/
noncomputable def localToGlobal (v : HeightOneSpectrum (RingOfIntegers F)) :
    (Γ (v.adicCompletion F)) →ₜ* unramifiedOutsideGaloisGroup F S :=
  (toGKS F S).comp (Field.absoluteGaloisGroup.map (algebraMap F (v.adicCompletion F)))

section ConjInvariance

variable {k : Type*} [Ring k] [TopologicalSpace k]
variable {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Conjugation by `g` as a continuous monoid homomorphism. -/
def conjCMHom (g : G) : G →ₜ* G where
  __ := (MulAut.conj g).toMonoidHom
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const

/-- The coefficient intertwiner for `continuousCohomology_map_conjAux`: `ρ g⁻¹` intertwines the
restriction of `X` along `conj g ∘ φ` with its restriction along `φ`. -/
def conjResHom (X : TopRep k G) (φ : H →ₜ* G) (g : G) :
    TopRep.res (((conjCMHom g).comp φ : H →ₜ* G) : H →* G) X ⟶
      TopRep.res (φ : H →* G) X :=
  TopRep.ofHom
    { toContinuousLinearMap := X.ρ g⁻¹
      isIntertwining' := fun h => by
        ext x
        change (X.ρ g⁻¹ * X.ρ (g * φ h * g⁻¹)) x = (X.ρ (φ h) * X.ρ g⁻¹) x
        rw [← map_mul, ← map_mul]
        congr 2
        group }

/-- Blueprint §1.1, "the choices have no effect on the `Hⁱ`": the map induced on continuous
cohomology by `conj g ∘ φ` (with coefficients twisted by `ρ g⁻¹`) agrees with the map induced
by `φ`. In particular the maps `Hⁱ(G_{F,S}, M) → Hⁱ(G_v, M)` do not depend on the choice of
`ṽ` above `v` (any two choices differ by conjugation). -/
theorem continuousCohomology_map_conjAux (X : TopRep k G) (φ : H →ₜ* G) (g : G) (n : ℕ) :
    ContinuousCohomology.map ((conjCMHom g).comp φ) (conjResHom X φ g) n =
      ContinuousCohomology.map φ (𝟙 (TopRep.res (φ : H →* G) X)) n :=
  sorry

end ConjInvariance

end NumberField.PoitouTate
