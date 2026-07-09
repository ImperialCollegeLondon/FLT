/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.inflmap

/-!
# Inflation–restriction for continuous cohomology (blueprint §"Inflation-Restriction")

`PTblueprint.tex` (§1.2) records the five-term inflation–restriction exact sequence for a
group `G`, a normal subgroup `N ≤ G` and a `G`-module `M`:

`0 → H¹(G/N, M^N) → H¹(G, M) → H¹(N, M)^{G/N} → H²(G/N, M^N) → H²(G, M)`

The inflation map `Hⁿ(G/N, M^N) ⟶ Hⁿ(G, M)` for **continuous** cohomology is provided by
`ContinuousCohomology.inflApp` in `FLT/Slop/PoitouTate/inflmap.lean`; the restriction map is
`ContinuousCohomology.map` along the subgroup inclusion. This file states the three-term part
of the sequence (injectivity of inflation in degree 1, and exactness at `H¹(G, M)`), which is
what the blueprint's red note ("do we only need the restriction map?") suggests may suffice.
For discrete group cohomology the analogous three terms are mathlib's
`groupCohomology.H1InfRes` / `groupCohomology.H1InfRes_exact`.

The continuation of the sequence (the `G/N`-action on `H¹(N, M)`, the transgression map to
`H²(G/N, M^N)`, and exactness at the two remaining positions) is deliberately not scaffolded
(kept to minimal effort per the project plan); it can be added here later if needed.

All theorem bodies are `sorry`; this file only fixes the statements.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace NumberField.PoitouTate

variable {k : Type u} [CommRing k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (N : Subgroup G) [N.Normal]

/-- The inclusion of a subgroup as a continuous monoid homomorphism. -/
def subgroupInclusionₜ : ↥N →ₜ* G where
  toMonoidHom := N.subtype
  continuous_toFun := continuous_subtype_val

/-- **Blueprint §1.2** (first nontrivial part): in degree 1, the inflation map
`H¹(G/N, π^N) → H¹(G, π)` on continuous cohomology is injective. -/
theorem inflApp_one_injective (π : TopRep k G) :
    Function.Injective ⇑(ContinuousCohomology.inflApp N 1 π).hom :=
  sorry

/-- **Blueprint §1.2** (exactness at `H¹(G, π)`): the image of inflation
`H¹(G/N, π^N) → H¹(G, π)` is exactly the kernel of restriction `H¹(G, π) → H¹(N, π)`. -/
theorem range_inflApp_one_eq_ker_res (π : TopRep k G) :
    LinearMap.range (ContinuousCohomology.inflApp N 1 π).hom.toLinearMap =
      LinearMap.ker (ContinuousCohomology.map (subgroupInclusionₜ N)
        (𝟙 (TopRep.res (subgroupInclusionₜ N : ↥N →* G) π)) 1).hom.toLinearMap :=
  sorry

end NumberField.PoitouTate
