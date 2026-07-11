/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.LocalGlobalMaps
public import FLT.Slop.PoitouTate.DualModule
public import FLT.Slop.PoitouTate.inflmap
public import FLT.Slop.PoitouTate.cupprod
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Local Tate duality (blueprint §"Local–Tate duality")

This file develops the local statements of `PTblueprint.tex` needed for Poitou–Tate, for a
finite place `v` of a number field `F`. Throughout (in both the docstrings and the local
notation of this file):

* `Fᵥ = v.adicCompletion F` is the local field, `F̄ᵥ` a fixed algebraic closure;
* `G_v = Gal(F̄ᵥ/Fᵥ)` is the local absolute Galois group, `I_v = localInertiaGroup v` its
  inertia subgroup, and `g_v = G_v/I_v ≅ Ẑ` the unramified quotient;
* `N : TopRep 𝔽 G_v` is a finite discrete module over a finite field `𝔽` of
  characteristic `p`, and `N* = Hom_ℤ(N, F̄ᵥ^×)` its local Tate dual.

## Main declarations

* `NumberField.PoitouTate.algClosureUnitsRep` — `F̄ᵥ^×` as a discrete `TopRep ℤ G_v`, the
  coefficient module of local Tate duality.
* `NumberField.PoitouTate.localDualRep N` — the local dual `N* = Hom_ℤ(N, F̄ᵥ^×)`.
* `NumberField.PoitouTate.finite_continuousCohomology_local` — **Milne, Theorem 2.1**:
  `Hⁱ(G_v, N)` is finite for all `i`.
* `NumberField.PoitouTate.isZero_continuousCohomology_local` — **Milne, Corollary 2.3(2)**:
  `Hⁱ(G_v, N) = 0` for `i ≥ 3`.
* `NumberField.PoitouTate.localInvariantMap` — **Milne, Example 1.6**: the invariant map
  `inv_{G_v} : H²(G_v, F̄ᵥ^×) → ℚ/ℤ` of local class field theory, constructed as the
  composite

  `H²(G_v, F̄ᵥ^×) ← H²(g_v, (Fᵥ^un)^×) → H²(g_v, ℤ) → ℚ/ℤ`

  of the inverse of the inflation isomorphism (`inflationAddEquiv`), the coefficient map
  induced by the valuation `ord : (Fᵥ^un)^× → ℤ` (`unramifiedOrdHom`), and the invariant map
  of `Ẑ ≅ g_v` (`invariantMapZHat`).
* `NumberField.PoitouTate.localTatePairing` — **Milne, Corollary 2.3**: the cup-product
  pairing `Hⁱ(G_v, N*) × Hʲ(G_v, N) → H²(G_v, F̄ᵥ^×) → ℚ/ℤ` for `i + j = 2`, constructed
  from `ContRepresentation.cup` of `cupprod.lean` applied over `ℤ` to the evaluation
  intertwiner `localEvalIntertwiner : N* →ⁱL Hom(N, F̄ᵥ^×)`, composed with
  `localInvariantMap`. (The statement layer works `𝔽`-linearly while the cup product lives
  over `ℤ`, so the arguments are transported along the scalar-restriction identification
  `continuousCohomologyIntResAddEquiv`.)
* `NumberField.PoitouTate.localTatePairing_bijective_left` / `_right` — **Milne,
  Corollary 2.3(1)**: the pairing is perfect.
* `NumberField.PoitouTate.unramifiedClasses` — the unramified classes
  `H¹(g_v, Y^{I_v}) ⊆ H¹(G_v, Y)`, the image of the inflation map of `inflmap.lean`.
* `NumberField.PoitouTate.mem_unramifiedClasses_localDualRep_iff` — **Milne, Theorem 2.6**:
  for `N` unramified with torsion prime to the residue characteristic, the unramified classes
  of `N*` and of `N` are the exact annihilators of each other under the pairing. (Milne states
  this with `N^d = Hom(N, R^{un,×})`; for finite `N` of order prime to `char k(v)` this equals
  `(N*)^{I_v}`, whose `H¹(g_v, ·)` gives the unramified classes used here.)

## Remaining `sorry`s

All definitions in this file are fully constructed; the `sorry`s are exactly the following
propositions.

Deep arithmetic/local-CFT inputs:

* `normal_localInertiaGroup` — the inertia subgroup is normal in `G_v`;
* `finite_continuousCohomology_local`, `isZero_continuousCohomology_local` — finiteness and
  vanishing of local cohomology (Milne 2.1, 2.3(2));
* `bijective_inflApp_two_algClosureUnitsRep` — inflation from the unramified quotient is an
  isomorphism on `H²` of `F̄ᵥ^×` (Milne 1.6(2));
* `exists_unramifiedOrd` — the valuation `(Fᵥ^un)^× → ℤ` exists (surjective, normalized,
  `g_v`-equivariant);
* `exists_invariantMapZHat` — `H²(g_v, ℤ) ≅ ℚ/ℤ` (Milne 1.6(1): inverse Bockstein followed
  by evaluation at a Frobenius generator);
* `localTatePairing_bijective_left` / `_right`, `localInvariantMap_bijective`,
  `mem_unramifiedClasses_localDualRep_iff` — the duality theorems themselves.

Comparison glue (routine, deferred):

* `nonempty_continuousCohomology_intRes_addEquiv` — restriction of scalars along `ℤ → 𝔽`
  does not change continuous cohomology (the cochain complexes agree on the nose).
-/

@[expose] public section

universe u

open IsDedekindDomain

namespace NumberField.PoitouTate

variable (𝔽 : Type*) [Field 𝔽] [Finite 𝔽] [TopologicalSpace 𝔽] [DiscreteTopology 𝔽]
variable (F : Type u) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (RingOfIntegers F))

/- Local abbreviations for the objects attached to the place `v` (source-level only; the
pretty-printed statements below unfold them). These cannot be used inside `variable`
commands — the section-variable dependency tracking does not see through them. -/
local notation3 "Fᵥ" => HeightOneSpectrum.adicCompletion F v
local notation3 "F̄ᵥ" => AlgebraicClosure (HeightOneSpectrum.adicCompletion F v)
local notation3 "G_v" => Field.absoluteGaloisGroup (HeightOneSpectrum.adicCompletion F v)

/-! ### The coefficient module `F̄ᵥ^×` and the local dual `N*` -/

/-- The units `F̄ᵥ^×` of an algebraic closure of the local field `Fᵥ`, as a discrete
topological `ℤ`-representation of the local absolute Galois group `G_v` (the coefficients of
local Tate duality). -/
noncomputable def algClosureUnitsRep : TopRep ℤ G_v :=
  unitsAddRep G_v F̄ᵥ

/-- `F̄ᵥ^×` carries the discrete topology by construction. -/
instance discreteTopology_algClosureUnitsRep : DiscreteTopology ↥(algClosureUnitsRep F v) :=
  ⟨rfl⟩

variable (N : TopRep 𝔽 (Field.absoluteGaloisGroup (v.adicCompletion F)))

/-- The local dual `N* = Hom_ℤ(N, F̄ᵥ^×)` of a finite discrete `G_v`-module `N`, with
`G_v`-action `(g • f) (n) = g (f (g⁻¹ n))` (blueprint §"Local–Tate duality"). -/
noncomputable def localDualRep : TopRep 𝔽 G_v :=
  homUnitsRep 𝔽 N F̄ᵥ

/-- The local dual of a finite module is finite (values are roots of unity of order dividing
`#N`). -/
instance finite_localDualRep [Finite N] : Finite ↥(localDualRep 𝔽 F v N) :=
  inferInstanceAs (Finite (↥N →+ Additive (F̄ᵥ)ˣ))

/-- The local dual carries the discrete topology by construction. -/
instance discreteTopology_localDualRep : DiscreteTopology ↥(localDualRep 𝔽 F v N) :=
  ⟨rfl⟩

/-! ### Finiteness and vanishing of local cohomology -/

/-- **Milne, Theorem 2.1**: for a finite discrete `G_v`-module `N`, the continuous cohomology
`Hⁱ(G_v, N)` is finite for all `i`. -/
theorem finite_continuousCohomology_local [Finite N] [DiscreteTopology N] (i : ℕ) :
    Finite ↥(continuousCohomology i N) :=
  sorry

/-- **Milne, Corollary 2.3(2)**: for a finite discrete `G_v`-module `N`, the continuous
cohomology `Hⁱ(G_v, N)` vanishes for `i ≥ 3`. -/
theorem isZero_continuousCohomology_local [Finite N] [DiscreteTopology N] {i : ℕ}
    (hi : 3 ≤ i) : CategoryTheory.Limits.IsZero (continuousCohomology i N) :=
  sorry

/-! ### The local invariant map

Following Milne, Example 1.6, the invariant map `inv_{G_v} : H²(G_v, F̄ᵥ^×) → ℚ/ℤ` is
assembled in three steps:

1. inflation from the unramified quotient `g_v = G_v/I_v` is an isomorphism
   `H²(g_v, (Fᵥ^un)^×) ≅ H²(G_v, F̄ᵥ^×)`, where `(Fᵥ^un)^× = (F̄ᵥ^×)^{I_v}` is realised as
   the inertia invariants of `F̄ᵥ^×` (`unramifiedUnitsRep`, via `relInvariantsFunctor` of
   `inflmap.lean`);
2. the valuation `ord : (Fᵥ^un)^× → ℤ` induces a coefficient map
   `H²(g_v, (Fᵥ^un)^×) → H²(g_v, ℤ)`;
3. the invariant map of `Ẑ ≅ g_v` identifies `H²(g_v, ℤ) ≅ ℚ/ℤ` (inverse Bockstein, then
   evaluation at a Frobenius topological generator).
-/

/-- The local inertia subgroup is normal in the local absolute Galois group (it is the kernel
of the action on the residue field of the integral closure). Needed to form the unramified
quotient `G_v/I_v`. -/
instance normal_localInertiaGroup : (localInertiaGroup v).Normal :=
  sorry

/-- The unramified quotient `g_v := G_v/I_v = Gal(k(v)ˢ/k(v)) ≅ Ẑ` of the local Galois group
by the inertia subgroup; a topological group under the quotient topology. -/
abbrev localUnramifiedQuotient : Type u :=
  G_v ⧸ localInertiaGroup v

/-- The unramified units `(Fᵥ^un)^× = (F̄ᵥ^×)^{I_v}`, as a representation of the unramified
quotient `g_v` — the inertia invariants of `F̄ᵥ^×` with the descended action
(`TopRep.relInvariantsFunctor` of `inflmap.lean`). -/
noncomputable def unramifiedUnitsRep : TopRep ℤ (localUnramifiedQuotient F v) :=
  (TopRep.relInvariantsFunctor (localInertiaGroup v)).obj (algClosureUnitsRep F v)

/-- **Milne, Example 1.6(2)**: inflation `H²(g_v, (Fᵥ^un)^×) → H²(G_v, F̄ᵥ^×)` from the
unramified quotient is bijective (`ContinuousCohomology.inflApp` of `inflmap.lean`). -/
theorem bijective_inflApp_two_algClosureUnitsRep :
    Function.Bijective
      (ContinuousCohomology.inflApp (localInertiaGroup v) 2 (algClosureUnitsRep F v)).hom :=
  sorry

/-- The inflation isomorphism `H²(g_v, (Fᵥ^un)^×) ≃+ H²(G_v, F̄ᵥ^×)` (Milne, Example
1.6(2)), bundled additively from `inflApp` and its bijectivity. -/
noncomputable def inflationAddEquiv :
    ↥(continuousCohomology 2 (unramifiedUnitsRep F v)) ≃+
      ↥(continuousCohomology 2 (algClosureUnitsRep F v)) :=
  AddEquiv.ofBijective _ (bijective_inflApp_two_algClosureUnitsRep F v)

/-- Existence of the valuation homomorphism `ord : (Fᵥ^un)^× →+ ℤ`, which is:

* surjective;
* normalized, so that a uniformizer of `Fᵥ` (an element of valuation `-1` in the
  multiplicative convention of `Valued`) is sent to `1`;
* `g_v`-equivariant, for the trivial action on `ℤ`.

(Milne, Theorem 1.4 context.) The chosen `unramifiedOrd` below is unique with these
properties. In the second clause the uniformizer is pushed into `F̄ᵥ^×` along
`Fᵥ ↪ F̄ᵥ`; the hypothesis `hmem` records that its image is inertia-invariant, i.e. lies in
the carrier `(F̄ᵥ^×)^{I_v}` of `unramifiedUnitsRep`. -/
theorem exists_unramifiedOrd :
    ∃ ord : ↥(unramifiedUnitsRep F v) →+ ℤ,
      Function.Surjective ⇑ord ∧
        (∀ (π : (Fᵥ)ˣ)
          (_ : Valued.v (π : Fᵥ)
            = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
                WithZero (Multiplicative ℤ)))
          (hmem : Additive.ofMul (Units.map (algebraMap Fᵥ F̄ᵥ).toMonoidHom π)
            ∈ (algClosureUnitsRep F v).ρ.relInvariants (localInertiaGroup v)),
          ord ⟨_, hmem⟩ = 1) ∧
        ∀ (σ : localUnramifiedQuotient F v) (x : ↥(unramifiedUnitsRep F v)),
          ord ((unramifiedUnitsRep F v).ρ σ x) = ord x :=
  sorry

/-- The valuation `ord : (Fᵥ^un)^× →+ ℤ`, chosen from `exists_unramifiedOrd`. -/
noncomputable def unramifiedOrd : ↥(unramifiedUnitsRep F v) →+ ℤ :=
  (exists_unramifiedOrd F v).choose

universe w in
/-- The trivial topological `ℤ`-representation of a topological group on discrete `ℤ`
(universe-lifted so that it lives in the same category as the arithmetic
representations). -/
noncomputable def trivialIntRep (H : Type*) [Group H] :
    TopRep.{w} ℤ H :=
  TopRep.of (X := ULift.{w} ℤ) (ContRepresentation.ofMonoidHom 1)

/-- The valuation `ord` as a morphism of `g_v`-representations `(Fᵥ^un)^× ⟶ ℤ` (trivial
action on `ℤ`), using the `g_v`-equivariance clause of `exists_unramifiedOrd`. -/
noncomputable def unramifiedOrdHom :
    unramifiedUnitsRep F v ⟶ trivialIntRep (localUnramifiedQuotient F v) :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        { toLinearMap :=
            ((AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom.comp
              (unramifiedOrd F v)).toIntLinearMap
          cont := continuous_of_discreteTopology }
      isIntertwining' := fun g => ContinuousLinearMap.ext fun x =>
        congrArg (⇑(AddEquiv.ulift (α := ℤ)).symm)
          ((exists_unramifiedOrd F v).choose_spec.2.2 g x) }

/-- **Milne, Example 1.6(1)** (`H²(Ẑ, ℤ) ≅ ℚ/ℤ`): the invariant map of the unramified
quotient `g_v ≅ Ẑ` — the inverse of the Bockstein isomorphism `H¹(g_v, ℚ/ℤ) → H²(g_v, ℤ)`
(from `0 → ℤ → ℚ → ℚ/ℤ → 0`, trivial actions) followed by evaluation at a Frobenius
topological generator of `g_v`. Its existence (with bijectivity) is stated here and the map
is chosen from it; the explicit Bockstein/evaluation construction is deferred. -/
theorem exists_invariantMapZHat :
    ∃ φ : ↥(continuousCohomology 2 (trivialIntRep (localUnramifiedQuotient F v))) →+
        AddCircle (1 : ℚ), Function.Bijective ⇑φ :=
  sorry

/-- The invariant map `H²(g_v, ℤ) → ℚ/ℤ` of `Ẑ ≅ g_v`, chosen from
`exists_invariantMapZHat`. -/
noncomputable def invariantMapZHat :
    ↥(continuousCohomology 2 (trivialIntRep (localUnramifiedQuotient F v))) →+
      AddCircle (1 : ℚ) :=
  (exists_invariantMapZHat F v).choose

/-- **Milne, Example 1.6**: the invariant map `inv_{G_v} : H²(G_v, F̄ᵥ^×) → ℚ/ℤ` of local
class field theory: the composite of the inverse of the inflation isomorphism from the
unramified quotient (`inflationAddEquiv`), the coefficient map on `H²(g_v, ·)` induced by
the valuation `ord : (Fᵥ^un)^× → ℤ` (`unramifiedOrdHom`), and the invariant map
`H²(g_v, ℤ) ≅ ℚ/ℤ` of `Ẑ` (`invariantMapZHat`). -/
noncomputable def localInvariantMap :
    ↥(continuousCohomology 2 (algClosureUnitsRep F v)) →+ AddCircle (1 : ℚ) :=
  ((invariantMapZHat F v).comp
      (AddMonoidHomClass.toAddMonoidHom
        ((ContinuousCohomology.Functor ℤ (localUnramifiedQuotient F v) 2).map
          (unramifiedOrdHom F v)).hom)).comp
    (inflationAddEquiv F v).symm.toAddMonoidHom

/-- **Milne, Example 1.6**: the invariant map is an isomorphism `H²(G_v, F̄ᵥ^×) ≅ ℚ/ℤ`. -/
theorem localInvariantMap_bijective : Function.Bijective (localInvariantMap F v) :=
  sorry

/-! ### Restriction of scalars to `ℤ`

The cup product `ContRepresentation.cup` of `cupprod.lean` lives over a single coefficient
ring, and the target `F̄ᵥ^×` of the evaluation pairing is only a `ℤ`-module — so the Tate
pairing below is constructed at the `ℤ`-linear level and transported to the `𝔽`-linear
cohomology of the statement layer along the (additive) restriction-of-scalars
identification of this section. -/

section IntRes

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Restriction of scalars to `ℤ` of a topological `𝔽`-representation: the same carrier with
the same topology and the same `G`-action, viewed `ℤ`-linearly. -/
noncomputable def intRes (X : TopRep 𝔽 G) : TopRep ℤ G :=
  TopRep.of (X := ↥X)
    (ContRepresentation.ofMonoidHom
      { toFun g :=
          { toLinearMap := (X.ρ g).toLinearMap.toAddMonoidHom.toIntLinearMap
            cont := (X.ρ g).cont }
        map_one' := by ext x; exact congr($(map_one X.ρ) x)
        map_mul' g h := by ext x; exact congr($(map_mul X.ρ g h) x) })

/-- The `ℤ`-scalar restriction has the same carrier and topology, so discreteness passes
through. -/
instance discreteTopology_intRes (X : TopRep 𝔽 G) [DiscreteTopology X] :
    DiscreteTopology ↥(intRes 𝔽 X) :=
  inferInstanceAs (DiscreteTopology ↥X)

/-- Restriction of scalars along `ℤ → 𝔽` leaves the homogeneous cochain complex unchanged
(same carriers, same differentials), so it identifies the continuous cohomology of `X` with
that of `intRes 𝔽 X` additively. The identification is stated as an existence lemma and the
map below is chosen from it, in lieu of the (routine but lengthy) cochain-level comparison. -/
theorem nonempty_continuousCohomology_intRes_addEquiv [IsTopologicalGroup G]
    (X : TopRep 𝔽 G) (j : ℕ) :
    Nonempty (↥(continuousCohomology j X) ≃+ ↥(continuousCohomology j (intRes 𝔽 X))) :=
  sorry

/-- The chosen additive identification `Hʲ(G, X) ≃+ Hʲ(G, intRes 𝔽 X)` of continuous
cohomology with the cohomology of the `ℤ`-scalar restriction
(`nonempty_continuousCohomology_intRes_addEquiv`). -/
noncomputable def continuousCohomologyIntResAddEquiv [IsTopologicalGroup G]
    (X : TopRep 𝔽 G) (j : ℕ) :
    ↥(continuousCohomology j X) ≃+ ↥(continuousCohomology j (intRes 𝔽 X)) :=
  (nonempty_continuousCohomology_intRes_addEquiv 𝔽 X j).some

end IntRes

/-! ### The local Tate pairing -/

open ContRepresentation ContinuousLinearMap.CompactOpen in
/-- The evaluation pairing `N* × N → F̄ᵥ^×`, `(x, n) ↦ x n`, as a `ℤ`-linear intertwiner
`N* →ⁱL Hom(N, F̄ᵥ^×)` of the local Galois action: `G_v`-equivariance is
`(g • x)(n) = g • x(g⁻¹ • n)`, which is the defining formula of the action on
`N* = Hom_ℤ(N, F̄ᵥ^×)` (`homUnitsRep`). This is the input to the cup product of
`cupprod.lean` producing the local Tate pairing. -/
noncomputable def localEvalIntertwiner [DiscreteTopology N] :
    (intRes 𝔽 (localDualRep 𝔽 F v N)).ρ →ⁱL
      ContRepresentation.linHom (intRes 𝔽 N).ρ (algClosureUnitsRep F v).ρ where
  toContinuousLinearMap :=
    { toFun := fun x =>
        { toLinearMap := AddMonoidHom.toIntLinearMap
            (show ↥N →+ Additive (F̄ᵥ)ˣ from x)
          cont := continuous_of_discreteTopology }
      map_add' := fun _ _ => ContinuousLinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => ContinuousLinearMap.ext fun _ => rfl
      cont := continuous_of_discreteTopology }
  isIntertwining' _ := ContinuousLinearMap.ext fun _ => ContinuousLinearMap.ext fun _ => rfl

open ContRepresentation ContinuousLinearMap.CompactOpen in
/-- The bilinear cup product `Hⁱ(G_v, N*) ⟶ (Hʲ(G_v, N) →L H²(G_v, F̄ᵥ^×))` on the
`ℤ`-scalar restrictions: `ContRepresentation.cup` of `cupprod.lean`, applied over `ℤ` to the
evaluation intertwiner `localEvalIntertwiner : N* →ⁱL linHom N F̄ᵥ^×`. -/
noncomputable def localTateCup [DiscreteTopology N] (i j : ℕ) (hij : i + j = 2) :
    continuousCohomology i (intRes 𝔽 (localDualRep 𝔽 F v N)) ⟶
      TopModuleCat.linHom (continuousCohomology j (intRes 𝔽 N))
        (continuousCohomology 2 (algClosureUnitsRep F v)) :=
  ContRepresentation.cup
    (intRes 𝔽 (localDualRep 𝔽 F v N)).ρ (intRes 𝔽 N).ρ (algClosureUnitsRep F v).ρ
    (localEvalIntertwiner 𝔽 F v N) i j 2 hij.symm

open ContRepresentation ContinuousLinearMap.CompactOpen in
/-- **Milne, Corollary 2.3** (the pairing): for `i + j = 2`, the cup-product pairing
`Hⁱ(G_v, N*) × Hʲ(G_v, N) → H²(G_v, F̄ᵥ^×) → ℚ/ℤ`.

The construction is the cup product `localTateCup` over `ℤ` composed with
`localInvariantMap`; the `𝔽`-linear cohomology groups of the statement layer are carried to
their `ℤ`-linear restrictions along `continuousCohomologyIntResAddEquiv`. Bi-additivity is
inherited from the bilinearity of the cup product, so no well-definedness `sorry` is needed
here; the remaining gaps are the inputs to `localInvariantMap` and the
restriction-of-scalars identification. -/
noncomputable def localTatePairing [DiscreteTopology N] (i j : ℕ) (hij : i + j = 2) :
    ↥(continuousCohomology i (localDualRep 𝔽 F v N)) →+
      ↥(continuousCohomology j N) →+ AddCircle (1 : ℚ) :=
  AddMonoidHom.mk'
    (fun x =>
      AddMonoidHom.mk'
        (fun y => localInvariantMap F v
          (((localTateCup 𝔽 F v N i j hij).hom
            (continuousCohomologyIntResAddEquiv 𝔽 (localDualRep 𝔽 F v N) i x))
            (continuousCohomologyIntResAddEquiv 𝔽 N j y)))
        (fun y y' => by rw [map_add, map_add, map_add]))
    (fun x x' => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [map_add, map_add, add_apply, map_add])

/-- **Milne, Corollary 2.3(1)**, left perfectness: cup product followed by the invariant map
identifies `Hⁱ(G_v, N*)` with the `ℚ/ℤ`-dual of `H^{2-i}(G_v, N)`. -/
theorem localTatePairing_bijective_left [Finite N] [DiscreteTopology N] (i j : ℕ)
    (hij : i + j = 2) : Function.Bijective (localTatePairing 𝔽 F v N i j hij) :=
  sorry

/-- **Milne, Corollary 2.3(1)**, right perfectness: the flipped pairing identifies
`Hʲ(G_v, N)` with the `ℚ/ℤ`-dual of `H^{2-j}(G_v, N*)`. -/
theorem localTatePairing_bijective_right [Finite N] [DiscreteTopology N] (i j : ℕ)
    (hij : i + j = 2) : Function.Bijective (localTatePairing 𝔽 F v N i j hij).flip :=
  sorry

/-! ### Unramified classes and Milne's Theorem 2.6 -/

/-- **Unramified cohomology** (blueprint §"Local–Tate duality"): the submodule of unramified
classes `H¹(g_v, Y^{I_v}) ⊆ H¹(G_v, Y)`, the image of the inflation map
`ContinuousCohomology.inflApp` of `inflmap.lean` at the inertia subgroup. -/
noncomputable def unramifiedClasses (Y : TopRep 𝔽 G_v) :
    Submodule 𝔽 ↥(continuousCohomology 1 Y) :=
  LinearMap.range (ContinuousCohomology.inflApp (localInertiaGroup v) 1 Y).hom.toLinearMap

/-- **Milne, Theorem 2.6**: let `N` be a finite discrete `G_v`-module, unramified (inertia
acts trivially) and of order prime to the residue characteristic (automatic here: `N` is an
`𝔽`-module of characteristic `p` and `v ∤ p`). Then the unramified classes of `N*` and of `N`
are the exact annihilators of each other under the local Tate pairing on `H¹ × H¹`. -/
theorem mem_unramifiedClasses_localDualRep_iff [Finite N] [DiscreteTopology N]
    (p : ℕ) [Fact p.Prime] [CharP 𝔽 p]
    (hv : (p : RingOfIntegers F) ∉ v.asIdeal)
    (hunr : ∀ g ∈ localInertiaGroup v, ∀ n : ↥N, N.ρ g n = n)
    (x : ↥(continuousCohomology 1 (localDualRep 𝔽 F v N))) :
    x ∈ unramifiedClasses 𝔽 F v (localDualRep 𝔽 F v N) ↔
      ∀ y ∈ unramifiedClasses 𝔽 F v N, localTatePairing 𝔽 F v N 1 1 rfl x y = 0 :=
  sorry

end NumberField.PoitouTate
