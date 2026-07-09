/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.LocalGlobalMaps

/-!
# The dual module `M* = Hom_ℤ(M, K_S^×)` and global finiteness lemmas

This file scaffolds the coefficient modules and the "Connecting maps" lemmas of
`PTblueprint.tex` for the Poitou–Tate sequence. Throughout, `𝔽` is a finite field of
characteristic `p`, `F` is a number field, `S` a finite set of finite places of `F`, and
`M : TopRep 𝔽 (G_{F,S})` is a finite discrete module (per the blueprint's notation list).

## Main declarations

* `NumberField.PoitouTate.unitsAddRep G L` — for a group `G` acting on a field `L` by ring
  automorphisms, the additive `TopRep ℤ G` on `Additive Lˣ` with the discrete topology.
* `NumberField.PoitouTate.ksUnitsRep` — `K_S^×` as a `TopRep ℤ (G_{F,S})`, the coefficient
  module of the blueprint's `H³` lemma. This is the only genuinely ℤ-linear object in the
  scaffold: `K_S^×` is not an `𝔽`-module.
* `NumberField.PoitouTate.homUnitsRep X L` — the `𝔽`-linear topological representation on
  `Hom_ℤ(X, Additive Lˣ)`, with `G`-action `(g • f) (m) = g • f (g⁻¹ • m)` and `𝔽`-action
  `(a • f) (m) = f (a • m)`. Specializing:
* `NumberField.PoitouTate.dualRep M` — the blueprint's `M* = Hom_ℤ(M, K_S^×)`.
* `AddMonoidHom.finite_toAdditiveUnits` — additive homomorphisms from a finite additive group
  into the units of a domain form a finite type (each value is a root of unity of order
  dividing the cardinality of the source).
* `NumberField.PoitouTate.finite_dualRep` — blueprint lemma: `M*` is finite, a special case of
  the previous instance.
* `NumberField.PoitouTate.finite_continuousCohomology_two`,
  `NumberField.PoitouTate.finite_continuousCohomology_one_dualRep` — blueprint lemma:
  `H²(G_S, M)` and `H¹(G_S, M*)` are finite.
* `NumberField.PoitouTate.eq_zero_of_smul_continuousCohomology_three_ksUnitsRep` — blueprint
  lemma `H³-n-torsion-trivial`: if every prime dividing `n` lies in `S` (i.e. `n` is a unit in
  `R_{F,S}`), then `H³(G_S, K_S^×)` has no nonzero element killed by `n`.

The definitions and the finiteness/discreteness of `M*` are proved. The three remaining
`sorry`s are the deep arithmetic inputs: the two global cohomological finiteness lemmas
(which rest on Hermite–Minkowski, cf. the `Φ_p` discussion in `GKSDefn.lean`) and the `H³`
torsion-vanishing lemma (global class field theory).
-/

@[expose] public section

universe u

open IsDedekindDomain

/-- Additive homomorphisms from a finite additive group into the (additive) units of a domain
form a finite type: every value is a root of unity of order dividing the cardinality of the
source. -/
instance AddMonoidHom.finite_toAdditiveUnits {M R : Type*} [AddCommGroup M] [Finite M]
    [CommRing R] [IsDomain R] : Finite (M →+ Additive Rˣ) := by
  have : NeZero (Nat.card M) := .of_pos Nat.card_pos
  refine Finite.of_injective
    (fun f (m : M) => (⟨(f m).toMul, ?_⟩ : rootsOfUnity (Nat.card M) R))
    (fun f g hfg => ?_)
  · rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, card_nsmul_eq_zero', map_zero, toMul_zero]
  · ext m
    exact congrArg (fun x : rootsOfUnity (Nat.card M) R => (x.1 : R)) (congrFun hfg m)

namespace NumberField.PoitouTate

/-! ### Units of a Galois-stable field as a topological `ℤ`-representation -/

/-- For a group `G` acting on a field `L` by ring automorphisms, the units `Lˣ` (written
additively) form a discrete topological `ℤ`-representation of `G`, with `g` acting by
`Units.map` of the ring automorphism `MulSemiringAction.toRingHom G L g`. -/
noncomputable def unitsAddRep (G : Type*) [Group G] (L : Type*) [Field L]
    [MulSemiringAction G L] : TopRep ℤ G :=
  letI : TopologicalSpace (Additive Lˣ) := ⊥
  haveI : DiscreteTopology (Additive Lˣ) := ⟨rfl⟩
  TopRep.of (X := Additive Lˣ)
    { toMonoidHom :=
      { toFun g :=
          { toLinearMap := (MonoidHom.toAdditive
              (Units.map (MulSemiringAction.toRingHom G L g).toMonoidHom)).toIntLinearMap
            cont := continuous_of_discreteTopology }
        map_one' := by ext x; simp
        map_mul' g h := by ext x; simp [mul_smul] } }

/-- The units `K_S^×` of the maximal extension of `F` unramified outside `S`, as a discrete
topological `ℤ`-representation of `G_{F,S}` (blueprint notation item 7: the target of the
`H³` lemma and of the global pairing). -/
noncomputable def ksUnitsRep (F : Type u) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) :
    TopRep ℤ (unramifiedOutsideGaloisGroup F S) :=
  unitsAddRep (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S)

/-! ### The dual module `Hom_ℤ(X, Lˣ)` as an `𝔽`-linear topological representation -/

variable (𝔽 : Type*) [Field 𝔽] [Finite 𝔽] [TopologicalSpace 𝔽] [DiscreteTopology 𝔽]

section HomUnitsRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable (X : TopRep 𝔽 G) (L : Type*) [Field L] [MulSemiringAction G L]

omit [Finite 𝔽] [DiscreteTopology 𝔽] [TopologicalSpace G] [MulSemiringAction G L] in
/-- The `𝔽`-module structure on `Hom_ℤ(X, Additive Lˣ)` through the domain:
`(a • f) (m) = f (a • m)`. As for `CharacterModule`, this is the `DomMulAct` module structure
pulled back along `𝔽 →+* 𝔽ᵈᵐᵃ`, using commutativity of `𝔽`. -/
instance : Module 𝔽 (↥X →+ Additive Lˣ) :=
  fast_instance% Module.compHom (R := 𝔽ᵈᵐᵃ) _ ((RingEquiv.toOpposite 𝔽).toRingHom : 𝔽 →+* 𝔽ᵈᵐᵃ)

omit [Finite 𝔽] [DiscreteTopology 𝔽] [TopologicalSpace G] [MulSemiringAction G L] in
@[simp]
lemma smul_addMonoidHom_apply (a : 𝔽) (f : ↥X →+ Additive Lˣ) (m : ↥X) :
    (a • f) m = f (a • m) :=
  rfl

/-- The `𝔽`-linear topological representation of `G` on `Hom_ℤ(X, Additive Lˣ)`, with the
discrete topology, `G` acting by `(g • f) (m) = g • f (g⁻¹ • m)` and `𝔽` acting through the
domain by `(a • f) (m) = f (a • m)`. This is the common pattern of the blueprint's global
dual `M* = Hom_ℤ(M, K_S^×)` and its local analogue `Hom_ℤ(M, K̄ᵥ^×)`. -/
noncomputable def homUnitsRep : TopRep 𝔽 G :=
  letI : TopologicalSpace (↥X →+ Additive Lˣ) := ⊥
  haveI : DiscreteTopology (↥X →+ Additive Lˣ) := ⟨rfl⟩
  haveI : ContinuousSMul 𝔽 (↥X →+ Additive Lˣ) := ⟨continuous_of_discreteTopology⟩
  TopRep.of (X := ↥X →+ Additive Lˣ)
    { toMonoidHom :=
      { toFun g :=
          { toLinearMap :=
              { toFun f := ((MonoidHom.toAdditive
                    (Units.map (MulSemiringAction.toRingHom G L g).toMonoidHom)).comp f).comp
                    (X.ρ g⁻¹).toLinearMap.toAddMonoidHom
                map_add' f₁ f₂ := by ext m; simp
                map_smul' a f := by ext m; simp }
            cont := continuous_of_discreteTopology }
        map_one' := by ext f m; simp
        map_mul' g h := by ext f m; simp [mul_smul] } }

end HomUnitsRep

variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
variable (M : TopRep 𝔽 (unramifiedOutsideGaloisGroup F S))

/-- **Blueprint, notation item 10 / §"Connecting maps"**: the dual module
`M* = Hom_ℤ(M, K_S^×)`, with `G_{F,S}`-action `(g • f) (m) = g (f (g⁻¹ m))`. -/
noncomputable def dualRep : TopRep 𝔽 (unramifiedOutsideGaloisGroup F S) :=
  homUnitsRep 𝔽 M ↥(maximalUnramifiedOutside F S)

/-- **Blueprint lemma** (§"Connecting maps"): for `M` finite, `M* = Hom_ℤ(M, K_S^×)` is
finite — every value of `f : M →+ K_S^×` is a root of unity of order dividing `#M`, and a
field has at most `n` roots of `xⁿ = 1`. Registered as an instance since downstream
statements need it. -/
instance finite_dualRep [Finite M] : Finite ↥(dualRep 𝔽 F S M) :=
  inferInstanceAs (Finite (↥M →+ Additive (↥(maximalUnramifiedOutside F S))ˣ))

/-- The dual module is discrete (it carries the discrete topology by construction). -/
instance discreteTopology_dualRep : DiscreteTopology ↥(dualRep 𝔽 F S M) :=
  ⟨rfl⟩

/-- **Blueprint lemma** (§"Connecting maps"): `H²(G_S, M)` is finite for `M` finite. -/
theorem finite_continuousCohomology_two [Finite M] [DiscreteTopology M] :
    Finite ↥(continuousCohomology 2 M) :=
  sorry

/-- **Blueprint lemma** (§"Connecting maps"): `H¹(G_S, M*)` is finite for `M` finite. -/
theorem finite_continuousCohomology_one_dualRep [Finite M] [DiscreteTopology M] :
    Finite ↥(continuousCohomology 1 (dualRep 𝔽 F S M)) :=
  sorry

/-- **Blueprint lemma `H³-n-torsion-trivial`** (§"Some pre-requisites needed for defining the
pairing"): if every prime dividing `n` lies in `S` — i.e. `n` is a unit in the ring of
`S`-integers `R_{F,S}` — then there is no nonzero element of order dividing `n` in
`H³(G_{F,S}, K_S^×)`. -/
theorem eq_zero_of_smul_continuousCohomology_three_ksUnitsRep (n : ℕ)
    (hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), (n : RingOfIntegers F) ∈ v.asIdeal → v ∈ S)
    (x : ↥(continuousCohomology 3 (ksUnitsRep F S))) (hx : n • x = 0) : x = 0 :=
  sorry

end NumberField.PoitouTate
