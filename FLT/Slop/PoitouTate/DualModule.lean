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
* `NumberField.PoitouTate.hS_dualRep` — the hypothesis "`#M` is a unit in `R_{F,S}`"
  transfers from `M` to `M*` (both cardinalities are powers of `#𝔽`).
* `NumberField.PoitouTate.doubleDualHom` / `NumberField.PoitouTate.doubleDualIso` — the
  evaluation map `M ⟶ M** = Hom_ℤ(Hom_ℤ(M, K_S^×), K_S^×)`, and the identification
  `M ≅ M**` it induces (blueprint §"Connecting maps", step 2, where it feeds `psi`); its
  bijectivity `doubleDualHom_bijective` is a deep sorry (it needs `μ_{#M} ⊆ K_S`).
* `NumberField.PoitouTate.finite_continuousCohomology_two`,
  `NumberField.PoitouTate.finite_continuousCohomology_one_dualRep` — blueprint lemma:
  `H²(G_S, M)` and `H¹(G_S, M*)` are finite.
* `NumberField.PoitouTate.eq_zero_of_smul_continuousCohomology_three_ksUnitsRep` — blueprint
  lemma `H³-n-torsion-trivial`: if every prime dividing `n` lies in `S` (i.e. `n` is a unit in
  `R_{F,S}`), then `H³(G_S, K_S^×)` has no nonzero element killed by `n`.

The definitions, the finiteness/discreteness of `M*`, and the `hS`-transfer are proved. The
four remaining `sorry`s are the deep arithmetic inputs: the two global cohomological
finiteness lemmas (which rest on Hermite–Minkowski, cf. the `Φ_p` discussion in
`GKSDefn.lean`), the `H³` torsion-vanishing lemma (global class field theory), and the
bijectivity of the double-dual evaluation (cyclotomic ramification).
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

section SmulCancel

variable {G : Type*} [Group G] {L : Type*} [Field L] [MulSemiringAction G L]

/-- Cancellation for the additive units action. -/
lemma toAdditive_unitsMap_smul_inv_smul (g : G) (y : Additive Lˣ) :
    (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom G L g).toMonoidHom))
      ((MonoidHom.toAdditive
        (Units.map (MulSemiringAction.toRingHom G L g⁻¹).toMonoidHom)) y) = y := by
  refine Additive.toMul.injective (Units.ext ?_)
  change g • (g⁻¹ • ((y.toMul : Lˣ) : L)) = ((y.toMul : Lˣ) : L)
  exact smul_inv_smul g _

end SmulCancel

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

/-- Evaluation of an element of the dual module `M* = Hom_ℤ(M, K_S^×)`, unfolding the
carrier of `dualRep`. -/
noncomputable def dualEval (x : ↥(dualRep 𝔽 F S M)) :
    ↥M →+ Additive (↥(maximalUnramifiedOutside F S))ˣ := x

omit [Finite 𝔽] [NumberField F] in
lemma dualRep_ρ_apply (g : unramifiedOutsideGaloisGroup F S) (x : ↥(dualRep 𝔽 F S M))
    (m : ↥M) :
    dualEval 𝔽 F S M ((dualRep 𝔽 F S M).ρ g x) m =
      (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S) g).toMonoidHom))
        (dualEval 𝔽 F S M x (M.ρ g⁻¹ m)) :=
  rfl

/-! ### The double dual and the evaluation map `M ⟶ M**`

As in `KerPairing.lean`: the carrier of `M** = dualRep (dualRep M)` is definitionally the
raw type `↥M* →+ Additive K_S^×-units`, which carries no global topology (the representation
equips it with the discrete topology via a local `letI`). The instances below expose that
topology globally on the raw carrier type, so that continuous linear maps into `↥M**` can be
elaborated. -/

noncomputable instance :
    TopologicalSpace
      (↥(dualRep 𝔽 F S M) →+ Additive (↥(maximalUnramifiedOutside F S))ˣ) := ⊥

instance :
    DiscreteTopology
      (↥(dualRep 𝔽 F S M) →+ Additive (↥(maximalUnramifiedOutside F S))ˣ) :=
  ⟨rfl⟩

instance :
    IsTopologicalAddGroup
      (↥(dualRep 𝔽 F S M) →+ Additive (↥(maximalUnramifiedOutside F S))ˣ) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

instance :
    ContinuousSMul 𝔽
      (↥(dualRep 𝔽 F S M) →+ Additive (↥(maximalUnramifiedOutside F S))ˣ) :=
  ⟨continuous_of_discreteTopology⟩

omit [Finite 𝔽] [NumberField F] in
/-- **`hS` transfers from `M` to `M*`**: any prime containing `#M*` already contains `#M`,
so the blueprint's hypothesis "`#M` is a unit in `R_{F,S}`" for `M` implies the same for
`M*`. Indeed both `M` and `M* = Hom_ℤ(M, K_S^×)` are finite `𝔽`-modules, so `#M` and `#M*`
are powers of `#𝔽` (and `M* ≠ 0` forces `M ≠ 0`). This lets the kernel pairing and its
perfectness be applied to `M*` under the hypothesis `hS` stated for `M`. -/
theorem hS_dualRep [Finite M]
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥(dualRep 𝔽 F S M) : RingOfIntegers F) ∈ w.asIdeal → w ∈ S := by
  intro w hw
  rw [Module.natCard_eq_pow_finrank (K := 𝔽), Nat.cast_pow] at hw
  rcases Nat.eq_zero_or_pos (Module.finrank 𝔽 ↥(dualRep 𝔽 F S M)) with h0 | hpos
  · rw [h0, pow_zero] at hw
    exact absurd ((Ideal.eq_top_iff_one _).mpr hw) w.isPrime.ne_top
  · have hq : ((Nat.card 𝔽 : ℕ) : RingOfIntegers F) ∈ w.asIdeal :=
      w.isPrime.mem_of_pow_mem _ hw
    haveI : Nontrivial ↥M := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      haveI : Subsingleton ↥(dualRep 𝔽 F S M) :=
        inferInstanceAs (Subsingleton (↥M →+ Additive (↥(maximalUnramifiedOutside F S))ˣ))
      rw [Module.finrank_zero_of_subsingleton] at hpos
      exact absurd hpos (lt_irrefl 0)
    refine hS w ?_
    rw [Module.natCard_eq_pow_finrank (K := 𝔽), Nat.cast_pow]
    exact w.asIdeal.pow_mem_of_mem hq _ Module.finrank_pos

/-- Evaluation of `M` at an element of the dual module, `m ↦ (x ↦ x m)`: an element of the
double dual `M** = Hom_ℤ(M*, K_S^×)`. -/
noncomputable def doubleDualEvalAt (m : ↥M) : ↥(dualRep 𝔽 F S (dualRep 𝔽 F S M)) :=
  ({ toFun := fun x ↦ dualEval 𝔽 F S M x m
     map_zero' := rfl
     map_add' := fun _ _ ↦ rfl } :
    ↥(dualRep 𝔽 F S M) →+ Additive (↥(maximalUnramifiedOutside F S))ˣ)

/-- The continuous `𝔽`-linear map underlying the evaluation `M ⟶ M**`. It is `𝔽`-linear
because the `𝔽`-actions on `M*` and `M**` are both through the domain
(`smul_addMonoidHom_apply`). -/
noncomputable def doubleDualCLM [DiscreteTopology M] :
    ↥M →L[𝔽] ↥(dualRep 𝔽 F S (dualRep 𝔽 F S M)) where
  toFun := doubleDualEvalAt 𝔽 F S M
  map_add' m₁ m₂ := AddMonoidHom.ext fun x ↦ map_add (dualEval 𝔽 F S M x) m₁ m₂
  map_smul' _ _ := AddMonoidHom.ext fun _ ↦ rfl
  cont := continuous_of_discreteTopology

omit [Finite 𝔽] [NumberField F] in
/-- The evaluation is `G_{F,S}`-equivariant, by the same cancellation as `evalIntertwiner`
in `KerPairing.lean`. -/
lemma doubleDualCLM_equivariant [DiscreteTopology M] (g : unramifiedOutsideGaloisGroup F S)
    (m : ↥M) :
    doubleDualCLM 𝔽 F S M (M.ρ g m) =
      (dualRep 𝔽 F S (dualRep 𝔽 F S M)).ρ g (doubleDualCLM 𝔽 F S M m) := by
  refine AddMonoidHom.ext fun x ↦ ?_
  change dualEval 𝔽 F S M x (M.ρ g m) =
    dualEval 𝔽 F S (dualRep 𝔽 F S M)
      ((dualRep 𝔽 F S (dualRep 𝔽 F S M)).ρ g (doubleDualEvalAt 𝔽 F S M m)) x
  rw [dualRep_ρ_apply]
  change dualEval 𝔽 F S M x (M.ρ g m) =
    (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
      (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S)
      g).toMonoidHom))
      (dualEval 𝔽 F S M ((dualRep 𝔽 F S M).ρ g⁻¹ x) m)
  rw [dualRep_ρ_apply, inv_inv, toAdditive_unitsMap_smul_inv_smul]

/-- **The evaluation map `M ⟶ M**`**, `m ↦ (x ↦ x m)`, as a morphism of topological
representations. -/
noncomputable def doubleDualHom [DiscreteTopology M] :
    M ⟶ dualRep 𝔽 F S (dualRep 𝔽 F S M) :=
  TopRep.ofHom
    { toContinuousLinearMap := doubleDualCLM 𝔽 F S M
      isIntertwining' := fun g ↦
        ContinuousLinearMap.ext fun m ↦ doubleDualCLM_equivariant 𝔽 F S M g m }

/-- **Deep input** (the blueprint glosses this): the evaluation map `M → M**` is bijective.
This is where `hS` is genuinely arithmetic: it forces `μ_{#M} ⊆ K_S` — the cyclotomic
extension `F(μ_{#M})/F` is ramified only above the primes dividing `#M`, which all lie in
`S` — so that `Hom_ℤ(M, K_S^×)` is the full Pontryagin dual of `M` and finite double
duality applies. (No oddness hypothesis is needed: `IsUnramifiedOutside` constrains no
archimedean places.) -/
theorem doubleDualHom_bijective [Finite M] [DiscreteTopology M]
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    Function.Bijective ⇑(doubleDualCLM 𝔽 F S M) :=
  sorry

/-- The evaluation `M ≃ₗ[𝔽] M**` as an `𝔽`-linear equivalence
(`doubleDualCLM` plus `doubleDualHom_bijective`). -/
noncomputable def doubleDualEquiv [Finite M] [DiscreteTopology M]
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    ↥M ≃ₗ[𝔽] ↥(dualRep 𝔽 F S (dualRep 𝔽 F S M)) :=
  LinearEquiv.ofBijective (doubleDualCLM 𝔽 F S M).toLinearMap
    (doubleDualHom_bijective 𝔽 F S M hS)

lemma doubleDualEquiv_apply [Finite M] [DiscreteTopology M]
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) (m : ↥M) :
    doubleDualEquiv 𝔽 F S M hS m = doubleDualCLM 𝔽 F S M m :=
  rfl

/-- **`M ≅ M**`** as topological representations: the evaluation map, an isomorphism by
`doubleDualHom_bijective` (both sides are discrete, so the set-theoretic inverse is
automatically continuous, and it is equivariant because the forward map is). -/
noncomputable def doubleDualIso [Finite M] [DiscreteTopology M]
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S) :
    M ≅ dualRep 𝔽 F S (dualRep 𝔽 F S M) where
  hom := doubleDualHom 𝔽 F S M
  inv := TopRep.ofHom
    { toContinuousLinearMap :=
        ({ toLinearMap := (doubleDualEquiv 𝔽 F S M hS).symm.toLinearMap
           cont := continuous_of_discreteTopology } :
          ↥(dualRep 𝔽 F S (dualRep 𝔽 F S M)) →L[𝔽] ↥M)
      isIntertwining' := fun g ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        refine (doubleDualEquiv 𝔽 F S M hS).injective ?_
        change (doubleDualEquiv 𝔽 F S M hS) ((doubleDualEquiv 𝔽 F S M hS).symm
            ((dualRep 𝔽 F S (dualRep 𝔽 F S M)).ρ g x)) =
          (doubleDualEquiv 𝔽 F S M hS) (M.ρ g ((doubleDualEquiv 𝔽 F S M hS).symm x))
        rw [LinearEquiv.apply_symm_apply, doubleDualEquiv_apply,
          doubleDualCLM_equivariant, ← doubleDualEquiv_apply 𝔽 F S M hS,
          LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    ext m
    change (doubleDualEquiv 𝔽 F S M hS).symm (doubleDualCLM 𝔽 F S M m) = m
    rw [← doubleDualEquiv_apply 𝔽 F S M hS, LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    ext x
    change doubleDualCLM 𝔽 F S M ((doubleDualEquiv 𝔽 F S M hS).symm x) = x
    rw [← doubleDualEquiv_apply 𝔽 F S M hS, LinearEquiv.apply_symm_apply]

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
