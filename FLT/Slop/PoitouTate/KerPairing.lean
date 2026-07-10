/-
Copyright (c) 2026 Y. Samanda Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Y. Samanda Zhang
-/
module

public import Mathlib
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Slop.PoitouTate.CochainLemmas
public import FLT.Slop.PoitouTate.DualModule
public import FLT.Slop.PoitouTate.GKSDefn
public import FLT.Slop.PoitouTate.LocalGlobalMaps
public import FLT.Slop.PoitouTate.LocalTateDuality

/-!
# The kernel pairing `Ker²(G_S, M) × Ker¹(G_S, M*) → ℚ/ℤ` (blueprint §4)

This file constructs the pairing of `PTblueprint.tex` §"Explicitly defining the pairing":
for classes `f ∈ Ker²(G_S, M)` and `g ∈ Ker¹(G_S, M*)` (locally trivial at every `v ∈ S`),
choose cocycle representatives, a global primitive `h` with `f ∪ g = dh` (possible because
`f ∪ g` is `#M`-torsion in `H³(G_S, K_S^×)`, which has no nonzero `#M`-torsion by the
blueprint's `H³` lemma), and local primitives `ψ_v` with `res_v g = dψ_v`; then
`x_v := f_v ∪ ψ_v − h_v` is a local `2`-cocycle valued in `K̄ᵥ^×` and
`⟨f, g⟩ := ∑_{v ∈ S} inv_v [x_v]`.

## Main declarations

* `NumberField.PoitouTate.ksEmbedding` — the field embedding `K_S ↪ K̄ᵥ` implicit in
  `localToGlobal`, and `ksUnitsGlue`, the induced equivariant map `K_S^× → K̄ᵥ^×` of
  `ℤ`-representations of `G_v`.
* `NumberField.PoitouTate.evalIntertwiner` / `evalIntertwinerLoc` — the evaluation
  intertwiners `M →ⁱL Hom(M*, K_S^×)` (and the local variant valued in `K̄ᵥ^×`) feeding the
  cochain-level cup products of `cupprod.lean`.
* `NumberField.PoitouTate.sum_localInvariantMap_map_eq_zero` — global reciprocity relative to
  `S`: the sum over `v ∈ S` of the local invariants of a class from `H²(G_S, K_S^×)`
  vanishes. This is the deep class-field-theory input to the well-definedness of the pairing
  (Milne, ADT I.4.10); it is the one `sorry` of this file.
* `NumberField.PoitouTate.PairingChoices` — the bundle of cochain-level choices
  `(f₂, g₁, h, ψ)` underlying the pairing, `xCocycle` the local `2`-cocycles
  `x_v = f_v ∪ ψ_v − h_v`, and `pairingValue` the sum `∑_{v ∈ S} inv_v [x_v]`.
* `NumberField.PoitouTate.pairingValue_congr` — the value depends only on the two classes,
  not on the choices; `pairingChoices_nonempty` — choices exist; `kerPairingFun` and its
  additivity in each argument — the data needed to fill `kerPairing` in
  `PoitouTateStatement.lean`.
-/

@[expose] public section

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

-- The cochain-level computations in this file unify large types across the
-- `TopRep.of`/named-representation and `𝔽`/`ℤ` seams in almost every declaration; the
-- default heartbeat budgets are far too small for them, so they are raised file-wide.
set_option linter.style.maxHeartbeats false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

universe u

open IsDedekindDomain CategoryTheory ContRepresentation TopRep TopCup

namespace NumberField.PoitouTate

variable (𝔽 : Type*) [Field 𝔽] [Finite 𝔽] [TopologicalSpace 𝔽] [DiscreteTopology 𝔽]
variable (F : Type u) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (RingOfIntegers F)))

/- The carriers of `ksUnitsRep` and `algClosureUnitsRep` are `Additive Lˣ` for fields `L`
carrying no topology; the representations equip them with the discrete topology via a local
`letI`. The instances below expose that topology globally on the raw carrier types (there is
no competing instance, the underlying fields having no `TopologicalSpace` instance), so that
continuous linear maps between the carriers can be elaborated. -/

noncomputable instance :
    TopologicalSpace (Additive (↥(maximalUnramifiedOutside F S))ˣ) := ⊥

instance : DiscreteTopology (Additive (↥(maximalUnramifiedOutside F S))ˣ) := ⟨rfl⟩

instance : IsTopologicalAddGroup (Additive (↥(maximalUnramifiedOutside F S))ˣ) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

noncomputable instance (v : HeightOneSpectrum (RingOfIntegers F)) :
    TopologicalSpace (Additive (AlgebraicClosure (v.adicCompletion F))ˣ) := ⊥

instance (v : HeightOneSpectrum (RingOfIntegers F)) :
    DiscreteTopology (Additive (AlgebraicClosure (v.adicCompletion F))ˣ) := ⟨rfl⟩

instance (v : HeightOneSpectrum (RingOfIntegers F)) :
    IsTopologicalAddGroup (Additive (AlgebraicClosure (v.adicCompletion F))ˣ) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

instance : DiscreteTopology ↥(ksUnitsRep F S) := ⟨rfl⟩

instance (v : HeightOneSpectrum (RingOfIntegers F)) :
    DiscreteTopology ↥(algClosureUnitsRep F v) := ⟨rfl⟩

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

variable (M : TopRep.{u} 𝔽 (unramifiedOutsideGaloisGroup F S))

/-- Evaluation of an element of the dual module `M* = Hom_ℤ(M, K_S^×)`, unfolding the
carrier of `dualRep`. -/
noncomputable def dualEval (x : ↥(dualRep 𝔽 F S M)) :
    ↥M →+ Additive (↥(maximalUnramifiedOutside F S))ˣ := x

lemma dualRep_ρ_apply (g : unramifiedOutsideGaloisGroup F S) (x : ↥(dualRep 𝔽 F S M))
    (m : ↥M) :
    dualEval 𝔽 F S M ((dualRep 𝔽 F S M).ρ g x) m =
      (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S) g).toMonoidHom))
        (dualEval 𝔽 F S M x (M.ρ g⁻¹ m)) :=
  rfl

lemma ksUnitsRep_ρ_apply (g : unramifiedOutsideGaloisGroup F S) (u : ↥(ksUnitsRep F S)) :
    (ksUnitsRep F S).ρ g u =
      (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S) g).toMonoidHom)) u :=
  rfl

lemma algClosureUnitsRep_ρ_apply (v : HeightOneSpectrum (RingOfIntegers F))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion F)) (u : ↥(algClosureUnitsRep F v)) :
    (algClosureUnitsRep F v).ρ σ u =
      (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (Field.absoluteGaloisGroup (v.adicCompletion F))
        (AlgebraicClosure (v.adicCompletion F)) σ).toMonoidHom)) u :=
  rfl

/-- The embedding `K_S ↪ K̄ᵥ` implicit in `localToGlobal`: the inclusion of the maximal
extension unramified outside `S` into `F̄`, followed by the chosen embedding `F̄ ↪ F̄ᵥ` of
`Field.absoluteGaloisGroup.map`. -/
noncomputable def ksEmbedding (v : HeightOneSpectrum (RingOfIntegers F)) :
    ↥(maximalUnramifiedOutside F S) →+* AlgebraicClosure (v.adicCompletion F) :=
  (AlgebraicClosure.map (algebraMap F (v.adicCompletion F))).comp
    (algebraMap ↥(maximalUnramifiedOutside F S) (AlgebraicClosure F))

/-- The embedding `K_S ↪ K̄ᵥ` intertwines the `G_v`-actions along `localToGlobal`. -/
lemma ksEmbedding_equivariant (v : HeightOneSpectrum (RingOfIntegers F))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion F))
    (x : ↥(maximalUnramifiedOutside F S)) :
    ksEmbedding F S v (localToGlobal F S v σ • x) = σ • ksEmbedding F S v x := by
  have h1 : (algebraMap ↥(maximalUnramifiedOutside F S) (AlgebraicClosure F))
      (localToGlobal F S v σ • x) =
      (Field.absoluteGaloisGroup.map (algebraMap F (v.adicCompletion F)) σ)
        ((algebraMap ↥(maximalUnramifiedOutside F S) (AlgebraicClosure F)) x) :=
    AlgEquiv.restrictNormal_commutes
      (Field.absoluteGaloisGroup.map (algebraMap F (v.adicCompletion F)) σ)
      ↥(maximalUnramifiedOutside F S) x
  unfold ksEmbedding
  rw [RingHom.comp_apply, RingHom.comp_apply, h1]
  exact Field.absoluteGaloisGroup.lift_map (algebraMap F (v.adicCompletion F)) σ _

/-- The local-to-global map as a bare monoid homomorphism (elaboration aid). -/
noncomputable abbrev locToGlob (v : HeightOneSpectrum (RingOfIntegers F)) :
    Field.absoluteGaloisGroup (v.adicCompletion F) →* unramifiedOutsideGaloisGroup F S :=
  (localToGlobal F S v : _ →* _)

/-- The continuous linear map underlying the coefficient glue. -/
noncomputable def ksUnitsGlueCLM (v : HeightOneSpectrum (RingOfIntegers F)) :
    ↥(TopRep.res (locToGlob F S v) (ksUnitsRep F S)) →L[ℤ]
      ↥(algClosureUnitsRep F v) where
  toFun u := (MonoidHom.toAdditive (Units.map (ksEmbedding F S v).toMonoidHom)) u
  map_add' u₁ u₂ :=
    map_add (MonoidHom.toAdditive (Units.map (ksEmbedding F S v).toMonoidHom)) u₁ u₂
  map_smul' n u :=
    map_zsmul (MonoidHom.toAdditive (Units.map (ksEmbedding F S v).toMonoidHom)) n u
  cont := continuous_of_discreteTopology

/-- The glue commutes with the `G_v`-actions. -/
lemma ksUnitsGlueCLM_intertwining (v : HeightOneSpectrum (RingOfIntegers F))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion F))
    (u : ↥(TopRep.res (locToGlob F S v) (ksUnitsRep F S))) :
    ksUnitsGlueCLM F S v ((TopRep.res (locToGlob F S v) (ksUnitsRep F S)).ρ σ u) =
      (algClosureUnitsRep F v).ρ σ (ksUnitsGlueCLM F S v u) := by
  refine Additive.toMul.injective ?_
  refine Units.ext ?_
  exact ksEmbedding_equivariant F S v σ _

/-- The coefficient glue: the equivariant map from `K_S^×` (restricted to `G_v` along
`localToGlobal`) to `K̄ᵥ^×`, induced by `ksEmbedding`. -/
noncomputable def ksUnitsGlue (v : HeightOneSpectrum (RingOfIntegers F)) :
    TopRep.res (locToGlob F S v) (ksUnitsRep F S) ⟶ algClosureUnitsRep F v :=
  TopRep.ofHom
    { toContinuousLinearMap := ksUnitsGlueCLM F S v
      isIntertwining' := fun σ ↦ by
        refine ContinuousLinearMap.ext fun u ↦ ?_
        exact ksUnitsGlueCLM_intertwining F S v σ u }

/-- The glue commutes with the additive units actions, in unfolded form. -/
lemma ksUnitsGlue_toAdditive_comm (v : HeightOneSpectrum (RingOfIntegers F))
    (σ : Field.absoluteGaloisGroup (v.adicCompletion F)) (y : ↥(ksUnitsRep F S)) :
    (ksUnitsGlue F S v).hom
      ((MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (unramifiedOutsideGaloisGroup F S) ↥(maximalUnramifiedOutside F S)
        (localToGlobal F S v σ)).toMonoidHom)) y) =
      (MonoidHom.toAdditive (Units.map (MulSemiringAction.toRingHom
        (Field.absoluteGaloisGroup (v.adicCompletion F))
        (AlgebraicClosure (v.adicCompletion F)) σ).toMonoidHom))
        ((ksUnitsGlue F S v).hom y) :=
  (ksUnitsGlue F S v).hom.isIntertwining σ y

variable [Finite M] [DiscreteTopology M]

/-- The evaluation intertwiner `M →ⁱL Hom(M*, K_S^×)`, `m ↦ (x ↦ x m)`, feeding the
cochain-level cup products: over `ℤ`, with `f ∈ H²(G_S, M)` in the first slot and
`g ∈ H¹(G_S, M*)` in the second, `cupCochain evalIntertwiner` computes `f ∪ g` valued in
`K_S^×`. -/
noncomputable def evalIntertwiner :
    (toInt M).ρ →ⁱL ContRepresentation.linHom (toInt (dualRep 𝔽 F S M)).ρ
      (ksUnitsRep F S).ρ where
  toContinuousLinearMap :=
    { toFun := fun m ↦
        { toFun := fun x ↦ dualEval 𝔽 F S M x m
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl
          cont := continuous_of_discreteTopology }
      map_add' := fun m₁ m₂ ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change dualEval 𝔽 F S M x (m₁ + m₂) =
          dualEval 𝔽 F S M x m₁ + dualEval 𝔽 F S M x m₂
        exact map_add (dualEval 𝔽 F S M x) m₁ m₂
      map_smul' := fun n m ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change dualEval 𝔽 F S M x (n • m) = n • dualEval 𝔽 F S M x m
        exact map_zsmul (dualEval 𝔽 F S M x) n m
      cont := continuous_of_discreteTopology }
  isIntertwining' := fun g ↦ by
    refine ContinuousLinearMap.ext fun m ↦ ?_
    refine ContinuousLinearMap.ext fun x ↦ ?_
    change dualEval 𝔽 F S M x (M.ρ g m) =
      (ksUnitsRep F S).ρ g (dualEval 𝔽 F S M ((dualRep 𝔽 F S M).ρ g⁻¹ x) m)
    rw [dualRep_ρ_apply, ksUnitsRep_ρ_apply, inv_inv, toAdditive_unitsMap_smul_inv_smul]

/-- The local evaluation intertwiner `M →ⁱL Hom(M*, K̄ᵥ^×)` over `G_v`: evaluation followed
by the coefficient glue `K_S^× → K̄ᵥ^×`. -/
noncomputable def evalIntertwinerLoc (v : HeightOneSpectrum (RingOfIntegers F)) :
    ((toInt M).ρ.restrict (localToGlobal F S v : _ →* _)) →ⁱL
      ContRepresentation.linHom
        ((toInt (dualRep 𝔽 F S M)).ρ.restrict (localToGlobal F S v : _ →* _))
        (algClosureUnitsRep F v).ρ where
  toContinuousLinearMap :=
    { toFun := fun m ↦
        { toFun := fun x ↦ (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x m)
          map_add' := fun x₁ x₂ ↦ map_add ((ksUnitsGlue F S v).hom) _ _
          map_smul' := fun n x ↦ by
            simp only [RingHom.id_apply]
            exact map_zsmul ((ksUnitsGlue F S v).hom) n _
          cont := continuous_of_discreteTopology }
      map_add' := fun m₁ m₂ ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x (m₁ + m₂)) =
          (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x m₁) +
            (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x m₂)
        exact (congrArg ((ksUnitsGlue F S v).hom)
          (map_add (dualEval 𝔽 F S M x) m₁ m₂)).trans
          (map_add ((ksUnitsGlue F S v).hom) _ _)
      map_smul' := fun n m ↦ by
        refine ContinuousLinearMap.ext fun x ↦ ?_
        change (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x (n • m)) =
          n • (ksUnitsGlue F S v).hom (dualEval 𝔽 F S M x m)
        exact (congrArg ((ksUnitsGlue F S v).hom)
          (map_zsmul (dualEval 𝔽 F S M x) n m)).trans
          (map_zsmul ((ksUnitsGlue F S v).hom) n _)
      cont := continuous_of_discreteTopology }
  isIntertwining' := fun σ ↦ by
    refine ContinuousLinearMap.ext fun m ↦ ?_
    refine ContinuousLinearMap.ext fun x ↦ ?_
    change (ksUnitsGlue F S v).hom
        (dualEval 𝔽 F S M x (M.ρ (localToGlobal F S v σ) m)) =
      (algClosureUnitsRep F v).ρ σ ((ksUnitsGlue F S v).hom
        (dualEval 𝔽 F S M ((dualRep 𝔽 F S M).ρ (localToGlobal F S v σ⁻¹) x) m))
    rw [dualRep_ρ_apply, ksUnitsGlue_toAdditive_comm, algClosureUnitsRep_ρ_apply,
      toAdditive_unitsMap_smul_inv_smul, map_inv (localToGlobal F S v) σ, inv_inv]

/-- The compatibility between the global and local evaluation intertwiners through the
coefficient glue, feeding `cochainsMap_cupCochain`. -/
lemma ksUnitsGlue_evalIntertwiner (v : HeightOneSpectrum (RingOfIntegers F)) (m : ↥M)
    (x : ↥(dualRep 𝔽 F S M)) :
    (ksUnitsGlue F S v).hom (evalIntertwiner 𝔽 F S M m x) =
      evalIntertwinerLoc 𝔽 F S M v m x := by
  with_unfolding_all rfl

/-- **Global reciprocity relative to `S`** (Milne, ADT I.4.10 internals): the sum over
`v ∈ S` of the local invariants of a class from `H²(G_{F,S}, K_S^×)` vanishes.

This is the class-field-theory input to the well-definedness of the kernel pairing (it
controls the ambiguity in the choice of the primitive `h` with `f ∪ g = dh`); it plays the
same role as `localInvariantMap`, which is likewise a deliberate `sorry` in
`LocalTateDuality.lean`. -/
theorem sum_localInvariantMap_map_eq_zero (z : ↥(continuousCohomology 2 (ksUnitsRep F S))) :
    ∑ v ∈ S.attach, localInvariantMap F v.1
      (ContinuousCohomology.map (localToGlobal F S v.1) (ksUnitsGlue F S v.1) 2 z) = 0 :=
  sorry

/-- The bundle of cochain-level choices underlying the blueprint's pairing
`⟨f, g⟩ = ∑_{v ∈ S} inv_v [x_v]`: cocycle representatives `f₂` of `f ∈ H²(G_S, M)` and `g₁`
of `g ∈ H¹(G_S, M*)`, a global `2`-cochain `h₂` valued in `K_S^×` with `f₂ ∪ g₁ = d h₂`, and
for each `v ∈ S` a local `0`-cochain `ψ_v` (recorded on the `ℤ`-linear side, where the cup
products live) with `res_v g₁ = d ψ_v`. -/
structure PairingChoices (x : ↥(continuousCohomology 2 M))
    (y : ↥(continuousCohomology 1 (dualRep 𝔽 F S M))) where
  /-- The cocycle representative of `f ∈ H²(G_S, M)`. -/
  f2 : ↥((homogeneousCochains M).X 2)
  hf2 : (homogeneousCochains M).d 2 3 f2 = 0
  hf2x : cocycleClass M 2 f2 hf2 = x
  /-- The cocycle representative of `g ∈ H¹(G_S, M*)`. -/
  g1 : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 1)
  hg1 : (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 g1 = 0
  hg1y : cocycleClass (dualRep 𝔽 F S M) 1 g1 hg1 = y
  /-- The global primitive: `f₂ ∪ g₁ = d h₂` in the `K_S^×`-valued cochains. -/
  h2 : ↥((homogeneousCochains (ksUnitsRep F S)).X 2)
  hh : (homogeneousCochains (ksUnitsRep F S)).d 2 3 h2 =
    cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
      ((toIntCochainEquiv M 2).symm f2) ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1)
  /-- The local primitives: `res_v g₁ = d ψ_v`, on the `ℤ`-linear side. -/
  psi : (v : S) → ↥((homogeneousCochains
    (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).X 0)
  hpsi : ∀ v : S, (homogeneousCochains
      (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (psi v) =
    (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1)

variable {𝔽 F S M} {x : ↥(continuousCohomology 2 M)}
  {y : ↥(continuousCohomology 1 (dualRep 𝔽 F S M))}

/-- The `ℤ`-side representative of `f` is a cocycle. -/
lemma d_toInt_f2 (f2 : ↥((homogeneousCochains M).X 2))
    (hf2 : (homogeneousCochains M).d 2 3 f2 = 0) :
    (homogeneousCochains (toInt M)).d 2 3 ((toIntCochainEquiv M 2).symm f2) = 0 := by
  rw [toIntCochainEquiv_symm_d, hf2, (toIntCochainEquiv M 3).symm.map_zero]

/-- The `ℤ`-side representative of `g` is a cocycle. -/
lemma d_toInt_g1 (g1 : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 1))
    (hg1 : (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 g1 = 0) :
    (homogeneousCochains (toInt (dualRep 𝔽 F S M))).d 1 2
      ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1) = 0 := by
  rw [toIntCochainEquiv_symm_d, hg1, (toIntCochainEquiv (dualRep 𝔽 F S M) 2).symm.map_zero]

/-- The blueprint's local `2`-cochain `x_v = f_v ∪ ψ_v − h_v`, valued in `K̄ᵥ^×`. -/
noncomputable def xCocycle (c : PairingChoices 𝔽 F S M x y) (v : S) :
    ↥((homogeneousCochains (algClosureUnitsRep F v.1)).X 2) :=
  cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2 ((toIntCochainEquiv M 2).symm c.f2))
      (c.psi v)
    - (ContinuousCohomology.cochainsMap (localToGlobal F S v.1) (ksUnitsGlue F S v.1)).f 2 c.h2

/-- The `ℤ`-side restriction of the representative of `f` is a cocycle. -/
lemma d_cochainsMap_toInt_f2 (c : PairingChoices 𝔽 F S M x y) (v : S) :
    (homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 2 3
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c.f2)) = 0 := by
  rw [ContRepresentation.cochainsMap_f_d, d_toInt_f2 c.f2 c.hf2]
  exact ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
    (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 3).hom.map_zero

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- **Blueprint §4, claim 1**: `x_v` is a `2`-cocycle. -/
lemma d_xCocycle (c : PairingChoices 𝔽 F S M x y) (v : S) :
    (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle c v) = 0 := by
  set fv := (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
    (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
      ((toIntCochainEquiv M 2).symm c.f2) with hfv
  set hv := (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
    (ksUnitsGlue F S v.1)).f 2 c.h2 with hhv
  have hsub : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle c v) =
      (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
        (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl fv (c.psi v)) -
      (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 hv :=
    ((homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3).hom.map_sub _ _
  -- Leibniz on the cup term.
  have hleib := ContRepresentation.cup_d_comm _ _ _ (evalIntertwinerLoc 𝔽 F S M v.1)
    2 0 2 rfl fv (c.psi v)
  -- The first Leibniz summand vanishes: `d f_v = 0`.
  have hdfv : cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 3 0 3 (by omega)
      ((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 2 3 fv)
      (c.psi v) = 0 := by
    rw [d_cochainsMap_toInt_f2 c v]
    exact ContRepresentation.cupCochain_zero_apply (evalIntertwinerLoc 𝔽 F S M v.1) 3 0 3
      (by omega) (c.psi v)
  -- The second Leibniz summand is `f_v ∪ (res_v g₁)`.
  have hdψ : cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 1 3 (by omega) fv
      ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
        (toInt (dualRep 𝔽 F S M)))).d 0 1 (c.psi v)) =
      cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 1 3 (by omega) fv
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) :=
    congrArg _ (c.hpsi v)
  -- `d h_v` is `f_v ∪ (res_v g₁)` by the global relation and restriction-cup compatibility.
  have hdh : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 hv =
      cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 1 3 rfl fv
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) := by
    rw [hhv, ContRepresentation.cochainsMap_f_d, c.hh]
    exact ContRepresentation.cochainsMap_cupCochain (localToGlobal F S v.1)
      (ksUnitsGlue F S v.1) (evalIntertwiner 𝔽 F S M) (evalIntertwinerLoc 𝔽 F S M v.1)
      (ksUnitsGlue_evalIntertwiner 𝔽 F S M v.1) 2 1 3 rfl
      ((toIntCochainEquiv M 2).symm c.f2) ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)
  rw [hsub, hleib, hdfv, hdψ, hdh]
  have hsgn : ((-1 : ℤ) ^ 2 : ℤ) = 1 := by norm_num
  rw [hsgn, one_smul, zero_add, sub_self]

variable (S) in
/-- **Blueprint §4**: the value `∑_{v ∈ S} inv_v [x_v]` of the pairing at the given
choices. -/
noncomputable def pairingValue (c : PairingChoices 𝔽 F S M x y) : AddCircle (1 : ℚ) :=
  ∑ v ∈ S.attach, localInvariantMap F v.1
    (cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c v) (d_xCocycle c v))

/-- Local triviality of `x` gives a local primitive for the restriction of its
representative: `res_v f₂ = d φ_v`. -/
lemma exists_local_primitive (c : PairingChoices 𝔽 F S M x y) (v : S)
    (hxv : ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x = 0) :
    ∃ φ1 : ↥((homogeneousCochains (TopRep.res (locToGlob F S v.1) M)).X 1),
      (homogeneousCochains (TopRep.res (locToGlob F S v.1) M)).d 1 2 φ1 =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) M))).f 2 c.f2 := by
  have h := map_cocycleClass (localToGlobal F S v.1)
    (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 c.f2 c.hf2
  rw [c.hf2x, hxv] at h
  exact (cocycleClass_eq_zero_iff _ 2 _ _).mp h.symm

/-- The `ℤ`-side restricted representative of `f` is a coboundary when `x` is locally
trivial. -/
lemma exists_local_primitive_int (c : PairingChoices 𝔽 F S M x y) (v : S)
    (hxv : ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x = 0) :
    ∃ φ1 : ↥((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).X 1),
      (homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 1 2 φ1 =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c.f2) := by
  obtain ⟨φ1, hφ1⟩ := exists_local_primitive c v hxv
  refine ⟨(toIntCochainEquiv (TopRep.res (locToGlob F S v.1) M) 1).symm φ1, ?_⟩
  have h1 := toIntCochainEquiv_symm_d (TopRep.res (locToGlob F S v.1) M) 1 φ1
  have h2 := toIntCochainEquiv_symm_cochainsMap (localToGlobal F S v.1) M 2 c.f2
  exact h1.trans ((congrArg _ hφ1).trans h2.symm)

/-- The class of the cup of a coboundary with a `0`-cochain vanishes. -/
lemma cocycleClass_cup_d_left (v : S)
    (φ1 : ↥((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).X 1))
    (θ : ↥((homogeneousCochains
      (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).X 0))
    (hθ : (homogeneousCochains
      (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 θ = 0)
    (hd : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
      (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 1 2 φ1) θ) = 0) :
    cocycleClass (algClosureUnitsRep F v.1) 2
      (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 1 2 φ1) θ)
      hd = 0 := by
  refine (cocycleClass_eq_zero_iff _ 2 _ _).2
    ⟨cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 0 1 rfl φ1 θ, ?_⟩
  exact (ContRepresentation.d_cupCochain_of_d_eq_zero (evalIntertwinerLoc 𝔽 F S M v.1)
    1 0 1 rfl φ1 hθ).symm

/-- The value does not depend on the choice of the global primitive `h₂` (given the other
choices are equal): the difference is a global `2`-cocycle in `K_S^×`, whose local
invariants sum to zero by the reciprocity input. -/
lemma pairingValue_congr_h (c c' : PairingChoices 𝔽 F S M x y)
    (hf : c.f2 = c'.f2) (hg : c.g1 = c'.g1) (hψ : c.psi = c'.psi) :
    pairingValue S c = pairingValue S c' := by
  have hzd : (homogeneousCochains (ksUnitsRep F S)).d 2 3 (c'.h2 - c.h2) = 0 := by
    have h1 : (homogeneousCochains (ksUnitsRep F S)).d 2 3 (c'.h2 - c.h2) =
        (homogeneousCochains (ksUnitsRep F S)).d 2 3 c'.h2 -
        (homogeneousCochains (ksUnitsRep F S)).d 2 3 c.h2 :=
      ((homogeneousCochains (ksUnitsRep F S)).d 2 3).hom.map_sub _ _
    rw [h1, c'.hh, c.hh, hf, hg, sub_self]
  have hxv : ∀ v : S, xCocycle c v - xCocycle c' v =
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c'.h2 - c.h2) := by
    intro v
    have h2 : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c'.h2 - c.h2) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c'.h2 -
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c.h2 :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2).hom.map_sub _ _
    rw [h2]
    unfold xCocycle
    rw [hf, hψ]
    abel
  have hcls : ∀ v : S,
      cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c v) (d_xCocycle c v) -
        cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c' v) (d_xCocycle c' v) =
      ContinuousCohomology.map (localToGlobal F S v.1) (ksUnitsGlue F S v.1) 2
        (cocycleClass (ksUnitsRep F S) 2 (c'.h2 - c.h2) hzd) := by
    intro v
    rw [map_cocycleClass (localToGlobal F S v.1) (ksUnitsGlue F S v.1) 2 _ hzd,
      ← cocycleClass_sub (algClosureUnitsRep F v.1) 2 (xCocycle c v) (xCocycle c' v)
        (d_xCocycle c v) (d_xCocycle c' v)]
    exact cocycleClass_congr (algClosureUnitsRep F v.1) 2 (hxv v) _
  have hsum : pairingValue S c - pairingValue S c' =
      ∑ v ∈ S.attach, localInvariantMap F v.1
        (ContinuousCohomology.map (localToGlobal F S v.1) (ksUnitsGlue F S v.1) 2
          (cocycleClass (ksUnitsRep F S) 2 (c'.h2 - c.h2) hzd)) := by
    unfold pairingValue
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← map_sub (localInvariantMap F v.1), hcls v]
  exact sub_eq_zero.mp
    (hsum.trans (sum_localInvariantMap_map_eq_zero F S
      (cocycleClass (ksUnitsRep F S) 2 (c'.h2 - c.h2) hzd)))

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- The value does not depend on the choice of the local primitives `ψ_v` (given the other
choices are equal): the local cocycles change by `f_v ∪ θ_v` with `θ_v` a `0`-cocycle and
`f_v` a coboundary (local triviality of `x`), hence by a coboundary. -/
lemma pairingValue_congr_psi (c c' : PairingChoices 𝔽 F S M x y)
    (hx : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x = 0)
    (hf : c.f2 = c'.f2) (hg : c.g1 = c'.g1) (hh2 : c.h2 = c'.h2) :
    pairingValue S c = pairingValue S c' := by
  unfold pairingValue
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  refine congrArg (localInvariantMap F v.1) ?_
  obtain ⟨φ1, hφ1⟩ := exists_local_primitive_int c v (hx v)
  have hθ : (homogeneousCochains
      (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
      (c.psi v - c'.psi v) = 0 := by
    have h1 : (homogeneousCochains
        (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
        (c.psi v - c'.psi v) =
        (homogeneousCochains
          (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (c.psi v) -
        (homogeneousCochains
          (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (c'.psi v) :=
      ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
        (toInt (dualRep 𝔽 F S M)))).d 0 1).hom.map_sub _ _
    rw [h1, c.hpsi v, c'.hpsi v, hg, sub_self]
  refine cocycleClass_eq_of_sub_coboundary (algClosureUnitsRep F v.1) 2
    (xCocycle c v) (xCocycle c' v) (d_xCocycle c v) (d_xCocycle c' v)
    (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 0 1 rfl φ1 (c.psi v - c'.psi v)) ?_
  have hcupd := ContRepresentation.d_cupCochain_of_d_eq_zero
    (evalIntertwinerLoc 𝔽 F S M v.1) 1 0 1 rfl φ1 hθ
  rw [hcupd.symm, hφ1]
  have hcup_sub := ContRepresentation.cupCochain_sub_right'
    (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
    ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
        ((toIntCochainEquiv M 2).symm c.f2)) (c.psi v) (c'.psi v)
  rw [hcup_sub]
  unfold xCocycle
  rw [hf, hh2]
  abel

/-- Modify the choices along a change of representative of `g`: for `g₁' = g₁ + dη`, the new
global primitive is `h₂ + f₂ ∪ η` and the new local primitives are `ψ_v + res_v η`. The
local cocycles `x_v` are unchanged **on the nose**. -/
noncomputable def PairingChoices.moveG (c : PairingChoices 𝔽 F S M x y)
    (g1' : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 1))
    (hg1' : (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 g1' = 0)
    (hg1y' : cocycleClass (dualRep 𝔽 F S M) 1 g1' hg1' = y)
    (η : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 0))
    (hη : (homogeneousCochains (dualRep 𝔽 F S M)).d 0 1 η = g1' - c.g1) :
    PairingChoices 𝔽 F S M x y where
  f2 := c.f2
  hf2 := c.hf2
  hf2x := c.hf2x
  g1 := g1'
  hg1 := hg1'
  hg1y := hg1y'
  h2 := c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
    ((toIntCochainEquiv M 2).symm c.f2) ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)
  hh := by
    have hdη : (homogeneousCochains (toInt (dualRep 𝔽 F S M))).d 0 1
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η) =
        (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1' -
        (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1 := by
      rw [toIntCochainEquiv_symm_d, hη]
      exact map_sub (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1' c.g1
    have h1 := ContRepresentation.cupCochain_d_of_d_eq_zero (evalIntertwiner 𝔽 F S M)
      2 0 2 rfl ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η) (d_toInt_f2 c.f2 c.hf2)
    rw [hdη, ContRepresentation.cupCochain_sub_right'] at h1
    have hsgn : ((-1 : ℤ) ^ 2 : ℤ) = 1 := by norm_num
    rw [hsgn, one_smul] at h1
    have hadd : (homogeneousCochains (ksUnitsRep F S)).d 2 3
        (c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
          ((toIntCochainEquiv M 2).symm c.f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) =
        (homogeneousCochains (ksUnitsRep F S)).d 2 3 c.h2 +
        (homogeneousCochains (ksUnitsRep F S)).d 2 3
          (cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
            ((toIntCochainEquiv M 2).symm c.f2)
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) :=
      ((homogeneousCochains (ksUnitsRep F S)).d 2 3).hom.map_add _ _
    rw [hadd, c.hh, ← h1]
    abel
  psi := fun v ↦ c.psi v + (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
    (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
      ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)
  hpsi := fun v ↦ by
    have hdη : (homogeneousCochains (toInt (dualRep 𝔽 F S M))).d 0 1
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η) =
        (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1' -
        (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1 := by
      rw [toIntCochainEquiv_symm_d, hη]
      exact map_sub (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1' c.g1
    have hadd : (homogeneousCochains
        (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
        (c.psi v + (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) =
        (homogeneousCochains
          (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (c.psi v) +
        (homogeneousCochains
          (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
              ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) :=
      ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
        (toInt (dualRep 𝔽 F S M)))).d 0 1).hom.map_add _ _
    have hdres : (homogeneousCochains
        (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1') -
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1) := by
      rw [ContRepresentation.cochainsMap_f_d, hdη]
      exact ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1).hom.map_sub _ _
    rw [hadd, c.hpsi v, hdres]
    abel

@[simp] lemma PairingChoices.moveG_f2 (c : PairingChoices 𝔽 F S M x y) (g1' hg1' hg1y' η hη) :
    (c.moveG g1' hg1' hg1y' η hη).f2 = c.f2 := rfl

@[simp] lemma PairingChoices.moveG_g1 (c : PairingChoices 𝔽 F S M x y) (g1' hg1' hg1y' η hη) :
    (c.moveG g1' hg1' hg1y' η hη).g1 = g1' := rfl

@[simp] lemma PairingChoices.moveG_h2 (c : PairingChoices 𝔽 F S M x y) (g1' hg1' hg1y' η hη) :
    (c.moveG g1' hg1' hg1y' η hη).h2 =
      c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
        ((toIntCochainEquiv M 2).symm c.f2)
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η) := rfl

@[simp] lemma PairingChoices.moveG_psi (c : PairingChoices 𝔽 F S M x y) (g1' hg1' hg1y' η hη)
    (v : S) :
    (c.moveG g1' hg1' hg1y' η hη).psi v =
      c.psi v + (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η) := rfl

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- The local cocycles, hence the value, are unchanged by `moveG`. -/
lemma pairingValue_moveG (c : PairingChoices 𝔽 F S M x y)
    (g1' : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 1))
    (hg1' : (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 g1' = 0)
    (hg1y' : cocycleClass (dualRep 𝔽 F S M) 1 g1' hg1' = y)
    (η : ↥((homogeneousCochains (dualRep 𝔽 F S M)).X 0))
    (hη : (homogeneousCochains (dualRep 𝔽 F S M)).d 0 1 η = g1' - c.g1) :
    pairingValue S (c.moveG g1' hg1' hg1y' η hη) = pairingValue S c := by
  unfold pairingValue
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  refine congrArg (localInvariantMap F v.1) ?_
  have hxeq : xCocycle (c.moveG g1' hg1' hg1y' η hη) v = xCocycle c v := by
    unfold xCocycle
    rw [PairingChoices.moveG_f2, PairingChoices.moveG_h2, PairingChoices.moveG_psi]
    have hcupadd := ContRepresentation.cupCochain_add_right'
      (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c.f2))
      (c.psi v)
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η))
    have hres : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2
        (c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
          ((toIntCochainEquiv M 2).symm c.f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c.h2 +
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2
          (cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
            ((toIntCochainEquiv M 2).symm c.f2)
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2).hom.map_add _ _
    have hresC : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2
        (cupCochain (evalIntertwiner 𝔽 F S M) 2 0 2 rfl
          ((toIntCochainEquiv M 2).symm c.f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) =
        cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
              ((toIntCochainEquiv M 2).symm c.f2))
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 0
              ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)) :=
      ContRepresentation.cochainsMap_cupCochain (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1) (evalIntertwiner 𝔽 F S M) (evalIntertwinerLoc 𝔽 F S M v.1)
        (ksUnitsGlue_evalIntertwiner 𝔽 F S M v.1) 2 0 2 rfl
        ((toIntCochainEquiv M 2).symm c.f2) ((toIntCochainEquiv (dualRep 𝔽 F S M) 0).symm η)
    rw [hcupadd, hres, hresC]
    abel
  exact cocycleClass_congr (algClosureUnitsRep F v.1) 2 hxeq _

/-- Modify the choices along a change of representative of `f`: for `f₂' = f₂ + dξ`, the new
global primitive is `h₂ + ξ ∪ g₁`. The local cocycles change by a coboundary. -/
noncomputable def PairingChoices.moveF (c : PairingChoices 𝔽 F S M x y)
    (f2' : ↥((homogeneousCochains M).X 2))
    (hf2' : (homogeneousCochains M).d 2 3 f2' = 0)
    (hf2x' : cocycleClass M 2 f2' hf2' = x)
    (ξ : ↥((homogeneousCochains M).X 1))
    (hξ : (homogeneousCochains M).d 1 2 ξ = f2' - c.f2) :
    PairingChoices 𝔽 F S M x y where
  f2 := f2'
  hf2 := hf2'
  hf2x := hf2x'
  g1 := c.g1
  hg1 := c.hg1
  hg1y := c.hg1y
  h2 := c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
    ((toIntCochainEquiv M 1).symm ξ) ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)
  hh := by
    have hdξ : (homogeneousCochains (toInt M)).d 1 2 ((toIntCochainEquiv M 1).symm ξ) =
        (toIntCochainEquiv M 2).symm f2' - (toIntCochainEquiv M 2).symm c.f2 := by
      rw [toIntCochainEquiv_symm_d, hξ]
      exact map_sub (toIntCochainEquiv M 2).symm f2' c.f2
    have h1 := ContRepresentation.d_cupCochain_of_d_eq_zero (evalIntertwiner 𝔽 F S M)
      1 1 2 rfl ((toIntCochainEquiv M 1).symm ξ) (d_toInt_g1 c.g1 c.hg1)
    rw [hdξ, ContRepresentation.cupCochain_sub_left'] at h1
    have hadd : (homogeneousCochains (ksUnitsRep F S)).d 2 3
        (c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
          ((toIntCochainEquiv M 1).symm ξ)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) =
        (homogeneousCochains (ksUnitsRep F S)).d 2 3 c.h2 +
        (homogeneousCochains (ksUnitsRep F S)).d 2 3
          (cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
            ((toIntCochainEquiv M 1).symm ξ)
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) :=
      ((homogeneousCochains (ksUnitsRep F S)).d 2 3).hom.map_add _ _
    rw [hadd, c.hh, ← h1]
    abel
  psi := c.psi
  hpsi := c.hpsi

@[simp] lemma PairingChoices.moveF_f2 (c : PairingChoices 𝔽 F S M x y) (f2' hf2' hf2x' ξ hξ) :
    (c.moveF f2' hf2' hf2x' ξ hξ).f2 = f2' := rfl

@[simp] lemma PairingChoices.moveF_g1 (c : PairingChoices 𝔽 F S M x y) (f2' hf2' hf2x' ξ hξ) :
    (c.moveF f2' hf2' hf2x' ξ hξ).g1 = c.g1 := rfl

@[simp] lemma PairingChoices.moveF_h2 (c : PairingChoices 𝔽 F S M x y) (f2' hf2' hf2x' ξ hξ) :
    (c.moveF f2' hf2' hf2x' ξ hξ).h2 =
      c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
        ((toIntCochainEquiv M 1).symm ξ)
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1) := rfl

@[simp] lemma PairingChoices.moveF_psi (c : PairingChoices 𝔽 F S M x y) (f2' hf2' hf2x' ξ hξ) :
    (c.moveF f2' hf2' hf2x' ξ hξ).psi = c.psi := rfl

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- The local cocycles change by a coboundary under `moveF`, so the value is unchanged. -/
lemma pairingValue_moveF (c : PairingChoices 𝔽 F S M x y)
    (f2' : ↥((homogeneousCochains M).X 2))
    (hf2' : (homogeneousCochains M).d 2 3 f2' = 0)
    (hf2x' : cocycleClass M 2 f2' hf2' = x)
    (ξ : ↥((homogeneousCochains M).X 1))
    (hξ : (homogeneousCochains M).d 1 2 ξ = f2' - c.f2) :
    pairingValue S (c.moveF f2' hf2' hf2x' ξ hξ) = pairingValue S c := by
  unfold pairingValue
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  refine congrArg (localInvariantMap F v.1) ?_
  set ξv := (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
    (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 1
      ((toIntCochainEquiv M 1).symm ξ) with hξvdef
  -- The difference of the local cochains is the coboundary of `ξ_v ∪ ψ_v`.
  refine cocycleClass_eq_of_sub_coboundary (algClosureUnitsRep F v.1) 2 _ _
    (d_xCocycle _ v) (d_xCocycle c v)
    (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 0 1 rfl ξv (c.psi v)) ?_
  -- Leibniz: `d (ξ_v ∪ ψ_v) = (d ξ_v) ∪ ψ_v − ξ_v ∪ (d ψ_v)`.
  have hleib := ContRepresentation.cup_d_comm _ _ _ (evalIntertwinerLoc 𝔽 F S M v.1)
    1 0 1 rfl ξv (c.psi v)
  have hsgn : ((-1 : ℤ) ^ 1 • cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 1 2 (by omega) ξv
      ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
        (toInt (dualRep 𝔽 F S M)))).d 0 1 (c.psi v))) =
      -cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 1 2 (by omega) ξv
        ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
          (toInt (dualRep 𝔽 F S M)))).d 0 1 (c.psi v)) := by
    rw [pow_one, neg_smul, one_smul]
  rw [hsgn] at hleib
  -- `d ξ_v = f₂'_v − f₂_v`.
  have hdξv : (homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 1 2 ξv =
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm f2') -
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c.f2) := by
    have hdξ : (homogeneousCochains (toInt M)).d 1 2 ((toIntCochainEquiv M 1).symm ξ) =
        (toIntCochainEquiv M 2).symm f2' - (toIntCochainEquiv M 2).symm c.f2 := by
      rw [toIntCochainEquiv_symm_d, hξ]
      exact map_sub (toIntCochainEquiv M 2).symm f2' c.f2
    rw [hξvdef, ContRepresentation.cochainsMap_f_d, hdξ]
    exact ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2).hom.map_sub _ _
  -- The restriction of the correction term in `h₂`.
  have hressum : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (ksUnitsGlue F S v.1)).f 2
      (c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
        ((toIntCochainEquiv M 1).symm ξ)
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) =
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 c.h2 +
      cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 1 2 rfl ξv
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) := by
    have hadd : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2
        (c.h2 + cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
          ((toIntCochainEquiv M 1).symm ξ)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c.h2 +
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2
          (cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
            ((toIntCochainEquiv M 1).symm ξ)
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2).hom.map_add _ _
    have hresC : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2
        (cupCochain (evalIntertwiner 𝔽 F S M) 1 1 2 rfl
          ((toIntCochainEquiv M 1).symm ξ)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) =
        cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 1 1 2 rfl ξv
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
              ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)) := by
      rw [hξvdef]
      exact ContRepresentation.cochainsMap_cupCochain (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1) (evalIntertwiner 𝔽 F S M) (evalIntertwinerLoc 𝔽 F S M v.1)
        (ksUnitsGlue_evalIntertwiner 𝔽 F S M v.1) 1 1 2 rfl
        ((toIntCochainEquiv M 1).symm ξ) ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c.g1)
    rw [hadd, hresC]
  -- Split the cup against `f₂' − f₂` and assemble.
  have hcup_split := ContRepresentation.cupCochain_sub_left'
    (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
    ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
        ((toIntCochainEquiv M 2).symm f2'))
    ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
        ((toIntCochainEquiv M 2).symm c.f2)) (c.psi v)
  -- `d ψ_v = res_v g₁`.
  have hdψ := c.hpsi v
  unfold xCocycle
  rw [PairingChoices.moveF_f2, PairingChoices.moveF_h2, PairingChoices.moveF_psi, hressum,
    hleib, hdξv, hcup_split, hdψ]
  abel

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- **Well-definedness of the pairing** (blueprint §4, glossed there): the value depends
only on the classes `x` and `y`, not on the choices of representatives and primitives. Uses
the local triviality of `x` (for the `ψ`-step) and global reciprocity (for the `h`-step). -/
lemma pairingValue_congr
    (hx : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x = 0)
    (c c' : PairingChoices 𝔽 F S M x y) :
    pairingValue S c = pairingValue S c' := by
  -- Change the representative of `f`.
  have hfsub : cocycleClass M 2 (c'.f2 - c.f2)
      (by rw [map_sub, c'.hf2, c.hf2, sub_zero]) = 0 := by
    rw [cocycleClass_sub M 2 c'.f2 c.f2 c'.hf2 c.hf2, c.hf2x, c'.hf2x, sub_self]
  obtain ⟨ξ, hξ⟩ := (cocycleClass_eq_zero_iff M 2 _ _).mp hfsub
  set c₁ := c.moveF c'.f2 c'.hf2 c'.hf2x ξ hξ with hc₁
  -- Change the representative of `g`.
  have hgsub : cocycleClass (dualRep 𝔽 F S M) 1 (c'.g1 - c₁.g1)
      (by rw [map_sub, c'.hg1, c₁.hg1, sub_zero]) = 0 := by
    rw [cocycleClass_sub (dualRep 𝔽 F S M) 1 c'.g1 c₁.g1 c'.hg1 c₁.hg1, c₁.hg1y, c'.hg1y,
      sub_self]
  obtain ⟨η, hη⟩ := (cocycleClass_eq_zero_iff (dualRep 𝔽 F S M) 1 _ _).mp hgsub
  set c₂ := c₁.moveG c'.g1 c'.hg1 c'.hg1y η hη with hc₂
  -- Change the local primitives, then the global primitive.
  set c₃ : PairingChoices 𝔽 F S M x y :=
    { f2 := c'.f2
      hf2 := c'.hf2
      hf2x := c'.hf2x
      g1 := c'.g1
      hg1 := c'.hg1
      hg1y := c'.hg1y
      h2 := c₂.h2
      hh := c₂.hh
      psi := c'.psi
      hpsi := c'.hpsi } with hc₃
  calc pairingValue S c = pairingValue S c₁ := (pairingValue_moveF c _ _ _ ξ hξ).symm
    _ = pairingValue S c₂ := (pairingValue_moveG c₁ _ _ _ η hη).symm
    _ = pairingValue S c₃ := pairingValue_congr_psi c₂ c₃ hx rfl rfl rfl
    _ = pairingValue S c' := pairingValue_congr_h c₃ c' rfl rfl rfl

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- **Blueprint §4** (existence of the choices): given that the primes dividing `#M` lie in
`S` (so that the `H³` lemma applies) and that `y` is locally trivial, the cochain-level
choices underlying the pairing exist. -/
lemma pairingChoices_nonempty
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (hy : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y = 0) :
    Nonempty (PairingChoices 𝔽 F S M x y) := by
  obtain ⟨f2, hf2, hf2x⟩ := cocycleClass_surjective M 2 x
  obtain ⟨g1, hg1, hg1y⟩ := cocycleClass_surjective (dualRep 𝔽 F S M) 1 y
  -- The cup of the two representatives is a `3`-cocycle.
  have hcup : (homogeneousCochains (ksUnitsRep F S)).d 3 4
      (cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
        ((toIntCochainEquiv M 2).symm f2)
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1)) = 0 :=
    ContRepresentation.d_cupCochain_eq_zero (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
      (d_toInt_f2 f2 hf2) (d_toInt_g1 g1 hg1)
  -- It is `#M`-torsion at the cochain level, since `M` is.
  have hsmul : (Nat.card ↥M) • cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
      ((toIntCochainEquiv M 2).symm f2)
      ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1) = 0 := by
    have h1 : (Nat.card ↥M) • ((toIntCochainEquiv M 2).symm f2) = 0 :=
      nsmul_homogeneousCochains_eq_zero (toInt M) (Nat.card ↥M)
        (fun z ↦ card_nsmul_eq_zero') 2 ((toIntCochainEquiv M 2).symm f2)
    have h2 := congr($(_root_.map_nsmul (cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl).hom
      (Nat.card ↥M) ((toIntCochainEquiv M 2).symm f2))
      ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1))
    have h3 : cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
        ((Nat.card ↥M) • ((toIntCochainEquiv M 2).symm f2))
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1) =
        (Nat.card ↥M) • cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
          ((toIntCochainEquiv M 2).symm f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1) := h2
    rw [h1] at h3
    rw [← h3]
    exact ContRepresentation.cupCochain_zero_apply (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
      ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1)
  -- Hence its class is `#M`-torsion, hence zero by the `H³` lemma.
  have hclass : (Nat.card ↥M) • cocycleClass (ksUnitsRep F S) 3
      (cupCochain (evalIntertwiner 𝔽 F S M) 2 1 3 rfl
        ((toIntCochainEquiv M 2).symm f2)
        ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1)) hcup = 0 := by
    rw [← cocycleClass_nsmul (ksUnitsRep F S) 3 (Nat.card ↥M) _ hcup]
    exact (cocycleClass_congr (ksUnitsRep F S) 3 hsmul _).trans
      (cocycleClass_zero (ksUnitsRep F S) 3)
  have hzero := eq_zero_of_smul_continuousCohomology_three_ksUnitsRep F S (Nat.card ↥M) hS
    (cocycleClass (ksUnitsRep F S) 3 _ hcup) hclass
  obtain ⟨h2, hh⟩ := (cocycleClass_eq_zero_iff (ksUnitsRep F S) 3 _ hcup).mp hzero
  -- The local primitives, from local triviality of `y`.
  have hψ : ∀ v : S, ∃ ψ : ↥((homogeneousCochains
      (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).X 0),
      (homogeneousCochains
        (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 ψ =
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm g1) := by
    intro v
    have h := map_cocycleClass (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 g1 hg1
    rw [hg1y, hy v] at h
    obtain ⟨ψF, hψF⟩ := (cocycleClass_eq_zero_iff _ 1 _ _).mp h.symm
    refine ⟨(toIntCochainEquiv (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M)) 0).symm
      ψF, ?_⟩
    have h1 := toIntCochainEquiv_symm_d
      (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M)) 0 ψF
    have h2 := toIntCochainEquiv_symm_cochainsMap (localToGlobal F S v.1)
      (dualRep 𝔽 F S M) 1 g1
    exact h1.trans ((congrArg _ hψF).trans h2.symm)
  exact ⟨⟨f2, hf2, hf2x, g1, hg1, hg1y, h2, hh, fun v ↦ (hψ v).choose,
    fun v ↦ (hψ v).choose_spec⟩⟩

/-- **Blueprint §4**: the pairing value `⟨x, y⟩ = ∑_{v ∈ S} inv_v [x_v]`, defined through an
arbitrary choice of the cochain-level data. -/
noncomputable def kerPairingFun
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (x₀ : ↥(continuousCohomology 2 M)) (y₀ : ↥(continuousCohomology 1 (dualRep 𝔽 F S M)))
    (hy : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y₀ = 0) :
    AddCircle (1 : ℚ) :=
  pairingValue S (pairingChoices_nonempty (x := x₀) (y := y₀) hS hy).some

/-- The pairing value computed at any system of choices. -/
lemma kerPairingFun_eq
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (x₀ : ↥(continuousCohomology 2 M)) (y₀ : ↥(continuousCohomology 1 (dualRep 𝔽 F S M)))
    (hx : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x₀ = 0)
    (hy : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y₀ = 0)
    (c : PairingChoices 𝔽 F S M x₀ y₀) :
    kerPairingFun hS x₀ y₀ hy = pairingValue S c :=
  pairingValue_congr hx _ c

set_option maxHeartbeats 3200000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- The pairing is additive in the second argument. -/
lemma kerPairingFun_add_right
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (x₀ : ↥(continuousCohomology 2 M))
    (y₁ y₂ : ↥(continuousCohomology 1 (dualRep 𝔽 F S M)))
    (hx : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x₀ = 0)
    (hy₁ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y₁ = 0)
    (hy₂ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y₂ = 0)
    (hy₁₂ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 (y₁ + y₂) = 0) :
    kerPairingFun hS x₀ (y₁ + y₂) hy₁₂ =
      kerPairingFun hS x₀ y₁ hy₁ + kerPairingFun hS x₀ y₂ hy₂ := by
  set c₁ := (pairingChoices_nonempty (x := x₀) (y := y₁) hS hy₁).some with hc₁
  set c₂ := (pairingChoices_nonempty (x := x₀) (y := y₂) hS hy₂).some with hc₂
  -- Align the representatives of `x₀`.
  have hfsub : cocycleClass M 2 (c₁.f2 - c₂.f2)
      (by rw [map_sub, c₁.hf2, c₂.hf2, sub_zero]) = 0 := by
    rw [cocycleClass_sub M 2 c₁.f2 c₂.f2 c₁.hf2 c₂.hf2, c₁.hf2x, c₂.hf2x, sub_self]
  obtain ⟨ξ, hξ⟩ := (cocycleClass_eq_zero_iff M 2 _ _).mp hfsub
  set c₂' := c₂.moveF c₁.f2 c₁.hf2 c₁.hf2x ξ hξ with hc₂'
  have hf2eq : c₂'.f2 = c₁.f2 := by rw [hc₂']; rfl
  -- The combined choice for `y₁ + y₂`.
  set cSum : PairingChoices 𝔽 F S M x₀ (y₁ + y₂) :=
    { f2 := c₁.f2
      hf2 := c₁.hf2
      hf2x := c₁.hf2x
      g1 := c₁.g1 + c₂'.g1
      hg1 := by
        have h1 : (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 (c₁.g1 + c₂'.g1) =
            (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 c₁.g1 +
            (homogeneousCochains (dualRep 𝔽 F S M)).d 1 2 c₂'.g1 :=
          ((homogeneousCochains (dualRep 𝔽 F S M)).d 1 2).hom.map_add _ _
        rw [h1, c₁.hg1, c₂'.hg1, add_zero]
      hg1y := by
        rw [cocycleClass_add (dualRep 𝔽 F S M) 1 c₁.g1 c₂'.g1 c₁.hg1 c₂'.hg1, c₁.hg1y,
          c₂'.hg1y]
      h2 := c₁.h2 + c₂'.h2
      hh := by
        have h1 : (homogeneousCochains (ksUnitsRep F S)).d 2 3 (c₁.h2 + c₂'.h2) =
            (homogeneousCochains (ksUnitsRep F S)).d 2 3 c₁.h2 +
            (homogeneousCochains (ksUnitsRep F S)).d 2 3 c₂'.h2 :=
          ((homogeneousCochains (ksUnitsRep F S)).d 2 3).hom.map_add _ _
        have h2 : (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm (c₁.g1 + c₂'.g1) =
            (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1 +
            (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₂'.g1 :=
          map_add (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm _ _
        have h3 := ContRepresentation.cupCochain_add_right' (evalIntertwiner 𝔽 F S M)
          2 1 3 rfl ((toIntCochainEquiv M 2).symm c₁.f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₂'.g1)
        rw [h1, c₁.hh, c₂'.hh, hf2eq, h2, h3]
      psi := fun v ↦ c₁.psi v + c₂'.psi v
      hpsi := fun v ↦ by
        have h1 : (homogeneousCochains
            (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
            (c₁.psi v + c₂'.psi v) =
            (homogeneousCochains
              (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (c₁.psi v) +
            (homogeneousCochains
              (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
              (c₂'.psi v) :=
          ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
            (toInt (dualRep 𝔽 F S M)))).d 0 1).hom.map_add _ _
        have h2 : (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm (c₁.g1 + c₂'.g1) =
            (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1 +
            (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₂'.g1 :=
          map_add (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm _ _
        have h3 : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
            ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1 +
              (toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₂'.g1) =
            (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
              (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
              ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1) +
            (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
              (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1
              ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₂'.g1) :=
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M))))).f 1).hom.map_add
            _ _
        rw [h1, c₁.hpsi v, c₂'.hpsi v, h2, h3] } with hcSum
  -- The local cochains split on the nose.
  have hsplit : ∀ v : S, xCocycle cSum v = xCocycle c₁ v + xCocycle c₂' v := by
    intro v
    unfold xCocycle
    have hψadd := ContRepresentation.cupCochain_add_right'
      (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c₁.f2))
      (c₁.psi v) (c₂'.psi v)
    have hglue : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c₁.h2 + c₂'.h2) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c₁.h2 +
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c₂'.h2 :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2).hom.map_add _ _
    show cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c₁.f2))
        (c₁.psi v + c₂'.psi v) -
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c₁.h2 + c₂'.h2) = _
    rw [hψadd, hglue, hf2eq]
    abel
  -- Sum the values.
  have hval : pairingValue S cSum = pairingValue S c₁ + pairingValue S c₂' := by
    unfold pairingValue
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← map_add (localInvariantMap F v.1)]
    refine congrArg (localInvariantMap F v.1) ?_
    rw [← cocycleClass_add (algClosureUnitsRep F v.1) 2 (xCocycle c₁ v) (xCocycle c₂' v)
      (d_xCocycle c₁ v) (d_xCocycle c₂' v)]
    exact cocycleClass_congr (algClosureUnitsRep F v.1) 2 (hsplit v) _
  calc kerPairingFun hS x₀ (y₁ + y₂) hy₁₂ = pairingValue S cSum :=
        kerPairingFun_eq hS x₀ (y₁ + y₂) hx hy₁₂ cSum
    _ = pairingValue S c₁ + pairingValue S c₂' := hval
    _ = pairingValue S c₁ + pairingValue S c₂ := by
        rw [pairingValue_moveF c₂ c₁.f2 c₁.hf2 c₁.hf2x ξ hξ]
    _ = kerPairingFun hS x₀ y₁ hy₁ + kerPairingFun hS x₀ y₂ hy₂ := rfl

set_option maxHeartbeats 6400000 in
-- the cochain-level computation unifies large types across the `TopRep.of` and `𝔽`/`ℤ` seams
/-- The pairing is additive in the first argument. -/
lemma kerPairingFun_add_left
    (hS : ∀ w : HeightOneSpectrum (RingOfIntegers F),
      (Nat.card ↥M : RingOfIntegers F) ∈ w.asIdeal → w ∈ S)
    (x₁ x₂ : ↥(continuousCohomology 2 M))
    (y₀ : ↥(continuousCohomology 1 (dualRep 𝔽 F S M)))
    (hx₁ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x₁ = 0)
    (hx₂ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 x₂ = 0)
    (hx₁₂ : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) M)) 2 (x₁ + x₂) = 0)
    (hy : ∀ v : S, ContinuousCohomology.map (localToGlobal F S v.1)
      (𝟙 (TopRep.res (locToGlob F S v.1) (dualRep 𝔽 F S M))) 1 y₀ = 0) :
    kerPairingFun hS (x₁ + x₂) y₀ hy =
      kerPairingFun hS x₁ y₀ hy + kerPairingFun hS x₂ y₀ hy := by
  set c₁ := (pairingChoices_nonempty (x := x₁) (y := y₀) hS hy).some with hc₁
  set c₂ := (pairingChoices_nonempty (x := x₂) (y := y₀) hS hy).some with hc₂
  -- Align the representatives of `y₀`.
  have hgsub : cocycleClass (dualRep 𝔽 F S M) 1 (c₁.g1 - c₂.g1)
      (by rw [map_sub, c₁.hg1, c₂.hg1, sub_zero]) = 0 := by
    rw [cocycleClass_sub (dualRep 𝔽 F S M) 1 c₁.g1 c₂.g1 c₁.hg1 c₂.hg1, c₁.hg1y, c₂.hg1y,
      sub_self]
  obtain ⟨η, hη⟩ := (cocycleClass_eq_zero_iff (dualRep 𝔽 F S M) 1 _ _).mp hgsub
  set c₂' := c₂.moveG c₁.g1 c₁.hg1 c₁.hg1y η hη with hc₂'
  have hg1eq : c₂'.g1 = c₁.g1 := by rw [hc₂']; rfl
  have hf2eq : c₂'.f2 = c₂.f2 := by rw [hc₂']; rfl
  -- The combined choice for `x₁ + x₂`.
  set cSum : PairingChoices 𝔽 F S M (x₁ + x₂) y₀ :=
    { f2 := c₁.f2 + c₂'.f2
      hf2 := by
        have h1 : (homogeneousCochains M).d 2 3 (c₁.f2 + c₂'.f2) =
            (homogeneousCochains M).d 2 3 c₁.f2 + (homogeneousCochains M).d 2 3 c₂'.f2 :=
          ((homogeneousCochains M).d 2 3).hom.map_add _ _
        rw [h1, c₁.hf2, c₂'.hf2, add_zero]
      hf2x := by
        rw [cocycleClass_add M 2 c₁.f2 c₂'.f2 c₁.hf2 c₂'.hf2, c₁.hf2x]
        have h := (cocycleClass_congr M 2 hf2eq c₂'.hf2).trans c₂.hf2x
        rw [h]
      g1 := c₁.g1
      hg1 := c₁.hg1
      hg1y := c₁.hg1y
      h2 := c₁.h2 + c₂'.h2
      hh := by
        have h1 : (homogeneousCochains (ksUnitsRep F S)).d 2 3 (c₁.h2 + c₂'.h2) =
            (homogeneousCochains (ksUnitsRep F S)).d 2 3 c₁.h2 +
            (homogeneousCochains (ksUnitsRep F S)).d 2 3 c₂'.h2 :=
          ((homogeneousCochains (ksUnitsRep F S)).d 2 3).hom.map_add _ _
        have h2 : (toIntCochainEquiv M 2).symm (c₁.f2 + c₂'.f2) =
            (toIntCochainEquiv M 2).symm c₁.f2 + (toIntCochainEquiv M 2).symm c₂'.f2 :=
          map_add (toIntCochainEquiv M 2).symm _ _
        have h3 := ContRepresentation.cupCochain_add_left' (evalIntertwiner 𝔽 F S M)
          2 1 3 rfl ((toIntCochainEquiv M 2).symm c₁.f2)
          ((toIntCochainEquiv M 2).symm c₂'.f2)
          ((toIntCochainEquiv (dualRep 𝔽 F S M) 1).symm c₁.g1)
        rw [h1, c₁.hh, c₂'.hh, hg1eq, h2, h3]
      psi := c₁.psi
      hpsi := c₁.hpsi } with hcSum
  -- The cross-term: the local cochains split up to `f₂_v ∪ (ψ₁ − ψ₂')`.
  have hsplit : ∀ v : S, xCocycle cSum v = (xCocycle c₁ v + xCocycle c₂' v) +
      cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c₂'.f2))
        (c₁.psi v - c₂'.psi v) := by
    intro v
    unfold xCocycle
    have h2 : (toIntCochainEquiv M 2).symm (c₁.f2 + c₂'.f2) =
        (toIntCochainEquiv M 2).symm c₁.f2 + (toIntCochainEquiv M 2).symm c₂'.f2 :=
      map_add (toIntCochainEquiv M 2).symm _ _
    have h3 : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
        ((toIntCochainEquiv M 2).symm c₁.f2 + (toIntCochainEquiv M 2).symm c₂'.f2) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c₁.f2) +
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c₂'.f2) :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2).hom.map_add _ _
    have h4 := ContRepresentation.cupCochain_add_left' (evalIntertwinerLoc 𝔽 F S M v.1)
      2 0 2 rfl
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c₁.f2))
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c₂'.f2))
      (c₁.psi v)
    have h5 := ContRepresentation.cupCochain_sub_right' (evalIntertwinerLoc 𝔽 F S M v.1)
      2 0 2 rfl
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
          ((toIntCochainEquiv M 2).symm c₂'.f2))
      (c₁.psi v) (c₂'.psi v)
    have hglue : (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c₁.h2 + c₂'.h2) =
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c₁.h2 +
        (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (ksUnitsGlue F S v.1)).f 2 c₂'.h2 :=
      ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2).hom.map_add _ _
    show cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm (c₁.f2 + c₂'.f2)))
        (c₁.psi v) -
      (ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
        (ksUnitsGlue F S v.1)).f 2 (c₁.h2 + c₂'.h2) = _
    rw [h2, h3, h4, h5, hglue]
    abel
  -- The cross-term has trivial class.
  have hcross : ∀ v : S,
      ∀ hd : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
        (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
              ((toIntCochainEquiv M 2).symm c₂'.f2))
          (c₁.psi v - c₂'.psi v)) = 0,
      cocycleClass (algClosureUnitsRep F v.1) 2
        (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
              ((toIntCochainEquiv M 2).symm c₂'.f2))
          (c₁.psi v - c₂'.psi v)) hd = 0 := by
    intro v hd
    obtain ⟨φ1, hφ1⟩ := exists_local_primitive_int c₂' v (hx₂ v)
    have hθ : (homogeneousCochains
        (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
        (c₁.psi v - c₂'.psi v) = 0 := by
      have h1 : (homogeneousCochains
          (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
          (c₁.psi v - c₂'.psi v) =
          (homogeneousCochains
            (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1 (c₁.psi v) -
          (homogeneousCochains
            (TopRep.res (locToGlob F S v.1) (toInt (dualRep 𝔽 F S M)))).d 0 1
            (c₂'.psi v) :=
        ((homogeneousCochains (TopRep.res (locToGlob F S v.1)
          (toInt (dualRep 𝔽 F S M)))).d 0 1).hom.map_sub _ _
      rw [h1, c₁.hpsi v, c₂'.hpsi v, hg1eq, sub_self]
    have hcongr : cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
        ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
          (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
            ((toIntCochainEquiv M 2).symm c₂'.f2))
        (c₁.psi v - c₂'.psi v) =
        cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
          ((homogeneousCochains (TopRep.res (locToGlob F S v.1) (toInt M))).d 1 2 φ1)
          (c₁.psi v - c₂'.psi v) := by
      rw [hφ1]
    rw [cocycleClass_congr (algClosureUnitsRep F v.1) 2 hcongr hd]
    exact cocycleClass_cup_d_left v φ1 (c₁.psi v - c₂'.psi v) hθ _
  -- Sum the values.
  have hval : pairingValue S cSum = pairingValue S c₁ + pairingValue S c₂' := by
    unfold pairingValue
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← map_add (localInvariantMap F v.1)]
    refine congrArg (localInvariantMap F v.1) ?_
    have hd3 : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
        (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
          ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
            (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
              ((toIntCochainEquiv M 2).symm c₂'.f2))
          (c₁.psi v - c₂'.psi v)) = 0 := by
      have h1 : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle cSum v) =
          0 := d_xCocycle cSum v
      rw [hsplit v] at h1
      have h2 : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
          ((xCocycle c₁ v + xCocycle c₂' v) +
            cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
              ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
                (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
                  ((toIntCochainEquiv M 2).symm c₂'.f2))
              (c₁.psi v - c₂'.psi v)) =
          ((homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle c₁ v) +
            (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle c₂' v)) +
          (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
            (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
              ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
                (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
                  ((toIntCochainEquiv M 2).symm c₂'.f2))
              (c₁.psi v - c₂'.psi v)) := by
        have ha := ((homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3).hom.map_add
          (xCocycle c₁ v + xCocycle c₂' v)
          (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
            ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
              (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
                ((toIntCochainEquiv M 2).symm c₂'.f2))
            (c₁.psi v - c₂'.psi v))
        have hb := ((homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3).hom.map_add
          (xCocycle c₁ v) (xCocycle c₂' v)
        rw [ha, hb]
      rw [h2, d_xCocycle c₁ v, d_xCocycle c₂' v, add_zero, zero_add] at h1
      exact h1
    calc cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle cSum v) (d_xCocycle cSum v) =
        cocycleClass (algClosureUnitsRep F v.1) 2
          ((xCocycle c₁ v + xCocycle c₂' v) +
            cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
              ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
                (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
                  ((toIntCochainEquiv M 2).symm c₂'.f2))
              (c₁.psi v - c₂'.psi v))
          (by
            have := d_xCocycle cSum v
            rwa [hsplit v] at this) :=
        cocycleClass_congr (algClosureUnitsRep F v.1) 2 (hsplit v) _
      _ = cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c₁ v + xCocycle c₂' v)
            (by
              have h1 : (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
                  (xCocycle c₁ v + xCocycle c₂' v) =
                  (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3 (xCocycle c₁ v) +
                  (homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3
                    (xCocycle c₂' v) :=
                ((homogeneousCochains (algClosureUnitsRep F v.1)).d 2 3).hom.map_add _ _
              rw [h1, d_xCocycle c₁ v, d_xCocycle c₂' v, add_zero]) +
          cocycleClass (algClosureUnitsRep F v.1) 2
            (cupCochain (evalIntertwinerLoc 𝔽 F S M v.1) 2 0 2 rfl
              ((ContinuousCohomology.cochainsMap (localToGlobal F S v.1)
                (𝟙 (TopRep.res (locToGlob F S v.1) (toInt M)))).f 2
                  ((toIntCochainEquiv M 2).symm c₂'.f2))
              (c₁.psi v - c₂'.psi v)) hd3 :=
        cocycleClass_add (algClosureUnitsRep F v.1) 2 _ _ _ hd3
      _ = cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c₁ v) (d_xCocycle c₁ v) +
          cocycleClass (algClosureUnitsRep F v.1) 2 (xCocycle c₂' v) (d_xCocycle c₂' v) := by
        rw [hcross v hd3, add_zero]
        exact cocycleClass_add (algClosureUnitsRep F v.1) 2 (xCocycle c₁ v)
          (xCocycle c₂' v) (d_xCocycle c₁ v) (d_xCocycle c₂' v)
  calc kerPairingFun hS (x₁ + x₂) y₀ hy = pairingValue S cSum :=
        kerPairingFun_eq hS (x₁ + x₂) y₀ hx₁₂ hy cSum
    _ = pairingValue S c₁ + pairingValue S c₂' := hval
    _ = pairingValue S c₁ + pairingValue S c₂ := by
        rw [pairingValue_moveG c₂ c₁.g1 c₁.hg1 c₁.hg1y η hη]
    _ = kerPairingFun hS x₁ y₀ hy + kerPairingFun hS x₂ y₀ hy := rfl

end NumberField.PoitouTate
