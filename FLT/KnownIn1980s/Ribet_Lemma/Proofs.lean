/-
Copyright (c) 2026 Bryan Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Feng, Bryan Hu, Y. Samanda Zhang
-/
module

public import FLT.KnownIn1980s.Ribet_Lemma.Defs
public import FLT.Slop.Ribet_Lemma.Brauer_Nesbitt
public import FLT.Slop.Ribet_Lemma.Ribet_Lemma
public import FLT.Slop.Ribet_Lemma.stable_lattices

/-!
# Proofs for the public Ribet's-lemma statements

This file imports the AI-generated development in `FLT.Slop.Ribet_Lemma` and
proves copies of the public statements from
`FLT.KnownIn1980s.Ribet_Lemma.Defs`.
-/

@[expose] public section

open IsLocalRing

namespace StableLattice

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]
variable {G : Type*} [Group G]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
theorem exists_isStableLattice_proof [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    (hopen : IsOpen (latticeStabilizer ρ Λ₀ : Set G)) :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ :=
  exists_isStableLattice_slop ρ Λ₀ hopen

omit [FiniteDimensional K V] in
theorem hasSemisimplification_independent_of_lattice_proof
    (ρ : Representation K G V) (hdim : Module.finrank K V = 2)
    {Λ Λ' : Submodule O V}
    (h : IsStableLattice ρ Λ) (h' : IsStableLattice ρ Λ')
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ h.stable) φ₁ φ₂) :
    HasSemisimplification (reducedRep ρ Λ' h'.stable) φ₁ φ₂ :=
  hasSemisimplification_independent_of_lattice_slop ρ hdim h h' φ₁ φ₂ hss

omit [FiniteDimensional K V] in
theorem ribet_lemma_proof [IsAdicComplete (maximalIdeal O) O]
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hdim : Module.finrank K V = 2)
    (Λ₀ : Submodule O V) (h₀ : IsStableLattice ρ Λ₀)
    (φ₁ φ₂ : G →* (ResidueField O)ˣ)
    (hss : HasSemisimplification (reducedRep ρ Λ₀ h₀.stable) φ₁ φ₂) :
    ∃ (Λ : Submodule O V) (h : IsStableLattice ρ Λ),
      IsExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ ∧
      ¬ IsSplitExtensionOf (reducedRep ρ Λ h.stable) φ₁ φ₂ :=
  ribet_lemma_slop ρ hdim Λ₀ h₀ φ₁ φ₂ hss

end StableLattice
