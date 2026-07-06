import Mathlib

/-!
# `G`-stable lattices in representations over the fraction field of a DVR

Foundational file of this directory, whose goal is Ribet's lemma
(Ribet, Invent. Math. 34 (1976), Prop. 2.1).  The directory is one linear
development, with sections numbered across the three files:

* §1–4 (`stable_lattices.lean`): lattices, reduction mod `𝔪`, stable lattices
  and reduced representations, existence of stable lattices;
* §5–6 (`Brauer_Nesbitt.lean`): extensions of characters in dimension 2;
  independence of the reduction from the lattice (Brauer–Nesbitt);
* §7–9 (`Ribet_Lemma.lean`): lattice modification (the engine of the proof),
  Ribet's lemma itself, concluding remarks.

Setting: `O` is a DVR with fraction field `K` and residue field `F = O ⧸ 𝔪`,
and `V` is a finite-dimensional `K`-vector space with a representation `ρ` of a
group `G`.  This file provides:

* complements to Mathlib's lattice API `Submodule.IsLattice`
  (`Mathlib.Algebra.Module.Lattice`): scaling elements and lattices into a
  lattice, images under `K`-automorphisms, existence;
* `StableLattice.Reduction O V Λ` — the reduction `Λ ⧸ 𝔪Λ` as a vector space
  over the residue field;
* `StableLattice.Stabilizes ρ Λ` and `StableLattice.IsStableLattice ρ Λ` —
  `G`-stability, and `G`-stable lattices;
* `StableLattice.reducedRep` — the induced representation of `G` on `Λ ⧸ 𝔪Λ`;
* `StableLattice.exists_isStableLattice` — existence of a stable lattice when
  `G` is compact and some lattice has open stabilizer.

## Design decisions

* A lattice is Mathlib's `Submodule.IsLattice K Λ`: a finitely generated
  `O`-submodule of `V` (with `V` an `O`-module via `IsScalarTower O K V`) which
  spans `V` over `K`.  Mathlib already provides `Submodule.IsLattice.sup`,
  `.inf`, `.smul` (scaling by `Kˣ`), `.free` and `.rank'`, so only the missing
  glue is stated here.
* Stability and (in `Brauer_Nesbitt.lean`) "acts by the character `φ`" are
  phrased directly with submodules and pointwise conditions, rather than
  through `MonoidAlgebra K G`-modules / `Representation.asModule`.  This keeps
  the files self-contained; a final refactor could provide the dictionary
  (e.g. via Mathlib's `Subrepresentation`).
* The residue-field module structure on `Λ ⧸ 𝔪Λ` is *not* an axiom: it is
  Mathlib's `O ⧸ I`-module instance on `M ⧸ I • ⊤` (from
  `Mathlib.Algebra.Module.Torsion.Basic`), transported along the definitional
  equality `ResidueField O = O ⧸ 𝔪`.
* Topology appears only where genuinely needed.  The averaging argument for
  existence of stable lattices is purely algebraic
  (`exists_isStableLattice_of_finiteIndex`, assuming the stabilizer has finite
  index); compactness of `G` and openness of the stabilizer enter only in the
  final wrapper `exists_isStableLattice`.  Completeness of `O` is not used in
  this file; it enters only in Ribet's lemma itself.

Everything whose proof is `sorry` is a stated target: this file is an API
skeleton.
-/

open Pointwise IsLocalRing

noncomputable section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [FiniteDimensional K V]

/-! ## 1. Lattices: complements to `Mathlib.Algebra.Module.Lattice`

Mathlib's `Submodule.IsLattice K Λ` is the predicate "`Λ` is finitely
generated and `Submodule.span K Λ = ⊤`".  Freeness over the DVR `O` is
`Submodule.IsLattice.free`, the rank computation `rank_O Λ = dim_K V` is
`Submodule.IsLattice.rank'`, and closure under `⊔`, `⊓` and scaling by `Kˣ`
are `Submodule.IsLattice.sup`, `.inf` and `.smul`.  The lemmas below are the
pieces missing from Mathlib that the arguments in this directory need. -/

namespace Submodule.IsLattice

/-- `Module.finrank` version of `Submodule.IsLattice.rank'`. -/
theorem finrank_eq (Λ : Submodule O V) [IsLattice K Λ] :
    Module.finrank O Λ = Module.finrank K V := sorry

/-- Every element of `V` can be scaled into a lattice by a nonzero element of
`O`.  (Uses `IsFractionRing`: clear denominators of the coordinates in an
`O`-basis of the lattice, extended to a `K`-basis of `V` by
`Basis.extendOfIsLattice`.) -/
theorem exists_smul_mem (Λ : Submodule O V) [IsLattice K Λ] (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ Λ := sorry

/-- Commensurability: any lattice can be scaled into any other.  (Apply
`exists_smul_mem` to the finitely many generators of `Λ'`.) -/
theorem exists_smul_le (Λ Λ' : Submodule O V) [IsLattice K Λ] [IsLattice K Λ'] :
    ∃ a : O, a ≠ 0 ∧ a • Λ' ≤ Λ := sorry

/-- Scaling a lattice by a nonzero element of `O` gives a lattice.  (Mathlib's
`Submodule.IsLattice.smul` treats scaling by units of `K`; this is the
`O`-pointwise version, used to normalize chains of lattices in the proof of
Ribet's lemma.) -/
theorem smul_of_ne_zero (Λ : Submodule O V) [IsLattice K Λ] {a : O} (ha : a ≠ 0) :
    IsLattice K (a • Λ) := sorry

/-- The image of a lattice under a `K`-linear automorphism is a lattice.
(Applied to `ρ g` in the averaging argument below.) -/
theorem map (Λ : Submodule O V) [IsLattice K Λ] (f : V ≃ₗ[K] V) :
    IsLattice K (Λ.map (f.toLinearMap.restrictScalars O)) := sorry

end Submodule.IsLattice

/-- `V` contains a lattice: the `O`-span of any `K`-basis of `V`. -/
theorem Submodule.exists_isLattice (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K V : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] :
    ∃ Λ : Submodule O V, Submodule.IsLattice K Λ := sorry

namespace StableLattice

/-! ## 2. Reduction modulo the maximal ideal -/

variable (O V) in
/-- The reduction of `Λ` modulo the maximal ideal `𝔪` of `O`: the vector space
`Λ ⧸ 𝔪Λ` over the residue field `F = O ⧸ 𝔪`. -/
abbrev Reduction (Λ : Submodule O V) : Type _ :=
  Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)

/-- The residue-field module structure on `Λ ⧸ 𝔪Λ`.  This is Mathlib's
`O ⧸ I`-module instance on `M ⧸ I • ⊤`, rephrased through the definitional
equality `ResidueField O = O ⧸ maximalIdeal O`. -/
instance (Λ : Submodule O V) : Module (ResidueField O) (Reduction O V Λ) :=
  inferInstanceAs
    (Module (O ⧸ maximalIdeal O) (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)))

/-- The `O`-action on `Λ ⧸ 𝔪Λ` factors through the residue field.  (Needed to
`restrictScalars` subspaces of the reduction back to `O`, as in
`preimageLattice` in `Ribet_Lemma.lean`.) -/
instance (Λ : Submodule O V) : IsScalarTower O (ResidueField O) (Reduction O V Λ) :=
  inferInstanceAs
    (IsScalarTower O (O ⧸ maximalIdeal O) (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)))

/-- The reduction of a lattice has the expected dimension:
`dim_F (Λ/𝔪Λ) = rank_O Λ = dim_K V`.  (Choose an `O`-basis of `Λ` via
`Submodule.IsLattice.free`; its image is an `F`-basis of the reduction.) -/
theorem finrank_reduction (Λ : Submodule O V) [Submodule.IsLattice K Λ] :
    Module.finrank (ResidueField O) (Reduction O V Λ) = Module.finrank K V := sorry

/-! ## 3. Group actions: stable lattices and reduced representations -/

variable {G : Type*} [Group G]

/-- The `O`-submodule `Λ` is stable under the representation `ρ`. -/
def Stabilizes (ρ : Representation K G V) (Λ : Submodule O V) : Prop :=
  ∀ g : G, Λ.map ((ρ g).restrictScalars O) = Λ

namespace Stabilizes

variable {ρ : Representation K G V} {Λ : Submodule O V}

/-- For a *group* action it suffices to check `≤` (apply the hypothesis to
`g⁻¹` and use that `ρ g` is bijective). -/
theorem of_le (h : ∀ g : G, Λ.map ((ρ g).restrictScalars O) ≤ Λ) :
    Stabilizes ρ Λ := sorry

/-- Stability is preserved by scaling: `Submodule.map` commutes with the
pointwise `O`-action. -/
theorem smul (h : Stabilizes ρ Λ) (a : O) : Stabilizes ρ (a • Λ) := sorry

end Stabilizes

/-- A `G`-stable `O`-lattice in `(V, ρ)`. -/
structure IsStableLattice (ρ : Representation K G V) (Λ : Submodule O V) : Prop where
  isLattice : Submodule.IsLattice K Λ
  stable : Stabilizes ρ Λ

/-- The `O`-linear representation of `G` on a stable submodule (each `ρ g`
restricts to an `O`-linear automorphism of `Λ`). -/
def latticeRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) : Representation O G Λ := sorry

/-- The reduced representation of `G` on `Λ ⧸ 𝔪Λ` over the residue field,
induced by `latticeRep` on the quotient. -/
def reducedRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) :
    Representation (ResidueField O) G (Reduction O V Λ) := sorry

/-- Scaling does not change the reduced representation: multiplication by `a`
is a `G`-equivariant `F`-linear isomorphism from the reduction of `Λ` to the
reduction of `a • Λ`. -/
theorem reducedRep_smul_equiv (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) {a : O} (ha : a ≠ 0) :
    ∃ e : Reduction O V Λ ≃ₗ[ResidueField O] Reduction O V (a • Λ),
      ∀ g x, e (reducedRep ρ Λ h g x) = reducedRep ρ (a • Λ) (h.smul a) g (e x) := sorry

/-! ## 4. Existence of stable lattices

The averaging argument is purely algebraic: if the stabilizer `H` of a lattice
`Λ₀` has finite index, then `Λ := ⨆ (gH : G ⧸ H), (ρ g) Λ₀` is well defined (the
summand depends only on the coset), is a lattice by `Submodule.IsLattice.sup` /
`.map`, and is `G`-stable.

Topology enters only to supply the finite index: an open subgroup of a compact
group has finite index (Mathlib: `Subgroup.quotient_finite_of_isOpen` together
with `Subgroup.finiteIndex_of_finite_quotient`).  Openness of the stabilizer is
where continuity of `ρ` would be used; we take it as a hypothesis, so this
section is usable without developing the topology of `GL(V)` over a valued
field.  Discharging it for continuous representations of profinite groups on
`p`-adic vector spaces is a separate (missing) piece of API.

This section is needed to *apply* Ribet's lemma (produce the initial stable
lattice), not for its proof — see the remarks in §9 (`Ribet_Lemma.lean`). -/

section Existence

/-- The stabilizer of a submodule under `ρ`, as a subgroup of `G`. -/
def latticeStabilizer (ρ : Representation K G V) (Λ : Submodule O V) : Subgroup G where
  carrier := {g | Λ.map ((ρ g).restrictScalars O) = Λ}
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
@[simp]
theorem mem_latticeStabilizer {ρ : Representation K G V} {Λ : Submodule O V} {g : G} :
    g ∈ latticeStabilizer ρ Λ ↔ Λ.map ((ρ g).restrictScalars O) = Λ :=
  Iff.rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
theorem stabilizes_iff_latticeStabilizer_eq_top
    {ρ : Representation K G V} {Λ : Submodule O V} :
    Stabilizes ρ Λ ↔ latticeStabilizer ρ Λ = ⊤ := by
  rw [Subgroup.eq_top_iff']; exact Iff.rfl

/-- Averaging over the finite coset space `G ⧸ H` of the stabilizer: if the
stabilizer of some lattice has finite index, a `G`-stable lattice exists. -/
theorem exists_isStableLattice_of_finiteIndex (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    [(latticeStabilizer ρ Λ₀).FiniteIndex] :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ := sorry

/-- If `G` is compact and some lattice has open stabilizer, then a `G`-stable
lattice exists.  (The stabilizer has finite index by
`Subgroup.quotient_finite_of_isOpen`; conclude with
`exists_isStableLattice_of_finiteIndex`.) -/
theorem exists_isStableLattice [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    (hopen : IsOpen (latticeStabilizer ρ Λ₀ : Set G)) :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ := sorry

end Existence

end StableLattice

end
