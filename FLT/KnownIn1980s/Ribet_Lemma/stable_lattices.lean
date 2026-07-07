import Mathlib

/-!
# `G`-stable lattices in representations over the fraction field of a DVR

Foundational file of this directory, whose goal is Ribet's lemma
(Ribet, Invent. Math. 34 (1976), Prop. 2.1).  The directory is one linear
development, with sections numbered across the three files:

* §1–4 (`stable_lattices.lean`): lattices, reduction mod `𝔪`, stable lattices
  and reduced representations, existence of stable lattices;
* §5–7 (`Brauer_Nesbitt.lean`): extensions of characters in dimension 2;
  lattice modification (the engine of the proofs); independence of the
  reduction from the lattice (Brauer–Nesbitt);
* §8–10 (`Ribet_Lemma.lean`): the completeness argument, Ribet's lemma
  itself, concluding remarks.

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

The whole directory is `sorry`-free.
-/

open Pointwise IsLocalRing
open scoped TensorProduct

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

omit [FiniteDimensional K V] in
/-- `Module.finrank` version of `Submodule.IsLattice.rank'`. -/
theorem finrank_eq (Λ : Submodule O V) [IsLattice K Λ] :
    Module.finrank O Λ = Module.finrank K V :=
  congrArg Cardinal.toNat (rank' K Λ)

omit [FiniteDimensional K V] in
/-- Every element of `V` can be scaled into a lattice by a nonzero element of
`O`.  (Uses `IsFractionRing`: clear denominators of the coordinates in an
`O`-basis of the lattice, extended to a `K`-basis of `V` by
`Basis.extendOfIsLattice`.) -/
theorem exists_smul_mem (Λ : Submodule O V) [IsLattice K Λ] (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ Λ := by
  classical
  let c := (Module.Free.chooseBasis O Λ).extendOfIsLattice K
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    Finset.univ fun i => c.repr v i
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, ?_⟩
  have hv : (s : O) • v = ∑ i, (s : O) • c.repr v i • c i := by
    rw [← Finset.smul_sum, c.sum_repr]
  rw [hv]
  refine Submodule.sum_mem Λ fun i _ => ?_
  obtain ⟨o, ho⟩ := hs i (Finset.mem_univ i)
  rw [← smul_assoc, ← ho, algebraMap_smul]
  exact Λ.smul_mem o (by simp [c])

omit [FiniteDimensional K V] in
/-- Commensurability: any lattice can be scaled into any other.  (Apply
`exists_smul_mem` to the finitely many generators of `Λ'`.) -/
theorem exists_smul_le (Λ Λ' : Submodule O V) [IsLattice K Λ] [IsLattice K Λ'] :
    ∃ a : O, a ≠ 0 ∧ a • Λ' ≤ Λ := by
  classical
  obtain ⟨s, hs⟩ := IsLattice.fg (A := K) (M := Λ')
  choose f hf0 hfm using fun x : s => exists_smul_mem Λ (x : V)
  refine ⟨∏ x ∈ s.attach, f x, Finset.prod_ne_zero_iff.mpr fun x _ => hf0 x, ?_⟩
  rw [← hs, Submodule.smul_span]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨x, hx, rfl⟩
  dsimp only
  rw [← Finset.mul_prod_erase s.attach f (Finset.mem_attach s ⟨x, hx⟩),
    mul_comm, mul_smul]
  exact Λ.smul_mem _ (hfm ⟨x, hx⟩)

omit [IsDomain O] [IsDiscreteValuationRing O] [FiniteDimensional K V] in
/-- Scaling a lattice by a nonzero element of `O` gives a lattice.  (Mathlib's
`Submodule.IsLattice.smul` treats scaling by units of `K`; this is the
`O`-pointwise version, used to normalize chains of lattices in the proof of
Ribet's lemma.) -/
theorem smul_of_ne_zero (Λ : Submodule O V) [IsLattice K Λ] {a : O} (ha : a ≠ 0) :
    IsLattice K (a • Λ) := by
  have ha' : algebraMap O K a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
  constructor
  · obtain ⟨s, hs⟩ := IsLattice.fg (A := K) (M := Λ)
    rw [← hs, Submodule.smul_span]
    exact Submodule.fg_span (s.finite_toSet.smul_set)
  · rw [eq_top_iff, ← IsLattice.span_eq_top (A := K) (M := Λ)]
    refine Submodule.span_le.mpr fun x hx => ?_
    have h1 : a • x ∈ Submodule.span K ((a • Λ : Submodule O V) : Set V) :=
      Submodule.subset_span (Submodule.smul_mem_pointwise_smul x a Λ hx)
    have h2 := Submodule.smul_mem _ ((algebraMap O K a)⁻¹) h1
    rwa [← algebraMap_smul K a x, inv_smul_smul₀ ha'] at h2

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- The image of a lattice under a `K`-linear automorphism is a lattice.
(Applied to `ρ g` in the averaging argument below.) -/
theorem map (Λ : Submodule O V) [IsLattice K Λ] (f : V ≃ₗ[K] V) :
    IsLattice K (Λ.map (f.toLinearMap.restrictScalars O)) where
  fg := (IsLattice.fg (A := K) (M := Λ)).map _
  span_eq_top := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      IsLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end Submodule.IsLattice

/-- `V` contains a lattice: the `O`-span of any `K`-basis of `V`. -/
theorem Submodule.exists_isLattice (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K V : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] :
    ∃ Λ : Submodule O V, Submodule.IsLattice K Λ := by
  let b := Module.finBasis K V
  refine ⟨Submodule.span O (Set.range b),
    ⟨Submodule.fg_span (Set.finite_range b), ?_⟩⟩
  rw [Submodule.span_span_of_tower, b.span_eq]

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
`preimageLattice` in `Brauer_Nesbitt.lean`.) -/
instance (Λ : Submodule O V) : IsScalarTower O (ResidueField O) (Reduction O V Λ) :=
  inferInstanceAs
    (IsScalarTower O (O ⧸ maximalIdeal O) (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)))

/-- The residue-field action on `Λ ⧸ 𝔪Λ` is computed by lifting the scalar to
`O` (definitionally). -/
@[simp]
theorem residue_smul_mk (Λ : Submodule O V) (u : O) (y : Λ) :
    residue O u • (Submodule.Quotient.mk y : Reduction O V Λ)
      = Submodule.Quotient.mk (u • y) :=
  rfl

omit [FiniteDimensional K V] in
/-- The reduction of a lattice has the expected dimension:
`dim_F (Λ/𝔪Λ) = rank_O Λ = dim_K V`.  (The reduction is the base change
`F ⊗[O] Λ` of the free module `Λ`, via `quotTensorEquivQuotSMul`.) -/
theorem finrank_reduction (Λ : Submodule O V) [Submodule.IsLattice K Λ] :
    Module.finrank (ResidueField O) (Reduction O V Λ) = Module.finrank K V := by
  -- Work with the spelling `O ⧸ 𝔪` throughout (`ResidueField O` is a
  -- non-reducible definition, which blocks instance unification if mixed in).
  suffices h : Module.finrank (O ⧸ maximalIdeal O)
      (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)) = Module.finrank K V from h
  have e : ((O ⧸ maximalIdeal O) ⊗[O] Λ) ≃ₗ[O ⧸ maximalIdeal O]
      (Λ ⧸ (maximalIdeal O • ⊤ : Submodule O Λ)) :=
    (TensorProduct.quotTensorEquivQuotSMul Λ (maximalIdeal O)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  rw [← e.finrank_eq, Module.finrank_baseChange, Submodule.IsLattice.finrank_eq]

/-! ## 3. Group actions: stable lattices and reduced representations -/

variable {G : Type*} [Group G]

/-- The `O`-submodule `Λ` is stable under the representation `ρ`. -/
def Stabilizes (ρ : Representation K G V) (Λ : Submodule O V) : Prop :=
  ∀ g : G, Λ.map ((ρ g).restrictScalars O) = Λ

namespace Stabilizes

variable {ρ : Representation K G V} {Λ : Submodule O V}

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- For a *group* action it suffices to check `≤` (apply the hypothesis to
`g⁻¹` and use that `ρ g` is bijective). -/
theorem of_le (h : ∀ g : G, Λ.map ((ρ g).restrictScalars O) ≤ Λ) :
    Stabilizes ρ Λ := by
  intro g
  refine le_antisymm (h g) fun x hx => Submodule.mem_map.mpr
    ⟨ρ g⁻¹ x, h g⁻¹ (Submodule.mem_map_of_mem hx), ?_⟩
  simp [← Module.End.mul_apply, ← map_mul]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- Stability is preserved by scaling: `Submodule.map` commutes with the
pointwise `O`-action. -/
theorem smul (h : Stabilizes ρ Λ) (a : O) : Stabilizes ρ (a • Λ) := fun g => by
  rw [Submodule.map_pointwise_smul, h g]

end Stabilizes

/-- A `G`-stable `O`-lattice in `(V, ρ)`. -/
structure IsStableLattice (ρ : Representation K G V) (Λ : Submodule O V) : Prop where
  isLattice : Submodule.IsLattice K Λ
  stable : Stabilizes ρ Λ

/-- The `O`-linear representation of `G` on a stable submodule (each `ρ g`
restricts to an `O`-linear automorphism of `Λ`). -/
def latticeRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) : Representation O G Λ where
  toFun g := ((ρ g).restrictScalars O).restrict
    fun x hx => (h g).le (Submodule.mem_map_of_mem hx)
  map_one' := by ext x; simp
  map_mul' g₁ g₂ := by ext x; simp

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
@[simp]
theorem latticeRep_apply_coe (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) (g : G) (y : Λ) :
    ((latticeRep ρ Λ h g y : Λ) : V) = ρ g (y : V) :=
  rfl

/-- Any `O`-linear map sends `𝔪M` into `𝔪N`. -/
private theorem smul_top_le_comap {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) :
    (maximalIdeal O • ⊤ : Submodule O M) ≤ (maximalIdeal O • ⊤ : Submodule O N).comap f :=
  Submodule.map_le_iff_le_comap.mp <| by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top

/-- An `O`-linear map between submodules of `V` induces a residue-field-linear
map between their reductions mod `𝔪`. -/
noncomputable def reductionMap {Λ₁ Λ₂ : Submodule O V} (f : Λ₁ →ₗ[O] Λ₂) :
    Reduction O V Λ₁ →ₗ[ResidueField O] Reduction O V Λ₂ where
  toFun := Submodule.mapQ _ _ f (smul_top_le_comap f)
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (map_smul f b y)

@[simp]
theorem reductionMap_mk {Λ₁ Λ₂ : Submodule O V} (f : Λ₁ →ₗ[O] Λ₂) (y : Λ₁) :
    reductionMap f (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y) :=
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- Membership in `𝔪N` can be checked in the ambient space `V`. -/
theorem mem_smul_top_iff (I : Ideal O) (N : Submodule O V) (x : N) :
    x ∈ (I • ⊤ : Submodule O N) ↔ (x : V) ∈ I • N := by
  have hmap : (I • ⊤ : Submodule O N).map N.subtype = I • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  constructor
  · intro hx
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rwa [show y = x from Subtype.ext hxy] at hy

/-- The reduced representation of `G` on `Λ ⧸ 𝔪Λ` over the residue field,
induced by `latticeRep` on the quotient. -/
noncomputable def reducedRep (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) :
    Representation (ResidueField O) G (Reduction O V Λ) where
  toFun g := reductionMap (latticeRep ρ Λ h g)
  map_one' := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [reductionMap, Submodule.mapQ_apply]
  map_mul' g₁ g₂ := LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [reductionMap, Submodule.mapQ_apply]

omit [IsFractionRing O K] [FiniteDimensional K V] in
@[simp]
theorem reducedRep_mk (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) (g : G) (y : Λ) :
    reducedRep ρ Λ h g (Submodule.Quotient.mk y)
      = Submodule.Quotient.mk (latticeRep ρ Λ h g y) :=
  rfl

omit [FiniteDimensional K V] in
/-- Scaling does not change the reduced representation: multiplication by `a`
is a `G`-equivariant `F`-linear isomorphism from the reduction of `Λ` to the
reduction of `a • Λ`. -/
theorem reducedRep_smul_equiv (ρ : Representation K G V) (Λ : Submodule O V)
    (h : Stabilizes ρ Λ) {a : O} (ha : a ≠ 0) :
    ∃ e : Reduction O V Λ ≃ₗ[ResidueField O] Reduction O V (a • Λ),
      ∀ g x, e (reducedRep ρ Λ h g x) = reducedRep ρ (a • Λ) (h.smul a) g (e x) := by
  have ha' : algebraMap O K a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
  -- multiplication by `a` as an `O`-linear map `Λ → a • Λ`
  let μ : Λ →ₗ[O] ↥(a • Λ) :=
    { toFun := fun x => ⟨a • (x : V), Submodule.smul_mem_pointwise_smul _ a Λ x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add a (x : V) (y : V))
      map_smul' := fun c x => Subtype.ext (smul_comm a c (x : V)) }
  have hμbij : Function.Bijective μ := by
    constructor
    · intro x y hxy
      have hval : a • (x : V) = a • (y : V) := congrArg Subtype.val hxy
      rw [← algebraMap_smul K a (x : V), ← algebraMap_smul K a (y : V)] at hval
      exact Subtype.ext (smul_right_injective V ha' hval)
    · rintro ⟨w, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let μe : Λ ≃ₗ[O] ↥(a • Λ) := LinearEquiv.ofBijective μ hμbij
  refine ⟨LinearEquiv.ofLinear (reductionMap μ) (reductionMap μe.symm.toLinearMap)
    ?_ ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (μe.apply_symm_apply y)
  · refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (μe.symm_apply_apply y)
  · intro g x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext ((ρ g).map_smul_of_tower a (y : V)).symm)

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
lattice), not for its proof — see the remarks in §10 (`Ribet_Lemma.lean`). -/

section Existence

/-- The stabilizer of a submodule under `ρ`, as a subgroup of `G`. -/
def latticeStabilizer (ρ : Representation K G V) (Λ : Submodule O V) : Subgroup G where
  carrier := {g | Λ.map ((ρ g).restrictScalars O) = Λ}
  one_mem' := by
    change Λ.map ((ρ 1).restrictScalars O) = Λ
    rw [map_one]
    exact Submodule.map_id Λ
  mul_mem' := by
    intro a b ha hb
    change Λ.map ((ρ (a * b)).restrictScalars O) = Λ
    rw [map_mul,
      show ((ρ a * ρ b).restrictScalars O)
          = ((ρ a).restrictScalars O).comp ((ρ b).restrictScalars O) from rfl,
      Submodule.map_comp, hb, ha]
  inv_mem' := by
    intro a ha
    change Λ.map ((ρ a⁻¹).restrictScalars O) = Λ
    conv_lhs => rw [← ha]
    rw [← Submodule.map_comp,
      show ((ρ a⁻¹).restrictScalars O).comp ((ρ a).restrictScalars O)
          = ((ρ a⁻¹ * ρ a).restrictScalars O) from rfl,
      ← map_mul, inv_mul_cancel, map_one]
    exact Submodule.map_id Λ

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

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- Averaging over the finite coset space `G ⧸ H` of the stabilizer: if the
stabilizer of some lattice has finite index, a `G`-stable lattice exists,
namely the (finite) supremum of the translates of the given one. -/
theorem exists_isStableLattice_of_finiteIndex (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    [(latticeStabilizer ρ Λ₀).FiniteIndex] :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ := by
  classical
  -- translates of `Λ₀` compose
  have hcomp : ∀ g₁ g₂ : G, Λ₀.map ((ρ (g₁ * g₂)).restrictScalars O)
      = (Λ₀.map ((ρ g₂).restrictScalars O)).map ((ρ g₁).restrictScalars O) := by
    intro g₁ g₂
    rw [map_mul, show ((ρ g₁ * ρ g₂).restrictScalars O)
        = ((ρ g₁).restrictScalars O).comp ((ρ g₂).restrictScalars O) from rfl,
      Submodule.map_comp]
  -- each translate is a lattice
  have hlat : ∀ g : G, Submodule.IsLattice K (Λ₀.map ((ρ g).restrictScalars O)) :=
    fun g => Submodule.IsLattice.map Λ₀
      (LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
        (by ext x; simp [← Module.End.mul_apply, ← map_mul])
        (by ext x; simp [← Module.End.mul_apply, ← map_mul]))
  refine ⟨⨆ c : G ⧸ latticeStabilizer ρ Λ₀,
    Λ₀.map ((ρ (Quotient.out c)).restrictScalars O), ⟨?_, ?_⟩, ?_⟩
  · exact Submodule.fg_iSup _ fun c => (hlat _).fg
  · -- the supremum contains a translate, whose `K`-span is already everything
    rw [eq_top_iff,
      ← (hlat (Quotient.out (QuotientGroup.mk (1 : G) :
        G ⧸ latticeStabilizer ρ Λ₀))).span_eq_top]
    exact Submodule.span_mono
      (SetLike.coe_subset_coe.mpr
        (le_iSup (fun c : G ⧸ latticeStabilizer ρ Λ₀ =>
          Λ₀.map ((ρ (Quotient.out c)).restrictScalars O))
          (QuotientGroup.mk (1 : G))))
  · -- stability: `g` permutes the translates
    refine Stabilizes.of_le fun g => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun c => ?_
    rw [← hcomp g (Quotient.out c)]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul
      (latticeStabilizer ρ Λ₀) (g * Quotient.out c)
    have key : Λ₀.map ((ρ (Quotient.out (QuotientGroup.mk (g * Quotient.out c) :
          G ⧸ latticeStabilizer ρ Λ₀))).restrictScalars O)
        = Λ₀.map ((ρ (g * Quotient.out c)).restrictScalars O) := by
      rw [hh, hcomp, mem_latticeStabilizer.mp h.2]
    rw [← key]
    exact le_iSup (fun c : G ⧸ latticeStabilizer ρ Λ₀ =>
      Λ₀.map ((ρ (Quotient.out c)).restrictScalars O))
      (QuotientGroup.mk (g * Quotient.out c))

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] [FiniteDimensional K V] in
/-- If `G` is compact and some lattice has open stabilizer, then a `G`-stable
lattice exists.  (The stabilizer has finite index by
`Subgroup.quotient_finite_of_isOpen`; conclude with
`exists_isStableLattice_of_finiteIndex`.) -/
theorem exists_isStableLattice [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (ρ : Representation K G V)
    (Λ₀ : Submodule O V) [Submodule.IsLattice K Λ₀]
    (hopen : IsOpen (latticeStabilizer ρ Λ₀ : Set G)) :
    ∃ Λ : Submodule O V, IsStableLattice ρ Λ := by
  haveI : Finite (G ⧸ latticeStabilizer ρ Λ₀) :=
    (latticeStabilizer ρ Λ₀).quotient_finite_of_isOpen hopen
  haveI : (latticeStabilizer ρ Λ₀).FiniteIndex :=
    (latticeStabilizer ρ Λ₀).finiteIndex_of_finite_quotient
  exact exists_isStableLattice_of_finiteIndex ρ Λ₀

end Existence

end StableLattice

end
