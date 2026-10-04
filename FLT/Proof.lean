/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Basic.Lemmas
public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
public import FLT.FreyCurve.Mazur
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.Automorphic
public import FLT.GaloisRepresentation.SMinimal
public import FLT.Deformations.Representable
public import FLT.Deformations.RepresentationTheory.GaloisRepFamily
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.Topology.Instances.ZMod

/-!
# The proof of Fermat's Last Theorem

This file contains the "main spine" of the proof of Fermat's
Last Theorem.

The strategy of the proof is to prove the theorem via a series
of reductions. In other words, we will define mathematical statements
B_1=FLT, B_2, B_3, B_4, ..., up to around B_{12}, and then prove
that B_2 implies B_1, B_3 implies B_2, B_4 implies B_3 etc etc,
and then ultimately that B_{12} is true.

-/

@[expose] public section

namespace FLT.Bosses

open GaloisRepresentation IsDedekindDomain

open scoped TensorProduct Pointwise

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-
## Statements of the intermediate "Boss theorems"

Important note: because verso does not allow me a chapter 0, all
these labels are off-by-one from the 2026 course notes.
-/

/-- B1 is the statement of FLT. -/
def B1 : Prop := FermatLastTheorem

/-- B2 is the statement that FLT is true for primes p ≥ 5. -/
def B2 : Prop := ∀ p ≥ 5, Nat.Prime p → FermatLastTheoremFor p

/-- B3 is the statement that there is no Frey Package.
A Frey package is 4 integers a,b,c,p satisfying a^p+b^p=c^p and
some other conditions (for example p is prime and at least 5,
a,b,c are pairwise coprime etc). These conditions guarantee that the
associated Frey curve Y^2=X(X-a^p)(X+b^p) is semistable. -/
def B3 : Prop := IsEmpty FreyPackage

/-- B4 is the statement that if E is the Frey curve attached
to a Frey package (a,b,c,p), then E[p] is a reducible Galois representation. -/
def B4 : Prop :=
  ∀ P : FreyPackage,
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  let ρbar := (E.galoisRep p P.hppos)
  ¬ GaloisRep.IsIrreducible ρbar

/-!
## The statements B5 to B12

The statements below follow the 2026 EPSRC TCC course notes
(`2026_EPSRC_TCC_course/level05.tex` to `level12.tex`). First we set up
some notation and helper definitions.
-/

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance algebraPadicIntZMod (p : ℕ) [Fact p.Prime] :
    Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- A ring homomorphism from `ℤ_p` to a discrete topological ring is continuous
as soon as its kernel contains the maximal ideal. -/
private theorem continuous_of_maximalIdeal_le_ker {p : ℕ} [Fact p.Prime] {A : Type*}
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (f : ℤ_[p] →+* A)
    (hf : IsLocalRing.maximalIdeal ℤ_[p] ≤ RingHom.ker f) : Continuous f := by
  have hopen : IsOpen ((RingHom.ker f : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    refine Submodule.isOpen_mono hf ?_
    have h1 : ((IsLocalRing.maximalIdeal ℤ_[p] : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.ball 0 1 := by
      ext x
      rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
        mem_ball_zero_iff]
    rw [h1]
    exact Metric.isOpen_ball
  rw [continuous_discrete_rng]
  intro b
  have h2 : f ⁻¹' {b} =
      ⋃ x ∈ f ⁻¹' {b}, x +ᵥ ((RingHom.ker f : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext z
    constructor
    · intro hz
      refine Set.mem_biUnion hz (Set.mem_vadd_set.mpr ⟨0, Submodule.zero_mem _, ?_⟩)
      simp
    · intro hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨x, hx, hz⟩ := hz
      obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hz
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rw [vadd_eq_add, map_add, hx, RingHom.mem_ker.1 hy, add_zero]
  rw [h2]
  exact isOpen_biUnion fun x _ => hopen.vadd x

/-- The action of `ℤ_p` on `ℤ/pℤ` is continuous. -/
local instance (p : ℕ) [Fact p.Prime] : ContinuousSMul ℤ_[p] (ZMod p) :=
  continuousSMul_of_algebraMap _ _
    (continuous_of_maximalIdeal_le_ker _ PadicInt.ker_toZMod.ge)

/-- The natural `ℤ_ℓ`-algebra structure on the residue field of a local
`ℤ_ℓ`-algebra `𝓞`, promoted to the corresponding object of `ProartinianCat 𝓞`. -/
noncomputable local instance (𝓞 : Type) [CommRing 𝓞] [IsLocalRing 𝓞]
    (ℓ : ℕ) [Fact ℓ.Prime] [Algebra ℤ_[ℓ] 𝓞] :
    Algebra ℤ_[ℓ] (Deformation.ProartinianCat.residueField (𝓞 := 𝓞)) :=
  inferInstanceAs (Algebra ℤ_[ℓ] (IsLocalRing.ResidueField 𝓞))

/-- The action of `ℤ_ℓ` on the residue field of a local `ℤ_ℓ`-algebra `𝓞` is
continuous (for the discrete topology on the residue field). -/
local instance (𝓞 : Type) [CommRing 𝓞] [IsLocalRing 𝓞]
    (ℓ : ℕ) [Fact ℓ.Prime] [Algebra ℤ_[ℓ] 𝓞] [IsLocalHom (algebraMap ℤ_[ℓ] 𝓞)] :
    ContinuousSMul ℤ_[ℓ] (Deformation.ProartinianCat.residueField (𝓞 := 𝓞)) := by
  refine continuousSMul_of_algebraMap _ _ (continuous_of_maximalIdeal_le_ker _ fun x hx => ?_)
  have h1 : algebraMap ℤ_[ℓ] 𝓞 x ∈ IsLocalRing.maximalIdeal 𝓞 := by
    rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
    exact fun h => hx (IsLocalHom.map_nonunit x h)
  have h2 : algebraMap ℤ_[ℓ] (IsLocalRing.ResidueField 𝓞) x = 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[ℓ] 𝓞 (IsLocalRing.ResidueField 𝓞),
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact h1
  exact h2

/-- `B5` is the statement that if `ℓ ≥ 5` is a prime then every continuous hardly
ramified representation of `Gal(ℚ̄/ℚ)` on a two-dimensional `𝔽_ℓ`-vector space is
reducible. See `2026_EPSRC_TCC_course/level05.tex`. -/
def B5 : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod ℓ) V] [Module.Finite (ZMod ℓ) V]
    [Module.Free (ZMod ℓ) V] (hV : Module.rank (ZMod ℓ) V = 2)
    (ρ : GaloisRep ℚ (ZMod ℓ) V),
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ → ¬ ρ.IsIrreducible

set_option linter.unusedVariables false in
/-- The statement that the mod-`ℓ` representation `ρ` lifts to a hardly ramified
`ℓ`-adic representation, i.e. a hardly ramified representation into `GL_2(R)` with `R`
the integers of a finite extension of `ℚ_ℓ` (or more precisely a local order in such a
ring of integers). This is the conclusion of statements `B6a` and `B8a`. -/
@[nolint unusedArguments]
def HasHardlyRamifiedLift {ℓ : ℕ} [Fact ℓ.Prime] (hℓodd : Odd ℓ)
    {k : Type} [Field k] [Finite k]
    [TopologicalSpace k] [DiscreteTopology k] [Algebra ℤ_[ℓ] k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V) : Prop :=
  -- There is a complete local domain `R`, finite free over `ℤ_ℓ`,
  ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
    (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : Algebra ℤ_[ℓ] R) (_ : IsLocalHom (algebraMap ℤ_[ℓ] R))
    (_ : Module.Finite ℤ_[ℓ] R) (_ : Module.Free ℤ_[ℓ] R)
    (_ : IsModuleTopology ℤ_[ℓ] R)
    -- with residue field `k`,
    (_ : Algebra R k) (_ : IsScalarTower ℤ_[ℓ] R k) (_ : ContinuousSMul R k)
    -- and a rank 2 representation `σ` of `Gal(ℚ̄/ℚ)` over `R`
    (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
    (_ : Module.Free R W) (hW : Module.rank R W = 2)
    (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
  -- which is hardly ramified and lifts `ρ`.
  IsHardlyRamified hℓodd hW σ ∧ (σ.baseChange k).conj r = ρ

/-- `B6a` (*lifting*) is the statement that if `ℓ ≥ 5` is a prime then every irreducible
hardly ramified representation of `Gal(ℚ̄/ℚ)` on a two-dimensional `𝔽_ℓ`-vector space
lifts to a hardly ramified `ℓ`-adic representation.
See `2026_EPSRC_TCC_course/level06.tex`. -/
def B6a : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod ℓ) V] [Module.Finite (ZMod ℓ) V]
    [Module.Free (ZMod ℓ) V] (hV : Module.rank (ZMod ℓ) V = 2)
    (ρ : GaloisRep ℚ (ZMod ℓ) V),
  ρ.IsIrreducible →
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ →
  HasHardlyRamifiedLift (hℓ.odd_of_ne_two (by omega)) hV ρ

set_option linter.unusedVariables false in
/-- The statement that the `ℓ`-adic representation `ρ` is a member of a compatible
family of 2-dimensional Galois representations, all of whose members with odd residue
characteristic are hardly ramified. This is the conclusion of statements `B6b`
and `B8b`. -/
@[nolint unusedArguments]
def MemHardlyRamifiedCompatibleFamily (ℓ : ℕ) [Fact ℓ.Prime]
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R]
    [IsModuleTopology ℤ_[ℓ] R]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V) : Prop :=
  -- There's a compatible family `σ` of 2-dimensional representations of `Gal(ℚ̄/ℚ)`
  -- parametrised by the maps from a number field `E` to `ℚ̄_q` for `q` running through
  -- the primes,
  ∃ (E : Type) (_ : Field E) (_ : NumberField E) (σ : GaloisRepFamily ℚ E 2),
    σ.isCompatible ∧
    -- whose members are "hardly ramified" in odd residue characteristic, meaning that
    -- each such member has a model over a local order `A` in a finite extension
    -- of `ℚ_q` which is hardly ramified,
    (∀ {q : ℕ} (hq : Fact q.Prime) (hqodd : Odd q) (φ : E →+* AlgebraicClosure ℚ_[q]),
      ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLocalRing A) (_ : Algebra ℤ_[q] A) (_ : Module.Finite ℤ_[q] A)
        (_ : Module.Free ℤ_[q] A) (_ : IsDomain A) (_ : Algebra A (AlgebraicClosure ℚ_[q]))
        (_ : IsScalarTower ℤ_[q] A (AlgebraicClosure ℚ_[q])) (_ : IsModuleTopology ℤ_[q] A)
        (_ : ContinuousSMul A (AlgebraicClosure ℚ_[q]))
        (W : Type) (_ : AddCommGroup W) (_ : Module A W) (_ : Module.Finite A W)
        (_ : Module.Free A W) (hW : Module.rank A W = 2)
        (τ : GaloisRep ℚ A W)
        (r : AlgebraicClosure ℚ_[q] ⊗[A] W ≃ₗ[AlgebraicClosure ℚ_[q]]
          (Fin 2 → AlgebraicClosure ℚ_[q])),
        IsHardlyRamified hqodd hW τ ∧
        (τ.baseChange (AlgebraicClosure ℚ_[q])).conj r = σ hq φ) ∧
    -- and such that `ρ` is a member of the family.
    (∃ (_ : Algebra R (AlgebraicClosure ℚ_[ℓ])) (_ : ContinuousSMul R (AlgebraicClosure ℚ_[ℓ]))
      (ψ : E →+* AlgebraicClosure ℚ_[ℓ])
      (r' : AlgebraicClosure ℚ_[ℓ] ⊗[R] V ≃ₗ[AlgebraicClosure ℚ_[ℓ]]
        (Fin 2 → AlgebraicClosure ℚ_[ℓ])),
      (ρ.baseChange (AlgebraicClosure ℚ_[ℓ])).conj r' = σ ‹Fact ℓ.Prime› ψ)

/-- `B6b` (*spreading out*) is the statement that if `ℓ ≥ 5` is a prime then every
hardly ramified `ℓ`-adic representation, whose reduction is the base change of an
absolutely irreducible representation over `𝔽_ℓ`, is a member of a compatible family
of hardly ramified representations. See `2026_EPSRC_TCC_course/level06.tex`. -/
def B6b : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R]
    [IsModuleTopology ℤ_[ℓ] R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V),
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ →
  -- if the reduction of `ρ` is an absolutely irreducible representation
  -- defined over `𝔽_ℓ`
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module (ZMod ℓ) V₀] [Module.Finite (ZMod ℓ) V₀]
    [Module.Free (ZMod ℓ) V₀] (ρ₀ : GaloisRep ℚ (ZMod ℓ) V₀),
  Representation.IsAbsolutelyIrreducible.{0} ρ₀.toRepresentation →
  ∀ [Algebra R (ZMod ℓ)] [IsScalarTower ℤ_[ℓ] R (ZMod ℓ)] [ContinuousSMul R (ZMod ℓ)]
    (r : ZMod ℓ ⊗[R] V ≃ₗ[ZMod ℓ] V₀),
  (ρ.baseChange (ZMod ℓ)).conj r = ρ₀ →
  -- then `ρ` is a member of a compatible family of hardly ramified representations.
  MemHardlyRamifiedCompatibleFamily ℓ hV ρ

/-- `B6c` (*classification at 3*) is the statement that every hardly ramified `3`-adic
representation of `Gal(ℚ̄/ℚ)` is an extension of the trivial character by the
cyclotomic character, i.e. upper triangular `(χ, *; 0, 1)` for a suitable basis.
See `2026_EPSRC_TCC_course/level06.tex`. -/
def B6c : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R] [Module.Free ℤ_[3] R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R] [IsModuleTopology ℤ_[3] R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V),
  IsHardlyRamified (ℓ := 3) (by decide) hV ρ →
  -- `ρ` has a free rank 1 quotient on which the Galois group acts trivially
  -- (and then the determinant condition forces the kernel to be the cyclotomic
  -- character).
  ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π), ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v

/-- `B6` is the conjunction of the statements `B6a` (lifting), `B6b` (spreading out)
and `B6c` (classification at 3). See `2026_EPSRC_TCC_course/level06.tex`. -/
def B6 : Prop := B6a ∧ B6b ∧ B6c

/-- `B7` is the conjunction of the statements `B6a` (lifting) and `B6b` (spreading out);
the classification `B6c` of hardly ramified 3-adic representations is a theorem
(modulo results known in the 1980s). See `2026_EPSRC_TCC_course/level07.tex`. -/
def B7 : Prop := B6a ∧ B6b

/-- `B8a` (*automorphic lifting*) is the statement that if `ℓ ≥ 5` is a prime and `k`
is a finite field of characteristic `ℓ`, then every hardly ramified `k`-representation
of `Gal(ℚ̄/ℚ)` which is potentially automorphic and absolutely irreducible after
restriction to `Gal(ℚ̄/ℚ(ζ_ℓ))` lifts to a hardly ramified `ℓ`-adic representation.
See `2026_EPSRC_TCC_course/level08.tex`. -/
def B8a : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (k : Type) [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[ℓ] k] [IsLocalHom (algebraMap ℤ_[ℓ] k)] [ContinuousSMul ℤ_[ℓ] k]
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V),
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ →
  ρ.IsPotentiallyAutomorphic ℓ (Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)) →
  Representation.IsAbsolutelyIrreducible.{0}
    ((ρ.map (algebraMap ℚ (CyclotomicField ℓ ℚ))).toRepresentation) →
  HasHardlyRamifiedLift (hℓ.odd_of_ne_two (by omega)) hV ρ

/-- `B8b` (*automorphic spreading out*) is the statement that if `ℓ ≥ 5` is a prime
then every hardly ramified `ℓ`-adic representation, whose reduction is potentially
automorphic and absolutely irreducible after restriction to `Gal(ℚ̄/ℚ(ζ_ℓ))`, is a
member of a compatible family of hardly ramified representations.
See `2026_EPSRC_TCC_course/level08.tex`. -/
def B8b : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] [Module.Finite ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R]
    [IsModuleTopology ℤ_[ℓ] R]
    (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V),
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ →
  -- if the reduction `ρ ⊗ k` of `ρ` is potentially automorphic
  ∀ (k : Type) [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[ℓ] k] [IsLocalHom (algebraMap ℤ_[ℓ] k)] [ContinuousSMul ℤ_[ℓ] k]
    [Algebra R k] [IsScalarTower ℤ_[ℓ] R k] [ContinuousSMul R k],
  (ρ.baseChange k).IsPotentiallyAutomorphic ℓ
    (by rw [Module.finrank_baseChange]
        exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hV)) →
  -- and absolutely irreducible after restriction to `Gal(ℚ̄/ℚ(ζ_ℓ))`
  Representation.IsAbsolutelyIrreducible.{0}
    (((ρ.baseChange k).map (algebraMap ℚ (CyclotomicField ℓ ℚ))).toRepresentation) →
  -- then `ρ` is a member of a compatible family of hardly ramified representations.
  MemHardlyRamifiedCompatibleFamily ℓ hV ρ

/-- `B8c` (*potential automorphy*) is the statement that if `ℓ ≥ 5` is a prime then
every irreducible hardly ramified representation of `Gal(ℚ̄/ℚ)` on a two-dimensional
`𝔽_ℓ`-vector space is potentially automorphic.
See `2026_EPSRC_TCC_course/level08.tex`. -/
def B8c : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod ℓ) V] [Module.Finite (ZMod ℓ) V]
    [Module.Free (ZMod ℓ) V] (hV : Module.rank (ZMod ℓ) V = 2)
    (ρ : GaloisRep ℚ (ZMod ℓ) V),
  ρ.IsIrreducible →
  IsHardlyRamified (hℓ.odd_of_ne_two (by omega)) hV ρ →
  ρ.IsPotentiallyAutomorphic ℓ (Module.finrank_eq_of_rank_eq (by exact_mod_cast hV))

/-- `B8` is the conjunction of the statements `B8a` (automorphic lifting),
`B8b` (automorphic spreading out) and `B8c` (potential automorphy).
See `2026_EPSRC_TCC_course/level08.tex`. -/
def B8 : Prop := B8a ∧ B8b ∧ B8c

/-- Part (a) of the automorphy lifting theorem: in the setting of the automorphy
lifting theorem (`ρ` an absolutely irreducible `S`-minimal mod-`ℓ` representation of
the absolute Galois group of a totally real field `F` unramified at `ℓ`, absolutely
irreducible after restriction to `F(ζ_ℓ)`, and automorphic of level `S`), the universal
`S`-minimal deformation ring of `ρ` exists and is a module-finite `𝓞`-algebra (and
hence a module-finite `ℤ_ℓ`-algebra). See `2026_EPSRC_TCC_course/level09.tex`. -/
def ALTa : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- Let `𝓞` be a complete Noetherian local `ℤ_ℓ`-algebra, module-finite over `ℤ_ℓ`
  -- (e.g. the Witt vectors of a finite field of characteristic `ℓ`),
  ∀ (𝓞 : Type) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [Finite (IsLocalRing.ResidueField 𝓞)]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝓞) 𝓞]
    [Algebra ℤ_[ℓ] 𝓞] [IsLocalHom (algebraMap ℤ_[ℓ] 𝓞)] [Module.Finite ℤ_[ℓ] 𝓞],
  -- let `F` be a totally real field
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
  -- which is unramified at `ℓ`,
  Algebra.IsUnramifiedIn (NumberField.RingOfIntegers F) (Ideal.span {(ℓ : ℤ)}) →
  ∀ (hp : 2 < Module.finrank F (CyclotomicField ℓ F)),
  -- let `S` be a finite set of finite places of `F` not dividing `ℓ`,
  ∀ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
  (∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F), ↑ℓ ∈ v.asIdeal → v ∉ S) →
  -- and let `ρ : Gal(F̄/F) → GL_2(𝕜)` (`𝕜` the residue field of `𝓞`) be absolutely
  -- irreducible
  ∀ (ρ : (Deformation.repnFunctor (Fin 2) (Γ F) 𝓞).obj .residueField)
    [Representation.IsAbsolutelyIrreducible.{0} (Deformation.toRepresentation ρ)],
  -- and `S`-minimal,
  ρ ∈ (Deformation.narrowSLiftFunctor 𝓞 ℓ S ρ).obj .residueField →
  -- absolutely irreducible after restriction to `Gal(F̄/F(ζ_ℓ))`,
  Representation.IsAbsolutelyIrreducible.{0}
    (((Deformation.toFramedGaloisRep ρ).map
      (algebraMap F (CyclotomicField ℓ F))).toRepresentation) →
  -- and automorphic of level `S`.
  (Deformation.toFramedGaloisRep ρ).IsAutomorphicOfLevel ℓ hp
    (by exact Module.finrank_fin_fun _) S →
  -- Then the universal `S`-minimal deformation ring of `ρ` exists
  ∃ (R : Deformation.ProartinianCat 𝓞)
    (_ : (Deformation.narrowSDeformationFunctor 𝓞 ℓ S ρ).toFunctor.CorepresentableBy R),
    -- and is module-finite over `𝓞`.
    Module.Finite 𝓞 R

/-- Part (b) of the automorphy lifting theorem: in the setting of the automorphy
lifting theorem, every `S`-minimal `ℓ`-adic lift of `ρ` is automorphic of level `S`.
Here, rather than quantifying over homomorphisms from the universal `S`-minimal
deformation ring to finite extensions of `ℚ_ℓ`, we quantify directly over the
`S`-minimal representations over local orders in such extensions, together with the
hypotheses on their reductions. See `2026_EPSRC_TCC_course/level09.tex`. -/
def ALTb : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ),
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- Let `F` be a totally real field
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
  -- which is unramified at `ℓ`,
  Algebra.IsUnramifiedIn (NumberField.RingOfIntegers F) (Ideal.span {(ℓ : ℤ)}) →
  ∀ (hp : 2 < Module.finrank F (CyclotomicField ℓ F)),
  -- let `S` be a finite set of finite places of `F` not dividing `ℓ`,
  ∀ (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F))),
  (∀ v ∈ S, ↑ℓ ∉ v.asIdeal) →
  -- and let `σ` be an `S`-minimal representation over a local order `R` in a finite
  -- extension of `ℚ_ℓ`,
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[ℓ] R] [IsLocalHom (algebraMap ℤ_[ℓ] R)] [ContinuousSMul ℤ_[ℓ] R]
    [Module.Finite ℤ_[ℓ] R] [Module.Free ℤ_[ℓ] R] [IsModuleTopology ℤ_[ℓ] R]
    (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Free R W]
    (hW : Module.rank R W = 2)
    (σ : GaloisRep F R W),
  IsSMinimal ℓ hW S σ →
  -- whose reduction `σ ⊗ k` is absolutely irreducible,
  ∀ (k : Type) [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[ℓ] k] [ContinuousSMul ℤ_[ℓ] k]
    [Algebra R k] [IsScalarTower ℤ_[ℓ] R k] [ContinuousSMul R k],
  Representation.IsAbsolutelyIrreducible.{0} (σ.baseChange k).toRepresentation →
  -- absolutely irreducible after restriction to `Gal(F̄/F(ζ_ℓ))`,
  Representation.IsAbsolutelyIrreducible.{0}
    (((σ.baseChange k).map (algebraMap F (CyclotomicField ℓ F))).toRepresentation) →
  -- and automorphic of level `S`.
  (σ.baseChange k).IsAutomorphicOfLevel ℓ hp
    (by rw [Module.finrank_baseChange]
        exact Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)) S →
  -- Then `σ` is automorphic of level `S`.
  σ.IsAutomorphicOfLevel ℓ hp (Module.finrank_eq_of_rank_eq (by exact_mod_cast hW)) S

/-- The automorphy lifting theorem (Wiles, Kisin, ...), the "final boss" of the proof
of Fermat's Last Theorem. It is an "R = T" theorem: part (a) says that the universal
`S`-minimal deformation ring `R` of a suitable automorphic mod-`ℓ` representation is
module-finite over `ℤ_ℓ` (the finiteness being obvious for the Hecke algebra `T`), and
part (b) says that all its specialisations in characteristic zero are automorphic.
See `2026_EPSRC_TCC_course/level09.tex`. -/
def ALT : Prop := ALTa ∧ ALTb

/-- `B9` is the conjunction of the statements `B8a`, `B8b`, `B8c` and the automorphy
lifting theorem `ALT`. See `2026_EPSRC_TCC_course/level09.tex`. -/
def B9 : Prop := B8a ∧ B8b ∧ B8c ∧ ALT

/-- `B10` is the conjunction of the statements `B8b`, `B8c` and the automorphy lifting
theorem `ALT`; the automorphic lifting statement `B8a` is a consequence of `ALT`.
See `2026_EPSRC_TCC_course/level10.tex`. -/
def B10 : Prop := B8b ∧ B8c ∧ ALT

/-- `B11` is the conjunction of the statement `B8c` and the automorphy lifting theorem
`ALT`; the automorphic spreading out statement `B8b` is a consequence of `ALT`.
See `2026_EPSRC_TCC_course/level11.tex`. -/
def B11 : Prop := B8c ∧ ALT

/-- `B12` is the automorphy lifting theorem `ALT`; the potential automorphy statement
`B8c` is a consequence of `ALT`. See `2026_EPSRC_TCC_course/level12.tex`. -/
def B12 : Prop := ALT

theorem B2_implies_B1 : B2 → B1 := FermatLastTheorem.of_p_ge_5

theorem B3_implies_B2 : B3 → B2 :=
  FreyPackage.fermatLastTheoremFor_p_ge_5

theorem B4_implies_B3 : B4 → B3 := by
  unfold B3 B4
  intro h
  rw [isEmpty_iff]
  intro P
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  -- Now let `ρbar` be the Galois representation on the p-torsion of the curve.
  let ρbar := (E.galoisRep p P.hppos)
  -- Deep work of Mazur from the 1970s implies that `ρbar` is an irreducible
  -- Galois representation;
  apply h P
  exact P.mazur

theorem B4_proof : B4 :=
  sorry

theorem B3_proof : B3 := B4_implies_B3 B4_proof

theorem B2_proof : B2 := B3_implies_B2 B3_proof

theorem B1_proof : B1 := B2_implies_B1 B2_proof

end FLT.Bosses

open FLT.Bosses

theorem flt : FermatLastTheorem :=
  B1_proof
