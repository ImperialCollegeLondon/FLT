/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Slop.CyclotomicAbsIrred.FlatCharacter
public import FLT.Slop.CyclotomicAbsIrred.ComplexConjugation
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# The assumed statements S1–S4

This file contains the four statements assumed (`sorry`ed) in the proof of the main theorem
of `FLT.Slop.CyclotomicAbsIrred.Main`, exactly as specified in §2 of `abs_irred_v2.tex`:

* **S1** (`flat_character_tame_bound`): *the local theorem*.  A flat continuous character
  `ψ` of the absolute Galois group of a ramified quadratic extension `K/ℚ_ℓ` (`ℓ ≥ 5`)
  satisfies `ψ(σ²) = χ(σ)^d` for all `σ` in the inertia subgroup of `ℚ_ℓ`, for some fixed
  `0 ≤ d ≤ 2`.  This carries all the arithmetic-geometric content (Raynaud's theory of finite
  flat group schemes: [Raynaud, *Schémas en groupes de type (p,…,p)*, Cor. 3.4.4], see also
  [Serre, *Propriétés galoisiennes…*, §1.13] and the write-up in the appendix of
  `abs_irred_v2.tex`) and is **the permanent `sorry`**: it is not expected to be formalized
  in the foreseeable future.

* **S2** (`isFlatCharacter_of_stable_line`): *flatness of stable-line characters*.  If a
  two-dimensional mod-`ℓ` representation of `Gal(ℚ̄/ℚ)` is flat at `ℓ` and a line `Λ` of the
  base-changed representation is stable under (the decomposition group restricted to) the
  absolute Galois group of a finite extension `K/ℚ_ℓ`, acting via a character `ψ`, then `ψ`
  is a flat character of `Gal(ℚ̄_ℓ/K)` in the sense of
  `CyclotomicAbsIrred.IsFlatCharacter`.  This is the standard stability of flatness under
  base change (`𝒪_{ℚ_ℓ} → 𝒪_K`) and subquotients (schematic closure,
  [Raynaud, §2.1, Prop. 2.3.1]; see [Darmon–Diamond–Taylor, Lemma 2.22] and
  [Ramakrishna, *On a variation of Mazur's deformation functor*, Lemma 2.1]), plus the
  automatic continuity of `ψ` (its values are eigenvalues of matrices in `GL₂(k)`).
  `sorry`ed for now; it can be discharged once finite flat group scheme infrastructure
  matures.

* **S3** (`exists_complex_conjugation`): there is an element `c` of `Gal(ℚ̄/ℚ)` with
  `c² = 1` and `χ(c) = -1` (any complex conjugation works).  This one is **proved** (no
  `sorry`): see `FLT.Slop.CyclotomicAbsIrred.ComplexConjugation`.

* **S4** (`modCycChar_image_localInertia`): the mod-`ℓ` cyclotomic character maps the inertia
  subgroup at `ℓ` *onto* `(ℤ/ℓ)ˣ`, because `ℓ` is totally ramified in `ℚ(ζ_ℓ)`
  (`Φ_ℓ(X+1)` is Eisenstein; mathlib knows this as part of `IsCyclotomicExtension.Rat`).
  Provable with current mathlib technology; `sorry`ed for now.  (Assessment: beyond
  irreducibility of `Φ_ℓ` over `ℚ_ℓ`, this needs the statement that for a totally ramified
  finite extension `E/ℚ_ℓ` inside `ℚ̄_ℓ`, the inertia subgroup of `Gal(ℚ̄_ℓ/ℚ_ℓ)` — in the
  repository's `AddSubgroup.inertia` formulation via the maximal ideal of the integral
  closure — surjects onto `Gal(E/ℚ_ℓ)`.  That in turn needs residue-field/unramified-tower
  infrastructure for `localInertiaGroup` that the repository does not yet have, so it is a
  genuine infrastructure project rather than an evening's work.)

The main theorem is proved in `FLT.Slop.CyclotomicAbsIrred.Main` assuming exactly these four
statements (plus the Clifford dichotomy quoted from PR #1067 in
`FLT.Slop.CyclotomicAbsIrred.CliffordTheory`).
-/

@[expose] public section

open IsDedekindDomain NumberField

open scoped TensorProduct

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

namespace CyclotomicAbsIrred

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **S1, the local theorem — the permanent `sorry`.**

Let `ℓ ≥ 5` be a prime and let `K/ℚ_ℓ` be a ramified quadratic extension: here encoded as an
intermediate field of `ℚ̄_ℓ/ℚ_ℓ` whose fixing subgroup `G_K = Gal(ℚ̄_ℓ/K)` has index 2 in
`G_{ℚ_ℓ}` and does not contain the inertia subgroup `I` of `ℚ_ℓ`.  Let
`ψ : G_K → 𝕂ˣ` be a flat continuous character (`IsFlatCharacter`), with `𝕂` algebraically
closed of characteristic `ℓ`.  Then there is an integer `0 ≤ d ≤ 2` such that

  `ψ(σ²) = χ(σ)^d` for all `σ ∈ I`,

where `χ = modCycChar ℓ ℚ_ℓ` is the mod-`ℓ` cyclotomic character (of `ℚ_ℓ`, evaluated on
`σ`, not `σ²`!) composed with the inclusion `(ℤ/ℓ)ˣ → 𝕂ˣ`.  Note that `σ` runs through the
inertia subgroup of `ℚ_ℓ`, not of `K`; since `G_K` has index 2, the square `σ²` automatically
lies in `G_K`, and the statement quantifies over all proofs `hσ2` of this membership.

Mathematical content: such a `ψ` is tame and of level 1, so is a power `θ_K^d` of the
fundamental tame character of `K` on inertia; Raynaud's theorem bounds the exponent by the
absolute ramification index `e(K/ℚ_ℓ) = 2 < ℓ - 1`; and a Kummer-theoretic computation gives
`θ_K(σ²) = χ(σ)` for `σ ∈ I`.  See the appendix of `abs_irred_v2.tex` for a complete proof
with references, and Remark `sanity` there for the three examples (`ℤ/ℓ`, `μ_ℓ`, and
Raynaud's `𝒪_K[X]/(X^ℓ - δX)` with `v(δ) = 1`) showing that each of `d = 0, 1, 2` occurs, so
that no stronger statement is correct. -/
theorem flat_character_tame_bound (hℓ5 : 5 ≤ ℓ)
    (𝕂 : Type) [Field 𝕂] [CharP 𝕂 ℓ] [IsAlgClosed 𝕂]
    (K : IntermediateField (Qell ℓ) (AlgebraicClosure (Qell ℓ)))
    (hK2 : K.fixingSubgroup.index = 2)
    (hram : ¬ localInertiaGroup (ellPlace ℓ) ≤ K.fixingSubgroup)
    (ψ : K.fixingSubgroup →* 𝕂ˣ)
    (hψ : IsFlatCharacter ℓ K 𝕂 ψ) :
    ∃ d ≤ 2, ∀ σ ∈ localInertiaGroup (ellPlace ℓ), ∀ (hσ2 : σ ^ 2 ∈ K.fixingSubgroup),
      ψ ⟨σ ^ 2, hσ2⟩ =
        Units.map (ZMod.castHom (dvd_refl ℓ) 𝕂).toMonoidHom (modCycChar ℓ (Qell ℓ) σ) ^ d := by
  sorry

/-- **S2, flatness of stable-line characters (assumed).**

Let `ρ : Gal(ℚ̄/ℚ) → GL(V)` be a two-dimensional mod-`ℓ` Galois representation which is flat
at `ℓ` (`GaloisRep.IsFlatAt`), let `K/ℚ_ℓ` be a finite extension inside `ℚ̄_ℓ`, and let
`Λ ⊆ 𝕂 ⊗ V` (`𝕂` the algebraic closure of `k`) be a line stable under the action of
`Gal(ℚ̄_ℓ/K)` — acting through the decomposition embedding `Gal(ℚ̄_ℓ/K) ⊆ Gal(ℚ̄_ℓ/ℚ_ℓ) →
Gal(ℚ̄/ℚ)` — with the action on `Λ` given by the character `ψ`.  Then `ψ` is a flat
character of `Gal(ℚ̄_ℓ/K)`.

Mathematical content: the base change `A ×_{ℤ_ℓ} 𝒪_K` of the finite flat group scheme
witnessing flatness of `ρ` is finite flat over `𝒪_K` with the same `ℚ̄_ℓ`-points as
`G_K`-module; `𝕂 ⊗_{𝔽_ℓ} A(ℚ̄_ℓ)` contains `𝕂 ⊗_k V` as a direct summand, and `Λ` is a
subquotient of it; and `ψ` automatically has open kernel since its values are eigenvalues of
the finitely many matrices `ρ(g) ∈ GL₂(k)`.  (Note the small interface point discussed in
`abs_irred_v2.tex` §4: `GaloisRep.IsFlatAt` carries no "killed by `ℓ`" condition, so this
`sorry` also absorbs the reduction that a finite flat group scheme whose generic fibre is
killed by `ℓ` is killed by `ℓ` — here `V` is killed by `ℓ` since it is a `k`-module.) -/
theorem isFlatCharacter_of_stable_line
    {k : Type} [Field k] [Finite k] [CharP k ℓ] [TopologicalSpace k] [DiscreteTopology k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hdim : Module.finrank k V = 2)
    (ρ : GaloisRep ℚ k V) (hflat : ρ.IsFlatAt (ellPlace ℓ))
    (K : IntermediateField (Qell ℓ) (AlgebraicClosure (Qell ℓ)))
    [FiniteDimensional (Qell ℓ) K]
    (Λ : Submodule (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] V))
    (hΛ : Module.finrank (AlgebraicClosure k) Λ = 1)
    (ψ : K.fixingSubgroup →* (AlgebraicClosure k)ˣ)
    (hψΛ : ∀ (σ : K.fixingSubgroup), ∀ x ∈ Λ,
      Slop.OddRep.baseChange (AlgebraicClosure k) ρ.toRepresentation
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (Qell ℓ)) σ.1) x
        = (ψ σ : AlgebraicClosure k) • x) :
    IsFlatCharacter ℓ K (AlgebraicClosure k) ψ := by
  sorry

/-- **S3, existence of a complex conjugation** (originally assumed; now proved, see
`CyclotomicAbsIrred.exists_conj_absoluteGaloisGroup`).

There is an element `c ∈ Gal(ℚ̄/ℚ)` with `c² = 1` and `χ(c) = -1` for the mod-`ℓ` cyclotomic
character `χ`: the restriction of complex conjugation (for any embedding `ℚ̄ ↪ ℂ`) to `ℚ̄`
has order two and inverts every root of unity. -/
theorem exists_complex_conjugation :
    ∃ c : Γ ℚ, c ^ 2 = 1 ∧ modCycChar ℓ ℚ c = -1 := by
  obtain ⟨c, hc2, hcroots⟩ := exists_conj_absoluteGaloisGroup
  refine ⟨c, hc2, ?_⟩
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have h : ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ) = modCycChar ℓ ℚ c := by
    apply modCycChar_unique
    intro t ht
    rw [mem_rootsOfUnity] at ht
    have htn : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ ℓ = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    have hct : c ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        = (((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))⁻¹ :=
      hcroots _ ℓ hℓpos htn
    have hval : ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ).val = ℓ - 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
      rw [Units.val_neg, Units.val_one]
      exact ZMod.val_neg_one m
    have hpow : (((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))⁻¹
        = ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (ℓ - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ']
      have : ℓ - 1 + 1 = ℓ := by omega
      rw [this, htn]
    change c ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
    rw [hct, hpow, hval]
  exact Units.ext h.symm

/-- **S4, total ramification (assumed).**

The mod-`ℓ` cyclotomic character, restricted along the decomposition embedding
`Gal(ℚ̄_ℓ/ℚ_ℓ) → Gal(ℚ̄/ℚ)`, maps the inertia subgroup at `ℓ` *onto* `(ℤ/ℓ)ˣ`.  Indeed `ℓ`
is totally ramified in `ℚ(ζ_ℓ)/ℚ` (`Φ_ℓ(X+1)` is Eisenstein at `ℓ`), so inertia surjects
onto `Gal(ℚ(ζ_ℓ)/ℚ) ≅ (ℤ/ℓ)ˣ`.  The ingredients are in mathlib
(`IsCyclotomicExtension.Rat`), but transporting them to the repository's
decomposition/inertia subgroups needs doing; `sorry`ed for now. -/
theorem modCycChar_image_localInertia :
    Subgroup.map ((modCycChar ℓ ℚ).comp
        (Field.absoluteGaloisGroup.map (algebraMap ℚ (Qell ℓ))).toMonoidHom)
      (localInertiaGroup (ellPlace ℓ)) = ⊤ := by
  sorry

end CyclotomicAbsIrred

end
