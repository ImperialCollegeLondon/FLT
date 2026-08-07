/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import FLT.Slop.CyclotomicAbsIrred.ModCyclotomicCharacter
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Group.End

/-!
# Flat characters of local Galois groups

Fix a prime `ℓ`, and let `ℚ_ℓ` denote the `ℓ`-adic completion of `ℚ` (implemented, as
everywhere in this repository, as the `v`-adic completion at the finite place `v` of `ℚ`
corresponding to `ℓ`).  For a finite extension `K/ℚ_ℓ` inside a fixed algebraic closure
`ℚ̄_ℓ`, with ring of integers `𝒪_K` (the integral closure of `𝒪_{ℚ_ℓ}` in `K`), and an
algebraically closed field `𝕂` of characteristic `ℓ`, we define what it means for a character

  `ψ : Gal(ℚ̄_ℓ/K) →* 𝕂ˣ`

to be **flat** (`IsFlatCharacter`): `ψ` is continuous for the discrete topology on `𝕂ˣ`
(i.e. has open kernel), and the one-dimensional `𝕂`-representation `𝕂(ψ)` of
`Gal(ℚ̄_ℓ/K)` is a subquotient of `A(ℚ̄_ℓ) ⊗ 𝕂` for some finite flat commutative group
scheme `A` over `𝒪_K` killed by `ℓ`.

Following the conventions of `GaloisRep.HasFlatProlongationAt`
(`FLT.Deformations.RepresentationTheory.GaloisRep`), the group scheme is encoded as a finite
flat Hopf algebra `A` over `𝒪_K`, and its `ℚ̄_ℓ`-points as the group
`Additive (K ⊗[𝒪_K] A →ₐ[K] ℚ̄_ℓ)` of `K`-algebra homomorphisms from the generic fibre,
with `Gal(ℚ̄_ℓ/K)` acting by postcomposition.  Two further encoding choices:

* Rather than putting hypotheses on the abstract points monoid, we ask (as in
  `HasFlatProlongationAt`) for an equivariant additive isomorphism `f` from the points to an
  auxiliary abelian group `P` equipped with an action `act` of `Gal(ℚ̄_ℓ/K)`.  The condition
  "`A` is killed by `ℓ`" is encoded as `∀ x : P, ℓ • x = 0`: for a *flat* group scheme over
  `𝒪_K`, being killed by `ℓ` is equivalent to its generic fibre being killed by `ℓ`
  (the coordinate ring injects into that of the generic fibre), which — the generic fibre
  being étale, since `K` has characteristic zero — is in turn equivalent to the group of
  `ℚ̄_ℓ`-points being killed by `ℓ`.  Note that commutativity of the group scheme is also
  subsumed: the points biject with the abelian group `P`, and a finite flat group scheme in
  characteristic zero fibre... more precisely the flat group scheme is commutative iff its
  (dense, by flatness) generic fibre is, iff its `ℚ̄_ℓ`-points are.
* "`𝕂(ψ)` is a subquotient of `A(ℚ̄_ℓ) ⊗_{𝔽_ℓ} 𝕂`" is encoded as: there are submodules
  `W₁ ≤ W₂` of `𝕂 ⊗[ℤ] P` with `W₁ ≠ W₂` such that every `σ` moves every `w ∈ W₂` to
  `ψ(σ) • w` modulo `W₁`.  (This forces `W₁` and `W₂` to be stable, and says exactly that the
  nonzero quotient `W₂/W₁` is `ψ`-isotypic, i.e. that `𝕂(ψ)` is a Jordan–Hölder constituent
  of `𝕂 ⊗ P`.  Since `P` is killed by `ℓ` and `𝕂` has characteristic `ℓ`, the tensor
  product over `ℤ` agrees with the tensor product over `𝔽_ℓ`.)

This definition is the interface between the two *assumed* statements S1 (the local theorem,
`FLT.Slop.CyclotomicAbsIrred.Assumed.flat_character_tame_bound`) and S2 (flatness of
stable-line characters, `FLT.Slop.CyclotomicAbsIrred.Assumed.isFlatCharacter_of_stable_line`);
see `abs_irred_v2.tex` §2 for the mathematical content and literature references.
-/

@[expose] public section

open IsDedekindDomain NumberField

open scoped TensorProduct

namespace CyclotomicAbsIrred

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The prime `ℓ`, considered as a finite place (height-one spectrum point) of `ℚ`. -/
noncomputable abbrev ellPlace : HeightOneSpectrum (𝓞 ℚ) :=
  Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime)

/-- The field `ℚ_ℓ` of `ℓ`-adic numbers, implemented as the adic completion of `ℚ` at the
place `ellPlace ℓ`. -/
noncomputable abbrev Qell : Type :=
  (ellPlace ℓ).adicCompletion ℚ

/-- The ring `ℤ_ℓ` of `ℓ`-adic integers, as a valuation subring of `ℚ_ℓ`. -/
noncomputable abbrev Zell : ValuationSubring (Qell ℓ) :=
  (ellPlace ℓ).adicCompletionIntegers ℚ

variable (K : IntermediateField (Qell ℓ) (AlgebraicClosure (Qell ℓ)))

/-- The ring of integers of a (finite) extension `K` of `ℚ_ℓ` inside `ℚ̄_ℓ`: the integral
closure of `ℤ_ℓ` in `K`. -/
noncomputable abbrev localRingOfIntegers : Type :=
  IntegralClosure (Zell ℓ) K

/-- A character `ψ : Gal(ℚ̄_ℓ/K) →* 𝕂ˣ` of the absolute Galois group of a finite extension
`K/ℚ_ℓ`, with values in an algebraically closed field `𝕂` of characteristic `ℓ`, is **flat**
if it is continuous (has open kernel) and the associated one-dimensional representation
`𝕂(ψ)` is a subquotient of `A(ℚ̄_ℓ) ⊗ 𝕂` for a finite flat group scheme `A` over `𝒪_K`
killed by `ℓ`.  See the module docstring for a discussion of the encoding.

The instances `[CharP 𝕂 ℓ]` and `[IsAlgClosed 𝕂]` are not used in the body, but they are
part of the intended setting of the definition, which is the interface for the assumed
statements S1 and S2 (`FLT.Slop.CyclotomicAbsIrred.Assumed`); dropping them here would make
those `sorry`ed statements assert more than the literature supports. -/
@[nolint unusedArguments]
def IsFlatCharacter (𝕂 : Type) [Field 𝕂] [CharP 𝕂 ℓ] [IsAlgClosed 𝕂]
    (ψ : K.fixingSubgroup →* 𝕂ˣ) : Prop :=
  IsOpen (ψ.ker : Set K.fixingSubgroup) ∧
  ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra (localRingOfIntegers ℓ K) A)
    (_ : Module.Flat (localRingOfIntegers ℓ K) A)
    (_ : Module.Finite (localRingOfIntegers ℓ K) A)
    (_ : Algebra.Etale K (K ⊗[localRingOfIntegers ℓ K] A))
    (P : Type) (_ : AddCommGroup P)
    (_ : DistribMulAction K.fixingSubgroup P)
    (f : Additive (K ⊗[localRingOfIntegers ℓ K] A →ₐ[K] AlgebraicClosure (Qell ℓ)) ≃+ P),
    -- `A` is killed by `ℓ` (equivalently, on the flat `A`, its points are)
    (∀ x : P, ℓ • x = 0) ∧
    -- `f` identifies the Galois action on the points of the generic fibre with the action on `P`
    (∀ (σ : K.fixingSubgroup)
      (p : K ⊗[localRingOfIntegers ℓ K] A →ₐ[K] AlgebraicClosure (Qell ℓ)),
      f (Additive.ofMul ((IntermediateField.fixingSubgroupEquiv K σ) • p)) =
        σ • (f (Additive.ofMul p))) ∧
    -- `𝕂(ψ)` is a subquotient of `𝕂 ⊗ P`
    ∃ W₁ W₂ : Submodule 𝕂 (𝕂 ⊗[ℤ] P), W₁ ≤ W₂ ∧ W₁ ≠ W₂ ∧
      ∀ (σ : K.fixingSubgroup), ∀ w ∈ W₂,
        LinearMap.baseChange 𝕂 (DistribSMul.toAddMonoidHom P σ).toIntLinearMap w
          - (ψ σ : 𝕂) • w ∈ W₁

end CyclotomicAbsIrred

end
