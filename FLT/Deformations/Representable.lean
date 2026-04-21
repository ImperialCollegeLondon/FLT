module

public import FLT.Deformations.LiftFunctor
public import FLT.Deformations.RepresentationTheory.Irreducible
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u

section

variable (n : Type) [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable [T0Space G] [TotallyDisconnectedSpace G] [CompactSpace G] -- profinite
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞] -- complete noetherian local
variable (ρ : (repnFunctor n G 𝓞).obj .residueField) [(toRepresentation ρ).IsAbsolutelyIrreducible]

lemma isCorepresentable_deformationFunctor :
    (deformationFunctor n G 𝓞 ρ).toFunctor.IsCorepresentable := by
  sorry -- de Smit and Lenstra, Proposition 2.3 (1).

end

noncomputable section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-!
Suppose `K` is a totally real number field with even degree, `l > 3` is a prime,
`𝓞` an `ℤₗ`-algebra which is noetherian complete local with finite residue field.
-/

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]
variable {K : Type u} [Field K] [NumberField K]
variable [NumberField.IsTotallyReal K] (hK : Even (Module.finrank ℚ K))
-- There's a glitch when `l = 3` when trying to find auxiliary primes when the rep is induced from a
-- character of `F(√-3)`. Hence the assumption `3 < l`.
variable (l : ℕ) [Fact l.Prime] (hl : 3 < l) [Algebra ℤ_[l] 𝓞]

/-!
Let `S` be a finite sets of finite primes of `K` not dividing `l`,
and `ρ : Gₖ → GL₂(κ)` (where `κ` is the residue field of `𝓞`)
be an absolutely irreducible galois representation.
-/

variable (S : Finset (Ω K)) (hS : ∀ v : Ω K, ↑l ∈ v.asIdeal → v ∉ S)
variable (ρ : (repnFunctor (Fin 2) (Γ K) 𝓞).obj .residueField)
variable [(toRepresentation ρ).IsAbsolutelyIrreducible]

/--
The functor of `S`-lifts of `ρ`, consisting of representations of `GL₂` satisfying:
1. It is a lift of `ρ`.
2. Its determinant is equal to `εₗ`, the `l`-adic cyclotomic character.
3. It is unramified outside `l` and `S`.
4. Its trace is `2` on `ker(Iᵥ → k(v)ˣ)`.
5. It is flat at all `v | l`.
-/
def SLiftFunctor : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) :=
  liftFunctor (Fin 2) _ 𝓞 ρ ⊓
  detConditionFunctor (Fin 2) 𝓞 l ⊓
  (⨅ (v : Ω K) (_ : ↑l ∉ v.asIdeal) (_ : v ∉ S), unramifiedFunctor (Fin 2) 𝓞 v) ⊓
  (⨅ (v : Ω K) (_ : v ∈ S), traceConditionFunctor 𝓞 v) ⊓
  (⨅ (v : Ω K) (_ : ↑l ∈ v.asIdeal), flatFunctor (Fin 2) 𝓞 v)

/--
The functor of narrow `S`-lifts of `ρ`, consisting of representations of `GL₂` satisfying:
1. It is a lift of `ρ`.
2. Its determinant is equal to `εₗ`, the `l`-adic cyclotomic character.
3. It is unramified outside `l` and `S`.
4. Its trace is `2` on `Iᵥ`.
5. It is flat at all `v | l`.
-/
def narrowSLiftFunctor : Subfunctor (repnFunctor (Fin 2) (Γ K) 𝓞) :=
  liftFunctor (Fin 2) _ 𝓞 ρ ⊓
  detConditionFunctor (Fin 2) 𝓞 l ⊓
  (⨅ (v : Ω K) (_ : ↑l ∉ v.asIdeal) (_ : v ∉ S), unramifiedFunctor (Fin 2) 𝓞 v) ⊓
  (⨅ (v : Ω K) (_ : v ∈ S), narrowTraceConditionFunctor 𝓞 v) ⊓
  (⨅ (v : Ω K) (_ : ↑l ∈ v.asIdeal), flatFunctor (Fin 2) 𝓞 v)

variable (hρ : ρ ∈ (narrowSLiftFunctor 𝓞 l S ρ).obj _)

include hK hl hS hρ in
lemma isCorepresentable_narrowSLiftFunctor :
    (narrowSLiftFunctor 𝓞 l S ρ).toFunctor.IsCorepresentable := by
  sorry

/-- The universal lifting ring `Rᵘⁿⁱᵛ` representing the functor of narrow `S`-lifts. -/
def narrowSLiftUniversalRing : ProartinianCat 𝓞 :=
  (isCorepresentable_narrowSLiftFunctor 𝓞 hK l hl S hS ρ hρ).has_corepresentation.choose

/-- The universal lifting ring `Rᵘⁿⁱᵛ` represents the functor of narrow `S`-lifts. -/
def narrowSLiftUniversalRingCorepresentableBy :
    (narrowSLiftFunctor 𝓞 l S ρ).toFunctor.CorepresentableBy
      (narrowSLiftUniversalRing 𝓞 hK l hl S hS ρ hρ) :=
  (isCorepresentable_narrowSLiftFunctor 𝓞 hK l hl S hS ρ hρ).has_corepresentation.choose_spec.some

end

end Deformation
