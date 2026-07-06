import FLT.Slop.DimensionTheorem.Numeric

/-!
# The Hilbert–Samuel function, `d(R)`, and `δ(R)`

Definitions of the quantities compared by the dimension theorem for a
Noetherian local ring `(R, 𝔪)` (the third, the Krull dimension, is Mathlib's
`ringKrullDim`), together with basic finiteness and monotonicity lemmas.

## Main definitions

* `DimensionTheorem.colength R I` — the length `ℓ_R(R ⧸ I)` as a natural
  number (`Module.length` truncated at `⊤`; by `colength_coe` nothing is lost
  when `I` is an ideal of definition).
* `DimensionTheorem.hilbertSamuel R` — the Hilbert–Samuel function
  `n ↦ ℓ_R(R ⧸ 𝔪ⁿ)`.
* `DimensionTheorem.growthDeg R` — `d(R)`, the least `d` such that
  `ℓ(R ⧸ 𝔪ⁿ) = O(nᵈ)`.
* `DimensionTheorem.minGenPrimary R` — `δ(R)`, the least number of generators
  (`Submodule.spanFinrank`) of an *ideal of definition* of `R`, i.e. an ideal
  with radical `𝔪`.

## Main results

* `length_quotient_ne_top_of_radical_eq` — quotients by ideals of definition
  have finite length; the Artinian input is Hopkins–Levitzki via Mathlib's
  `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`.
* `colength_le_colength`, `hilbertSamuel_monotone` — comparison lemmas.
* `length_quotient_eq_add` — additivity `ℓ(R/I) = ℓ(J/I) + ℓ(R/J)` for
  `I ≤ J`, from the exact sequence `0 → J/I → R/I → R/J → 0`.

## Design note

Classically (Atiyah–Macdonald Ch. 11; Stacks Project, tag 00KQ) `d(R)` is
defined as the degree of the Hilbert–Samuel polynomial, whose existence is the
Hilbert–Serre theorem. This development instead takes the growth-order
formulation above, which requires no graded machinery; the two definitions
agree once eventual polynomiality is known. Upgrading `growthDeg` to the
polynomial degree (i.e. formalizing Hilbert–Serre) is the natural next step.
-/

namespace DimensionTheorem

open IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The length of `R ⧸ I` as a natural number (junk value `0` when the length
is infinite; see `colength_coe` for the case of an ideal of definition). -/
noncomputable def colength (I : Ideal R) : ℕ :=
  (Module.length R (R ⧸ I)).toNat

/-- The Hilbert–Samuel function of a local ring: `n ↦ ℓ(R ⧸ 𝔪ⁿ)`. -/
noncomputable def hilbertSamuel (n : ℕ) : ℕ :=
  colength R (maximalIdeal R ^ n)

/-- The growth degree `d(R)` of the Hilbert–Samuel function: the least `d` such
that `ℓ(R ⧸ 𝔪ⁿ) = O(nᵈ)`.

Classically, for a Noetherian local ring, this is the degree of the
Hilbert–Samuel polynomial. The present development does not construct that
eventual polynomial; it uses this Big-O formulation as the formal invariant. -/
noncomputable def growthDeg : ℕ :=
  sInf {d | GrowthLE (hilbertSamuel R) d}

/-- `δ(R)`: the minimal number of generators of an ideal of definition of `R`,
i.e. of an `𝔪`-primary ideal (an ideal with radical `𝔪`). -/
noncomputable def minGenPrimary : ℕ :=
  sInf {k | ∃ I : Ideal R, I.radical = maximalIdeal R ∧ I.spanFinrank = k}

/-- A nontrivial quotient of a local ring is local. (Instance so that
`hilbertSamuel (R ⧸ I)` elaborates.) -/
instance (I : Ideal R) [Nontrivial (R ⧸ I)] : IsLocalRing (R ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

variable {R}

section Finiteness

variable [IsNoetherianRing R]

/-- A quotient by an ideal of definition is an Artinian ring. -/
lemma isArtinianRing_quotient_of_radical_eq {I : Ideal R}
    (h : I.radical = maximalIdeal R) : IsArtinianRing (R ⧸ I) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  refine ⟨⟨(maximalIdeal.isMaximal R).isPrime, h ▸ Ideal.le_radical⟩, ?_⟩
  intro p hp _
  rw [← h]
  exact hp.1.radical_le_iff.mpr hp.2

/-- A quotient by an ideal of definition has finite length over `R`. -/
lemma length_quotient_ne_top_of_radical_eq {I : Ideal R}
    (h : I.radical = maximalIdeal R) : Module.length R (R ⧸ I) ≠ ⊤ := by
  have hA : IsArtinian (R ⧸ I) (R ⧸ I) := isArtinianRing_quotient_of_radical_eq h
  have hN : IsNoetherian (R ⧸ I) (R ⧸ I) := by
    rw [← isNoetherianRing_iff]; infer_instance
  rw [Module.length_eq_of_surjective (S := R) (R := R ⧸ I) (M := R ⧸ I)
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

/-- For an ideal of definition, `colength` really is the length. -/
lemma colength_coe {I : Ideal R} (h : I.radical = maximalIdeal R) :
    (colength R I : ℕ∞) = Module.length R (R ⧸ I) := by
  rw [colength, ENat.coe_toNat (length_quotient_ne_top_of_radical_eq h)]

set_option linter.unusedSectionVars false in
/-- Powers of an ideal of definition are ideals of definition. -/
lemma radical_pow_eq_of_radical_eq {I : Ideal R} (h : I.radical = maximalIdeal R)
    {n : ℕ} (hn : n ≠ 0) : (I ^ n).radical = maximalIdeal R := by
  rw [I.radical_pow hn, h]

end Finiteness

section Monotone

variable [IsNoetherianRing R]

/-- `colength` is antitone: a larger ideal has a smaller quotient. The hypothesis
that `I` is an ideal of definition guarantees finiteness. -/
lemma colength_le_colength {I J : Ideal R} (hIJ : I ≤ J)
    (h : I.radical = maximalIdeal R) : colength R J ≤ colength R I := by
  have hle : (I : Submodule R R) ≤
      Submodule.comap LinearMap.id (J : Submodule R R) := by
    simpa using hIJ
  have hsurj : Function.Surjective
      (Submodule.mapQ (I : Submodule R R) (J : Submodule R R) LinearMap.id hle) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  exact ENat.toNat_le_toNat (Module.length_le_of_surjective _ hsurj)
    (length_quotient_ne_top_of_radical_eq h)

/-- The Hilbert–Samuel function is monotone. -/
lemma hilbertSamuel_monotone : Monotone (hilbertSamuel R) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  exact colength_le_colength (Ideal.pow_le_pow_right (Nat.le_succ n))
    (radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical
      (Nat.succ_ne_zero n))

set_option linter.unusedSectionVars false in
/-- Additivity of length along a pair of nested ideals `I ≤ J`, from the exact
sequence `0 → J/I → R/I → R/J → 0` (valid in `ℕ∞`, no finiteness needed). -/
lemma length_quotient_eq_add (I J : Ideal R) (hIJ : I ≤ J) :
    Module.length R (R ⧸ I) =
      Module.length R (Submodule.map (Submodule.mkQ (I : Submodule R R)) (J : Submodule R R)) +
      Module.length R (R ⧸ J) := by
  have hle : (I : Submodule R R) ≤
      Submodule.comap LinearMap.id (J : Submodule R R) := by
    simpa using hIJ
  have hsurj : Function.Surjective
      (Submodule.mapQ (I : Submodule R R) (J : Submodule R R) LinearMap.id hle) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  refine Module.length_eq_add_of_exact
    (Submodule.map (Submodule.mkQ (I : Submodule R R)) (J : Submodule R R)).subtype
    (Submodule.mapQ (I : Submodule R R) (J : Submodule R R) LinearMap.id hle)
    (Submodule.subtype_injective _) hsurj ?_
  rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.range_subtype, Submodule.comap_id]

end Monotone

end DimensionTheorem
