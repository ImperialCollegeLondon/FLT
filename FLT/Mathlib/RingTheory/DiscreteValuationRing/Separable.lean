/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import FLT.Mathlib.FieldTheory.Separable
public import FLT.Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Separability transfer over a discrete valuation ring

Proposed new Mathlib file `Mathlib.RingTheory.DiscreteValuationRing.Separable`: a monic
polynomial over a discrete valuation ring whose reduction is separable stays separable over
the fraction field.
-/

@[expose] public section

open IsLocalRing Polynomial

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

open IsLocalRing Polynomial

/-- A monic polynomial over a discrete valuation ring `R` whose reduction to the residue field is
separable stays separable over the fraction field `K`.

Proof: if `P.map (algebraMap R K)` is not separable, it has a monic common factor `g` of positive
degree with its derivative. Since `R` is integrally closed and `g` is a monic divisor of the
monic `P`, Gauss's lemma descends `g` to a monic `Q ∈ R[X]`, which then divides `P` and
`derivative P` already in `R[X]` (`map_dvd_map`). Reducing mod `𝔪_R`, the reduction of `Q` is a
common factor of positive degree of `P̄` and `derivative P̄`, contradicting `P̄.Separable`. -/
theorem Polynomial.Monic.separable_map_algebraMap_of_separable_map_residue {P : R[X]}
    (hmonic : P.Monic) (hsep : (P.map (residue R)).Separable) :
    (P.map (algebraMap R K)).Separable := by
  by_contra hns
  obtain ⟨g, hgmonic, hgdeg, hgdvd, hgdvd'⟩ :=
    exists_monic_dvd_dvd_derivative_of_not_separable (hmonic.map _).ne_zero hns
  obtain ⟨Q, hQmonic, hQ⟩ := hmonic.exists_monic_map_eq_of_monic_dvd_map hgmonic hgdvd
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdvdP : Q ∣ P := (map_dvd_map _ hinj hQmonic).mp (by rw [hQ]; exact hgdvd)
  have hdvdP' : Q ∣ derivative P := (map_dvd_map _ hinj hQmonic).mp
    (by rw [hQ, ← derivative_map]; exact hgdvd')
  refine not_isUnit_of_natDegree_pos (Q.map (residue R))
    (by rw [hQmonic.natDegree_map, ← hQmonic.natDegree_map (algebraMap R K), hQ]; exact hgdeg)
    (((separable_def _).mp hsep).isUnit_of_dvd' (map_dvd _ hdvdP) ?_)
  rw [derivative_map]
  exact map_dvd _ hdvdP'

end
