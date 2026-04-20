module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

/-

## Compatible families

-/

-- Note that `λ` is a reserved symbol in Lean, as Lean is a functional programming language,
-- so instead of lambda-adic representations we're doing `φ`-adic ones.

set_option linter.unusedVariables false in
/-- `GaloisRepFamily K E d` is an (unrelated) collection of d-dimensional
  p-adic Galois representations of the absolute Galois group of the field K,
  parametrised by field maps from the number field `E` into the algebraic
  closure of ℚ_p as p runs through the primes.
-/
@[nolint unusedArguments]
def GaloisRepFamily (K : Type*) [Field K]
    (E : Type*) [Field E] [NumberField E] (d : ℕ) : Type _ :=
    ∀ {p : ℕ} (_ : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p]),
    GaloisRep K (AlgebraicClosure ℚ_[p]) (Fin d → (AlgebraicClosure ℚ_[p]))

open IsDedekindDomain NumberField Polynomial

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

/-- A family `ρ_λ` of `E_λ`-adic Galois representations `GaloisRepFamily K E d` of the
absolute Galois group of a number field `K` is *compatible* if there is a finite set `S` of
finite places of `K` and, for each finite place `v` of `K` not in `S`, a monic
degree `d` polynomial `P_v` with coefficients in `E`, such that if
`v` and `λ` do not lie above the same rational prime then `ρ_λ` is unramified at `v`
and `P_v` is the characteristic polynomial of `ρ_λ(Frob_v)`, where `Frob_v` denotes
an arithmetic Frobenius element.

This is the weakest possible concept of a compatible family but it will
suffice for our needs.
-/
def GaloisRepFamily.isCompatible {K : Type*} [Field K] [NumberField K]
    {E : Type*} [Field E] [NumberField E] {d : ℕ} (ρ : GaloisRepFamily K E d) : Prop :=
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Pv : HeightOneSpectrum (𝓞 K) → E[X]),
    ∀ {p : ℕ} (hfp : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p])
      (v : HeightOneSpectrum (𝓞 K)),
    v ∉ S → (p : 𝓞 K) ∉ v.asIdeal →
      (ρ hfp φ).IsUnramifiedAt v ∧ ((ρ hfp φ).toLocal v (Frob v)).charpoly = (Pv v).map φ
