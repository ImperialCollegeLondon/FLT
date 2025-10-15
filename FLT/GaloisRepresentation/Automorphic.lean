/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kevin Buzzard
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
import FLT.Deformations.RepresentationTheory.Basic
import FLT.Deformations.Categories
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
/-!
# Automorphic Galois representations

For our proof of Fermat's Last Theorem, the following definition is the most convenient.

We say that a 2-dimensional $p$-adic or a mod $p$ Galois representation of the absolute
Galois of a totally real field number field $F$ of even degree is *automorphic* if there
exists a totally definite quaternion algebra $D/F$ unramified at all finite places,
a finite set $S$ of finite places of $F$, and an automorphic form of level $U_1(S)$
(matrices congruent to $(a *;0 a)$ mod $v$ for all $v\in S$) and weight 2 for $D$
such that the Galois representation is associated to the form by the construction of
Carayol, Taylor et al.

## Notes

Several things here are specialized to our case. We demand that the quaternion algebra is
unramified everywhere because this is the only case that we need. We stick to weight 2
because this is the only case that we need. The level is also more restrictive but again
the only thing we need: the automorphic forms it catches are trivial at all infinite places
and either principal series`π(χ₁, χ₂)` with `χᵢ` tame and `χ₁χ₂` unramified or
Steinberg at all finite places.

-/


open scoped TensorProduct

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

open Deformation

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

universe u v -- u for number field / quaternion algebra, v for target ring

set_option linter.unusedVariables false in -- we don't assume p is prime, p in A,
-- dim(V) = 2 etc etc in the definition itself, but it would be mathematically ridiculous
-- to leave these assumptions out of the definition.

/--
A 2-dimensional Galois representation `ρ` of the absolute Galois group of a totally
real field of even degree is said to be automorphic if it comes from a weight 2 trivial
character square-free level automorphic form on a totally definite quaternion algebra
of discriminant 1. More precisely, the level at each bad prime v has to be of the form
(a *;0 a) mod v.

This is a far more restrictive definition of automorphic than is found in the literature,
however it will suffice for the purpose of proving FLT.
-/
@[nolint unusedArguments]
def GaloisRep.IsAutomorphicOfLevel
    -- `F` is a totally real field
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (p : ℕ) [Fact p.Prime]
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
    [ContinuousSMul ℤ_[p] A]
    -- `V` is the rank 2 free `A`-module on which the Galois group will act
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V]
      [Module.Free A V] (_hV : Module.finrank A V = 2)
    -- `ρ` is the Galois representation
    (ρ : GaloisRep F A V)
    -- `S` is the level of the modular form
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  -- We say `ρ` is *automorphic* if there's a quaternion algebra D over F of discriminant 1
  ∃ (D : Type u) (_ : Ring D) (_ : Algebra F D) (_ : IsQuaternionAlgebra F D)
    (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
  -- and an `A`-valued automorphic eigenform,
  -- by which we mean a ℤ_p-linear map from the ℤ_p-Hecke algebra for (D,S) to `A`,
    (π : HeckeAlgebra F D r S ℤ_[p] →ₐ[ℤ_[p]] A),
  -- such that for all good primes `v` of `F`
  ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
    -- `ρ` is unramified at `v`,
    ρ.IsUnramifiedAt v ∧
    -- the det of `ρ(Frobᵥ)` (arithmetic Frobenius) is `N(v)` (i.e. `det(ρ) = cyclo`)
    (ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
    -- and the trace of `ρ(Frobᵥ)` is the eigenvalue of the form at `Tᵥ`
    LinearMap.trace A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T D r ℤ_[p] v hvS)

instance {F E D : Type*}
    [Field F]
    [Field E] [Algebra F E]
    [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] :
    IsQuaternionAlgebra E (E ⊗[F] D) := sorry -- Ask Edison?

variable (p : ℕ) [Fact p.Prime] in
instance : ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p]) where
  continuous_smul := sorry

variable (p : ℕ) [Fact p.Prime] in
#synth NormedField (AlgebraicClosure ℚ_[p])

--variable (p : ℕ) [Fact p.Prime] in
--#synth ContinuousSMul ℚ_[p] (AlgebraicClosure ℚ_[p])

--variable (p : ℕ) [Fact p.Prime] in
--#synth ContinuousSMul ℤ_[p] ℚ_[p]

variable (p : ℕ) [Fact p.Prime] in
#synth IsScalarTower ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])
/-- Let `E/F` be a finite solvable extension of totally real fields of even degree,
let `ρ : Gal(F-bar/F) -> GL_2(Q_p-bar)` be a representation, which is irreducible
when restricted to `Gal(E-bar/E)`.
-/
theorem cyclic_base_change_for_quat_algs
    -- let F be a totally real number field of even degree
    {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Module.finrank ℚ F = 2)
    -- let E/F be a finite solvable extension
    {E : Type*} [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra F E] [IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]
    -- let p be a prime
    (p : ℕ) [Fact p.Prime]
    -- let ρ:Gal(F-bar/F)->GL_2(Q_p-bar) be a continuous representation
    {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure ℚ_[p]) V]
      [Module.Finite (AlgebraicClosure ℚ_[p]) V] [Module.Free (AlgebraicClosure ℚ_[p]) V]
      (hV : Module.finrank (AlgebraicClosure ℚ_[p]) V = 2)
    (ρ : GaloisRep F (AlgebraicClosure ℚ_[p]) V)
    --(hρirred : GaloisRep.isIrreducible (ρ.map (algebraMap F E)))
    -- need: rho | G_E = irred
    -- need: det(rho)=cyclo
    -- need: rho flat at p
    -- Let S be a finite set of finite places of F, not dividing p
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    -- need: rho unram outside pS
    -- need: if v ∈ S then rho has a tame rank 1 quotient at v
    -- then
    :
  (ρ.IsAutomorphicOfLevel p hV S) ↔ sorry := sorry
  --(∃ T r', (ρ.map (algebraMap F E)).IsAutomorphic 𝒪 hp hpA hV (E ⊗[F] D) r' T) := sorry

-- ask RLT about this mess
