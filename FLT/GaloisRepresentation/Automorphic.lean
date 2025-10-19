/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kevin Buzzard
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Deformations.Categories

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

universe u

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
def GaloisRep.IsAutomorphic
    -- `F` is a totally real field
    {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    -- `𝒪` is in practice the integers in a finite extension of `ℚₚ` (for example
    -- the Witt vectors of a finite field) but in this definition we need less
    (𝒪 : Type u) [CommRing 𝒪]
    -- `A` is a "coefficient `𝒪`-algebra", the ring over which the representation is defined
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsLocalRing A] [Algebra 𝒪 A]
      [IsLocalProartinianAlgebra 𝒪 A]
    -- `p` is the residue characteristic of the local ring `A`
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
    -- `V` is the rank 2 free `A`-module on which the Galois group will act
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V]
      [Module.Free A V] (_hV : Module.finrank A V = 2)
    -- `ρ` is the Galois representation
    (ρ : GaloisRep F A V)
    -- `D` is the quaternion algebra where the modular form is coming from
    (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
    -- `D` is assumed to have discriminant 1
    (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
    -- `S` is the level of the modular form
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  -- We say `ρ` is *automorphic* if there's an `A`-valued automorphic eigenform
  ∃ (π : HeckeAlgebra F D r S 𝒪 →ₐ[𝒪] A),
  -- such that for all good primes `v` of `F`
    ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
      -- `ρ` is unramified at `v`,
      ρ.IsUnramifiedAt v ∧
      -- the det of `ρ(Frobᵥ)` (arithmetic Frobenius) is `N(v)` (i.e. `det(ρ) = cyclo`)
      (ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
      -- and the trace of `ρ(Frobᵥ)` is the eigenvalue of the form at `Tᵥ`
      LinearMap.trace A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T D r 𝒪 v hvS)
