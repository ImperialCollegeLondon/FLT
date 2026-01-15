/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.GaloisRepresentation.Automorphic

/-!
# A modularity lifting theorem

I believe that the below is the modularity lifting theorem which we need.

Suppose `F` is a totally real field of even degree over `ℚ`, that `l>3` is a prime
unramified in `F`, and that `S` is a finite set of finite places of `F`
not dividing `l`. Notation: Let `G_F` denote the absolute Galois group of `F`, and if `v` is a
finite place of `F` then let `Dᵥ` and `Iᵥ` denote a decomposition and inertia group at `v`.

Suppose `k` is a finite field (with the discrete topology) and `ρbar : G_F → GL₂(k)`
is a continuous representation. Suppose furthermore
that `ρbar | G_{F(ζₗ)}` is absolutely irreducible, and that `ρbar` is modular of level `U₀(S)`
in the sense that it comes from a weight 2 level `U₀(S)` mod `l` automorphic form on a totally
definite quaternion algebra over `F` which is unramified at all finite places.
Note that this implies that `ρbar` has cyclotomic determinant, and is unramified outside
`l` and `S`.

Let us furthermore impose the following local conditions at the bad primes:

At S): If `v ∈ S` then `#k(v)=1 mod l` and `ρbar(g)=1` for all `g ∈ Dᵥ`.
At l): `ρbar` is flat at all primes above `l`.

We now consider deformations of `ρbar`.  Suppose `R` is a compact Hausdorff local topological
ring with residue field `k`. We say that a lift of `ρbar` to a continuous `ρ : G_F → GL₂(R)` is
an *S-lift* if `det(ρ)=cyclo`, `ρ` is unramified outside `l` and `S`,
`trace(ρ(g))=2` for all `v ∈ S` and `g ∈ Iᵥ`, and `ρ` is flat at
all primes above `l`. Say that an *S-deformation* is an equivalence class of S-lifts,
where `ρ₁` and `ρ₂ : G_F → GL₂(R)` are equivalent if `ρ₂=aρ₁a⁻¹`, where `a ∈ ker(GL₂(R)→GL₂(k))`.

Consider the functor sending a compact Hausdorff local topological ring `R`
with residue field `k` to the set of `S`-deformations of `ρbar. It is a theorem
that this functor is representable by a compact Hausdorff ring `R^{univ}`.

The main results in this file are the following claims:

1) The ℤₗ-algebra R^{univ} is a finite ℤₗ-module.
2) `R^{univ}` has Krull dimension 1.
3) (the modularity lifting theorem) If R is a complete DVR with field of fractions of
characteristic 0 and with residue field k, and if `ρ` is an `S`-lift of `ρbar`, then `ρ` is modular.
-/

--open scoped TensorProduct

--open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u -- u for number field / quaternion algebra.
universe v -- v for finite field / deformation ring

/--
A 2-dimensional Galois representation `ρ` of the absolute Galois group of a totally
real field of even degree is said to be automorphic if it comes from a weight 2 trivial
character square-free level automorphic form on a totally definite quaternion algebra
of discriminant 1. More precisely, the level at each bad prime v has to be of the form
(a *;0 a) mod v.

This is a far more restrictive definition of automorphic than is found in the literature,
however it will suffice for the purpose of proving FLT.
-/
-- @[nolint unusedArguments]
-- def GaloisRep.ModularityLiftingTheorem
--     -- `F` is a totally real field
--     {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
--     (p : ℕ) [Fact p.Prime]
--     {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
--     [ContinuousSMul ℤ_[p] A]
--     -- `V` is the rank 2 free `A`-module on which the Galois group will act
--     {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V]
--       [Module.Free A V] (_hV : Module.finrank A V = 2)
--     -- `ρ` is the Galois representation
--     (ρ : GaloisRep F A V)
--     -- `S` is the level of the modular form
--     (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
--   -- We say `ρ` is *automorphic* if there's a quaternion algebra D over F of discriminant 1
--   ∃ (D : Type u) (_ : Ring D) (_ : Algebra F D) (_ : IsQuaternionAlgebra F D)
--     (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
--   -- and an `A`-valued automorphic eigenform,
--   -- by which we mean a ℤ_p-linear map from the ℤ_p-Hecke algebra for (D,S) to `A`,
--     (π : HeckeAlgebra F D r S ℤ_[p] →ₐ[ℤ_[p]] A),
--   -- such that for all good primes `v` of `F`
--   ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
--     -- `ρ` is unramified at `v`,
--     ρ.IsUnramifiedAt v ∧
--     -- the det of `ρ(Frobᵥ)` (arithmetic Frobenius) is `N(v)` (i.e. `det(ρ) = cyclo`)
--     (ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
--     -- and the trace of `ρ(Frobᵥ)` is the eigenvalue of the form at `Tᵥ`
--     LinearMap.trace A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T D r ℤ_[p] v hvS)

-- instance {F E D : Type*}
