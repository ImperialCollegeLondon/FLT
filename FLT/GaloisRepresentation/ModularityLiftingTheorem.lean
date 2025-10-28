/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Deformations.Categories

/-!
# A modularity lifting theorem

I believe that the below is the modularity lifting theorem which we need.

Suppose `F` is a totally real field of even degree over `ℚ`, that `l>3` is a prime
unramified in `F`, and that `S` is a finite set of finite places of `F`
not dividing `l`. Suppose `k` is a finite field (with the discrete
topology) and `ρbar : G_F → GL₂(k)` is an irreducible continuous representation.
Suppose furthermore that `ρbar | G_{F(ζₗ)}` is absolutely irreducible, and that
`ρbar` is modular of level `U₀(S)` in the sense that it comes from a weight 2 mod `l` automorphic
form on a totally definite quaternion algebra over `F` which is unramified at all finite places.
Note that this impplies that `ρbar` has cyclotomic determinant, and is unramified outside
`l` and `S`.

Let us furthermore impose the following local conditions at the bad primes:

At S): `ρbar(g)=I` for all `v ∈ S` and `g ∈ Dᵥ`, a local decomposition group at `v`,
  and furthermore `#k(v)=1 mod l`.
At l): `ρbar` is flat at all primes above `l`.

We now consider deformations of `ρbar`.  Suppose `R` is a compact Hausdorff local topological
ring with residue field `k`. We say that a lift of `ρbar` to a continuous `ρ : G_F → GL₂(R)` is
an *S-lift* if `det(ρ)=cyclo`, `ρ` is unramified outside `l` and `S`,
`trace(ρ(g))=2` for all `v ∈ S` and `g ∈ Iᵥ` (a local inertia group at `v`), and `ρ` is flat at
all primes above `l`. Say that an *S-deformation* is an equivalence class of S-lifts,
where `ρ₁` and `ρ₂ : G_F → GL₂(R)` are equivalent if `ρ₂=aρ₁a⁻¹`, where `a ∈ ker(GL₂(R)→GL₂(k))`.

Consider the functor sending a compact Hausdorff local topological ring `R`
with residue field `k` to the set of S-deformations of `ρbar`. It is a theorem
that this functor is representable by a compact Hausdorff ring `R^{univ}`.

The main results in this file are the following claims:

1) The ℤ_ₗ-algebra R^{univ} is a finite ℤₗ-module. **TODO** do we also want to claim that it's free?
2) If R is a complete DVR with field of fractions of characteristic 0 and with residue field k,
and if `ρ` is an `S`-lift of `ρbar`, then `ρ` is modular.
-/
