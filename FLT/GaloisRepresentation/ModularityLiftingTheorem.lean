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

Suppose `F` is a totally real field of even degree, that `l>3` is a prime
unramified in `F`, and that `S` is a finite set of finite places of `F`
not dividing `l`. Suppose `k` is a finite field (with the discrete
topology) and `ρ : G_F → GL₂(k)` is an irreducible continuous representation
unramified outside `l` and `S`, with `det(ρ) = cyclo`, and such that for
all `v ∈ S` and `g ∈ Iᵥ` (a local inertia subgroup at `v`) we have
`trace(ρ(g))=2`. Finally suppose that `ρ` is flat at all primes above `v`.

Consider



-/
