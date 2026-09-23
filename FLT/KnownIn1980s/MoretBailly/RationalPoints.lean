/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Over

/-!
# Rational points of a scheme, and their topology

Let `T` be a scheme over a field `K` and let `M` be a topological ring which
is a `K`-algebra (in the applications, `M` is a finite extension of the
completion of a number field `K` at a place `v`). This file defines:

* `AlgebraicGeometry.Scheme.specHomTopology` : the "`v`-adic" topology on the
  set of all scheme morphisms `Spec M ⟶ T`. It is the finest topology such
  that, for every affine open `U ⊆ T`, the natural inclusion
  `Hom_ring(Γ(T, U), M) → (Spec M ⟶ T)` is continuous, where the set of ring
  homomorphisms `Γ(T, U) → M` carries the topology of pointwise convergence.
* `AlgebraicGeometry.Scheme.pointsOver K M` : the set `T(M)` of `K`-morphisms
  `Spec M ⟶ T`, topologized as a subspace of the above.
* `AlgebraicGeometry.Scheme.pointsOver.map` : functoriality of `T(M)` in the
  `K`-algebra `M`.

If `T` is locally of finite type over `K` and `M` is a finite extension of a
completion `K_v` of a number field `K`, this recovers the classical `v`-adic
topology on `T(M)`: for `T` affine with a chosen presentation, `T(M)` is the
solution set of a system of polynomial equations in `M^n`, topologized by the
coordinatewise topology, and the general case is glued from affine pieces.
A reference for this construction is [Conrad, *Weil and Grothendieck
approaches to adelic points*], where its basic properties are developed
(functoriality, open/closed immersions give open/closed embeddings,
compatibility with products, smooth morphisms induce open maps, properness
gives compactness). None of these properties are formalized here; this file
contains only what is needed to *state* Moret-Bailly's theorem
(see `FLT.KnownIn1980s.MoretBailly.Statement`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (T : Scheme.{u})

/-- The topology on the set of morphisms `Spec M ⟶ T`, for `M` a topological
ring: the finest topology making, for every affine open `U ⊆ T`, the natural
map `(Γ(T, U) ⟶ M) → (Spec M ⟶ T)` continuous, where ring homomorphisms carry
the topology of pointwise convergence. For `T` locally of finite type over a
completion of a number field this is the classical `v`-adic topology. -/
@[implicit_reducible]
noncomputable def specHomTopology (M : Type u) [CommRing M] [TopologicalSpace M] :
    TopologicalSpace (Spec (CommRingCat.of M) ⟶ T) :=
  ⨆ U : T.affineOpens,
    TopologicalSpace.coinduced
      (fun ψ : Γ(T, U.1) ⟶ CommRingCat.of M ↦ Spec.map ψ ≫ U.2.isoSpec.inv ≫ U.1.ι)
      (TopologicalSpace.induced (fun ψ ↦ (ψ.hom : Γ(T, U.1) → M)) Pi.topologicalSpace)

variable (K : Type u) [CommRing K] [T.Over (Spec (CommRingCat.of K))]

/-- `T.pointsOver K M` is the set `T(M)` of `K`-morphisms `Spec M ⟶ T`, where
`T` is a scheme over `K` and `M` is a `K`-algebra. -/
def pointsOver (M : Type u) [CommRing M] [Algebra K M] : Type u :=
  { f : Spec (CommRingCat.of M) ⟶ T //
    f ≫ (T ↘ Spec (CommRingCat.of K)) = Spec.map (CommRingCat.ofHom (algebraMap K M)) }

/-- The `v`-adic topology on `T(M)`, as a subspace of the space of all
morphisms `Spec M ⟶ T` with the topology `Scheme.specHomTopology`. -/
noncomputable instance (M : Type u) [CommRing M] [Algebra K M] [TopologicalSpace M] :
    TopologicalSpace (T.pointsOver K M) :=
  TopologicalSpace.induced Subtype.val (T.specHomTopology M)

/-- A `K`-algebra homomorphism `g : M →ₐ[K] N` induces a map
`T(M) → T(N)` by composition with `Spec g`. -/
noncomputable def pointsOver.map {M N : Type u} [CommRing M] [CommRing N]
    [Algebra K M] [Algebra K N] (g : M →ₐ[K] N) (P : T.pointsOver K M) :
    T.pointsOver K N :=
  ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ P.1, by
    rw [Category.assoc, P.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom
      (RingHom.ext fun x ↦ g.commutes x))⟩

end AlgebraicGeometry.Scheme
