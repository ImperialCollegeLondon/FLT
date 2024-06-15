import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Tactic

/-

# A "module topology" for a module over a topological ring.

Let `A` denote a topological ring.

If `M` is an `A`-module, then we can let `M` inherit a topology from `A`, namely
the finest topology which makes all the `A`-linear maps `A →ₗ[A] M` continuous.

## Constructions on modules.

This module-topology may or may not have the following cool properties:

1) Any `A`-linear map `φ : M →ₗ[A] N` is continuous.
2) The `A`-module topology on `Unit` is the topology already present on `Unit`.
3) The `A`-module topology on `A` is `A`s original topology.
4) The `A`-module topology on a product `M × N` of two modules-with-module-topology is
   the product topology.
5) The `A`-module topology on a power `M^n`, that is, `n → M` with `n : Type`, is the
(now possibly infinite) product topology.

6) Now say `A` is commutative. Then the tensor product of two `A`-modules is an `A`-module,
and so we can ask if the canonical bilinear map from `M × N` (with the module or product topology?
probably they're the same) to `M ⊗[A] N` is continuous.

7) Commutativity of `A` also gives spaces of `A`-linear maps the structure of `A`-modules,
so we can ask for example whether the function application map `M × (M →ₗ[A] N) → N` is continuous.

8) We could also ask whether the evaluation map, from `M →ₗ[A] N` to the power space `N^M` of bare
functions from `M` (now considered only as an index set, so with no topology) to `N` is continuous.

-/

-- Let A be a ring, with a compatible topology.
variable (A : Type*) [CommRing A] [TopologicalSpace A] [TopologicalRing A]


/-- The "right topology" on a module `M` over a topological ring `A`. It's defined as
the finest topology on `M` which makes every `A`-linear map `A → M` continuous. It's called
the "right topology" because `M` goes on the right.  -/
abbrev Module.rtopology (M : Type*) [AddCommGroup M] [Module A M]: TopologicalSpace M :=
-- Topology defined as LUB of pushforward.
  ⨆ (f : A →ₗ[A] M), TopologicalSpace.coinduced f inferInstance

-- let `M` and `N` be `A`-modules
variable (M : Type*) [AddCommGroup M] [Module A M]
variable {N : Type*} [AddCommGroup N] [Module A N]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma Module.continuous_linear (e : M →ₗ[A] N) :
    @Continuous M N (Module.rtopology A M) (Module.rtopology A N) e := by
  sorry -- maybe some appropriate analogue of Hannah/Lugwig's proof will work?

-- A formal corollary should be that
def Module.homeomorphism_equiv (e : M ≃ₗ[A] N) :
    -- lean needs to be told the topologies explicitly in the statement
    let τM := Module.rtopology A M
    let τN := Module.rtopology A N
    M ≃ₜ N :=
  -- And also at the point where lean puts the structure together, unfortunately
  let τM := Module.rtopology A M
  let τN := Module.rtopology A N
  -- all the sorries should be formal.
  { toFun := e
    invFun := e.symm
    left_inv := sorry
    right_inv := sorry
    continuous_toFun := sorry
    continuous_invFun := sorry
  }

-- Claim: topology on A doesn't change
example : (inferInstance : TopologicalSpace A) = Module.rtopology A A := by
  sorry

-- claim: topology on the 1-point set is the canonical one
example : (inferInstance : TopologicalSpace Unit) = Module.rtopology A Unit := by
  sorry

example :
    let _τM : TopologicalSpace M := Module.rtopology A M
    let _τN : TopologicalSpace N := Module.rtopology A N
    (inferInstance : TopologicalSpace (M × N)) = Module.rtopology A (M × N) := by sorry

example :
    let _τM : TopologicalSpace M := Module.rtopology A M
    let _τN : TopologicalSpace N := Module.rtopology A N
    (inferInstance : TopologicalSpace (M × N)) = Module.rtopology A (M × N) := by sorry

example (ι : Type*) :
    let _τM : TopologicalSpace M := Module.rtopology A M
    (inferInstance : TopologicalSpace (ι → M)) = Module.rtopology A (ι → M) := by sorry

open scoped TensorProduct
lemma Module.continuous_bilinear :
    let _τM : TopologicalSpace M := Module.rtopology A _
    let _τN : TopologicalSpace N := Module.rtopology A _
    let _τMN : TopologicalSpace (M ⊗[A] N) := Module.rtopology A _
    Continuous (fun (mn : M × N) ↦ mn.1 ⊗ₜ mn.2 : M × N → M ⊗[A] N) := by sorry

-- Now say we have a non-commutative `A`-algebra `D` which is free of finite type.

-- are all these assumptions needed?
variable (D : Type*) [Ring D] [Algebra A D] [Module.Finite A D] [Module.Free A D]

instance Module.topologicalRing : @TopologicalRing D (Module.rtopology A D) _ :=
  let _ : TopologicalSpace D := Module.rtopology A D
  {
    continuous_add := by
      sorry
    continuous_mul := by
      sorry
    continuous_neg := by
      sorry }
