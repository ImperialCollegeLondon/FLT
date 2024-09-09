/-
Copyright (c) 2024 Kevin Buzzaed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Hannah Scholz, Ludwig Monnerjahn
-/

import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Topology.Algebra.Module.FiniteDimension
-- next two should be all we need for basic file to compile
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs
/-

# An "action topology" for monoid actions.

If `R` is a topological monoid and `A` is a type with an `R`-action,
then `A` inherits a topology from this set-up, which we call the *dual* topology.
It's the `≤`-biggest topology (i.e., the one with
the least open sets) making all `R`-maps `A → R` continuous.

In many cases this topology is the one you expect. For example if `R` is a topological field
and `A` is a finite-dimensional real vector space over `R` then picking a basis gives `A` a
product topology, and one can check that this is the action topology. Hence the product
topology on `A` is independent of choice of basis. **TODO** I haven't actually proved this.

## Overview

## NEEDS REWRITING

Let `R` denote a topological space, let `A` be a type (without
a topology, for now) and say `R` acts on `A`,
i.e., we're given `• : R × A → A`. In applications `R` might
be a topological monoid and `A` an abelian group with an action of `R`.
Or `R` might be a topological ring, for example the reals, and `A` an `R`-module
or an `R`-algebra.

There are now at least two ways of inducing a topology on `A`
(in the module over a ring situation, at least three ways).
One could demand that `(· • a)` is continuous for all `a : A`, for example,
and put the universal topology for this property on `A`.
In the module case one could demand that all `R`-linear maps `A →ₗ[R] R`
are continuous. But the definition here is one proposed by Yury
Kudryashov. He pointed out that if `τᵢ : TopologicalSpace A` all make
the action maps `R × A → A` continuous, then the `Inf` of the `τᵢ`
also has this property. This means that there is a smallest (in the `≤` sense,
i.e. the most open sets) topology on `A` such that `• : R × A → A` is
continuous. We call topology the *action topology*. It is some kind
of "pushforward topology" on `A` coming from the `R`-action, but
it is not a pushforward in the `f_*` sense of the word because
there is no fixed `f : R → A`.

## Basic properties

**NOTHING PROVED**

We fix a type `R` with a topology, and we let it act on things. We say an *R*-type
is a type `A` equipped with `SMul R A`.

0) (Unit) `Unit` is an `R`-type with the trivial action, action topology is the given topology on `Unit`
(because there is only one topology on `Unit`)

1) (Id) If `R` is a topological monoid (so `*` is continuous) then `R` becomes an `R`-type via `*`,
and the action topology agrees with `R`'s original topology.

2) (Functions) If `A` and `B` are `R`-types with the action topologies, then any `R`-equivariant map
`φ : A →[R] B` is automatically continuous.

3) (Prod) The action topology on a product `A × B` of `R`-types is the product of the action
topologies **NOT YET PROVED, MAY NOT BE TRUE**

4) (Pi): The action topology on an indexed product of `R`-types is the product topology
**NOT YET PROVED, MAY NOT BE TRUE**

5) (Sigma) The action topology on `Σ i, A i` is whatever topology mathlib has on this
**NOT YET PROVED, MAY NOT BE TRUE**

Now say `R` is a commutative topological ring. **NOTHING BELOW HERE IS PROVED YET**

6) Say `A`, `B` are `R`-modules with their
action topology. Then the tensor product `A ⊗[R] B` is also an `R`-module.
and so we can ask if the canonical bilinear map from `A × B` (with the action or product topology?
probably they're the same) to `A ⊗[R] B` is continuous.

7) Commutativity of `R` also gives spaces of `R`-linear maps the structure of `R`-modules,
so we can ask for example whether the function application map `A × (A →ₗ[R] B) → B` is continuous.

8) We could also ask whether the evaluation map, from `A →ₗ[R] B` to the power space `B^A` of bare
functions from `A` (now considered only as an index set, so with no topology) to `B` is continuous.

-/

namespace dual_topology

section basics

variable (R : Type*) [Monoid R] [TopologicalSpace R] [ContinuousMul R]
variable (A : Type*) [SMul R A]

abbrev dualTopology : TopologicalSpace A :=
  ⨅ (f : A →[R] R), TopologicalSpace.induced f inferInstance

class IsDualTopology [τA : TopologicalSpace A] : Prop where
  isDualTopology' : τA = dualTopology R A

lemma isDualTopology [τA : TopologicalSpace A] [IsDualTopology R A] :
    τA = dualTopology R A :=
  IsDualTopology.isDualTopology' (R := R) (A := A)

-- is this true? Yes but maybe we can only prove it later
-- lemma DualTopology.continuousSMul : @ContinuousSMul R A _ _ (dualTopology R A) :=
--   continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

-- instance isDualTopology_continuousSMul (R A : Type*) [SMul R A]
--     [TopologicalSpace R] [τA : TopologicalSpace A] [h : IsDualTopology R A] :
--   ContinuousSMul R A where
--     continuous_smul := by
--       obtain ⟨h⟩ := ActionTopology.continuousSMul R A
--       simpa [isActionTopology R A] using h

end basics

-- Non-commutative variables
variable (R : Type*) [Monoid R] [τR: TopologicalSpace R] [ContinuousMul R]


lemma Module.topology_self : τR = dualTopology R R := by
  refine le_antisymm (le_iInf (fun i ↦ ?_)) <| sInf_le ⟨MulActionHom.id R, induced_id⟩
  rw [← continuous_iff_le_induced,
    show i = ⟨fun r ↦ r • i 1, fun _ _ ↦ mul_assoc _ _ _⟩ by
    ext r; dsimp; rw [← mul_one r, ← smul_eq_mul, map_smul]; simp; rfl]
  dsimp
  simp_rw [← smul_eq_mul]
  change Continuous fun (r : R) ↦ r * i 1
  fun_prop

-- let M be an A-module
variable {M : Type*} [SMul R M] [τM : TopologicalSpace M] [IsDualTopology R M]

-- let `N` be another module
variable {N : Type*} [SMul R N] [τN : TopologicalSpace N] [IsDualTopology R N]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma MulActionHom.continuous (e : M →[R] N) :
    Continuous e := by
  -- rewrite the goal (continuity of `e`) as in inequality:
  --(canonical topology) ≤ (pullback of induced topology)
  rw [continuous_iff_le_induced]
  rw [isDualTopology R N, isDualTopology R M]
  -- There's an already-proven lemma in mathlib that says the pullback of an `iInf` of
  -- topologies is the `iInf` of the pullbacks
  rw [induced_iInf]
  -- composite of the induced topologies is just topology induced by the composition
  -- need `simp_rw` because it's under a binder.
  simp_rw [induced_compose]
  -- so now we've got to prove `iInf S` is `≤ iInf T` for `S` the set of all linear
  -- maps from `M` to `A` and `T` the subset of those which factor through `e`.
  -- It of course suffices to prove `T` ⊆ `S`.
  apply sInf_le_sInf
  -- and this is a trivial calculation.
  rintro τ ⟨φ, rfl⟩
  exact ⟨φ.comp e, rfl⟩


-- sanity check: the topology on A^n is the product topology
example (ι : Type*) [Finite ι] :
    (Pi.topologicalSpace : TopologicalSpace (ι → R)) = dualTopology R _ := by
  -- suffices to prove that each topology is ≤ the other one
  apply le_antisymm
  · -- you're ≤ `iInf S` iff you're ≤ all elements of `S`
    apply le_iInf
    -- so take an element of `S`, the topology induced by `b : (ι → A) → A`
    intro b
    -- and we've got to prove that the product topology is `≤` it, which is the
    -- same as saying that `b` is continuous with the product topology on `A^ι`
    rw [← continuous_iff_le_induced]
    -- and we've already proved that all linear maps are continuous.
    -- might not be true in this generality, might need addition on
    -- R and for it to be continuous.
    sorry
    --apply LinearMap.continuous_on_pi b
  · -- the set Inf application works better here for some reason
    -- We've got to prove the module topology is ≤ the product topology, which is defined here to
    -- be the coarsest topology making all the projection maps continuous
    -- So it suffices to prove that all projections are linear
    apply sInf_le_sInf
    -- so let's look at the i'th projection
    rintro _ ⟨i, rfl⟩
    -- it's linear, because Lean has the projections as linear maps.
    exact ⟨⟨fun f ↦ f i, fun r p ↦ rfl⟩, rfl⟩

#exit

-- Commutative variables
variable (A : Type*) [CommRing A] [iA: TopologicalSpace A] [TopologicalRing A]

-- let M be an A-module
variable {M : Type*} [AddCommGroup M] [Module A M]

-- let `N` be another module
variable {N : Type*} [AddCommGroup N] [Module A N]

-- Now say we have a non-commutative `A`-algebra `D` which is free of finite type.
variable (D : Type*) [Ring D] [Algebra A D] [Module.Finite A D] [Module.Free A D]

lemma LinearMap.continuous_on_prod (f : (M × N) →ₗ[A] A) :
    @Continuous _ _ (@instTopologicalSpaceProd M N (Module.topology A) (Module.topology A)) _ f := by
  let _τM : TopologicalSpace M := Module.topology A
  let _τN : TopologicalSpace N := Module.topology A
  suffices Continuous fun (⟨m, n⟩ : M × N) ↦ f (⟨m, 0⟩) + f (⟨0, n⟩) by
    simpa [← LinearMap.map_add, Prod.mk_add_mk, add_zero, zero_add]
  apply Continuous.add
  . refine Continuous.fst' (?_ : Continuous fun m ↦ f (m, 0))
    exact Module.continuous_linear_to_ring A
      ({toFun := fun m ↦ f (m, 0),
        map_add' := by {intro x y; rw [← LinearMap.map_add, Prod.mk_add_mk, zero_add]},
        map_smul' := by intro m x; rw [←LinearMap.map_smul,
          RingHom.id_apply, Prod.smul_mk, smul_zero]})
  . apply @Continuous.snd' _ _ _ _ _ _ (fun n ↦ f (0, n))
    exact Module.continuous_linear_to_ring A
      ({toFun := fun n ↦ f (0, n),
        map_add' := by {intro x y; rw [← LinearMap.map_add, Prod.mk_add_mk, add_zero]},
        map_smul' := by intro m x; rw [← LinearMap.map_smul,
          RingHom.id_apply, Prod.smul_mk, smul_zero]})

-- We need that the module topology on a product is the product topology
lemma Module.prod_canonical :
    @instTopologicalSpaceProd M N (Module.topology A) (Module.topology A) =
    (Module.topology A : TopologicalSpace (M × N)) := by
  -- the goal is to prove that an iInf equals an inf (of two topologies).
  apply le_antisymm
  · apply le_iInf
    intro f
    rw [← continuous_iff_le_induced]
    apply LinearMap.continuous_on_prod A f
  · apply le_inf
    · rw [induced_iInf]
      apply le_iInf
      intro f
      rw [induced_compose]
      exact iInf_le _ (LinearMap.lcomp _ _ (LinearMap.fst _ _ _) _)
    · rw [induced_iInf]
      apply le_iInf
      intro f
      rw [induced_compose]
      exact iInf_le _ (LinearMap.lcomp _ _ (LinearMap.snd _ _ _) _)

instance Module.instCommAdd {P : Type*} [AddCommGroup P] [Module A P]:
@ContinuousAdd P (Module.topology A) _ := by
  apply @ContinuousAdd.mk _ (topology A)
  rw [prod_canonical A]
  exact continuous_linear A ((LinearMap.fst A P P) + (LinearMap.snd A P P))

variable [Module.Finite A M] [Module.Free A M] [Module.Finite A N] [Module.Free A N]

instance Module.instContinuousSMul : @ContinuousSMul A M _ _ (topology A) := by
  let _τM : TopologicalSpace M := Module.topology A
  apply @ContinuousSMul.mk A M _ _ (topology A)
  let ι := Free.ChooseBasisIndex A M
  have b : Basis ι A M := Free.chooseBasis A M
  suffices Continuous fun (p : A × M) ↦ ∑ i : ι, p.1 • b.repr p.2 i • b i by
    simpa [← Finset.smul_sum, Basis.sum_repr]
  apply continuous_finset_sum
  intro i _
  simp_rw [← mul_smul]
  suffices Continuous ((fun (a : A) ↦ a • b i) ∘ (fun (m : A × A) ↦ m.1 * m.2)
    ∘ (fun (m : A × M) ↦ (m.1, b.repr m.2 i))) from this
  apply Continuous.comp
  · exact Module.continuous_linear_from_ring A ((LinearMap.lsmul A M).flip (b i))
  apply Continuous.comp
  · exact continuous_mul
  · apply @Continuous.prod_map _ _ _ _ _ _ _ (topology A) (fun m ↦ m) (fun m ↦ b.repr m i)
    exact continuous_id
    exact Module.continuous_linear_to_ring A (b.coord i)

lemma Module.bilinear_continuous_of_continuous_on_basis {P : Type*} {ι κ : Type*} [Fintype ι]
    [Fintype κ] [AddCommGroup P] [Module A P] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace P] [ContinuousAdd P] (b : Basis ι A M) (d : Basis κ A N) (f : M →ₗ[A] N →ₗ[A] P)
    (contonbasis : ∀ (k : κ) (i : ι), Continuous fun (mn : M × N) ↦ ((d.repr mn.2) k •
    (b.repr mn.1) i • f (b i)) (d k)) :Continuous fun (mn : M × N) ↦ f mn.1 mn.2 := by
  suffices Continuous fun (mn : M × N) ↦  (∑ k : κ, (∑ i : ι, d.repr mn.2 k •
    b.repr mn.1 i • f (b i)) (d k)) by
    convert this using 1
    ext mn
    rw [← Basis.sum_repr b mn.1, ← Basis.sum_repr d mn.2]
    simp only [map_sum, LinearMapClass.map_smul, LinearMap.coeFn_sum, Finset.sum_apply,
      LinearMap.smul_apply, Finset.smul_sum, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one, Finsupp.univ_sum_single]
  apply continuous_finset_sum
  intro k _
  suffices Continuous fun (a : M × N) ↦ ∑ i : ι, ((d.repr a.2 k • b.repr a.1 i • f (b i)) (d k)) by
    simpa [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply continuous_finset_sum
  intro i _
  exact contonbasis k i

lemma Module.continuous_bilinear {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    [Module.Free A P] (f : M →ₗ[A] N →ₗ[A] P) :
    let _τMN : TopologicalSpace (M × N) := Module.topology A
    let _τP : TopologicalSpace P := Module.topology A
    Continuous (fun mn ↦ f mn.1 mn.2 : M × N → P)  := by
  let ι := Free.ChooseBasisIndex A M
  let κ := Free.ChooseBasisIndex A N
  let _τM : TopologicalSpace M := Module.topology A
  let _τN : TopologicalSpace N := Module.topology A
  let _τP : TopologicalSpace P := Module.topology A
  have b : Basis ι A M := Free.chooseBasis A M
  have d : Basis κ A N := Free.chooseBasis A N
  rw [← prod_canonical]
  apply Module.bilinear_continuous_of_continuous_on_basis A b d f
  intro k i
  apply Continuous.smul ?_ ?_
  · suffices Continuous ((d.coord k) ∘ Prod.snd) from this
    apply Continuous.comp
    · exact Module.continuous_linear_to_ring A (d.coord k)
    · exact continuous_snd
  apply Continuous.smul
  · suffices Continuous ((b.coord i) ∘ Prod.fst) from this
    apply Continuous.comp
    · apply Module.continuous_linear_to_ring A (b.coord i)
    · exact continuous_fst
  · apply continuous_const

-- Note that we have multiplication as a bilinear map.

-- Let's put the module topology on `D`
def D_topology : TopologicalSpace D := Module.topology A

instance moobar : @TopologicalRing D (Module.topology A) _ :=
  let _ : TopologicalSpace D := Module.topology A
  { -- first we prove that addition is continuous
    continuous_add := by
      -- the product topology is the module topology
      rw [Module.prod_canonical A]
      -- and addition is linear so it's continuous for the module topology
      exact Module.continuous_linear A ((LinearMap.fst A D D) + (LinearMap.snd A D D))
    -- multiplication is continuous:
    continuous_mul := by
      -- the product topology is the module topology
      rw [Module.prod_canonical A]
      -- and multiplication is bilinear so it's continuous for the module topology (I hope)
      apply Module.continuous_bilinear A (LinearMap.mul A D)
    -- finally negation is continuous because it's linear.
    continuous_neg := Module.continuous_linear A (-LinearMap.id) }

end dual_topology
