import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Algebra.Module.LinearMap.Defs
import FLT.Mathlib.Topology.Algebra.Monoid

/-!
# An "action topology" for modules over a topological ring

If `R` is a topological group (or even just a topological space) acting on an additive
abelian group `A`, we define the *action topology* to be the finest topology on `A`
making `• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology).

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).

## Mathematical details

A crucial observation is that if `M` is a topological `R`-module, if `A` is an `R`-module with no
topology, and if `φ : A → M` is linear, then the pullback of `M`'s topology to `A` is a topology
making `A` into a topological module. Let's for example check that `•` is continuous.
If `U ⊆ A` is open then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`,
and now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that if `φ : A → M` is a linear map between topological `R`-modules
modules and if `A` has the action topology, then `φ` is automatically continuous.
Indeed the argument above shows that if `A → M` is linear then the action
topology on `A` is `≤` the pullback of the action topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the action topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the previous paragraph shows that
the linear maps `A → M` are precisely the continuous linear maps
from (`A` with its action topology) to `M`, so the action topology is a left adjoint
to the forgetful functor.

This file develops the theory of the action topology. We prove that the action topology on
`R` as a module over itself is `R`'s original topology, that the action topology on a product
of modules is the product of the action topologies, and that the action topology on a quotient
module is the quotient topology.

We also show the slightly more subtle result that if `M`, `N` and `P` are `R`-modules
equipped with the action topology and if furthermore `M` is finite as an `R`-module,
then any bilinear map `M × N → P` is continuous.

As a consequence of this, we deduce that if `R` is a commutative topological ring
and `A` is an `R`-algebra of finite type as `R`-module, then `A` with its module
topology becomes a topological ring (i.e., multiplication is continuous).

## TODO

1) add the statement that the action topology is a functor from the category of `R`-modules
to the category of topological `R`-modules, and prove it's an adjoint

2) PRs to mathlib:

3) weaken ring to semiring in some freeness statements in mathlib and then weaken
the corresponding statements in this file (this might have been done?)

-/

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

-- I need commutativity of R because we don't have bilinear maps for non-commutative rings.
-- **TODO** ask on the Zulip whether this is an issue.
variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

-- R^n x B -> C bilinear is continuous for module topologies.
-- Didn't someone give a counterexample when not fg on MO?
-- This works for semirings
theorem Module.continuous_bilinear_of_pi_finite (ι : Type*) [Finite ι]
    (bil : (ι → R) →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : ((ι → R) × B → C)) := by
  classical
  -- far too long proof that a bilinear map bil : R^n x B -> C
  -- equals the function sending (f,b) to ∑ i, f(i)*bil(eᵢ,b)
  have foo : (fun fb ↦ bil fb.1 fb.2 : ((ι → R) × B → C)) =
      (fun fb ↦ ∑ᶠ i, ((fb.1 i) • (bil (Pi.single i 1) fb.2) : C)) := by
    ext ⟨f, b⟩
    simp_rw [← LinearMap.smul_apply]
    rw [← LinearMap.finsum_apply]
    congr
    simp_rw [LinearMap.smul_apply, ← LinearMap.map_smul]
    convert AddMonoidHom.map_finsum bil.toAddMonoidHom _
    · ext j
      simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
      symm
      -- Is there a missing delaborator? No ∑ᶠ notation
      change (∑ᶠ (i : ι), Pi.single i (f i)) j = f j
      -- last tactic has no effect
      rw [finsum_apply (Set.toFinite _)]
      convert finsum_eq_single (fun i ↦ Pi.single i (f i) j) j
        (by simp (config := {contextual := true})) using 1
      simp
    · apply Set.toFinite _--(Function.support fun x ↦ f x • Pi.single x 1)
  rw [foo]
  haveI : ContinuousAdd C := toContinuousAdd R C
  exact continuous_finsum (fun i ↦ by fun_prop) (locallyFinite_of_finite _)

theorem Module.continuous_bilinear_of_finite_free [TopologicalSemiring R] [Module.Finite R A]
    [Module.Free R A] (bil : A →ₗ[R] B →ₗ[R] C) :
    Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
  let hι : Fintype ι := Module.Free.ChooseBasisIndex.fintype R A
  let b : Basis ι R A := Module.Free.chooseBasis R A
  let elinear : A ≃ₗ[R] (ι → R) := b.equivFun
  let bil' : (ι → R) →ₗ[R] B →ₗ[R] C := bil.comp elinear.symm.toLinearMap
  have := Module.continuous_bilinear_of_pi_finite ι bil'
  have foo : (fun ab ↦ (bil ab.1) ab.2 : A × B → C) = (fun fb ↦ bil' fb.1 fb.2) ∘
    (fun ab ↦ (elinear ab.1, ab.2) : A × B → (ι → R) × B) := by
    ext ⟨a, b⟩
    simp [bil']
  rw [foo]
  apply Continuous.comp this
  apply Continuous.prod_mk
  · exact continuous_of_linearMap (elinear.toLinearMap ∘ₗ (LinearMap.fst R A B))
  · fun_prop

end semiring_bilinear

section ring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommRing R] [TopologicalRing R]

variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

-- This needs rings
theorem Module.continuous_bilinear_of_finite [Module.Finite R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R A
  let bil' : (Fin m → R) →ₗ[R] B →ₗ[R] C := bil.comp f
  have := Module.continuous_bilinear_of_pi_finite (Fin m) bil'
  let φ := f.prodMap (LinearMap.id : B →ₗ[R] B)
  have foo : Function.Surjective (LinearMap.id : B →ₗ[R] B) :=
    Function.RightInverse.surjective (congrFun rfl)
  have hφ : Function.Surjective φ := Function.Surjective.prodMap hf foo
  have := (isQuotientMap_of_surjective hφ).2
  rw [this, continuous_def]
  intro U hU
  rw [isOpen_coinduced, ← Set.preimage_comp]
  suffices Continuous ((fun ab ↦ (bil ab.1) ab.2) ∘ φ : (Fin m → R) × B → C) by
    rw [continuous_def] at this
    convert this _ hU
  rw [show (fun ab ↦ (bil ab.1) ab.2 : A × B → C) ∘ φ = (fun fb ↦ bil' fb.1 fb.2) by
    ext ⟨a, b⟩
    simp [bil', φ]]
  apply Module.continuous_bilinear_of_finite_free

end ring_bilinear

section semiring_algebra

open scoped TensorProduct

-- these shouldn't be rings, they should be semirings
variable (R) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Free R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

@[continuity, fun_prop]
theorem continuous_mul'
    (R : Type*) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Free R D] [TopologicalSpace D]
    [IsModuleTopology R D] : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) :=
  Module.continuous_bilinear_of_finite (LinearMap.mul R D)

def topologicalSemiring : TopologicalSemiring D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul' R D

end semiring_algebra

section ring_algebra

-- confusion about whether these are rings or semirings should ideally be resolved
-- Is it: for D finite free R can be a semiring but for D finite it has to be a ring?
variable (R) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

include R in
@[continuity, fun_prop]
theorem continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := moduleTopology R _
  haveI : IsModuleTopology R (D ⊗[R] D) := { eq_moduleTopology' := rfl }
  convert Module.continuous_bilinear_of_finite <| (LinearMap.mul R D : D →ₗ[R] D →ₗ[R] D)

def Module.topologicalRing : TopologicalRing D where
  continuous_add := (toContinuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end ring_algebra
