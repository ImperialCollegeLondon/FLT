import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Algebra.Module.LinearMap.Defs
import FLT.Mathlib.Topology.Algebra.Module.Basic
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

2a) weaken ring to semiring in some freeness statements in mathlib and then weaken
the corresponding statements in this file

2b) PR `induced_sInf`, `induced_continuous_smul`, `induced_continuous_add`,
  `isOpenMap_of_coinduced`, `LinearEquiv.sumPiEquivProdPi` and whatever else I use here.

-/

namespace IsModuleTopology

open ModuleTopology

-- this section PRed in mathlib #20012
section function

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B]
    [ContinuousAdd B] [ContinuousSMul R B]

variable (R) in
theorem continuousNeg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : ContinuousNeg C where
  continuous_neg :=
    haveI : ContinuousAdd C := IsModuleTopology.toContinuousAdd R C
    continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

variable (R) in
theorem topologicalAddGroup (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsModuleTopology R C] : TopologicalAddGroup C where
      continuous_add := (IsModuleTopology.toContinuousAdd R C).1
      continuous_neg := (continuousNeg R C).1

end function

-- this section PRed in mathlib #20012
section surjection

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommGroup A] [Module R A] [TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [τB : TopologicalSpace B] [IsModuleTopology R B]

open Topology in
/-- A linear surjection between modules with the module topology is a quotient map.
Equivalently, the pushforward of the module topology along a surjective linear map is
again the module topology. -/
theorem coinduced_of_surjective {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    IsQuotientMap φ where
  surjective := hφ
  eq_coinduced := by
    -- We need to prove that the topology on B is coinduced from that on A.
    -- First tell the typeclass inference system that A and B are topological groups.
    haveI := topologicalAddGroup R A
    haveI := topologicalAddGroup R B
    -- Because φ is linear, it's continuous for the module topologies (by a previous result).
    have this : Continuous φ := continuous_of_linearMap φ
    -- So the coinduced topology is finer than the module topology on B.
    rw [continuous_iff_coinduced_le] at this
    -- So STP the module topology on B is ≤ the topology coinduced from A
    refine le_antisymm ?_ this
    rw [eq_moduleTopology R B]
    -- Now let's remove B's topology from the typeclass system
    clear! τB
    -- and replace it with the coinduced topology (which will be the same, but that's what we're
    -- trying to prove). This means we don't have to fight with the typeclass system.
    letI : TopologicalSpace B := .coinduced φ inferInstance
    -- With this new topology on `B`, φ is a quotient map by definition,
    -- and hence an open quotient map by a result in the library.
    have hφo : IsOpenQuotientMap φ := sorry --AddMonoidHom.isOpenQuotientMap_of_isQuotientMap ⟨hφ, rfl⟩
                                            -- this is in current mathlib but we can't bump
                                            -- because of https://github.com/leanprover/lean4/pull/6325
    -- We're trying to prove the module topology on B is ≤ the coinduced topology.
    -- But recall that the module topology is the Inf of the topologies on B making addition
    -- and scalar multiplication continuous, so it suffices to prove
    -- that the coinduced topology on B has these properties.
    refine sInf_le ⟨?_, ?_⟩
    · -- In this branch, we prove that `• : R × B → B` is continuous for the coinduced topology.
      apply ContinuousSMul.mk
      -- We know that `• : R × A → A` is continuous, by assumption.
      obtain ⟨hA⟩ : ContinuousSMul R A := inferInstance
      /- By linearity of φ, this diagram commutes:
        R × A --(•)--> A
          |            |
          |id × φ      |φ
          |            |
         \/            \/
        R × B --(•)--> B
      -/
      have hφ2 : (fun p ↦ p.1 • p.2 : R × B → B) ∘ (Prod.map id φ) =
        φ ∘ (fun p ↦ p.1 • p.2 : R × A → A) := by ext; simp
      -- Furthermore, the identity from R to R is an open quotient map
      have hido : IsOpenQuotientMap (AddMonoidHom.id R) := .id
      -- as is `φ`, so the product `id × φ` is an open quotient map, by a result in the library.
      have hoq : IsOpenQuotientMap (_ : R × A → R × B) := IsOpenQuotientMap.prodMap .id hφo
      -- This is the left map in the diagram. So by a standard fact about open quotient maps,
      -- to prove that the bottom map is continuous, it suffices to prove
      -- that the diagonal map is continuous.
      rw [← hoq.continuous_comp_iff]
      -- but the diagonal is the composite of the continuous maps `φ` and `• : R × A → A`
      rw [hφ2]
      -- so we're done
      exact Continuous.comp hφo.continuous hA
    · /- In this branch we show that addition is continuous for the coinduced topology on `B`.
        The argument is basically the same, this time using commutativity of
        A × A --(+)--> A
          |            |
          |φ × φ       |φ
          |            |
         \/            \/
        B × B --(+)--> B
      -/
      apply ContinuousAdd.mk
      obtain ⟨hA⟩ := IsModuleTopology.toContinuousAdd R A
      have hφ2 : (fun p ↦ p.1 + p.2 : B × B → B) ∘ (Prod.map φ φ) =
        φ ∘ (fun p ↦ p.1 + p.2 : A × A → A) := by ext; simp
      rw [← (IsOpenQuotientMap.prodMap hφo hφo).continuous_comp_iff, hφ2]
      exact Continuous.comp hφo.continuous hA

end surjection

section prod

variable {R : Type*} [TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

/-- The product of the module topologies for two modules over a topological ring
is the module topology. -/
instance prod : IsModuleTopology R (M × N) := by
  constructor
  haveI : ContinuousAdd M := toContinuousAdd R M
  haveI : ContinuousAdd N := toContinuousAdd R N
  -- In this proof, `M × N` always denotes the product with its product topology.
  -- Addition `(M × N)² → M × N` and scalar multiplication `R × (M × N) → M × N`
  -- are continuous for the product topology (by results in the library), so the module topology
  -- on `M × N` is finer than the product topology (as it's the Inf of such topologies).
  -- It thus remains to show that the product topology is finer than the module topology.
  refine le_antisymm ?_ <| sInf_le ⟨Prod.continuousSMul, Prod.continuousAdd⟩
  -- Or equivalently, if `P` denotes `M × N` with the module topology,
  -- that the identity map from `M × N` to `P` is continuous.
  rw [← continuous_id_iff_le]
  -- Now let P denote M × N with the module topology.
  let P := M × N
  letI τP : TopologicalSpace P := moduleTopology R P
  haveI : IsModuleTopology R P := ⟨rfl⟩
  haveI : ContinuousAdd P := ModuleTopology.continuousAdd R P
  -- We want to show that the identity map `i` from M × N to P is continuous.
  let i : M × N → P := id
  change @Continuous (M × N) P (_) τP i
  -- But the identity map can be written as (m,n) ↦ (m,0)+(0,n)
  -- or equivalently as i₁ ∘ pr₁ + i₂ ∘ pr₂, where prᵢ are the projections,
  -- the i's are linear inclusions M → P and N → P, and the addition is P × P → P.
  let i₁ : M →ₗ[R] P := LinearMap.inl R M N
  let i₂ : N →ₗ[R] P := LinearMap.inr R M N
  rw [show (i : M × N → P) =
       (fun abcd ↦ abcd.1 + abcd.2 : P × P → P) ∘
       (fun ab ↦ (i₁ ab.1,i₂ ab.2)) by
       ext ⟨a, b⟩ <;> aesop]
  -- and these maps are all continuous, hence `i` is too
  fun_prop

end prod

section Pi

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsModuleTopology R (A i)]

instance pi : IsModuleTopology R (∀ i, A i) := by
  induction ι using Finite.induction_empty_option
  · case of_equiv X Y e _ _ _ _ _ =>
    exact iso (ContinuousLinearEquiv.piCongrLeft R A e)
  · infer_instance
  · case h_option X _ hind _ _ _ _ =>
    let e : Option X ≃ X ⊕ Unit := Equiv.optionEquivSumPUnit X
    apply @iso (e := ContinuousLinearEquiv.piCongrLeft R A e.symm)
    apply @iso (e := (ContinuousLinearEquiv.sumPiEquivProdPi R X Unit _).symm)
    refine @prod _ _ _ _ _ _ (_) (hind) _ _ _ (_) (?_)
    let φ : Unit → Option X := fun t ↦ e.symm (Sum.inr t)
    exact iso (ContinuousLinearEquiv.pUnitPiEquiv R (fun t ↦ A (φ t))).symm

end Pi

section semiring_bilinear

-- I need rings not semirings here, because ` ChooseBasisIndex.fintype` incorrectly(?) needs
-- a ring instead of a semiring. This should be fixed if I'm right.
-- I also need commutativity because we don't have bilinear maps for non-commutative rings.
-- **TODO** ask on the Zulip whether this is an issue.
variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

-- similarly these don't need to be groups
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

theorem Module.continuous_bilinear_of_pi_finite (ι : Type*) [Finite ι]
    (bil : (ι → R) →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : ((ι → R) × B → C)) := by
  classical
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
      rw [finsum_apply]
      convert finsum_eq_single (fun i ↦ Pi.single i (f i) j) j
        (by simp (config := {contextual := true})) using 1
      simp
    · apply Set.toFinite _--(Function.support fun x ↦ f x • Pi.single x 1)
  rw [foo]
  haveI : ContinuousAdd C := toContinuousAdd R C
  apply continuous_finsum (fun i ↦ by fun_prop)
  intro x
  use Set.univ
  simp [Set.toFinite _]

-- Probably this can be beefed up to semirings.
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

-- This needs rings though
theorem Module.continuous_bilinear_of_finite [Module.Finite R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R A
  let bil' : (Fin m → R) →ₗ[R] B →ₗ[R] C := bil.comp f
  have := Module.continuous_bilinear_of_pi_finite (Fin m) bil'
  let φ := f.prodMap (LinearMap.id : B →ₗ[R] B)
  have foo : Function.Surjective (LinearMap.id : B →ₗ[R] B) :=
    Function.RightInverse.surjective (congrFun rfl)
  have hφ : Function.Surjective φ := Function.Surjective.prodMap hf foo
  have := (coinduced_of_surjective hφ).2
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
