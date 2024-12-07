import FLT.ForMathlib.MiscLemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# An "action topology" for modules over a topological ring

If `R` is a topological group (or even just a topological space) acting on an additive
abelian group `A`, we define the *action topology* to be the finest topology on `A`
making `• : R × A → A` and `+ : A × A → A` continuous (with all the products having the
product topology).

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).

## Mathematical details

I (buzzard) don't know of any reference for this other than Sawin's mathoverflow answer,
so I expand some of the details here.

First note that there *is* a finest topology with this property! Indeed, topologies on a fixed
type form a complete lattice (infinite infs and sups exist). So if `τ` is the Inf of all
the topologies on `A` which make `+` and `•` continuous, then the claim is that `+` and `•`
are still continuous for `τ` (note that topologies are ordered so that finer topologies
are smaller). To show `+ : A × A → A` is continuous we equivalently need to show
that the pushforward of the product topology `τ × τ` along `+` is `≤ τ`, and because `τ` is
the greatest lower bound of the topologies making `•` and `+` continuous,
it suffices to show that it's `≤ σ` for any topology `σ` on `A` which makes `+` and `•` continuous.
However pushforward and products are monotone, so `τ × τ ≤ σ × σ`, and the pushforward of
`σ × σ` is `≤ σ` because that's precisely the statement that `+` is continuous for `σ`.
The proof for `•` follows mutatis mutandis.

A *topological module* for a topological ring `R` is an `R`-module `A` with a topology
making `+` and `•` continuous. The discussion so far has shown that the action topology makes `A`
into a topological module.

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

namespace ModuleTopology

open IsModuleTopology

section surjection

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] --[aA : TopologicalSpace A] [IsModuleTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] --[aB : TopologicalSpace B] [IsModuleTopology R B]

-- Here I need the lemma about how quotients are open so I do need groups
-- because this relies on translates of an open being open
theorem coinduced_of_surjective {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (moduleTopology R A) = moduleTopology R B := by
  letI : TopologicalSpace A := moduleTopology R A
  letI τB : TopologicalSpace B := moduleTopology R B
  haveI : IsModuleTopology R A := ⟨rfl⟩
  haveI : ContinuousAdd A := continuousAdd R A
  haveI : IsModuleTopology R B := ⟨rfl⟩
  haveI : ContinuousAdd B := continuousAdd R B
  have : Continuous φ := continuous_of_linearMap φ
  rw [continuous_iff_coinduced_le, eq_moduleTopology R A, eq_moduleTopology R B] at this
  apply le_antisymm this
  have : ContinuousAdd A := continuousAdd R A
  refine sInf_le ⟨?_, ?_⟩
  · apply @ContinuousSMul.mk R B _ _ (_)
    obtain ⟨foo⟩ : ContinuousSMul R A := inferInstance
    rw [continuous_def] at foo ⊢
    intro U hU
    rw [isOpen_coinduced, ← eq_moduleTopology R A] at hU
    specialize foo _ hU; clear hU
    rw [← Set.preimage_comp, show φ ∘ (fun p ↦ p.1 • p.2 : R × A → A) =
      (fun p ↦ p.1 • p.2 : R × B → B) ∘
      (Prod.map id ⇑φ.toAddMonoidHom) by ext; simp, Set.preimage_comp] at foo
    clear! τB -- easiest to just remove topology on B completely now so typeclass inference
    -- never sees it
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap (AddMonoidHom.id R) φ.toAddMonoidHom)
      (_) (_) (_) foo
    · -- aesop would do this if `Function.surjective_id : Surjective ⇑(AddMonoidHom.id R)`
      -- was known by it
      apply (Set.image_preimage_eq _ _).symm
      rw [AddMonoidHom.coe_prodMap, Prod.map_surjective]
      exact ⟨Function.surjective_id, by simp_all⟩
    · -- should `apply continuousprodmap ctrl-space` find `Continuous.prod_map`?
      apply @Continuous.prodMap _ _ _ _ (_) (_) (_) (_) id φ continuous_id
      rw [continuous_iff_coinduced_le, eq_moduleTopology R A]
    · rw [← eq_moduleTopology R A]
      exact coinduced_prod_eq_prod_coinduced (AddMonoidHom.id R) φ.toAddMonoidHom
       (Function.surjective_id) hφ
  · apply @ContinuousAdd.mk _ (_)
    obtain ⟨bar⟩ := continuousAdd R A
    rw [continuous_def] at bar ⊢
    intro U hU
    rw [isOpen_coinduced, ← eq_moduleTopology R A] at hU
    specialize bar _ hU; clear hU
    rw [← Set.preimage_comp, show φ ∘ (fun p ↦ p.1 + p.2 : A × A → A) =
      (fun p ↦ p.1 + p.2 : B × B → B) ∘
      (Prod.map ⇑φ.toAddMonoidHom ⇑φ.toAddMonoidHom) by ext; simp, Set.preimage_comp] at bar
    clear! τB -- easiest to just remove topology on B completely now
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap φ.toAddMonoidHom φ.toAddMonoidHom)
      (_) (_) (_) bar
    · aesop
    · apply @Continuous.prodMap _ _ _ _ (_) (_) (_) (_) <;>
      · rw [continuous_iff_coinduced_le, eq_moduleTopology R A]; rfl
    · rw [← eq_moduleTopology R A]
      exact coinduced_prod_eq_prod_coinduced (X := A) (Y := A) (S := B) (T := B) φ φ hφ hφ

end surjection

section prod

variable {R : Type*} [TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

instance prod : IsModuleTopology R (M × N) := by
  constructor
  haveI : ContinuousAdd M := toContinuousAdd R M
  haveI : ContinuousAdd N := toContinuousAdd R N
  refine le_antisymm ?_ <| sInf_le ⟨Prod.continuousSMul, Prod.continuousAdd⟩
  rw [← continuous_id_iff_le]
  rw [show (id : M × N → M × N) =
       (fun abcd ↦ abcd.1 + abcd.2 : (M × N) × (M × N) → M × N) ∘
       (fun ab ↦ ((ab.1, 0),(0, ab.2))) by
       ext ⟨a, b⟩ <;> simp]
  -- The rest of the proof is a massive fight against typeclass inference, which is desperate
  -- to always put the product topology on M × N, when we sometimes want the action topology
  -- (they are equal, but that's exactly what we're proving so we can't assume it yet).
  -- This issue stops the standard continuity tactics from working.
  obtain ⟨this⟩ : @ContinuousAdd (M × N) (moduleTopology R (M × N)) _ :=
    ModuleTopology.continuousAdd _ _
  refine @Continuous.comp _ ((M × N) × (M × N)) _ (_) (_) (_) _ _ this ?_
  haveI : @ContinuousSMul R (M × N) _ _ (moduleTopology R _) := continuousSMul R (M × N)
  refine (@continuous_prod_mk _ _ _ (_) (_) (_) _ _).2 ⟨?_, ?_⟩
  · refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inl R M N)) ?_ continuous_fst
    apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (moduleTopology _ _) (?_)
    exact continuousAdd R (M × N)
  · refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inr R M N)) ?_ continuous_snd
    apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (moduleTopology _ _) (?_)
    exact continuousAdd R (M × N)

end prod

section Pi

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddCommMonoid (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsModuleTopology R (A i)]

-- elsewhere
def ContinuousLinearEquiv.piCongrLeft (R : Type*) [Semiring R] {ι ι' : Type*}
    (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
    [∀ i, TopologicalSpace (φ i)]
    (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃L[R] (i : ι) → φ i where
  __ := Homeomorph.piCongrLeft e
  __ := LinearEquiv.piCongrLeft R φ e

-- elsewhere
def ContinuousLinearEquiv.sumPiEquivProdPi (R : Type*) [Semiring R] (S T : Type*)
    (A : S ⊕ T → Type*) [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
    [∀ st, TopologicalSpace (A st)] :
    ((st : S ⊕ T) → A st) ≃L[R] ((s : S) → A (Sum.inl s)) × ((t : T) → A (Sum.inr t)) where
  __ := LinearEquiv.sumPiEquivProdPi R S T A
  __ := Homeomorph.sumPiEquivProdPi S T A

-- elsewhere
def ContinuousLinearEquiv.pUnitPiEquiv (R : Type*) [Semiring R] (f : PUnit → Type*)
    [∀ x, AddCommMonoid (f x)] [∀ x, Module R (f x)] [∀ x, TopologicalSpace (f x)] :
    ((t : PUnit) → f t) ≃L[R] f () where
  __ := LinearEquiv.pUnitPiEquiv R f
  __ := Homeomorph.pUnitPiEquiv f

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
  have := coinduced_of_surjective hφ
  rw [eq_moduleTopology R (A × B), ← this, continuous_def]
  intro U hU
  rw [isOpen_coinduced, ← Set.preimage_comp]
  suffices Continuous ((fun ab ↦ (bil ab.1) ab.2) ∘ φ : (Fin m → R) × B → C) by
    rw [continuous_def] at this
    convert this _ hU
    rw [← prod.eq_moduleTopology']
  rw [show (fun ab ↦ (bil ab.1) ab.2 : A × B → C) ∘ φ = (fun fb ↦ bil' fb.1 fb.2) by
    ext ⟨a, b⟩
    simp [bil', φ]]
  apply Module.continuous_bilinear_of_finite_free

end ring_bilinear

section semiring_algebra

open scoped TensorProduct

open DedekindDomain

open scoped NumberField

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
