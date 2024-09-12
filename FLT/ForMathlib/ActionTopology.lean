import FLT.ForMathlib.MiscLemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# An "action topology" for modules over a topological ring

If `R` is a topological space acting on an additive abelian group `A`, we define
the *action topology* to be the finest topology on `A` making `• : R × A → A`
and `+ : A × A → A` continuous (with all the products having the product topology).

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
The proof for `•` is similar.

A *topological module* for a topological ring `R` is an `R`-module `A` with a topology
making `+` and `•` continuous. A crucial observation is that if `M` is a topological `R`-module,
if `A` is an `R`-module with no topology, and if `φ : A → M` is linear, then the pullback of
`M`'s topology to `A` is a topology making `A` into a topological module. Let's for example
check that `•` is continuous. If `U ⊆ A` is open
then by definition of the pullback topology, `U = φ⁻¹(V)` for some open `V ⊆ M`, and
now the pullback of `U` under `•` is just the pullback along the continuous map
`id × φ : R × A → R × M` of the preimage of `V` under the continuous map `• : R × M → M`,
so it's open. The proof for `+` is similar.

As a consequence of this, we see that all linear maps are automatically continuous for
the action topology. Indeed the argument above shows that if `A → M` is linear then the action
topology on `A` is `≤` the pullback of the action topology on `M` (because it's the inf of a set
containing this topology) which is the definition of continuity.

We also deduce that the action topology is a functor from the category of `R`-modules
(`R` a topological ring) to the category of topological `R`-modules, and it is perhaps
unsurprising that this is an adjoint to the forgetful functor. Indeed, if `A` is an `R`-module
and `M` is a topological `R`-module, then the linear maps `A → M` are precisely the continuous
linear maps from `A` with its action topology, to `M`, so the action topology is a left adjoint
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

section basics

/-
This section is just boilerplate, defining the action topology and making
some infrastructure.
-/
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

/-- The action topology, for a module `A` over a topological ring `R`. It's the finest topology
making addition and the `R`-action continuous, or equivalently the finest topology making `A`
into a topological `R`-module. More precisely it's the Inf of the set of
topologies with these properties; theorems `continuousSMul` and `continuousAdd` show
that the action topology also has these properties. -/
abbrev actionTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

/-- A class asserting that the topology on a module over a topological ring `R` is
the action topology. See `actionTopology` for more discussion of the action topology. -/
class IsActionTopology [τA : TopologicalSpace A] : Prop where
  isActionTopology' : τA = actionTopology R A

theorem isActionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

/-- Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
theorem ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
  -- Proof: We need to prove that the product topology is finer than the pullback
  -- of the action topology. But the action topology is an Inf and thus a limit,
  -- and pullback is a right adjoint, so it preserves limits.
  -- We must thus show that the product topology is finer than an Inf, so it suffices
  -- to show it's a lower bound, which is not hard. All this is wrapped into
  -- `continuousSMul_sInf`.
  continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

/-- Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
theorem ActionTopology.continuousAdd : @ContinuousAdd A (actionTopology R A) _ :=
  continuousAdd_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

instance instIsActionTopology_continuousSMul [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousSMul R A := isActionTopology R A ▸ ActionTopology.continuousSMul R A

theorem isActionTopology_continuousAdd [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousAdd A := isActionTopology R A ▸ ActionTopology.continuousAdd R A

theorem actionTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    actionTopology R A ≤ τA := sInf_le ⟨‹ContinuousSMul R A›, ‹ContinuousAdd A›⟩

end basics

namespace ActionTopology

section zero

instance subsingleton (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]
    [Subsingleton A] [TopologicalSpace A] : IsActionTopology R A where
  isActionTopology' := by
    ext U
    simp only [isOpen_discrete]

end zero


section one

/-

We now fix once and for all a topological semiring `R`.

We first prove that the action topology on `R` considered as a module over itself,
is `R`'s topology.

-/
instance instId (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R] :
    IsActionTopology R R := by
  constructor
  /- Let `R` be a topological ring with topology τR. To prove that `τR` is the action
  topology, it suffices to prove inclusions in both directions.
  One way is obvious: addition and multiplication are continuous for `R`, so the
  action topology is finer than `R` because it's the finest topology with these properties.-/
  refine le_antisymm ?_ (actionTopology_le R R)
  /- The other way is more interesting. We can interpret the problem as proving that
  the identity function is continuous from `R` with the action topology to `R` with
  its usual topology to `R` with the action topology.
  -/
  rw [← continuous_id_iff_le]
  /-
  The idea needed here is to rewrite the identity function as the composite of `r ↦ (r,1)`
  from `R` to `R × R`, and multiplication on `R × R`, where we topologise `R × R`
  by giving the first `R` the usual topology and the second `R` the action topology.
  -/
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  /-
  It thus suffices to show that each of these maps are continuous.
  -/
  apply @Continuous.comp R (R × R) R τR (@instTopologicalSpaceProd R R τR (actionTopology R R))
      (actionTopology R R)
  · /-
    The map R × R → R is `•`, so by a fundamental property of the action topology,
    this is continuous. -/
    exact @continuous_smul _ _ _ _ (actionTopology R R) <| ActionTopology.continuousSMul ..
  · /-
    The map `R → R × R` sending `r` to `(r,1)` is a map into a product, so it suffices to show
    that each of the two factors is continuous. But the first is the identity function and the
    second is a constant function. -/
    exact @Continuous.prod_mk _ _ _ _ (actionTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (actionTopology R R) _

end one

section iso

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] --[TopologicalSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]

-- this is horrible. Why isn't it easy?
-- One reason: we are rolling our own continuous linear equivs!
-- **TODO** Ask about making continuous linear equivs properly
theorem iso (ehomeo : A ≃ₜ B) (elinear : A ≃ₗ[R] B) (he : ∀ a, ehomeo a = elinear a) :
    IsActionTopology R B where
  isActionTopology' := by
    simp_rw [ehomeo.symm.inducing.1, isActionTopology R A, actionTopology, induced_sInf]
    congr 1
    ext τ
    rw [Set.mem_image]
    -- it's the same picture
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · convert @induced_continuous_smul (f := @id R) (hf := continuous_id)
          (g := elinear.symm.toMulActionHom) (τA := σ) _ _ _ _ _
        ext x
        rw [@Homeomorph.symm_apply_eq, he, ← LinearEquiv.symm_apply_eq elinear]
        rfl
      · convert @induced_continuous_add (h := elinear.symm.toAddMonoidHom) σ _
        ext x
        rw [@Homeomorph.symm_apply_eq, he, ← LinearEquiv.symm_apply_eq elinear]
        rfl
    · rintro ⟨h1, h2⟩
      use τ.induced elinear
      rw [induced_compose]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact @induced_continuous_smul (f := @id R) (hf := continuous_id)
          (g := elinear.toMulActionHom) (τA := τ) _ _ _ _ _
      · exact @induced_continuous_add (h := elinear.toAddMonoidHom) τ _
      · nth_rw 2 [← induced_id (t := τ)]
        congr
        ext x
        simp [(he _).symm]

end iso

section function

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

/-- Every `R`-linear map between two `R`-modules with the canonical topology is continuous. -/
@[fun_prop, continuity]
theorem continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ := by
  -- the proof: We know that `+ : B × B → B` and `• : R × B → B` are continuous for the action
  -- topology on `B`, and two earlier theorems (`induced_continuous_smul` and
  -- `induced_continuous_add`) say that hence `+` and `•` on `A` are continuous if `A`
  -- is given the topology induced from `φ`. Hence the action topology is finer than
  -- the induced topology, and so the function is continuous.
  rw [isActionTopology R A, continuous_iff_le_induced]
  haveI : ContinuousAdd B := isActionTopology_continuousAdd R B
  exact sInf_le <| ⟨induced_continuous_smul (φ.toMulActionHom) continuous_id,
    induced_continuous_add φ.toAddMonoidHom⟩

@[fun_prop, continuity]
theorem continuous_of_linearMap (φ : A →ₗ[R] B) : Continuous φ :=
  continuous_of_distribMulActionHom φ.toDistribMulActionHom

variable (R) in
theorem continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C]
    [IsActionTopology R C] : Continuous (fun a ↦ -a : C → C) :=
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

end function

section surjection

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

-- Here I need the lemma about how quotients are open so I do need groups
-- because this relies on translates of an open being open
theorem coinduced_of_surjective {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (actionTopology R A) = actionTopology R B := by
  have : Continuous φ := continuous_of_linearMap φ
  rw [continuous_iff_coinduced_le, isActionTopology R A, isActionTopology R B] at this
  apply le_antisymm this
  have : ContinuousAdd A := isActionTopology_continuousAdd R A
  refine sInf_le ⟨?_, ?_⟩
  · apply @ContinuousSMul.mk R B _ _ (_)
    obtain ⟨foo⟩ : ContinuousSMul R A := inferInstance
    rw [continuous_def] at foo ⊢
    intro U hU
    rw [isOpen_coinduced, ← isActionTopology R A] at hU
    specialize foo _ hU; clear hU
    rw [← Set.preimage_comp, show φ ∘ (fun p ↦ p.1 • p.2 : R × A → A) =
      (fun p ↦ p.1 • p.2 : R × B → B) ∘
      (Prod.map id ⇑φ.toAddMonoidHom) by ext; simp, Set.preimage_comp] at foo
    clear! aB -- easiest to just remove topology on B completely now so typeclass inference
    -- never sees it
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap (AddMonoidHom.id R) φ.toAddMonoidHom)
      (_) (_) (_) foo
    · -- aesop would do this if `Function.surjective_id : Surjective ⇑(AddMonoidHom.id R)`
      -- was known by it
      apply (Set.image_preimage_eq _ _).symm
      rw [AddMonoidHom.coe_prodMap, Prod.map_surjective]
      exact ⟨Function.surjective_id, by simp_all⟩
    · -- should `apply continuousprodmap ctrl-space` find `Continuous.prod_map`?
      apply @Continuous.prod_map _ _ _ _ (_) (_) (_) (_) id φ continuous_id
      rw [continuous_iff_coinduced_le, isActionTopology R A]
    · rw [← isActionTopology R A]
      exact coinduced_prod_eq_prod_coinduced (AddMonoidHom.id R) φ.toAddMonoidHom
       (Function.surjective_id) hφ
  · apply @ContinuousAdd.mk _ (_)
    obtain ⟨bar⟩ := isActionTopology_continuousAdd R A
    rw [continuous_def] at bar ⊢
    intro U hU
    rw [isOpen_coinduced, ← isActionTopology R A] at hU
    specialize bar _ hU; clear hU
    rw [← Set.preimage_comp, show φ ∘ (fun p ↦ p.1 + p.2 : A × A → A) =
      (fun p ↦ p.1 + p.2 : B × B → B) ∘
      (Prod.map ⇑φ.toAddMonoidHom ⇑φ.toAddMonoidHom) by ext; simp, Set.preimage_comp] at bar
    clear! aB -- easiest to just remove topology on B completely now
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap φ.toAddMonoidHom φ.toAddMonoidHom)
      (_) (_) (_) bar
    · aesop
    · apply @Continuous.prod_map _ _ _ _ (_) (_) (_) (_) <;>
      · rw [continuous_iff_coinduced_le, isActionTopology R A]; rfl
    · rw [← isActionTopology R A]
      exact coinduced_prod_eq_prod_coinduced φ φ hφ hφ


end surjection


section prod

variable {R : Type*} [TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsActionTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [TopologicalSpace N] [IsActionTopology R N]

instance prod : IsActionTopology R (M × N) := by
  constructor
  haveI : ContinuousAdd M := isActionTopology_continuousAdd R M
  haveI : ContinuousAdd N := isActionTopology_continuousAdd R N
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
  obtain ⟨this⟩ : @ContinuousAdd (M × N) (actionTopology R (M × N)) _ :=
    ActionTopology.continuousAdd _ _
  refine @Continuous.comp _ ((M × N) × (M × N)) _ (_) (_) (_) _ _ this ?_
  refine (@continuous_prod_mk _ _ _ (_) (_) (_) _ _).2 ⟨?_, ?_⟩
  · refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inl R M N)) ?_ continuous_fst
    apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (actionTopology _ _) (?_)
    exact @IsActionTopology.mk _ _ _ _ _ (_) rfl
  · refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inr R M N)) ?_ continuous_snd
    apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (actionTopology _ _) (?_)
    exact @IsActionTopology.mk _ _ _ _ _ (_) rfl

end prod

section Pi

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddCommGroup (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

/-
-- ActionTopology.iso.{u_1, u_2, u_3} {R : Type u_1} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
--   {A : Type u_2} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsActionTopology R A] {B : Type u_3}
--   [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B] (ehomeo : A ≃ₜ B) (elinear : A ≃ₗ[R] B)
--   (he : ∀ (a : A), ehomeo a = elinear a) [IsActionTopology R A] : IsActionTopology R B

-/
instance pi : IsActionTopology R (∀ i, A i) := by
  induction ι using Finite.induction_empty_option
  · case of_equiv X Y e _ _ _ _ _ =>
    exact iso (Homeomorph.piCongrLeft e) (LinearEquiv.piCongrLeft R A e) (fun _ ↦ rfl)
  · apply subsingleton
  · case h_option X _ hind _ _ _ _ =>
    let e : Option X ≃ X ⊕ Unit := Equiv.optionEquivSumPUnit X
    refine @iso (ehomeo := Homeomorph.piCongrLeft e.symm)
        (elinear := LinearEquiv.piCongrLeft R A e.symm)
        (he := fun f ↦ rfl) _ _ _ _ _ ?_
    apply @iso (ehomeo := (Homeomorph.sumPiEquivProdPi X Unit _).symm)
        (elinear := (LinearEquiv.sumPiEquivProdPi R X Unit _).symm)
        (he := fun f ↦ rfl) _ _ _ _ _ ?_
    refine @prod _ _ _ _ _ _ (_) (hind) _ _ _ (_) (?_)
    let φ : Unit → Option X := fun t ↦ e.symm (Sum.inr t)
    exact iso (Homeomorph.pUnitPiEquiv (fun t ↦ A (φ t))).symm
      (LinearEquiv.pUnitPiEquiv R (fun t ↦ A (φ t))).symm (fun a ↦ rfl)

end Pi

section semiring_bilinear

-- I need rings not semirings here, because ` ChooseBasisIndex.fintype` incorrectly(?) needs
-- a ring instead of a semiring. This should be fixed.
-- I also need commutativity because we don't have bilinear maps for non-commutative rings.
-- **TODO** ask on the Zulip whether this is an issue.
variable {R : Type*} [τR : TopologicalSpace R] [CommRing R]

-- similarly these don't need to be groups
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsActionTopology R C]

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
  haveI : ContinuousAdd C := isActionTopology_continuousAdd R C
  apply continuous_finsum (fun i ↦ by fun_prop)
  intro x
  use Set.univ
  simp [Set.toFinite _]

-- Probably this can be beefed up to semirings.
theorem Module.continuous_bilinear_of_finite_free [TopologicalSemiring R] [Module.Finite R A] [Module.Free R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
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

variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsActionTopology R C]

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
  rw [isActionTopology R (A × B), ← this, continuous_def]
  intro U hU
  rw [isOpen_coinduced, ← Set.preimage_comp]
  suffices Continuous ((fun ab ↦ (bil ab.1) ab.2) ∘ φ : (Fin m → R) × B → C) by
    rw [continuous_def] at this
    convert this _ hU
    rw [← prod.isActionTopology']
  rw [show (fun ab ↦ (bil ab.1) ab.2 : A × B → C) ∘ φ = (fun fb ↦ bil' fb.1 fb.2) by
    ext ⟨a, b⟩
    simp [bil', φ]]
  apply Module.continuous_bilinear_of_finite_free

end ring_bilinear

section semiring_algebra

-- these shouldn't be rings, they should be semirings
variable (R) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Fre(D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) e R D]
variable [TopologicalSpace D] [IsActionTopology R D]

open scoped TensorProduct

@[continuity, fun_prop]
theorem continuous_mul'
    (R) [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]
    (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Free R D] [TopologicalSpace D]
    [IsActionTopology R D]: Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := actionTopology R _
  haveI : IsActionTopology R (D ⊗[R] D) := { isActionTopology' := rfl }
  convert Module.continuous_bilinear_of_finite_free <| LinearMap.mul R D

-- this should be about top semirings
def Module.topologicalSemiring : TopologicalSemiring D where
  continuous_add := (isActionTopology_continuousAdd R D).1
  continuous_mul := continuous_mul' R D

end semiring_algebra

section ring_algebra

-- these shouldn't be rings, they should be semirings
variable (R) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]
variable [TopologicalSpace D] [IsActionTopology R D]

open scoped TensorProduct

-- @[continuity, fun_prop]
-- lemma continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
--   letI : TopologicalSpace (D ⊗[R] D) := actionTopology R _
--   haveI : IsActionTopology R (D ⊗[R] D) := { isActionTopology' := rfl }
--   convert Module.continuous_bilinear_of_finite <| LinearMap.mul R D

-- def Module.topologicalRing : TopologicalRing D where
--   continuous_add := (isActionTopology_continuousAdd R D).1
--   continuous_mul := continuous_mul' R D
--   continuous_neg := continuous_neg R D

end ring_algebra
