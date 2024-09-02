import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs
import FLT.ForMathlib.MiscLemmas
import Mathlib -- just for development

/-!
# An "action topology" for modules over a topological ring

If `R` is a topological space acting on an additive abelian group `A`, we define
the *action topology* to be the finest topology on `A` making `• : R × A → A`
and `+ : A × A → A` continuous (with all the products having the product topology).

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).

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

lemma isActionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

/-- Scalar multiplication `• : R × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
lemma ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
  -- Proof: We need to prove that the product topology is finer than the pullback
  -- of the action topology. But the action topology is an Inf and thus a limit,
  -- and pullback is a right adjoint, so it preserves limits.
  -- We must thus show that the product topology is finer than an Inf, so it suffices
  -- to show it's a lower bound, which is not hard. All this is wrapped into
  -- `continuousSMul_sInf`.
  continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

/-- Addition `+ : A × A → A` is continuous if `R` is a topological
ring, and `A` is an `R` module with the action topology. -/
lemma ActionTopology.continuousAdd : @ContinuousAdd A (actionTopology R A) _ :=
  continuousAdd_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

instance instIsActionTopology_continuousSMul [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousSMul R A := isActionTopology R A ▸ ActionTopology.continuousSMul R A

lemma isActionTopology_continuousAdd [TopologicalSpace A] [IsActionTopology R A] :
    ContinuousAdd A := isActionTopology R A ▸ ActionTopology.continuousAdd R A

lemma actionTopology_le [τA : TopologicalSpace A] [ContinuousSMul R A] [ContinuousAdd A] :
    actionTopology R A ≤ τA := sInf_le ⟨‹ContinuousSMul R A›, ‹ContinuousAdd A›⟩

end basics

namespace ActionTopology

section zero

instance subsingleton (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A] [Subsingleton A]
    [TopologicalSpace A] : IsActionTopology R A := by
  constructor
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
  action topology is finer than `R` because it's the finest topology wih these properties.-/
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

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [τA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [τB : TopologicalSpace B]

-- this is horrible. Why isn't it easy?
lemma iso (ehomeo : A ≃ₜ B) (elinear : A ≃ₗ[R] B) (he : ∀ a, ehomeo a = elinear a)
    [IsActionTopology R A] : IsActionTopology R B where
  isActionTopology' := by
    have ⟨foo⟩ := ehomeo.symm.inducing
    rw [foo]
    simp_rw [isActionTopology R A, actionTopology]
    rw [induced_sInf]
    congr 1
    ext τ
    rw [Set.mem_image]
    -- bleurgh
    constructor
    · rintro ⟨σ, ⟨hσ1, hσ2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · convert @induced_continuous_smul (f := @id R) (hf := continuous_id) (g := elinear.symm.toMulActionHom) (τA := σ) _ _ _ _ _
        ext x
        rw [@Homeomorph.symm_apply_eq, he]
        exact (LinearEquiv.symm_apply_eq elinear).mp rfl
      · convert @induced_continuous_add (h := elinear.symm.toAddMonoidHom) σ _
        ext x
        rw [@Homeomorph.symm_apply_eq, he]
        exact (LinearEquiv.symm_apply_eq elinear).mp rfl
    · rintro ⟨h1, h2⟩
      use τ.induced elinear
      rw [induced_compose]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · convert @induced_continuous_smul (f := @id R) (hf := continuous_id) (g := elinear.toMulActionHom) (τA := τ) _ _ _ _ _
      · convert @induced_continuous_add (h := elinear.toAddMonoidHom) τ _
      · nth_rw 2 [← induced_id (t := τ)]
        congr
        ext x
        simp [(he _).symm]

end iso

section function

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

/-- Every `R`-linear map between two `R`-modules with the canonical topology is continuous. -/
@[fun_prop, continuity]
lemma continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ := by
  -- the proof: We know that `+ : B × B → B` and `• : R × B → B` are continuous for the action
  -- topology on `B`, and two earlier theorems (`induced_continuous_smul` and
  -- `induced_continuous_add`) say that hence `+` and `•` on `A` are continuous if `A`
  -- is given the topology induced from `φ`. Hence the action topology is finer than
  -- the induced topology, and so the function is continuous.
  rw [isActionTopology R A, continuous_iff_le_induced]
  haveI : ContinuousAdd B := isActionTopology_continuousAdd R B
  exact sInf_le <| ⟨induced_continuous_smul continuous_id (φ.toMulActionHom),
    induced_continuous_add φ.toAddMonoidHom⟩

@[fun_prop, continuity]
lemma continuous_of_linearMap (φ : A →ₗ[R] B) : Continuous φ :=
  continuous_of_distribMulActionHom φ.toDistribMulActionHom

variable (R) in
lemma continuous_neg (C : Type*) [AddCommGroup C] [Module R C] [TopologicalSpace C] [IsActionTopology R C] :
    Continuous (fun a ↦ -a : C → C) :=
  continuous_of_linearMap (LinearEquiv.neg R).toLinearMap

end function

section prod

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M] [aM : TopologicalSpace M] [IsActionTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [aN : TopologicalSpace N] [IsActionTopology R N]

instance prod : IsActionTopology R (M × N) := by
  constructor
  haveI : ContinuousAdd M := isActionTopology_continuousAdd R M
  haveI : ContinuousAdd N := isActionTopology_continuousAdd R N
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    have foo : (id : M × N → M × N) =
      (fun abcd ↦ abcd.1 + abcd.2 : (M × N) × (M × N) → M × N) ∘
      (fun ab ↦ ((ab.1, 0),(0, ab.2))) := by
      ext ⟨a, b⟩ <;> simp
    rw [foo]
    obtain ⟨bar⟩ : @ContinuousAdd (M × N) (actionTopology R (M × N)) _ := ActionTopology.continuousAdd _ _
    refine @Continuous.comp _ _ _ (_) ((_ : TopologicalSpace ((M × N) × (M × N)))) (_) _ _ bar ?_
    apply (@continuous_prod_mk _ _ _ (_) (_) (_) _ _).2
    constructor
    · -- bleurgh, fighting typeclass inference all the time, which wants one "canonical"
      -- topology on e.g. M × N.
      refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inl R M N)) ?_
        (continuous_fst : Continuous (Prod.fst : M × N → M))
      apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (actionTopology _ _) (?_)
      exact @IsActionTopology.mk _ _ _ _ _ (_) rfl
    · refine @Continuous.comp _ _ _ (_) (_) (_) _ ((LinearMap.inr R M N)) ?_
        (continuous_snd : Continuous (Prod.snd : M × N → N))
      apply @continuous_of_linearMap _ _ _ _ _ _ _ _ _ _ _ (actionTopology _ _) (?_)
      exact @IsActionTopology.mk _ _ _ _ _ (_) rfl
  · exact sInf_le ⟨Prod.continuousSMul, Prod.continuousAdd⟩

end prod

section Pi

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

-- not sure I'm going to do it this way -- see `pi` below.
-- instance piNat (n : ℕ) {A : Fin n → Type*} [∀ i, AddCommGroup (A i)]
--     [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
--     [∀ i, IsActionTopology R (A i)]: IsActionTopology R (Π i, A i) := by
--   induction n
--   · infer_instance
--   · case succ n IH _ _ _ _ =>
--     specialize IH (A := fun i => A (Fin.castSucc i))
--     sorry

variable {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, AddCommGroup (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

-- elsewhere
variable (R) in
def LinearEquiv.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, AddCommGroup (A st)] [∀ st, Module R (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₗ[R] (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
      toFun f := (fun s ↦ f (.inl s), fun t ↦ f (.inr t))
      map_add' f g := by aesop
      map_smul' := by aesop
      invFun fg st := Sum.rec (fun s => fg.1 s) (fun t => fg.2 t) st
      left_inv := by intro x; aesop
      right_inv := by intro x; aesop

-- elsewhere
def Homeomorph.sumPiEquivProdPi (S T : Type*) (A : S ⊕ T → Type*)
    [∀ st, TopologicalSpace (A st)] :
    (∀ (st : S ⊕ T), A st) ≃ₜ (∀ (s : S), A (.inl s)) × (∀ (t : T), A (.inr t)) where
      toFun f := (fun s ↦ f (.inl s), fun t ↦ f (.inr t))
      invFun fg st := Sum.rec (fun s => fg.1 s) (fun t => fg.2 t) st
      left_inv := by intro x; aesop
      right_inv := by intro x; aesop
      continuous_toFun := Continuous.prod_mk (by fun_prop) (by fun_prop)
      continuous_invFun := continuous_pi <| fun st ↦ by
        rcases st with s | t
        · simp
          fun_prop
        · simp
          fun_prop

-- elsewhere
def Homeomorph.pUnitPiEquiv (f : PUnit → Type*) [∀ x, TopologicalSpace (f x)]: ((t : PUnit) → (f t)) ≃ₜ f () where
  toFun a := a ()
  invFun a _t := a
  left_inv x := by aesop
  right_inv x := by aesop
  continuous_toFun := by simp; fun_prop
  continuous_invFun := by simp; fun_prop

-- elsewhere
variable (R) in
def LinearEquiv.pUnitPiEquiv (f : PUnit → Type*) [∀ x, AddCommGroup (f x)] [∀ x, Module R (f x)] :
    ((t : PUnit) → (f t)) ≃ₗ[R] f () where
  toFun a := a ()
  invFun a _t := a
  left_inv x := by aesop
  right_inv x := by aesop
  map_add' f g := rfl
  map_smul' r f := rfl

instance pi : IsActionTopology R (∀ i, A i) := by
  induction ι using Finite.induction_empty_option
  · case of_equiv X Y e hind _ _ _ _ =>
    specialize hind (A := fun x ↦ A (e x))
    apply iso (R := R) (A := ∀ j, A (e j)) (B := ∀ i, A i)
      (Homeomorph.piCongrLeft e) (by exact LinearEquiv.piCongrLeft R A e)
    aesop
  · apply subsingleton
  · case h_option X _ hind _ _ _ _ =>
    specialize hind (A := fun x ↦ A (some x))
    let e : Option X ≃ X ⊕ Unit := Equiv.optionEquivSumPUnit X
    refine @iso (ehomeo := Homeomorph.piCongrLeft e.symm)
      (elinear := LinearEquiv.piCongrLeft R A e.symm) _ (fun f ↦ rfl) ?_
    apply @iso (ehomeo := (Homeomorph.sumPiEquivProdPi X Unit _).symm)
      (elinear := (LinearEquiv.sumPiEquivProdPi R X Unit _).symm) _ (fun f ↦ rfl) ?_
    refine @prod _ _ _ _ _ _ (_) (hind) _ _ _ (_) (?_)
    let φ : Unit → Option X := fun t ↦ e.symm (Sum.inr t)
    let f : (∀ t, A (φ t)) ≃ₜ A (φ ()) := Homeomorph.pUnitPiEquiv _
    let g : (∀ t, A (φ t)) ≃ₗ[R] A (φ ()) := LinearEquiv.pUnitPiEquiv R _
    exact iso f.symm g.symm (fun a ↦ rfl)

end Pi

-- elsewhere
lemma finsum_apply {α ι N : Type*} [AddCommMonoid N] [Finite ι]
    (f : ι → α → N) (a : α) : (∑ᶠ i, f i) a = ∑ᶠ i, (f i) a := by
  classical
  simp only [finsum_def, dif_pos (Set.toFinite _), Finset.sum_apply]
  symm
  apply Finset.sum_subset <;> aesop

section bilinear

-- I need these because ` ChooseBasisIndex.fintype` needs a ring instead of a semiring
variable {R : Type*} [τR : TopologicalSpace R] [CommRing R] [TopologicalRing R]

-- similarly these don't need to be groups
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]
variable {C : Type*} [AddCommGroup C] [Module R C] [aC : TopologicalSpace C] [IsActionTopology R C]

lemma Module.continuous_bilinear_of_pi_finite (ι : Type*) [Finite ι]
    (bil : (ι → R) →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : ((ι → R) × B → C)) := by
  classical
  have foo : (fun fb ↦ bil fb.1 fb.2 : ((ι → R) × B → C)) = (fun fb ↦ ∑ᶠ i, ((fb.1 i) • (bil (Pi.single i 1) fb.2) : C)) := by
    ext ⟨f, b⟩
    simp_rw [← LinearMap.smul_apply]
    rw [← LinearMap.finsum_apply]
    congr
    simp_rw [LinearMap.smul_apply]
    simp_rw [← LinearMap.map_smul]
    --rw [LinearMap.finsum_apply]
    convert AddMonoidHom.map_finsum bil.toAddMonoidHom _
    ·
      ext j
      simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
      symm
      change (∑ᶠ (i : ι), Pi.single i (f i)) j = f j
      rw [finsum_apply]
      convert finsum_eq_single (fun i ↦ Pi.single i (f i) j) j _ using 1
      · simp
      · aesop
    · exact Set.toFinite _--(Function.support fun x ↦ f x • Pi.single x 1)
  rw [foo]
  haveI : ContinuousAdd C := isActionTopology_continuousAdd R C
  apply continuous_finsum (fun i ↦ by fun_prop)
  intro x
  use Set.univ
  simp [Set.toFinite _]

lemma Module.continuous_bilinear_of_finite_free [Module.Finite R A] [Module.Free R A]
    (bil : A →ₗ[R] B →ₗ[R] C) : Continuous (fun ab ↦ bil ab.1 ab.2 : (A × B → C)) := by
  let ι := Module.Free.ChooseBasisIndex R A
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

end bilinear

section algebra

-- these shouldn't be rings, they should be semirings
variable (R) [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D] [Module.Free R D]
variable [TopologicalSpace D] [IsActionTopology R D]

open scoped TensorProduct

@[continuity, fun_prop]
lemma continuous_mul : Continuous (fun ab ↦ ab.1 * ab.2 : D × D → D) := by
  letI : TopologicalSpace (D ⊗[R] D) := actionTopology R _
  haveI : IsActionTopology R (D ⊗[R] D) := { isActionTopology' := rfl }
  convert Module.continuous_bilinear_of_finite_free <| LinearMap.mul R D

def Module.topologicalRing : TopologicalRing D where
  continuous_add := (isActionTopology_continuousAdd R D).1
  continuous_mul := continuous_mul R D
  continuous_neg := continuous_neg R D

end algebra

-- everything from here on is dead code and ideas which use other topologies
section topology_problem

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommGroup B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

-- is this true? I used it with topology 4 to "reduce to the case of R^n -> B".
-- It might not be true here. Maybe the quotient topology `R / I` is strictly finer than
-- the action topology?
-- Here I need this lemma about how quotients are open so I need groups
-- because this relies on translates of an open being open
lemma coinduced_of_surjective {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (actionTopology R A) = actionTopology R B := by
  have : Continuous φ := continuous_of_linearMap φ
  rw [continuous_iff_coinduced_le] at this
  rw [isActionTopology R A, isActionTopology R B] at this
  apply le_antisymm this
  clear this
  apply sInf_le
  constructor
  · -- Is this true? Will Sawin thinks so
    apply @ContinuousSMul.mk R B _ _ (_)
    obtain ⟨foo⟩ : ContinuousSMul R A := inferInstance
    rw [continuous_def] at foo ⊢
    intro U hU
    rw [isOpen_coinduced, ← isActionTopology R A] at hU
    specialize foo _ hU
    rw [← Set.preimage_comp] at foo
    rw [show φ ∘ (fun p ↦ p.1 • p.2 : R × A → A) =
      (fun p ↦ p.1 • p.2 : R × B → B) ∘
      (Prod.map id ⇑φ.toAddMonoidHom) by ext; simp] at foo
    rw [Set.preimage_comp] at foo
    clear! aB -- easiest to just remove topology on B completely now
    have : ContinuousAdd A := isActionTopology_continuousAdd R A
    have := coinduced_prod_eq_prod_coinduced (AddMonoidHom.id R) φ.toAddMonoidHom (Function.surjective_id) hφ
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap (AddMonoidHom.id R) φ.toAddMonoidHom) (_) (_) (_) foo
    · -- aesop would do this if Function.surjective_id was known by it
      apply (Set.image_preimage_eq _ _).symm
      rw [AddMonoidHom.coe_prodMap, Prod.map_surjective]
      exact ⟨Function.surjective_id, by simp_all⟩
    · -- should `apply continuousprodmap ctrl-space` find `Continuous.prod_map`?
      apply @Continuous.prod_map _ _ _ _ (_) (_) (_) (_) id φ
      · exact continuous_id
      · rw [continuous_iff_coinduced_le, isActionTopology R A]
    · rw [← isActionTopology R A]
      exact this
  · apply @ContinuousAdd.mk _ (_)
    have foo : ContinuousAdd A := isActionTopology_continuousAdd R A
    let bar := foo
    obtain ⟨bar⟩ := bar
    rw [continuous_def] at bar ⊢
    intro U hU
    rw [isOpen_coinduced, ← isActionTopology R A] at hU
    specialize bar _ hU
    rw [← Set.preimage_comp] at bar
    rw [show φ ∘ (fun p ↦ p.1 + p.2 : A × A → A) =
      (fun p ↦ p.1 + p.2 : B × B → B) ∘
      (Prod.map ⇑φ.toAddMonoidHom ⇑φ.toAddMonoidHom) by ext; simp] at bar
    rw [Set.preimage_comp] at bar
    clear! aB -- easiest to just remove topology on B completely now
    have := coinduced_prod_eq_prod_coinduced (φ.toAddMonoidHom : A →+ B) φ.toAddMonoidHom hφ hφ
    convert isOpenMap_of_coinduced (AddMonoidHom.prodMap φ.toAddMonoidHom φ.toAddMonoidHom) (_) (_) (_) bar
    · aesop
    · -- should `apply continuousprodmap ctrl-space` find `Continuous.prod_map`?
      apply @Continuous.prod_map _ _ _ _ (_) (_) (_) (_) <;>
      · rw [continuous_iff_coinduced_le, isActionTopology R A]; rfl
    · rw [← isActionTopology R A]
      exact this


end topology_problem
