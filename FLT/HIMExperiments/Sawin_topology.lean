import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs
import FLT.ForMathlib.MiscLemmas
import Mathlib
/-
# An "action topology" for monoid actions.

If `R` is a topological space acting on an additive abelian group `A`, we define
the *action topology* to be the finest topology on `M` making `• : R × A → A`
and `+ : A × A → A` continuous.

This topology was suggested by Will Sawin [here](https://mathoverflow.net/a/477763/1384).

-/

section basics

/-!
This section is just boilerplate, defining the action topology and making
some infrastructure.
-/
variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

/-- The action topology, for a module over a topological ring `R`. It's the finest topology
making addition and the `R`-action continuous. -/
abbrev actionTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

/-- A class asserting that the topology on a module over a topological ring `R` is
the action topology. See `actionTopology` for more discussion of the action topology. -/
class IsActionTopology [τA : TopologicalSpace A] : Prop where
  isActionTopology' : τA = actionTopology R A

lemma isActionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

lemma ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
  continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

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

section one

/-

We now fix once and for all a topological semiring `R`.

We first prove that the action topology on `R` considered as a module over itself,
is `R`'s topology.

-/
protected lemma id (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R] :
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
    The map `R → R × R` is a map into a product, so it suffices to show that each of the
    two factors is continuous. But the first is the identity function and the second
    is a constant function. -/
    exact @Continuous.prod_mk _ _ _ _ (actionTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (actionTopology R R) _

end one

section function

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

/-- Every `R`-linear map between two `R`-modules with the canonical topology is continuous. -/
@[fun_prop, continuity]
lemma continuous_of_distribMulActionHom (φ : A →+[R] B) : Continuous φ := by
  -- the proof: We know that `+ : B × B → B` and `• : R × B → B` are continuous for the action
  -- topology on `B`, and two theorems in mathlib (`induced_continuous_smul` and
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

end function



section prod

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

-- let `M` and `N` have an action of `R`
-- We do not need Mul on R, but there seems to be no class saying just 1 • m = m
-- so we have to use MulAction
--variable [Monoid R] -- no ContinuousMul becasuse we never need
-- we do not need MulAction because we do not need mul_smul.
-- We only need one_smul
variable {M : Type*} [AddCommMonoid M] [Module R M] [aM : TopologicalSpace M] [IsActionTopology R M]
variable {N : Type*} [AddCommMonoid N] [Module R N] [aN : TopologicalSpace N] [IsActionTopology R N]

open TopologicalSpace in
lemma prod : IsActionTopology R (M × N) := by
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
    ·
      -- bleurgh, fighting typeclass inference all the time, which wants one "canonical"
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

variable {R : Type} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]

variable {ι : Type} {A : ι → Type} [∀ i, AddCommGroup (A i)]
  [∀ i, Module R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

lemma Pi : IsActionTopology R (∀ i, A i) := by
  sorry

end Pi

-- everything from here on is dead code and ideas which use other topologies
#exit

section Sigma

variable {R : Type} [τR : TopologicalSpace R]

variable {ι : Type} {A : ι → Type} [∀ i, SMul R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

instance : SMul R (Σ i, A i) where
  smul r s := ⟨s.1, r • s.2⟩

-- this looks true to me
lemma sigma : IsActionTopology R (Σ i, A i) := by
  constructor
  --unfold instTopologicalSpaceProd actionTopology
  apply le_antisymm
  sorry
  sorry

/-
coinduced_iSup.{w, u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {ι : Sort w} {t : ι → TopologicalSpace α} :
  TopologicalSpace.coinduced f (⨆ i, t i) = ⨆ i, TopologicalSpace.coinduced f (t i)
-/
-- lemma induced_.{w, u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {ι : Sort w} {t : ι → TopologicalSpace α} :
--   TopologicalSpace.coinduced f (⨆ i, t i) = ⨆ i, TopologicalSpace.coinduced f (t i)

  -- -- original proof, now broken
  -- rw [coinduced_le_iff_le_induced]
  -- -- There's an already-proven lemma in mathlib that says that coinducing an `iSup` is the
  -- -- same thing as taking the `iSup`s of the coinduced topologies
  -- -- composite of the coinduced topologies is just topology coinduced by the composite
  -- rw [coinduced_iSup]
  -- simp_rw [coinduced_compose]
  -- -- restate the current state of the question with better variables
  -- change ⨆ m, TopologicalSpace.coinduced (fun r ↦ e (r • m)) τR ≤
  --   ⨆ n, TopologicalSpace.coinduced (fun x ↦ x • n) τR
  -- -- use the fact that `e (r • m) = r • (e m)`
  -- simp_rw [map_smul]
  -- -- and now the goal follows from the fact that the sup over a small set is ≤ the sup
  -- -- over a big set
  -- apply iSup_comp_le (_ : N → TopologicalSpace N)

section topology

variable {R : Type*} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

-- is this true? I used it with topology 4 to "reduce to the case of R^n -> B".
lemma coinduced_of_surjective {φ : A →ₗ[R] B} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ (actionTopology R A) = actionTopology R B := by
  have : Continuous φ := continuous_of_linearMap φ
  rw [continuous_iff_coinduced_le] at this
  rw [isActionTopology R A, isActionTopology R B] at this
  apply le_antisymm this
  clear this
  apply sInf_le
  constructor
  · apply @ContinuousSMul.mk R B _ _ (_)
    obtain ⟨foo⟩ : ContinuousSMul R A := inferInstance
    rw [continuous_def] at foo ⊢
    intro U hU
    rw [isOpen_coinduced, ← isActionTopology R A] at hU
    specialize foo _ hU
    -- don't know if this is true
    sorry
  · -- is this true?
    sorry


end topology
#exit
section
-- Let R be a monoid, with a compatible topology.
variable (R : Type*) [Monoid R] [TopologicalSpace R] [ContinuousMul R]
-- let `A` and `B` be types with an `R`-action
variable (A : Type*) [SMul R A]
variable (B : Type*) [SMul R B]

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


-- claim: topology on the 1-point set is the canonical one
example : (inferInstance : TopologicalSpace Unit) = Module.rtopology A Unit := by
  sorry

-- Anything from this point on *might* need commutative.
-- Just move it to the commutative section and prove it there.

-- Claim: topology on A doesn't change
example : (inferInstance : TopologicalSpace A) = Module.rtopology A A := by
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

end noncommutative

section commutative

-- Let A be a commutative ring, with a compatible topology.
variable (A : Type*) [CommRing A] [TopologicalSpace A] [TopologicalRing A]
-- let `M` and `N` be `A`-modules
variable (M : Type*) [AddCommGroup M] [Module A M]
variable {N : Type*} [AddCommGroup N] [Module A N]

open scoped TensorProduct
lemma Module.continuous_bilinear :
    let _τM : TopologicalSpace M := Module.rtopology A _
    let _τN : TopologicalSpace N := Module.rtopology A _
    let _τMN : TopologicalSpace (M ⊗[A] N) := Module.rtopology A _
    Continuous (fun (mn : M × N) ↦ mn.1 ⊗ₜ mn.2 : M × N → M ⊗[A] N) := by sorry

-- Now say we have a (not necessarily commutative) `A`-algebra `D` which is free of finite type.

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

end commutative
