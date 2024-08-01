import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Tactic
-- next two should be all we need for basic file to compile
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs

/-
-- todo : A -> R, M -> A
# An "action topology" for monoid actions.

Let `A` denote a topological monoid, and say `A` acts on the type `M`.
There is then a smallest (in the sense of Lean's `≤`) topology on `M`
making the induced action map `A × M → M` continuous.
We call this topology on `M` the "action topology". It is some kind
of "pushforward topology" on `M` coming from the topology on `A` and
the action.

## Constructions on modules.

This action topology (or `A`-action topology, if you want to specify
the underlying monoid)
may or may not have the following cool properties:

1) Any `A`-linear map `φ : M →[A] N` is continuous.
2) The `A`-module topology on `Unit` is the topology already present on `Unit`.
3) The `A`-module topology on `A` acting on itself via `*`, is `A`s original topology.
4) The `A`-module topology on a product `M × N` of two modules-with-action-topology is
   the product topology.
5) The `A`-module topology on a power `M^n`, that is, `n → M` with `n : Type`, is the
(now possibly infinite) product topology.
5.5) sigma types

6) Now say `A` is commutative. Then the tensor product of two `A`-modules is an `A`-module,
and so we can ask if the canonical bilinear map from `M × N` (with the module or product topology?
probably they're the same) to `M ⊗[A] N` is continuous.

7) Commutativity of `A` also gives spaces of `A`-linear maps the structure of `A`-modules,
so we can ask for example whether the function application map `M × (M →ₗ[A] N) → N` is continuous.

8) We could also ask whether the evaluation map, from `M →ₗ[A] N` to the power space `N^M` of bare
functions from `M` (now considered only as an index set, so with no topology) to `N` is continuous.

-/
section basics

abbrev actionTopology (R A : Type*) [SMul R A] [TopologicalSpace R] :
    TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t}

-- I think R and A is good notation. R is a module. We could
-- have called it M; the problem with M is htat we could have
-- called A M as well. Here we completely avoid the M ambiguity.
class IsActionTopology (R A : Type*) [SMul R A]
    [TopologicalSpace R] [τA : TopologicalSpace A] : Prop where
  isActionTopology' : τA = actionTopology R A

lemma isActionTopology (R A : Type*) [SMul R A]
    [TopologicalSpace R] [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

variable (R A : Type*) [SMul R A] [TopologicalSpace R] in
example : @ContinuousSMul R A _ _ (actionTopology R A) :=
  continuousSMul_sInf <| by aesop

variable (R A : Type*) [SMul R A] [TopologicalSpace R]
    [TopologicalSpace A] [IsActionTopology R A] in
example : ContinuousSMul R A := by
  rw [isActionTopology R A]
  exact continuousSMul_sInf <| by aesop

end basics

namespace ActionTopology
section scratch

example (L : Type*) [CompleteLattice L] (ι : Type*) (f : ι → L) (t : L) :
    t = ⨆ i, f i ↔ (∀ i, t ≤ f i) ∧ (∀ j, (∀ i, j ≤ f i) → j ≤ t) := by
  --rw [iSup_eq]
  sorry

end scratch

section one

lemma id' (R : Type*) [Monoid R] [τ : TopologicalSpace R] [ContinuousMul R] :
    IsActionTopology R R := by
  constructor
  unfold actionTopology
  symm
  rw [← isGLB_iff_sInf_eq]
  constructor
  · intro σ hσ
    cases' hσ with hσ
    rw [← continuous_id_iff_le]
    have foo : (id : R → R) = (fun ab ↦ ab.1 * ab.2 : R × R → R) ∘ (fun r ↦ (r, 1)) := by
      funext
      simp
    rw [foo]
    apply @Continuous.comp R (R × R) R τ (@instTopologicalSpaceProd R R τ σ)
    · apply hσ
    · refine @Continuous.prod_mk R R R ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · refine @continuous_id R ?_
      · refine @continuous_const R R ?_ ?_ 1
  · intro σ hσ
    rw [mem_lowerBounds] at hσ
    apply hσ
    clear σ hσ
    simp
    constructor
    rename_i foo
    cases foo with
    | mk continuous_mul => exact continuous_mul

end one
section prod

variable {R : Type} [TopologicalSpace R]

-- let `M` and `N` have an action of `R`
variable {M : Type*} [SMul R M] [aM : TopologicalSpace M] [IsActionTopology R M]
variable {N : Type*} [SMul R N] [aN : TopologicalSpace N] [IsActionTopology R N]

--example (L) [CompleteLattice L] (f : M → N) (g : N → L) : ⨆ m, g (f m) ≤ ⨆ n, g n := by
--  exact iSup_comp_le g f

--theorem map_smul_pointfree (f : M →[R] N) (r : R) : (fun m ↦ f (r • m)) = fun m ↦ r • f m :=
--  by ext; apply map_smul

lemma prod : IsActionTopology R (M × N) := by
  constructor
  unfold instTopologicalSpaceProd actionTopology
  apply le_antisymm
  · apply le_sInf
    intro σMN hσ
    sorry
  ·
    sorry

end prod
#exit

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma continuous_of_mulActionHom (φ : M →[R] N) : Continuous φ := by
  -- Let's turn this question into an inequality question about coinduced topologies
  -- Now let's use the fact that τM and τN are action topologies (hence also coinduced)
  rw [isActionTopology R M, isActionTopology R N]
  unfold actionTopology
--  rw [continuous_iff_le_induced]
--  sorry

-- coinduced attempt, got tangled, pre paper approach
  rw [continuous_iff_coinduced_le]
  rw [le_sInf_iff]
  intro τN hτN
  rw [coinduced_le_iff_le_induced]


  rw [sInf_le_iff]
  intro τM hτM
  change ∀ _, _ at hτM
  apply hτM
  simp
  rw [@DFunLike.coe_eq_coe_fn]
  simp

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
