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
lemma ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
  continuousSMul_sInf <| by aesop

lemma isActionTopology_continuousSMul (R A : Type*) [SMul R A]
    [TopologicalSpace R] [τA : TopologicalSpace A] [h : IsActionTopology R A] :
  ContinuousSMul R A where
    continuous_smul := by
      obtain ⟨h⟩ := h
      let _τA2 := τA
      subst h
      exact (ActionTopology.continuousSMul R A).1


variable (R A : Type*) [SMul R A] [TopologicalSpace R]
    [TopologicalSpace A] [IsActionTopology R A] in
lemma continuousSMul_of_isActionTopology : ContinuousSMul R A := by
  rw [isActionTopology R A]
  exact continuousSMul_sInf <| by aesop

end basics

namespace ActionTopology
section scratch

-- example (L : Type*) [CompleteLattice L] (ι : Type*) (f : ι → L) (t : L) :
--     t = ⨆ i, f i ↔ (∀ i, t ≤ f i) ∧ (∀ j, (∀ i, j ≤ f i) → j ≤ t) := by
--   --rw [iSup_eq]
--   sorry

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

lemma TopologicalSpace.induced_id (X : Type*) : TopologicalSpace.induced (id : X → X) = id := by
  ext τ S
  constructor
  · rintro ⟨T,hT,rfl⟩
    exact hT
  · rintro hS
    exact ⟨S, hS, rfl⟩

end one

section prod

variable {R : Type} [τR : TopologicalSpace R]

-- let `M` and `N` have an action of `R`
-- We do not need Mul on R, but there seems to be no class saying just 1 • m = m
-- so we have to use MulAction
--variable [Monoid R] -- no ContinuousMul becasuse we never need
-- we do not need MulAction because we do not need mul_smul.
-- We only need one_smul
variable {M : Type} [Zero M] [SMul R M] [aM : TopologicalSpace M] [IsActionTopology R M]
variable {N : Type} [Zero N] [SMul R N] [aN : TopologicalSpace N] [IsActionTopology R N]

lemma prod [MulOneClass.{0} R] : IsActionTopology.{0} R (M × N) := by
  constructor
  --unfold instTopologicalSpaceProd actionTopology
  apply le_antisymm
  ·
    -- NOTE
    -- this is the one that isn't done
    rw [← continuous_id_iff_le]


    -- idea: map R x M -> M is R x M -> R x M x N, τR x σ
    -- R x M has topology τR x (m ↦ Prod.mk m (0 : N))^*σ
    -- M x N -> M is pr₁⋆σ
    -- is pr1_*sigma=Prod.mk' 0^*sigma
    --rw [← continuous_id_iff_le]
    have := isActionTopology R M
    let τ1 : TopologicalSpace M := (actionTopology R (M × N)).coinduced (Prod.fst)
    have foo : aM ≤ τ1 := by
      rw [this]
      apply sInf_le
      unfold_let
      constructor
      rw [continuous_iff_coinduced_le]
      --rw [continuous_iff_le_induced]
      --rw [instTopologicalSpaceProd]
      have := ActionTopology.continuousSMul R (M × N)
      obtain ⟨h⟩ := this
      rw [continuous_iff_coinduced_le] at h
      have h2 := coinduced_mono (f := (Prod.fst : M × N → M)) h
      refine le_trans ?_ h2
      rw [@coinduced_compose]
      --rw [coinduced_le_iff_le_induced]
      rw [show ((Prod.fst : M × N → M) ∘ (fun p ↦ p.1 • p.2 : R × M × N → M × N)) =
        (fun rm ↦ rm.1 • rm.2) ∘ (fun rmn ↦ (rmn.1, rmn.2.1)) by
        ext ⟨r, m, n⟩
        rfl]
      rw [← @coinduced_compose]
      apply coinduced_mono
      rw [← continuous_id_iff_le]
      have this2 := @Continuous.prod_map R M R M τR ((TopologicalSpace.coinduced Prod.fst (actionTopology R (M × N)))) τR aM id id ?_ ?_
      swap; fun_prop
      swap; sorry -- action top ≤ coinduced Prod.fst (action)
      convert this2
      sorry -- action top on M now equals coinduced Prod.fst
      sorry -- same
      -- so we're going around in circles
    sorry
    -- let τ2 : TopologicalSpace M := (actionTopology R (M × N)).induced (fun m ↦ (m, 0))
    -- have moo : τ1 = τ2 := by
    --   unfold_let
    --   apply le_antisymm
    --   · rw [coinduced_le_iff_le_induced]
    --     apply le_of_eq
    -- --     rw [induced_compose]



    --     sorry
    --   ·
    --     sorry
    -- sorry
  · sorry
--     --have foo : @Continuous (M × N) (M × N) _ _ _ := @Continuous.prod_map M N M N (σMN.coinduced Prod.fst) (σMN.coinduced Prod.snd) aM aN id id ?_ ?_-- Z * W -> X * Y
--     -- conjecture: pushforward of σMN is continuous
--     -- ⊢ instTopologicalSpaceProd ≤ σMN
--     --rw [continuous_iff_coinduced_le] at hσ
-- #exit
--     refine le_trans ?_ (continuous_iff_coinduced_le.1 hσ)
--     rw [← continuous_id_iff_le]
--     have foo : (id : M × N → M × N) = fun mn ↦ Prod.mk mn.1 mn.2 := by
--       ext <;> rfl
--     rw [foo]
--     --have h1 := @Continuous.prod_mk M N (M × N) _ _ (instTopologicalSpaceProd) Prod.fst Prod.snd (by continuity) (by continuity)
--     --have h2 := @Continuous.prod_mk M N (M × N) _ _ ((TopologicalSpace.coinduced (fun p ↦ p.1 • p.2) (instTopologicalSpaceProd : TopologicalSpace (R × M × N))) Prod.fst Prod.snd ?_ ?_
--     rw [continuous_iff_le_induced] at *
--     simp
--     have foo : TopologicalSpace.induced (fun (mn : M × N) ↦ mn) = id := by
--       have := TopologicalSpace.induced_id (M × N)
--       exact TopologicalSpace.induced_id (M × N)
--     --refine le_trans h1 ?_
--     rw [foo]
--     simp
--     rw [← continuous_id_iff_le]
--     --have bar : (id : M × N → M × N) = fun mn ↦ ((1, mn).snd) := by rfl
--     --rw [bar]
--     have mar : (id : M × N → M × N) = (fun rmn ↦ rmn.1 • rmn.2 : R × M × N → M × N) ∘
--         (fun mn ↦ (1, mn)) := by
--       ext mn
--       cases mn
--       simp only [id_eq, Function.comp_apply, one_smul]
--       cases mn
--       simp only [id_eq, Function.comp_apply, one_smul]
--     --have car : (id : M × N → M × N) = fun mn ↦ (((1, mn) : R × M × N).snd) := sorry
--     --(Prod.snd : R × M × N → M × N) ∘ (fun mn ↦ ((1, mn) : R × M × N)) := by

--     rw [mar]
--     rw [← continuous_iff_le_induced] at hσ
--     letI τfoo : TopologicalSpace (R × M × N) := instTopologicalSpaceProd (t₁ := (inferInstance : TopologicalSpace R)) (t₂ := σMN)
--     refine @Continuous.comp (M × N) (R × M × N) (M × N) instTopologicalSpaceProd τfoo (TopologicalSpace.coinduced (fun (rmn : R × M × N) ↦ rmn.1 • rmn.2) ?_) ?_ ?_ ?_ ?_
--     · --exact hσ
--       rw [continuous_iff_coinduced_le]
--     · simp only [τfoo]
-- --      rw [continuous_iff_coinduced_le]

--       --rw [continuous_iff_le_induced]
--       clear foo
--       clear foo
--       refine @Continuous.prod_mk R (M × N) (M × N) ?_ ?_ ?_ (fun _ ↦ 1) id ?_ ?_
--       --refine le_trans h1 ?_
--       refine @continuous_const (M × N) R ?_ ?_ 1
--       rw [continuous_iff_coinduced_le]


--       sorry
--     -- refine moo ?_ ?_
--     -- · skip
--     --   have := Continuous.snd
--     --   sorry
--     --   done
--     -- · -- looks hard to solve for τsoln
--     --   rw [continuous_iff_coinduced_le]
--     --   -- wtf where is τsoln?
--     --   sorry
--     --   done
--   · apply sInf_le
--     simp only [Set.mem_setOf_eq]
--     constructor
--     apply Continuous.prod_mk
--     · have := continuousSMul_of_isActionTopology R M
--       obtain ⟨this⟩ := this
--       convert Continuous.comp this ?_
--       rename_i rmn
--       swap
--       exact fun rmn ↦ (rmn.1, rmn.2.1)
--       rfl
--       fun_prop
--     · have := continuousSMul_of_isActionTopology R N
--       obtain ⟨this⟩ := this
--       convert Continuous.comp this ?_
--       rename_i rmn
--       swap
--       exact fun rmn ↦ (rmn.1, rmn.2.2)
--       rfl
--       fun_prop

end prod

section function

variable {R : Type} [τR : TopologicalSpace R]
variable {M : Type} [SMul R M] [aM : TopologicalSpace M] [iM : IsActionTopology R M]
variable {N : Type} [SMul R N] [aN : TopologicalSpace N] [iN : IsActionTopology R N]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma continuous_of_mulActionHom (φ : M →[R] N) : Continuous φ := by
  -- Let's turn this question into an inequality question about coinduced topologies
  -- Now let's use the fact that τM and τN are action topologies (hence also coinduced)
  rw [isActionTopology R M, isActionTopology R N]
  unfold actionTopology
  rw [continuous_iff_le_induced]
  nth_rw 2 [sInf_eq_iInf]
  rw [induced_iInf] --induced_sInf missing?
  apply le_iInf
  simp only [Set.mem_setOf_eq, induced_iInf, le_iInf_iff]
  intro σN hσ
  apply sInf_le
  refine @ContinuousSMul.mk R M _ τR (TopologicalSpace.induced (⇑φ) σN) ?_
  rw [continuous_iff_le_induced]
  rw [induced_compose]
  rw [← continuous_iff_le_induced]
  rw [show φ ∘ (fun (p : R × M) ↦ p.1 • p.2) = fun rm ↦ rm.1 • φ (rm.2) by
        ext rm
        cases rm
        simp]
  obtain ⟨hσ'⟩ := hσ
  rw [continuous_iff_le_induced] at *
  have := induced_mono (g := fun (rm : R × M) ↦ (rm.1, φ (rm.2))) hσ'
  rw [induced_compose] at this
  refine le_trans ?_ this
  rw [← continuous_iff_le_induced]
  refine @Continuous.prod_map R N R M τR σN τR (TopologicalSpace.induced (φ : M → N) σN) id φ ?_ ?_
  · fun_prop
  · fun_prop

#check coinduced_iSup
#check induced_iInf
#exit
/-
coinduced_iSup.{w, u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {ι : Sort w} {t : ι → TopologicalSpace α} :
  TopologicalSpace.coinduced f (⨆ i, t i) = ⨆ i, TopologicalSpace.coinduced f (t i)
-/
lemma induced_.{w, u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {ι : Sort w} {t : ι → TopologicalSpace α} :
  TopologicalSpace.coinduced f (⨆ i, t i) = ⨆ i, TopologicalSpace.coinduced f (t i)

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

end function

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
