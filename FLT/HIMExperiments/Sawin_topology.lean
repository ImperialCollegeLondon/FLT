import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs

/-
# An "action topology" for monoid actions.

If `R` is a topological space acting on an additive abelian group `A`, we define
the *action topology* to be the finest topology on `M` making `• : R × A → A`
and `+ : A × A → A` continuous.

-/

section continuous_smul

variable {R : Type} [τR : TopologicalSpace R]
variable {A : Type} [SMul R A]
variable {S : Type} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type} [SMul S B]

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
lemma induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A) :
    @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert Inducing.continuousSMul (inducing_induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

lemma induced_continuous_add [AddCommMonoid A] [τA : TopologicalSpace A] [ContinuousAdd A]
    [AddCommMonoid B] (h : B →+ A) :
    @ContinuousAdd B (TopologicalSpace.induced h τA) _ := by
  convert Inducing.continuousAdd h (inducing_induced h)

-- this should be elsewhere
lemma TopologicalSpace.induced_id (X : Type*) : TopologicalSpace.induced (id : X → X) = id := by
  ext τ S
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact hT
  · rintro hS
    exact ⟨S, hS, rfl⟩

-- #check Prod.continuousSMul -- exists and is an instance :-)
--#check Induced.continuousSMul -- doesn't exist

end continuous_smul

section basics

variable (R : Type*) [TopologicalSpace R] (A : Type*) [Add A] [SMul R A]

abbrev actionTopology : TopologicalSpace A :=
  sInf {t | @ContinuousSMul R A _ _ t ∧ @ContinuousAdd A t _}

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

-- I use `mul_one` in this proof and in particular I use `1`.
-- Is the lemma true if `R` doesn't have a `1`?
protected lemma id (R : Type*) [Semiring R] [τ : TopologicalSpace R] [TopologicalSemiring R] :
    IsActionTopology R R := by
  constructor
  refine le_antisymm ?_ (actionTopology_le R R)
  rw [← continuous_id_iff_le]
  rw [show (id : R → R) = (fun rs ↦ rs.1 • rs.2) ∘ (fun r ↦ (r, 1)) by ext; simp]
  apply @Continuous.comp R (R × R) R τ (@instTopologicalSpaceProd R R τ (actionTopology R R))
      (actionTopology R R)
  · exact @continuous_smul _ _ _ _ (actionTopology R R) <| ActionTopology.continuousSMul ..
  · exact @Continuous.prod_mk _ _ _ _ (actionTopology R R) _ _ _ continuous_id <|
      @continuous_const _ _ _ (actionTopology R R) _

end one

section function

variable {R : Type} [τR : TopologicalSpace R] [Semiring R] [TopologicalSemiring R]
variable {A : Type} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
lemma continuous_of_mulActionHom (φ : A →+[R] B) : Continuous φ := by
  -- the proof: We know that R × B → B is continuous for the action
  -- topology, and `induced_continuous_smul` says that R × A → A
  -- is continuous if A is given B's action topology pulled back along φ.
  -- Because the action topology is an Inf, this means that A's
  -- action topology is `≤` the the pullback of B's action topology.
  -- But this is precisely the statement that `φ` is continuous.
  rw [isActionTopology R A, continuous_iff_le_induced]
  haveI : ContinuousAdd B := isActionTopology_continuousAdd R B
  exact sInf_le <| ⟨induced_continuous_smul continuous_id (φ.toMulActionHom),
    induced_continuous_add φ.toAddMonoidHom⟩

end function

#exit

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

open TopologicalSpace in
lemma prod [MulOneClass.{0} R] : IsActionTopology.{0} R (M × N) := by
  constructor
  -- goal: to prove product topology is action topology.
  -- Well product topology will obviously have continuous_smul becasue
  -- of continuous_smulprod or whatever, assuming that exists.
  --unfold instTopologicalSpaceProd actionTopology
  apply le_antisymm
  · trans @instTopologicalSpaceProd M N (coinduced Prod.fst (actionTopology R (M × N))) (coinduced Prod.snd (actionTopology R (M × N)))
    · apply le_inf
      · rw [← continuous_iff_le_induced]
        rw [continuous_iff_coinduced_le]
        apply coinduced_mono
        sorry
      ·
        sorry
--      apply TopologicalSpace.prod_mono
    -- NOTE
    -- this is the one that isn't done
    rw [← continuous_id_iff_le]
    -- There is no more proof here.
    -- In the code below I go off on a tangent
    -- trying to prove something else,
    -- and then sorry this goal.

    sorry
  sorry

#exit


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
  · apply actionTopology_le
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

section Pi

variable {R : Type} [τR : TopologicalSpace R]

variable {ι : Type} {A : ι → Type} [∀ i, SMul R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

lemma Pi : IsActionTopology R (∀ i, A i) := by
  sorry

end Pi

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
