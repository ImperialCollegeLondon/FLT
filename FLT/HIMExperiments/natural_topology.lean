import Mathlib.RingTheory.TensorProduct.Basic -- we need tensor products of rings at some point
import Mathlib.Topology.Algebra.Module.Basic -- and we need topological rings and modules
import Mathlib.Tactic
-- next two should be all we need for basic file to compile
import Mathlib.Topology.Order
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Projective

/-
# An topology for monoid actions.

If `R` and `A` are types, and if `R` has a topology `[TopologicalSpace R]`
and acts on `A` `[SMul R A]`, then `A` inherits a topology from this set-up,
which we call the *something* topology.
-/

-- section continuous_smul

-- variable {R : Type} [τR : TopologicalSpace R]
-- variable {A : Type} [SMul R A]
-- variable {S : Type} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
-- variable {B : Type} [SMul S B] (g : B →ₑ[f] A)

-- -- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
-- lemma induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] :
--     @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
--   convert Inducing.continuousSMul (inducing_induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

-- #check Prod.continuousSMul -- exists and is an instance :-)
-- --#check Induced.continuousSMul -- doesn't exist

-- end continuous_smul

section basics

variable (R : Type*) [TopologicalSpace R] [Ring R] [TopologicalRing R]
variable (A : Type*) [AddCommMonoid A] [Module R A]

-- "smallest" (i.e. most open sets) topology on `A` such
-- that all R-linear maps R^n → A are continuous
abbrev actionTopology : TopologicalSpace A :=
  ⨆ (n : ℕ), ⨆ (φ : (Fin n → R) →ₗ[R] A), .coinduced φ inferInstance

class IsActionTopology [τA : TopologicalSpace A] : Prop where
  isActionTopology' : τA = actionTopology R A

lemma isActionTopology [τA : TopologicalSpace A] [IsActionTopology R A] :
    τA = actionTopology R A :=
  IsActionTopology.isActionTopology' (R := R) (A := A)

-- **TODO** is this true?
-- lemma ActionTopology.continuousSMul : @ContinuousSMul R A _ _ (actionTopology R A) :=
--   continuousSMul_sInf <| fun _ _ ↦ by simp_all only [Set.mem_setOf_eq]

-- **TODO** is this true?
-- instance isActionTopology_continuousSMul (R A : Type*) [SMul R A]
--     [TopologicalSpace R] [τA : TopologicalSpace A] [h : IsActionTopology R A] :
--   ContinuousSMul R A where
--     continuous_smul := by
--       obtain ⟨h⟩ := ActionTopology.continuousSMul R A
--       simpa [isActionTopology R A] using h

end basics

namespace ActionTopology

section one

variable (R : Type*) [Ring R] [τ : TopologicalSpace R] [TopologicalRing R]

abbrev thing : (Fin 1 → R) →ₗ[R] R where
  toFun := fun f ↦ f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

protected lemma id : IsActionTopology R R := by
  constructor
  apply le_antisymm
  · refine le_iSup_of_le 1 ?_
    refine le_iSup_of_le (thing R) ?_
    intro U hU
    rw [isOpen_coinduced] at hU
    exact Continuous.isOpen_preimage (f := fun r ↦ (fun _ ↦ r)) (by fun_prop) _ hU
  · apply iSup_le
    intro n
    apply iSup_le
    intro φ
    rw [← continuous_iff_coinduced_le]
    exact LinearMap.continuous_on_pi φ

instance pow (n : ℕ) : IsActionTopology R (Fin n → R) := by
  constructor
  apply le_antisymm
  · refine le_iSup_of_le n ?_
    refine le_iSup_of_le (LinearMap.id) ?_
    intro U hU
    rw [isOpen_coinduced] at hU
    apply hU
  · apply iSup_le
    intro m
    apply iSup_le
    intro φ
    rw [← continuous_iff_coinduced_le]
    exact LinearMap.continuous_on_pi φ

end one

section function

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

/-- Every `A`-linear map between two `A`-modules with the canonical topology is continuous. -/
@[continuity, fun_prop]
lemma continuous_of_linearMap (f : A →ₗ[R] B) : Continuous f := by
  rw [isActionTopology R A, continuous_iff_le_induced]
  apply iSup_le <| fun n ↦ ?_
  apply iSup_le <| fun φ ↦ ?_
  rw [isActionTopology R B, ← coinduced_le_iff_le_induced, coinduced_compose]
  apply le_iSup_of_le n
  apply le_iSup_of_le (f.comp φ)
  rfl

lemma continuous_of_linearMap' {A : Type*} [AddCommMonoid A] [Module R A]
    {B : Type*} [AddCommMonoid B] [Module R B] (f : A →ₗ[R] B) :
    @Continuous _ _ (actionTopology R A) (actionTopology R B) f := by
  letI : TopologicalSpace A := actionTopology R A
  letI : TopologicalSpace B := actionTopology R B
  haveI : IsActionTopology R A := ⟨rfl⟩
  haveI : IsActionTopology R B := ⟨rfl⟩
  fun_prop

end function

section surj

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]

lemma surj {n : ℕ} {φ : ((Fin n) → R) →ₗ[R] A} (hφ : Function.Surjective φ) :
    TopologicalSpace.coinduced φ Pi.topologicalSpace = actionTopology R A := by
  apply le_antisymm
  · rw [← continuous_iff_coinduced_le]
    rw [← isActionTopology R A]
    fun_prop
  · rw [iSup_le_iff]
    intro m
    rw [iSup_le_iff]
    intro ψ
    obtain ⟨α, rfl⟩ : ∃ α : (Fin m → R) →ₗ[R] (Fin n → R), φ.comp α = ψ :=
      Module.projective_lifting_property _ _ hφ
    change TopologicalSpace.coinduced (φ ∘ α) _ ≤ _
    rw [← coinduced_compose]
    apply coinduced_mono
    rw [← continuous_iff_coinduced_le]
    fun_prop

end surj

section add

variable {R : Type*} [τR : TopologicalSpace R] [Ring R] [TopologicalRing R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]

variable (R A) in
abbrev thing2 : A × A →ₗ[R] A where
  toFun ab := ab.1 + ab.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_add_add_comm]
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add]

lemma continuous_add [Module.Finite R A]: Continuous (fun ab ↦ ab.1 + ab.2 : A × A → A) := by
  rw [continuous_iff_coinduced_le, isActionTopology R A]
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R A
  rw [← surj hf]
  rw [← continuous_iff_coinduced_le]

  --refine le_iSup_of_le 2 ?_

  -- rw [le_iSup_iff]
  -- intro τA hτA
  -- rw [←continuous_iff_coinduced_le]
  sorry

end add


section prod

variable {R : Type*} [τR : TopologicalSpace R] [Ring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsActionTopology R A]
variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsActionTopology R B]

example : A × B →ₗ[R] A := by exact LinearMap.fst R A B

open TopologicalSpace in
lemma prod : IsActionTopology R (A × B) := by
  constructor
  apply le_antisymm
  · rw [← continuous_id_iff_le]
    let id' : A × B → A × B := fun ab ↦ (ab.1, 0) + (0, ab.2)
    have hid : @id (A × B) = fun ab ↦ (ab.1, 0) + (0, ab.2) := by ext ⟨a, b⟩ <;> simp
    rw [hid]


    sorry
  · apply le_inf
    · rw [← continuous_iff_le_induced]
      convert continuous_of_linearMap (LinearMap.fst R A B)
      ·
        sorry
      ·
        sorry
    ·
      sorry
--   · trans @instTopologicalSpaceProd M N (coinduced Prod.fst (actionTopology R (M × N))) (coinduced Prod.snd (actionTopology R (M × N)))
--     · apply le_inf
--       · rw [← continuous_iff_le_induced]
--         rw [continuous_iff_coinduced_le]
--         apply coinduced_mono
--         sorry
--       ·
--         sorry
-- --      apply TopologicalSpace.prod_mono
--     -- NOTE
--     -- this is the one that isn't done
--     rw [← continuous_id_iff_le]
--     -- There is no more proof here.
--     -- In the code below I go off on a tangent
--     -- trying to prove something else,
--     -- and then sorry this goal.

--     sorry
--   sorry

#exit

    -- idea: map R x M -> M is R x M -> R x M x N, τR x σ
    -- R x M has topology τR x (m ↦ Prod.mk m (0 : N))^*σ
    -- M x N -> M is pr₁⋆σ
    -- is pr1_*sigma=Prod.mk' 0^*sigma

end prod

section Pi

variable {R : Type} [τR : TopologicalSpace R]

variable {ι : Type} {A : ι → Type} [∀ i, SMul R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsActionTopology R (A i)]

lemma Pi : IsActionTopology R (∀ i, A i) := by
  sorry

end Pi


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
