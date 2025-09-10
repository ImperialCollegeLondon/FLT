import FLT.Mathlib.Algebra.Algebra.Bilinear
import FLT.Mathlib.Algebra.Algebra.Pi
import FLT.Mathlib.Algebra.Module.Submodule.Basic
import FLT.Mathlib.NumberTheory.RamificationInertia.Basic
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.UniformRing
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Algebra.Valued.WithVal
import FLT.Mathlib.RingTheory.TensorProduct.Basis
import FLT.Mathlib.RingTheory.Finiteness.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Data.Int.WithZero
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import FLT.DedekindDomain.AdicValuation
import FLT.DedekindDomain.Completion.BaseChange
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Algebra.Colimit.Module
import Mathlib.RingTheory.Flat.Basic
import FLT.DedekindDomain.FiniteAdeleRing.TensorPi
import Mathlib.Order.DirectedInverseSystem




section IsDirectLimit

namespace Module

universe u

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type u)
variable [AddCommMonoid P] [Module R P]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i, M i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem M (f · · ·)]

@[mk_iff] class IsDirectLimit : Prop where
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x
  universal_property :
    ∀ {X : Type u} [AddCommMonoid X] [Module R X],
    ∀ gX : ∀ i, M i →ₗ[R] X, ∀ _ : ∀ i j hij x, gX j (f i j hij x) = gX i x,
    ∃! φ : P →ₗ[R] X, ∀ i x, φ (g i x) = gX i x

-- instance isDirectLimit :
--     IsDirectLimit M (Module.DirectLimit M f) f
--     (Module.DirectLimit.of R ι M f) where
--   compatibility i j hij x := Module.DirectLimit.of_f
--   universal_property gX HgX :=
--     ⟨Module.DirectLimit.lift R ι M f gX HgX,
--       by simp,
--       by
--         intro y hy
--         ext x
--         convert Module.DirectLimit.lift_unique y x with i
--         ext x'
--         simp only [LinearMap.coe_comp, Function.comp_apply]
--         exact (hy i x').symm⟩

section Iso

theorem universal_prop_identity [h : IsDirectLimit M P f g] :
  (h.universal_property g h.compatibility).exists.choose = LinearMap.id := by
  apply ExistsUnique.unique (h.universal_property g h.compatibility)
  · exact (h.universal_property g h.compatibility).exists.choose_spec
  · simp only [LinearMap.id_coe, id_eq, implies_true]

theorem IsDirectLimit.surj' [h : IsDirectLimit M P f g] : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m := by
  intro m
  let Q : Submodule R P := Submodule.span R (⋃ i, Set.range (g i))


  sorry

variable (P₁ P₂ : Type u) [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
variable (g₁ : ∀ i, M i →ₗ[R] P₁)
variable (g₂ : ∀ i, M i →ₗ[R] P₂)

set_option pp.proofs true in
noncomputable def iso_of_isDirectLimit
    [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂] :
    P₁ ≃ₗ[R] P₂ where
  __ := (h₁.universal_property g₂ h₂.compatibility).exists.choose
  invFun := (h₂.universal_property g₁ h₁.compatibility).exists.choose
  left_inv := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    refine Function.leftInverse_iff_comp.mpr ?_
    rw [← LinearMap.coe_comp, ← LinearMap.id_coe (R:=R)]
    refine DFunLike.coe_fn_eq.mpr
      (ExistsUnique.unique (h₁.universal_property g₁ h₁.compatibility) ?_ ?_)
    · intro i mi
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [(ExistsUnique.exists (h₁.universal_property g₂ h₂.compatibility)).choose_spec i mi,
        (ExistsUnique.exists (h₂.universal_property g₁ h₁.compatibility)).choose_spec i mi]
    · intro i mi
      simp only [LinearMap.id_coe, id_eq]
  right_inv := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    refine Function.rightInverse_iff_comp.mpr ?_
    rw [← LinearMap.coe_comp, ← LinearMap.id_coe (R:=R)]
    refine DFunLike.coe_fn_eq.mpr
      (ExistsUnique.unique (h₂.universal_property g₂ h₂.compatibility) ?_ ?_)
    · intro i mi
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [(ExistsUnique.exists (h₂.universal_property g₁ h₁.compatibility)).choose_spec i mi,
        (ExistsUnique.exists (h₁.universal_property g₂ h₂.compatibility)).choose_spec i mi]
    · intro i mi
      simp only [LinearMap.id_coe, id_eq]

end Iso

end Module

end IsDirectLimit

section IsDirectLimit

namespace Module

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
variable [AddCommMonoid P] [Module R P]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i, M i →ₗ[R] P)
variable [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem M (f · · ·)]

@[mk_iff] class IsDirectLimit' : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [IsDirectLimit M P f g]


instance isDirectLimit' : IsDirectLimit' M (Module.DirectLimit M f) f
  (Module.DirectLimit.of R ι M f) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of] at h
    have ⟨k, hi, hj, hij⟩ := Quotient.exact h
    exact ⟨k, hi, hj, hij⟩
  compatibility i j hij x := DirectLimit.of_f

variable (P₁ P₂ : Type*) [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
variable (g₁ : ∀ i, M i →ₗ[R] P₁)
variable (g₂ : ∀ i, M i →ₗ[R] P₂)


-- this is a nightmare. need to clean up and fully understand
set_option pp.proofs true in
open Classical in
noncomputable def lift [IsDirectLimit' M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) :
  P₁ →ₗ[R] P₂ where
    toFun p :=
      g₂ (choose (IsDirectLimit'.surj f p))
                   (choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) p)))
    map_add' x y := by
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) x))
      have hy := Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) y))
      have hxy := Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (x + y)))
      set ix := Classical.choose (IsDirectLimit'.surj f (g:= g₁) x)
      set mx := Classical.choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) x))
      set iy := Classical.choose (IsDirectLimit'.surj f (g:= g₁) y)
      set my := Classical.choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) y))
      set ixy := Classical.choose (IsDirectLimit'.surj f (g:= g₁) (x + y))
      set mxy := Classical.choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (x + y)))

      obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) ix iy
      obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·)) ixy k
      have sum_eq : g₁ k' (f ix k' (le_trans hxk hkk') mx + f iy k' (le_trans hyk hkk') my) =
                    g₁ ixy mxy := by
        rw [LinearMap.map_add]
        rw [IsDirectLimit'.compatibility ix k' (le_trans hxk hkk') mx]
        rw [IsDirectLimit'.compatibility iy k' (le_trans hyk hkk') my]
        rw [hx, hy, hxy]

      obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := IsDirectLimit'.inj (f:= f) k' ixy
                                        (f ix k' (le_trans hxk hkk') mx + f iy k' (le_trans hyk hkk') my)
                                        mxy sum_eq
      rw [← Hg ixy k'' hxyk'' mxy]
      have key_eq := congr_arg (g₂ k'') h'''
      have g2_applied := congr_arg (g₂ k'') h'''
      rw [ Hg k' k'' hk'k''] at g2_applied
      rw [LinearMap.map_add] at g2_applied
      rw [Hg ix k' (le_trans hxk hkk') mx, Hg iy k' (le_trans hyk hkk') my] at g2_applied
      rw [Hg ixy k'' hxyk'' mxy] at g2_applied
      rw [ Hg ixy k'' hxyk'' mxy]
      exact g2_applied.symm

    map_smul' r x := by
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) x))
      have hrx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (r • x)))
      set ix := Classical.choose (IsDirectLimit'.surj f (g:= g₁) x)
      set mx := Classical.choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) x))
      set irx := Classical.choose (IsDirectLimit'.surj f (g:= g₁) (r • x))
      set mrx := Classical.choose (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (r • x)))
      -- Step 1: Simplify RingHom.id R
      simp only [RingHom.id_apply]
      -- Goal becomes: (g₂ irx) mrx = r • (g₂ ix) mx

      -- Step 2: We have hrx : g₁ irx mrx = r • x and hx : g₁ ix mx = x
      -- So: g₁ irx mrx = r • (g₁ ix mx)
      -- By linearity of g₁ ix: r • (g₁ ix mx) = g₁ ix (r • mx)

      -- We need to show: g₁ irx mrx = g₁ ix (r • mx)
      have smul_eq : g₁ irx mrx = g₁ ix (r • mx) := by
        rw [hrx, LinearMap.map_smul, hx]

      -- Step 3: By injectivity of the direct limit
      obtain ⟨k, hixk, hirxk, h_smul⟩ := IsDirectLimit'.inj (f := f) ix irx (r • mx) mrx smul_eq.symm

      -- Step 4: Now we have: f ix k hixk (r • mx) = f irx k hirxk mrx
      -- Apply g₂ k to both sides and use compatibility
      have g2_eq : (g₂ k) (f ix k hixk (r • mx)) = (g₂ k) (f irx k hirxk mrx) :=
        congr_arg (g₂ k) h_smul

      -- Step 5: Use compatibility to simplify both sides
      rw [ Hg ix k hixk (r • mx), Hg irx k hirxk mrx] at g2_eq
      -- Now: (g₂ ix) (r • mx) = (g₂ irx) mrx

      -- Step 6: Use linearity of g₂ ix
      rw [LinearMap.map_smul] at g2_eq
      -- Now: r • (g₂ ix) mx = (g₂ irx) mrx

      -- Step 7: This gives us exactly what we need!
      exact g2_eq.symm

set_option pp.proofs true in
@[simp] theorem lift_of [IsDirectLimit' M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
  (lift M f P₁ P₂ g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  -- have := (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (g₁ i x))).choose_spec
  have h_spec := Classical.choose_spec
    (Classical.choose_spec (IsDirectLimit'.surj f (g := g₁) (g₁ i x)))
-- h_spec : g₁ (Classical.choose (IsDirectLimit'.surj (g₁ i x)))
--              (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))) = g₁ i x

-- Now you have two equal elements in P₁: both equal g₁ i x
-- By injectivity of the direct limit:
  have ⟨k, hik, hjk, h_eq⟩ := IsDirectLimit'.inj (f:=f) i
    (Classical.choose (IsDirectLimit'.surj f (g := g₁) (g₁ i x)))
    x (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))) (h_spec.symm)
-- h_eq : f i k hik x = f (Classical.choose (IsDirectLimit'.surj (g₁ i x))) k hjk
--                      (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x)))

-- Now use compatibility (your hypothesis Hg):
  rw [← Hg i k hik x]
  rw [← Hg (Classical.choose (IsDirectLimit'.surj f (g := g₁) (g₁ i x))) k hjk
         (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x)))]
  rw [h_eq]


theorem lift_unique [IsDirectLimit' M P₁ f g₁]
  (F : P₁ →ₗ[R] P₂) (x) : F x = (lift M f P₁ P₂ g₁ (fun i ↦ F.comp <| g₁ i)
  (fun i j hij x ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact LinearMap.congr_arg (IsDirectLimit'.compatibility i j hij x))) x := by
    dsimp [lift]
    rw [Classical.choose_spec (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) x))]

noncomputable def iso_of_isDirectLimit'
    [h₁ : IsDirectLimit' M P₁ f g₁] [h₂ : IsDirectLimit' M P₂ f g₂] :
    P₁ ≃ₗ[R] P₂ where
  __ := (lift M f P₁ P₂ g₁ g₂ h₂.compatibility)
  invFun := (lift M f P₂ P₁ g₂ g₁ h₁.compatibility)
  left_inv x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    obtain ⟨i, mi, hmi⟩ := h₁.surj x
    rw [← hmi]
    simp only [lift_of]
  right_inv x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    obtain ⟨i, mi, hmi⟩ := h₂.surj x
    rw [← hmi]
    simp only [lift_of]


end Module

end IsDirectLimit

section TensorProduct

open scoped TensorProduct
open Module

variable {R : Type*} [CommSemiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
variable [AddCommMonoid P] [Module R P]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i, M i →ₗ[R] P)
variable [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem M (f · · ·)]
variable (N : Type*) [AddCommMonoid N] [Module R N] [h : IsDirectLimit' M P f g]

def incTensorMap (i j : ι) (h : i ≤ j) : M i ⊗[R] N →ₗ[R] M j ⊗[R] N :=
   LinearMap.rTensor N (f i j h)

def tensorMap (i : ι) : M i ⊗[R] N →ₗ[R] P ⊗[R] N :=
  LinearMap.rTensor N (g i)

instance : DirectedSystem (fun i ↦ M i ⊗[R] N) fun x1 x2 x3 ↦ ⇑(incTensorMap M f N x1 x2 x3) :=
  sorry

lemma comp (i k) (hik : i ≤ k) :
  (tensorMap M P g N k).comp (incTensorMap M f N i k hik)
    = tensorMap M P g N i := by
    dsimp [tensorMap, incTensorMap]
    ext u v
    simp [h.compatibility i k hik u]


theorem universal_property_inj {X : Type*} [AddCommMonoid X] [Module R X]
  (gX : ∀ i, M i →ₗ[R] X) (HgX : ∀ i j hij x, gX j (f i j hij x) = gX i x)
  (unique : ∃! φ : X →ₗ[R] P, ∀ i x, φ (gX i x) = g i x) {i j mi mj} (hij : i≤j)
  (hmij : gX i mi = gX j (mj)) :
    ∃ k, ∃ (hik : i ≤ k) (hjk : j ≤ k), (f i k hik) mi = (f j k hjk) mj := by
    obtain ⟨φ, hφ, unique⟩ := unique
    have hφi := hφ i mi
    have hφj := hφ j mj
    rw [hmij] at hφi
    rw [hφi] at hφj
    obtain ⟨k, hik, hjk, fijk⟩ := h.inj i j mi mj hφj
    exact ⟨k, hik, hjk, fijk⟩


theorem universal_property {X : Type*} [AddCommMonoid X] [Module R X]
  (gX : ∀ i, M i →ₗ[R] X) (HgX : ∀ i j hij x, gX j (f i j hij x) = gX i x)
  (unique : ∃! φ : X →ₗ[R] P, ∀ i x, φ (gX i x) = g i x) :
  IsDirectLimit' M X f gX where
  surj m := by

    sorry
  inj i j mi mj hmij := by
    obtain ⟨φ, hφ, unique⟩ := unique
    have hφi := hφ i mi
    have hφj := hφ j mj
    rw [hmij] at hφi
    rw [hφi] at hφj
    obtain ⟨k, hik, hjk, fijk⟩ := h.inj i j mi mj hφj
    exact ⟨k, hik, hjk, fijk⟩

  compatibility := by

    sorry


instance : IsDirectLimit' (fun i ↦ (M i ⊗[R] N)) (P ⊗[R] N) (incTensorMap M f N)
  (tensorMap M P g N) where
    surj m := by
      induction m --using TensorProduct.induction_on
      case zero =>
        obtain ⟨i, mi, hmi⟩ := h.surj (0 : P)
        exact ⟨i, mi ⊗ₜ[R] 0, by simp [tensorMap]⟩
      case tmul x y =>
        obtain ⟨i, mi, hmi⟩ := h.surj x
        exact ⟨i, mi ⊗ₜ[R] y, by dsimp [tensorMap]; rw [hmi]⟩
      case add x y hx hy =>
        obtain ⟨i, mi, hmi⟩ := hx
        obtain ⟨j, mj, hmj⟩ := hy
        have ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
        let mik := (incTensorMap M f N i k hik) mi
        let mjk := (incTensorMap M f N j k hjk) mj
        use k, mik + mjk
        simp only [mik, mjk, LinearMap.map_add]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, comp, comp, hmi, hmj]
    inj i j mi mj hmij := by
      sorry
    compatibility := sorry

instance : DirectedSystem (fun i ↦ M i ⊗[R] N) fun x1 x2 x3 ↦ ⇑(incTensorMap M f N x1 x2 x3) :=
  sorry

#check (Module.iso_of_isDirectLimit' (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)
 (Module.DirectLimit (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)) (P ⊗[R] N)
 (Module.DirectLimit.of R ι (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)) (tensorMap M P g N))

include g in
noncomputable def iso' :
  (Module.DirectLimit (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)) ≃ₗ[R] (P ⊗[R] N) := by
  haveI : DirectedSystem (fun i ↦ M i ⊗[R] N) fun x1 x2 x3 ↦ ⇑(incTensorMap M f N x1 x2 x3) := sorry
  apply (Module.iso_of_isDirectLimit' (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)
    (Module.DirectLimit (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)) (P ⊗[R] N)
    (Module.DirectLimit.of R ι (fun i ↦ (M i ⊗[R] N)) (incTensorMap M f N)) (tensorMap M P g N))




end TensorProduct



section RestrictedProduct



open Set Filter

variable {ι : Type*} {𝓕 : Filter ι}

variable (𝓕) in
/-- The complements of sets in a `Filter`.
E.g. for the cofinite filter, these are just the finite subsets. -/
def Filter.complement : Set (Set ι) := (fun S => Sᶜ) '' 𝓕.sets

theorem principal_filter_order {S₁ S₂ : 𝓕.complement} (h : S₁ ≤ S₂) :
    (𝓟 S₂ᶜ : Filter ι) ≤ 𝓟 S₁ᶜ := by
  simp only [le_principal_iff, mem_principal, compl_subset_compl]; exact h

theorem filter_bot :
    ∀ S : 𝓕.complement, 𝓕 ≤ (𝓟 Sᶜ : Filter ι) := by
  intro S
  simp only [le_principal_iff]
  refine Filter.mem_sets.mp ?_
  have h : 𝓕.sets = (fun S => Sᶜ) '' (𝓕.complement) := by
    rw[complement]
    exact Eq.symm (compl_compl_image 𝓕.sets)
  rw[h]
  simp

open scoped RestrictedProduct

variable {R : ι → Type*} {A : (i : ι) → Set (R i)}

variable (A) in
/-- This is (isomorphic to) `(Π i ∈ S, R i) × (Π i ∉ S, A i)` -/
def mem_A_away_from_S (S : 𝓕.complement) : Type _ :=
  Πʳ i, [R i, A i]_[𝓟 Sᶜ]

/-- The inclusions between `mem_A_away_from_S` which will form the directed system. -/
def inclusion (S₁ S₂ : 𝓕.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S A S₁ → mem_A_away_from_S A S₂ :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)

instance directed_system :
    @DirectedSystem (𝓕.complement) _ (mem_A_away_from_S A) (inclusion) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct (S : 𝓕.complement) :
    mem_A_away_from_S A S → Πʳ i, [R i, A i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)

-- ....


def inclusion' (S₁ S₂ : 𝓕.complement) (h : S₁ ≤ S₂) :
    Πʳ i, [R i, A i]_[𝓟 S₁ᶜ] → Πʳ i, [R i, A i]_[𝓟 S₂ᶜ] :=
  RestrictedProduct.inclusion _ _ (principal_filter_order h)

instance directed_system' :
    @DirectedSystem (𝓕.complement) _ (mem_A_away_from_S A) (inclusion') where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The maps from the directed system to the actual restricted product. -/
def inclusion_to_restrictedProduct' (S : 𝓕.complement) :
    Πʳ i, [R i, A i]_[𝓟 Sᶜ] → Πʳ i, [R i, A i]_[𝓕] :=
  RestrictedProduct.inclusion _ _ (filter_bot S)


end RestrictedProduct



variable {ι : Type*} {R : ι → Type*} {ℱ : Filter ι}

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {B : Π i, T i}

open scoped RestrictedProduct TensorProduct Module.IsDirectLimit

variable {A : Type*} [CommRing A]

-- In open PR #25715
-- restricted product of addcommgroups is an addcommgroup
instance [Π i, AddCommGroup (R i)] [∀ i, AddSubgroupClass (T i) (R i)] :
    AddCommGroup (Πʳ i, [R i, B i]_[ℱ]) where
  __ := inferInstanceAs (AddGroup (Πʳ i, [R i, B i]_[ℱ]))
  add_comm a b := by ext i; simp [add_comm]

-- when #25715 lands we'll be able to change these to AddCommMonoid
-- restricted product of A-modules is an A-module
instance module [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)]
    -- next line is how we do "SubmoduleClass"
    [∀ i, AddSubgroupClass (T i) (R i)] [∀ i, SMulMemClass (T i) A (R i)] :
    Module A (Πʳ i, [R i, B i]_[ℱ]) where
      smul a x := ⟨fun i ↦ a • x i, Filter.Eventually.mono x.property (fun _ hi ↦
     SMulMemClass.smul_mem a hi)⟩
      one_smul b := by ext; simp
      mul_smul x y b := by ext; simp [mul_smul]
      smul_zero b := by ext; simp
      smul_add x a b := by ext; simp
      add_smul a b x := by
        ext
        simp only [RestrictedProduct.smul_apply, RestrictedProduct.add_apply, add_smul]
      zero_smul b := by ext; simp

noncomputable def Submodule.lTensor (M : Type*) {N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (P : Submodule A N) : Submodule A (M ⊗[A] N) :=
  LinearMap.range (P.subtype.lTensor M)


variable {ι : Type*} {R : ι → Type*} {ℱ : Filter ι} [Preorder ι]

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {B : Π i, T i}
variable {A : Type*} [CommRing A]

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
{M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] (S : Filter.complement ℱ)

open Set Filter RestrictedProduct

instance add (S : ℱ.complement) :
  AddCommMonoid (mem_A_away_from_S (fun i ↦ (C i : Set (R i))) S) := by
  dsimp [mem_A_away_from_S]
  exact AddCommGroup.toDivisionAddCommMonoid.toAddCommMonoid

instance module' (S : ℱ.complement) :
  Module A (mem_A_away_from_S (fun i ↦ (C i : Set (R i))) S) := by
  dsimp [mem_A_away_from_S]
  exact module


def inclusion_module (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    mem_A_away_from_S (fun i ↦ (C i : Set (R i))) S₁ →ₗ[A]
      mem_A_away_from_S ((fun i ↦ (C i : Set (R i)))) S₂ where
  toFun := inclusion S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclusion_module' (S₁ S₂ : ℱ.complement) (h : S₁ ≤ S₂) :
    Πʳ i, [R i, C i]_[𝓟 S₁ᶜ]  →ₗ[A]
      Πʳ i, [R i, C i]_[𝓟 S₂ᶜ]  where
  toFun := inclusion' S₁ S₂ h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


def inclusion_to_restricted_product_module (S : ℱ.complement) :
  mem_A_away_from_S (fun i ↦ (C i : Set (R i))) S →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := inclusion_to_restrictedProduct S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclusion_to_restricted_product_module' (S : ℱ.complement) :
  Πʳ i, [R i, C i]_[𝓟 Sᶜ] →ₗ[A] Πʳ i, [R i, C i]_[ℱ] where
  toFun := inclusion_to_restrictedProduct S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance directed : IsDirected (ℱ.complement) (· ≤ ·) := by
  refine { directed := ?_ }
  intro Si Sj
  obtain ⟨Si, hi⟩ := Si
  obtain ⟨Sj, hj⟩ := Sj
  let c := Si ∪ Sj
  have : c ∈ ℱ.complement := by
    unfold Filter.complement at hi hj ⊢
    simp only [mem_image, Filter.mem_sets] at hi hj ⊢
    obtain ⟨si, hsi⟩ := hi
    obtain ⟨sj, hsj⟩ := hj
    use si ∩ sj
    constructor
    · exact ℱ.inter_sets hsi.1 hsj.1
    · unfold c
      rw [compl_inter, hsi.2, hsj.2]
  use ⟨c, this⟩
  constructor <;>
  simp [c]

open Set
instance RestrictedProductIsDirectLimit :
  Module.IsDirectLimit' (mem_A_away_from_S  (fun i ↦ (C i : Set (R i))))
  Πʳ i, [R i, C i]_[ℱ] (inclusion_module (ℱ := ℱ))
  (inclusion_to_restricted_product_module ) where
  inj Sᵢ Sⱼ mi mj hmij := by
    obtain ⟨Sₖ, hik, hjk⟩ := @directed_of _ (· ≤ ·) directed Sᵢ Sⱼ
    refine ⟨Sₖ, hik, hjk, ?_⟩
    dsimp [inclusion_module,_root_.inclusion, RestrictedProduct.inclusion]
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct,
      RestrictedProduct.inclusion] at hmij
    apply Subtype.ext
    simp only
    injection hmij
  surj r := by
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct]
    have : ∅ ∈ ℱ.complement := by
      rw [complement]
      simp only [mem_image, Filter.mem_sets, compl_empty_iff, exists_eq_right, univ_mem]
    let b:= r.property
    let c:= r.1
    have : { i : ι | r.1 i ∈ (C i : Set (R i)) }ᶜ ∈ ℱ.complement := by
      rw [complement]
      simp only [mem_image, Filter.mem_sets]
      refine ⟨{ i : ι | r.1 i ∈ (C i : Set (R i)) }, r.property, ?_⟩
      rfl
    use ⟨{ i : ι | r.1 i ∈ (C i : Set (R i)) }ᶜ, this⟩
    apply RestrictedProduct.exists_inclusion_eq_of_eventually
    simp only [SetLike.mem_coe, compl_compl, eventually_principal, mem_setOf_eq]
    exact fun x a ↦ a
  compatibility i j hij x := by
    dsimp [inclusion_to_restricted_product_module, inclusion_to_restrictedProduct,
    inclusion_module,_root_.inclusion, inclusion_module,RestrictedProduct.inclusion]
    exact Subtype.ext rfl


#check TensorProduct.directLimitRight


variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)]

open scoped Filter

namespace RestrictedProduct

section type

variable (A : (i : ι) → Set (R i))

def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : {i // i ∈ S}, A i) × (Π i : {i // i ∉ S}, R i) where
  toFun x := (fun i ↦ ⟨x i, x.property i.property⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  Filter.eventually_principal.mpr (fun i hi ↦ by simp only [hi]; exact (y.1 ⟨i, hi⟩).2)⟩
  left_inv x := by
    simp only [dite_eq_ite, ite_self]
    rfl
  right_inv x := by
    simp only [mk_apply, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
    ext i
    · rfl
    · simp only [dif_neg i.property]

def principalEquivProd' : Πʳ i, [R i, A i]_[𝓟 Sᶜ] ≃
    (Π i : {i // i ∉ S}, A i) × (Π i : {i // i ∈ S}, R i) where
  toFun x := (fun i ↦ ⟨x i, x.property i.property⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∉ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, by simpa using hi⟩,
  Filter.eventually_principal.mpr (fun i hi ↦ by
    simp only [mem_compl_iff] at hi
    simp only [hi]
    exact (y.1 ⟨i, hi⟩).2)⟩
  left_inv x := by
    simp only [dite_eq_ite, ite_self]
    rfl
  right_inv x := by
    simp only [dite_not, mk_apply, Subtype.coe_prop, ↓reduceDIte]
    ext i <;> simp only [i.property, ↓reduceDIte]



end type


variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
variable {A : Π i, T i}

section monoid

@[to_additive]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : {i // i ∈ S}, A i) × (Π i : {i // i ∉ S}, R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl

end monoid


end RestrictedProduct

section
variable {ι : Type*}
variable {R : ι → Type*}
variable {ℱ : Filter ι}

variable {T : ι → Type*} -- subobject type
variable [Π i, SetLike (T i) (R i)]
--variable {B : Π i, T i}

open scoped RestrictedProduct TensorProduct

variable {A : Type*} [CommRing A]



open Filter


noncomputable def RestrictedProduct.principal [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
   (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] ((Π i : {i // i ∈ S}, C i) ×
  (Π i : {i // i ∉ S}, R i)) where
    __ := principalAddEquivSum R S (A := C)
    map_smul' m x := by
      simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.id_apply]
      dsimp [principalAddEquivSum, principalEquivProd]
      ext i
      · simp only [Pi.smul_apply, SetLike.coe_sort_coe, SetLike.val_smul]
      · simp only [Pi.smul_apply]

noncomputable def RestrictedProduct.princpal' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] : Πʳ i, [R i, C i]_[𝓟 Sᶜ] ≃
    (Π i : {i // i ∉ S}, C i) × (Π i : {i // i ∈ S}, R i) := sorry


noncomputable def RestrictedProduct.principal_tensor_comm' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : Π i, Submodule A (R i)} {M : Type*} [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] {S : Set ι} :
   M ⊗[A] (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] (Πʳ i, [M ⊗[A] R i, (C i).lTensor M]_[𝓟 S]) := sorry

variable [Π i, AddCommGroup (R i)] [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
instance : DecidableEq ℱ.complement := sorry
instance : Nonempty ℱ.complement := sorry
instance : DirectedSystem (mem_A_away_from_S fun i ↦ (C i : Set (R i)))
      fun x1 x2 x3 ↦ ⇑(inclusion_module (ℱ := ℱ) (C:= C) x1 x2 x3) := directed_system

#check Module.DirectLimit (mem_A_away_from_S fun i ↦ (C i : Set (R i)))
  (f := inclusion_module (C:=C) (ℱ := ℱ))


#check Module.iso_of_isDirectLimit' (mem_A_away_from_S  (fun i ↦ (C i : Set (R i))))
       (inclusion_module (ℱ := ℱ)) (Πʳ i, [R i, C i]_[ℱ])
       (Module.DirectLimit (mem_A_away_from_S fun i ↦ (C i : Set (R i)))
       (inclusion_module (ℱ := ℱ)) )


-- this now compiles
noncomputable def RestrictedProduct.tensor_comm' [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)} [Preorder ι]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] :
    M ⊗[A] (Πʳ i, [R i, C i]_[ℱ]) ≃ₗ[A] Πʳ i, [M ⊗[A] R i, (C i).lTensor M]_[ℱ] := by
    haveI : Nonempty ℱ.complement := sorry
    haveI :  DirectedSystem (mem_A_away_from_S (fun i ↦ ((C i).lTensor M : Set (M ⊗[A] R i))))
      fun x1 x2 x3 ↦ ⇑(inclusion_module (ℱ := ℱ)  x1 x2 x3) := directed_system
    let comp1 := TensorProduct.directLimitRight (inclusion_module (C:=C) (ℱ := ℱ)) M (R:=A)
    let comp := Module.iso_of_isDirectLimit' (mem_A_away_from_S  (fun i ↦ (C i : Set (R i))))
       (inclusion_module (ℱ := ℱ)) (Πʳ i, [R i, C i]_[ℱ])
       (Module.DirectLimit (mem_A_away_from_S fun i ↦ (C i : Set (R i))) (inclusion_module (C:=C) (ℱ := ℱ)))
      (inclusion_to_restricted_product_module) (Module.DirectLimit.of A _
      (mem_A_away_from_S fun i ↦ (C i : Set (R i))) (inclusion_module (ℱ := ℱ)))
    let comp2 := Module.iso_of_isDirectLimit' (mem_A_away_from_S
      (fun i ↦ ((C i).lTensor M : Set (M ⊗[A] R i))))
       (inclusion_module (ℱ := ℱ)) Πʳ i, [M ⊗[A] R i, (C i).lTensor M]_[ℱ]
       (Module.DirectLimit (mem_A_away_from_S
      (fun i ↦ ((C i).lTensor M : Set (M ⊗[A] R i)))) (inclusion_module (ℱ := ℱ)))
      (inclusion_to_restricted_product_module) (Module.DirectLimit.of A _
    (mem_A_away_from_S
      (fun i ↦ ((C i).lTensor M : Set (M ⊗[A] R i)))) (inclusion_module (ℱ := ℱ)))
    -- haveI (i : ι) : Submodule A (M ⊗[A] C i) := Module.jacobson A (M ⊗[A] ↥(C i))
    let comp3 : M ⊗[A] (Πʳ i, [R i, C i]_[ℱ]) ≃ₗ[A]
      M ⊗[A] Module.DirectLimit (mem_A_away_from_S fun i ↦ (C i : Set (R i))) inclusion_module :=
      LinearEquiv.lTensor M comp
    let comp4 :=  comp3 ≪≫ₗ comp1
   -- let comp5 := comp4 ≪≫ₗ comp2.symm
    let comp5 (S : Set ι) : M ⊗[A] ((Π i : {i // i ∈ S}, R i) × (Π i : {i // i ∉ S}, C i)) ≃ₗ[A]
      (M ⊗[A] Π i : {i // i ∈ S}, R i) × (M ⊗[A] Π i : {i // i ∉ S}, C i)  :=
        TensorProduct.prodRight A A M ((i : { i // i ∈ S }) → R ↑i) ((i : { i // i ∉ S }) → ↥(C ↑i))
    have (i : ι):= (M ⊗[A] C i)
    unfold mem_A_away_from_S at comp
    simp at comp
    let comp6 : Module.DirectLimit (fun (S: ℱ.complement) ↦ Πʳ i, [R i, C i]_[𝓟 Sᶜ]) inclusion_module'
     ≃ₗ[A] Module.DirectLimit (fun (S:ℱ.complement) ↦ ((Π i : {i // i ∉ (S : Set ι)}, C i.1) ×
  (Π i : {i // i ∈ (S : Set ι) }, R i.1))) (inclusion_module')  := RestrictedProduct.principal'


  #exit

  LinearEquiv.ofBijective (TensorProduct.lift {
    toFun m := {
      toFun x := ⟨fun i ↦ m ⊗ₜ (x i), Filter.Eventually.mono x.property (fun i hi ↦
     LinearMap.mem_range.mpr ⟨m ⊗ₜ[A] ⟨x i, hi⟩, rfl⟩)⟩
      map_add' x y := by
        ext i
        simp only [add_apply, mk_apply, TensorProduct.tmul_add]
      map_smul' a x := by
        ext i
        simp only [smul_apply, TensorProduct.tmul_smul, mk_apply, RingHom.id_apply]
    }
    map_add' x y := by
      refine LinearMap.ext (fun x₁ ↦ ?_)
      ext i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mk_apply, LinearMap.add_apply, add_apply,
        TensorProduct.add_tmul]
    map_smul' a x := by
      refine LinearMap.ext (fun x₁ ↦ ?_)
      ext i
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mk_apply, RingHom.id_apply, LinearMap.smul_apply,
        smul_apply, TensorProduct.smul_tmul']
  }) ⟨
  fun a b h ↦ by
    -- injectivity proof: if `a`, `b` in `M ⊗[A] Πʳ (i : ι), [R i, ↑(C i)]_[ℱ]`
    -- and their images in `Πʳ (i : ι), [M ⊗[A] R i, ↑(Submodule.lTensor M (C i))]_[ℱ]`
    -- are the same, then choose some `S ∈ ℱ` such that `a`, `b` are both in
    -- `M ⊗ ((∏ i ∈ S, C i) × (∏ i ∉ S, R i))`, and then by your earlier work we know
    -- that the map from this to `(∏ i ∈ S, M ⊗ C i) × (∏ i ∉ S, M ⊗ R i)` is injective,
    -- and then by flatness the map from that to
    -- `Πʳ (i : ι), [M ⊗[A] R i, ↑(Submodule.lTensor M (C i))]_[ℱ]` is injective,
    -- and `a` and `b` have become equal after the composite of those two injections,
    -- so they are equal.
    -- have h_finite : ∃ (S : Finset ι), S.toSet ∈ ℱ ∧
    -- (∀ x ∈ {a, b}, ∃ (f : ι → A), Set.finite {i | f i ≠ 0} ∧
    --  ∀ i ∉ S, (TensorProduct.lift _ x : _) i ∈ Submodule.lTensor M (C i)) := by
    --   sorry


    -- haveI {S: Set ι} {h: S ∈ ℱ} : AddCommMonoid ((Π i ∈ S, C i) × (Π i ∉ S, R i)) := sorry
    -- have : ∃S ∈ ℱ, a.val ∈ (M ⊗[A] ((Π i ∈ S, C i) × (Π i ∉ S, R i))) ∧
    --   b.val ∈ (M ⊗[A] ((Π i ∈ S, C i) × (Π i ∉ S, R i))) := sorry
    sorry,
  by
    intro y
    -- by definition `y ∈ (∏ i ∈ S, ↑(Submodule.lTensor M (C i))) × (∏ i ∉ S, M ⊗ R i)`
    -- for some `S ∈ ℱ`, and there's a surjection (in fact a bijection) from
    -- `(∏ i ∈ S, M ⊗ (C i)) × (∏ i ∉ S, M ⊗ R i)` onto this, and then by your earlier
    -- work there's something in `M ⊗ ((∏ i ∈ S, C i) × (∏ i ∉ S, R i))` which hits
    -- this, and the image of that thing in `M ⊗[A] Πʳ (i : ι), [R i, ↑(C i)]_[ℱ]`
    -- will do
    sorry⟩




end

section
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]

variable (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
namespace IsDedekindDomain

open IsDedekindDomain HeightOneSpectrum
#check Module.DirectLimit

noncomputable instance : DecidableEq (HeightOneSpectrum A) :=
  Classical.typeDecidableEq (HeightOneSpectrum A)


noncomputable def f (S T : Finset (HeightOneSpectrum A)) (h : S ≤ T) :
  ((Π v : S, v.1.adicCompletion K) ×
  (Π v : {v // v ∉ S}, (adicCompletionIntegers K v.1))) →ₗ[A]
  ((Π v : T, v.1.adicCompletion K) ×
  (Π v : {v // v ∉ T}, (adicCompletionIntegers K v.1))) where
    toFun x := (fun v ↦
      if h' : (v : HeightOneSpectrum A) ∈ S then
        x.1 ⟨v, h'⟩
      else
        algebraMap _ _ (x.2 ⟨v, h'⟩),
     fun v ↦ x.2 ⟨v, Set.notMem_subset h v.2⟩)
    map_add' x y := by
      simp only [Prod.fst_add, Pi.add_apply, Prod.snd_add, ValuationSubring.algebraMap_apply,
        AddMemClass.coe_add, Prod.mk_add_mk, Prod.mk.injEq]
      constructor
      · ext v
        by_cases hv : (v : HeightOneSpectrum A) ∈ S
        · simp [hv]
        · simp [hv]
      · ext v
        simp only [AddMemClass.coe_add, Pi.add_apply]
    map_smul' r x := by
      simp only [Prod.smul_fst, Pi.smul_apply, Prod.smul_snd, ValuationSubring.algebraMap_apply,
        coe_smul_adicCompletionIntegers, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
      constructor
      · ext v
        by_cases hv : (v : HeightOneSpectrum A) ∈ S
        · simp [hv]
        · simp [hv]
      · ext v
        simp only [coe_smul_adicCompletionIntegers, Pi.smul_apply]


noncomputable def direct_limit : (@Module.DirectLimit A _ (Finset (HeightOneSpectrum A)) _
  (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
  (adicCompletionIntegers K v.1)))) _ _ (f A K) _) ≃ₗ[A] FiniteAdeleRing A K := by
  refine LinearEquiv.ofBijective (Module.DirectLimit.lift A (Finset (HeightOneSpectrum A))
    (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
   (adicCompletionIntegers K v.1)))) (f A K) ?_ ?_) ⟨?_, ?_⟩
  · intro v
    simp only
    -- can rw as restricted product on princpal filter and go from there?
    sorry
  · intro v w
    sorry
  · apply Module.DirectLimit.lift_injective
    intro v

    sorry
  ·
    sorry

end IsDedekindDomain


#exit



-- def G (S : Finset (HeightOneSpectrum A)):=
-- ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)), (adicCompletionIntegers K v.1)))

-- #check G A K

-- noncomputable instance (S : Finset (HeightOneSpectrum A)) : AddCommGroup (G A K S) :=
--   Prod.instAddCommGroup

-- instance (S : Finset (HeightOneSpectrum A)) : Module A (G A K S) := by
--   sorry

def DirectLimit' :=
  @Module.DirectLimit A _ (Finset (HeightOneSpectrum A)) _
  (fun S ↦ ((Π v : S, v.1.adicCompletion K) × (Π v : (Set.compl (Finset.toSet S)),
  (adicCompletionIntegers K v.1)))) _ _ (f A K) _

-- noncomputable def LHS (S : FiniteSubsets A) :=
--   M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
--           (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))

-- noncomputable def RHS (S : FiniteSubsets A) :=
--   (Π v : S.val, M ⊗[A] adicCompletion K v.1) ×
--   (Π v : (Set.compl S.val), M ⊗[A] adicCompletionIntegers K v.1)

-- instance (S: FiniteSubsets A): AddCommMonoid (LHS A K M S) := by
--   dsimp [LHS]
--   exact TensorProduct.addCommMonoid

variable (iso : ∀ S : FiniteSubsets A, (M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
          (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))) ≃ₗ[A]
          ((Π v : S.val, M ⊗[A] adicCompletion K v.1) ×
  (Π v : (Set.compl S.val), M ⊗[A] adicCompletionIntegers K v.1)))

let q : ℤ := 1
def LHS_limit : Type* :=
  lim (fun S : FiniteSubsets => (M ⊗[A] ((Π v : S.val, adicCompletion K v.1) ×
          (Π v : (Set.compl S.val), adicCompletionIntegers K v.1))))



end IsDedekindDomain
