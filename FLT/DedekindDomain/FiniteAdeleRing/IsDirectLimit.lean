import Mathlib.Algebra.Colimit.Module

section IsDirectLimit

namespace Module

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
variable [AddCommMonoid P] [Module R P]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i, M i →ₗ[R] P)
variable [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem M (f · · ·)]

@[mk_iff] class IsDirectLimit : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [IsDirectLimit M P f g]


instance isDirectLimit : IsDirectLimit M (Module.DirectLimit M f) f
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
noncomputable def lift [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) :
  P₁ →ₗ[R] P₂ where
    toFun p :=
      g₂ (choose (IsDirectLimit.surj f p))
                   (choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) p)))
    map_add' x y := by
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      have hy := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) y))
      have hxy := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) (x + y)))
      set ix := Classical.choose (IsDirectLimit.surj f (g:= g₁) x)
      set mx := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      set iy := Classical.choose (IsDirectLimit.surj f (g:= g₁) y)
      set my := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) y))
      set ixy := Classical.choose (IsDirectLimit.surj f (g:= g₁) (x + y))
      set mxy := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) (x + y)))

      obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) ix iy
      obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·)) ixy k
      have sum_eq : g₁ k' (f ix k' (le_trans hxk hkk') mx + f iy k' (le_trans hyk hkk') my) =
                    g₁ ixy mxy := by
        rw [LinearMap.map_add]
        rw [IsDirectLimit.compatibility ix k' (le_trans hxk hkk') mx]
        rw [IsDirectLimit.compatibility iy k' (le_trans hyk hkk') my]
        rw [hx, hy, hxy]

      obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := IsDirectLimit.inj (f:= f) k' ixy
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
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      have hrx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) (r • x)))
      set ix := Classical.choose (IsDirectLimit.surj f (g:= g₁) x)
      set mx := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      set irx := Classical.choose (IsDirectLimit.surj f (g:= g₁) (r • x))
      set mrx := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) (r • x)))
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
      obtain ⟨k, hixk, hirxk, h_smul⟩ := IsDirectLimit.inj (f := f) ix irx (r • mx) mrx smul_eq.symm

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
@[simp] theorem lift_of [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
  (lift M f P₁ P₂ g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  -- have := (Classical.choose_spec (IsDirectLimit'.surj f (g:= g₁) (g₁ i x))).choose_spec
  have h_spec := Classical.choose_spec
    (Classical.choose_spec (IsDirectLimit.surj f (g := g₁) (g₁ i x)))
-- h_spec : g₁ (Classical.choose (IsDirectLimit'.surj (g₁ i x)))
--              (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))) = g₁ i x

-- Now you have two equal elements in P₁: both equal g₁ i x
-- By injectivity of the direct limit:
  have ⟨k, hik, hjk, h_eq⟩ := IsDirectLimit.inj (f:=f) i
    (Classical.choose (IsDirectLimit.surj f (g := g₁) (g₁ i x)))
    x (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))) (h_spec.symm)
-- h_eq : f i k hik x = f (Classical.choose (IsDirectLimit'.surj (g₁ i x))) k hjk
--                      (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x)))

-- Now use compatibility (your hypothesis Hg):
  rw [← Hg i k hik x]
  rw [← Hg (Classical.choose (IsDirectLimit.surj f (g := g₁) (g₁ i x))) k hjk
         (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x)))]
  rw [h_eq]


theorem lift_unique [IsDirectLimit M P₁ f g₁]
  (F : P₁ →ₗ[R] P₂) (x) : F x = (lift M f P₁ P₂ g₁ (fun i ↦ F.comp <| g₁ i)
  (fun i j hij x ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact LinearMap.congr_arg (IsDirectLimit.compatibility i j hij x))) x := by
    dsimp [lift]
    rw [Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))]

noncomputable def iso_of_isDirectLimit
    [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂] :
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

@[simp]
lemma iso_of_isDirectLimit_apply [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂]
  (i : ι) (x : M i) : iso_of_isDirectLimit M f P₁ P₂ g₁ g₂ (g₁ i x) = g₂ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_mk, lift_of]

@[simp]
lemma iso_of_isDirectLimit_symm_apply [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂]
  (i : ι) (x : M i) : (iso_of_isDirectLimit M f P₁ P₂ g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_symm_mk', lift_of]

end Module

end IsDirectLimit
