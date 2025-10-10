/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import Mathlib.Algebra.Colimit.Module

section IsDirectLimit

namespace Module

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
 [AddCommMonoid P] [Module R P] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
 (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) (g : ∀ i, M i →ₗ[R] P) [DecidableEq ι] [IsDirected ι (· ≤ ·)]
 [Nonempty ι] [DirectedSystem M (f · · ·)]

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
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂)

open Classical in
noncomputable def lift [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) :
  P₁ →ₗ[R] P₂ where
    toFun p :=
      g₂ (choose (IsDirectLimit.surj f p))
                   (choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) p)))
    map_add' x y := by
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      have hy := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) y))
      have hxy := Classical.choose_spec (Classical.choose_spec
        (IsDirectLimit.surj f (g:= g₁) (x + y)))
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
        rw [LinearMap.map_add, IsDirectLimit.compatibility ix k' (le_trans hxk hkk') mx,
          IsDirectLimit.compatibility iy k' (le_trans hyk hkk') my, hx, hy, hxy]
      obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := IsDirectLimit.inj (f:= f) k' ixy
                                        (f ix k' (le_trans hxk hkk') mx +
                                         f iy k' (le_trans hyk hkk') my) mxy sum_eq
      rw [← Hg ixy k'' hxyk'' mxy]
      have key_eq := congr_arg (g₂ k'') h'''
      have g2_applied := congr_arg (g₂ k'') h'''
      rw [Hg k' k'' hk'k'', LinearMap.map_add, Hg ix k' (le_trans hxk hkk') mx,
        Hg iy k' (le_trans hyk hkk') my, Hg ixy k'' hxyk'' mxy] at g2_applied
      rw [ Hg ixy k'' hxyk'' mxy]
      exact g2_applied.symm
    map_smul' r x := by
      have hx := Classical.choose_spec (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      have hrx := Classical.choose_spec (Classical.choose_spec
        (IsDirectLimit.surj f (g:= g₁) (r • x)))
      set ix := Classical.choose (IsDirectLimit.surj f (g:= g₁) x)
      set mx := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) x))
      set irx := Classical.choose (IsDirectLimit.surj f (g:= g₁) (r • x))
      set mrx := Classical.choose (Classical.choose_spec (IsDirectLimit.surj f (g:= g₁) (r • x)))
      simp only [RingHom.id_apply]
      have smul_eq : g₁ irx mrx = g₁ ix (r • mx) := by
        rw [hrx, LinearMap.map_smul, hx]
      obtain ⟨k, hixk, hirxk, h_smul⟩ := IsDirectLimit.inj (f := f) ix irx (r • mx) mrx smul_eq.symm
      have g2_eq : (g₂ k) (f ix k hixk (r • mx)) = (g₂ k) (f irx k hirxk mrx) :=
        congr_arg (g₂ k) h_smul
      rw [ Hg ix k hixk (r • mx), Hg irx k hirxk mrx, LinearMap.map_smul] at g2_eq
      exact g2_eq.symm

omit [DecidableEq ι] [Nonempty ι] [DirectedSystem M fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] in
@[simp]
theorem lift_of [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
  (lift M f P₁ P₂ g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have h_spec := Classical.choose_spec
    (Classical.choose_spec (IsDirectLimit.surj f (g := g₁) (g₁ i x)))
  have ⟨k, hik, hjk, h_eq⟩ := IsDirectLimit.inj (f:=f) i
    (Classical.choose (IsDirectLimit.surj f (g := g₁) (g₁ i x)))
    x (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))) (h_spec.symm)
  rw [← Hg i k hik x, ← Hg (Classical.choose (IsDirectLimit.surj f (g := g₁) (g₁ i x))) k hjk
         (Classical.choose (lift._proof_1 M f P₁ g₁ ((g₁ i) x))), h_eq]

omit [DecidableEq ι] [Nonempty ι] [DirectedSystem M fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] in
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

omit [DecidableEq ι] [Nonempty ι] [DirectedSystem M fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] in
@[simp]
lemma iso_of_isDirectLimit_apply [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂]
  (i : ι) (x : M i) : iso_of_isDirectLimit M f P₁ P₂ g₁ g₂ (g₁ i x) = g₂ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_mk, lift_of]

omit [DecidableEq ι] [Nonempty ι] [DirectedSystem M fun x1 x2 x3 ↦ ⇑(f x1 x2 x3)] in
@[simp]
lemma iso_of_isDirectLimit_symm_apply [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂]
  (i : ι) (x : M i) : (iso_of_isDirectLimit M f P₁ P₂ g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_symm_mk', lift_of]

end Module

end IsDirectLimit
