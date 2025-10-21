/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import Mathlib.Algebra.Colimit.Module

section IsDirectLimit

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
 [AddCommMonoid P] [Module R P] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
 (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) (g : ∀ i, M i →ₗ[R] P)

/--
`IsDirectLimit f g` states that `P` is the direct limit of the system `(M i, f i j hij)`.
It requires:
* `surj`: says every element of `P` comes from some `M i` via the canonical map `g i`.
* `inj`: says that if two elements of (possibly different) modules `M i` and `M j` map
  to the same element of `P`, then they become equal after being mapped into a common
  later module `M k`.
* `compatibility`: ensures that the maps `g i` and `f i j hij` are compatible with one another.
-/
@[mk_iff] class IsDirectLimit : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x
  directedsystem : DirectedSystem M (f · · ·)

variable [IsDirectLimit M P f g]

namespace IsDirectLimit

variable {M P}

@[simp]
theorem compatibility' {i j hij} (x : M i) : g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

theorem is_injective {i j} {mi : M i} {mj : M j} (h : g i mi = g j mj) :
  ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

include f in
theorem is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj f

/--
Given an element `p : P` in the direct limit, `preimage_index f g p` returns an index in `ι` such
that `p` is in the image of the map `g (preimage_index f g p) : M (preimage_index f g p) →ₗ[R] P`.
-/
noncomputable def preimage_index [IsDirectLimit M P f g] (p : P) : ι := (is_surjective f g p).choose

/--
Given an element `p : P` in the direct limit, `preimage f g p` returns an element of
`M (preimage_index f g p)` that maps to `p` under `g (preimage_index f g p)`.
-/
noncomputable def preimage [IsDirectLimit M P f g] (p : P) : M (preimage_index f g p) :=
  (is_surjective f g p).choose_spec.choose

@[simp]
theorem image_preimage (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
   (is_surjective f g p).choose_spec.choose_spec

variable [IsDirectLimit M P f g] [IsDirected ι (· ≤ ·)]

instance isDirectLimit [DecidableEq ι] [Nonempty ι]
  [h : DirectedSystem M (f · · ·)] : IsDirectLimit M (Module.DirectLimit M f) f
  (Module.DirectLimit.of R ι M f) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of] at h
    simpa [Module.DirectLimit.linearEquiv_of] using h
  compatibility i j hij x := Module.DirectLimit.of_f
  directedsystem := h

variable (P₁ P₂ : Type*) [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂)

/--
The universal property of the direct limit: define a linear map from the direct limit
by giving a compatible family of linear maps from the components.
Each element of the limit is sent according to its representative in some component.
-/
noncomputable def lift [IsDirectLimit M P₁ f g₁]
  (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
    toFun p := g₂ (preimage_index f g₁ p) (preimage f g₁ p)
    map_add' x y := by
      obtain ⟨k, hxk, hyk⟩ :=
        IsDirected.directed (r := (· ≤ ·)) (preimage_index f g₁ x) (preimage_index f g₁ y)
      obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·)) (preimage_index f g₁ (x+y)) k
      have sum_eq : g₁ k' (f ((preimage_index f g₁ x)) k' (le_trans hxk hkk') (preimage f g₁ x) +
        f (preimage_index f g₁ y) k' (le_trans hyk hkk') (preimage f g₁ y)) =
                    g₁ (preimage_index f g₁ (x+y)) (preimage f g₁ (x+y)) := by
        simp only [LinearMap.map_add, compatibility', image_preimage]
      obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := is_injective (f:= f) g₁ sum_eq
      simpa [Hg] using congr_arg (g₂ k'') h'''.symm
    map_smul' r x := by
      have smul_eq : g₁ (preimage_index f g₁ (r • x))  (preimage f g₁ (r • x)) =
        g₁ (preimage_index f g₁ x) (r • (preimage f g₁ x)) := by
          simp only [image_preimage, map_smul]
      obtain ⟨k, hixk, hirxk, h_smul⟩ := is_injective f g₁ smul_eq
      simpa [Hg] using congr_arg (g₂ k) h_smul

@[simp]
theorem lift_of [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
  (lift f P₁ P₂ g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have h_spec := Classical.choose_spec
    (Classical.choose_spec (IsDirectLimit.surj f (g := g₁) (g₁ i x)))
  have ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

theorem lift_unique [IsDirectLimit M P₁ f g₁]
  (F : P₁ →ₗ[R] P₂) (x) : F x = (lift f P₁ P₂ g₁ (fun i ↦ F.comp <| g₁ i)
  (fun i j hij x ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact LinearMap.congr_arg (IsDirectLimit.compatibility i j hij x))) x := by
    simp [lift]

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def iso_of_isDirectLimit
    [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂] :
    P₁ ≃ₗ[R] P₂ where
  __ := (lift f P₁ P₂ g₁ g₂ h₂.compatibility)
  invFun := (lift f P₂ P₁ g₂ g₁ h₁.compatibility)
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
  (i : ι) (x : M i) : iso_of_isDirectLimit f P₁ P₂ g₁ g₂ (g₁ i x) = g₂ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_mk, lift_of]

@[simp]
lemma iso_of_isDirectLimit_symm_apply [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂]
  (i : ι) (x : M i) : (iso_of_isDirectLimit f P₁ P₂ g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp only [iso_of_isDirectLimit, LinearEquiv.coe_symm_mk', lift_of]

end IsDirectLimit

end IsDirectLimit
