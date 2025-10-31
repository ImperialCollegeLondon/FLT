/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/

import Mathlib.Algebra.Colimit.Module

variable {ι : Type*} [Preorder ι] (M : ι → Type*) (P : Type*)
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

/--
`IsDirectLimit f g` states that `P` is the direct limit of the system `(M i, f i j hij)`.
It requires:
* `surj`: says every element of `P` comes from some `M i` via the canonical map `g i`.
* `inj`: says that if two elements of (possibly different) modules `M i` and `M j` map
  to the same element of `P`, then they become equal after being mapped into a common
  later module `M k`.
* `compatibility`: ensures that the maps `g i` and `f i j hij` are compatible with one another.
-/
@[mk_iff] class IsDirectLimit [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [DirectedSystem M f] [IsDirectLimit M P f g]

namespace IsDirectLimit

variable {M P}

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
noncomputable def preimage_index (p : P) : ι := (is_surjective f g p).choose

/--
Given an element `p : P` in the direct limit, `preimage f g p` returns an element of
`M (preimage_index f g p)` that maps to `p` under `g (preimage_index f g p)`.
-/
noncomputable def preimage (p : P) : M (preimage_index f g p) :=
  (is_surjective f g p).choose_spec.choose

theorem image_preimage (p : P) :
    g (preimage_index f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

variable (P₁ P₂ : Type*) (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

/--
Construct a map `P₁ → P₂` from a direct limit by sending each element to its preimage
in some component `M i` and applying `g₂ i`. Used to define morphisms out of direct limits.
-/
noncomputable def lift [IsDirectLimit M P₁ f g₁] (p : P₁) : P₂ :=
  g₂ (preimage_index f g₁ p) (preimage f g₁ p)

@[simp]
theorem lift_of [IsDirectLimit M P₁ f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (lift f P₁ P₂ g₁ g₂) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimage_index f g₁ (g₁ i x)) k hpk, h_eq]

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def Equiv [h₁ : IsDirectLimit M P₁ f g₁] [h₂ : IsDirectLimit M P₂ f g₂] :
    P₁ ≃ P₂ where
  toFun := lift f P₁ P₂ g₁ g₂
  invFun := lift f P₂ P₁ g₂ g₁
  left_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₁.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]
  right_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₂.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]

@[simp]
lemma Equiv_apply (i : ι) (x : M i) [IsDirectLimit M P₁ f g₁] [IsDirectLimit M P₂ f g₂] :
  Equiv f P₁ P₂ g₁ g₂ (g₁ i x) = g₂ i x := by
  simp [Equiv, Equiv.coe_fn_mk, compatibility', implies_true, lift_of]

@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) [IsDirectLimit M P₁ f g₁]
  [IsDirectLimit M P₂ f g₂] : (Equiv f P₁ P₂ g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp [Equiv, Equiv.coe_fn_symm_mk, compatibility', implies_true, lift_of]

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit M P (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit M (Module.DirectLimit M f) (f · · ·)
    (Module.DirectLimit.of R ι M f ·) where
  surj := Module.DirectLimit.exists_of
  inj i j mi mj h := by
    apply_fun Module.DirectLimit.linearEquiv _ _ at h
    simp_rw [Module.DirectLimit.linearEquiv_of] at h
    simpa [Module.DirectLimit.linearEquiv_of] using h
  compatibility i j hij x := Module.DirectLimit.of_f

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit M P₁ (f · · ·) (g₁ · ·)]

omit [IsDirected ι (· ≤ ·)] in
theorem compatibility_module {i j hij} (x : M i) : g₁ j (f i j hij x) = g₁ i x :=
  compatibility' (f := (f · · ·)) (g := (g₁ · ·)) x

/--
The universal property of the direct limit: define a linear map from the direct limit
by giving a compatible family of linear maps from the components.
Each element of the limit is sent according to its representative in some component.
-/
noncomputable def lift
    (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
  toFun := IsDirectLimit.lift (f · · ·) P₁ P₂ (g₁ · ·) (g₂ · · )
  map_add' x y := by
    obtain ⟨k, hxk, hyk⟩ :=
      IsDirected.directed (r := (· ≤ ·)) (preimage_index (f · · ·) (g₁ · ·) x)
      (preimage_index (f · · ·) (g₁ · ·) y)
    obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·))
      (preimage_index (f · · ·) (g₁ · ·) (x+y)) k
    have sum_eq : g₁ k' (f (preimage_index (f · · ·) (g₁ · ·) x) k' (le_trans hxk hkk')
      (preimage (f · · ·) (g₁ · ·) x) + f (preimage_index (f · · ·) (g₁ · ·) y) k'
      (le_trans hyk hkk') (preimage (f · · ·) (g₁ · ·) y)) =
        g₁ (preimage_index (f · · ·) (g₁ · ·) (x+y)) (preimage (f · · ·) (g₁ · ·) (x+y)) := by
      simp only [LinearMap.map_add, image_preimage]
      repeat rw [compatibility' (f := (f · · ·)) (g := (g₁ · ·)),
        image_preimage (f := (f · · ·)) (g := (g₁ · ·))]
    obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := is_injective (f · · ·) (g₁ · ·) sum_eq
    simpa [Hg] using congr_arg (g₂ k'') h'''.symm
  map_smul' r x := by
    have smul_eq : g₁ (preimage_index (f · · ·) (g₁ · ·) (r • x)) (preimage (f · · ·) (g₁ · ·)
      (r • x)) = g₁ (preimage_index (f · · ·) (g₁ · ·) x) (r • preimage (f · · ·) (g₁ · ·) x) := by
      simp only [image_preimage, map_smul]
    obtain ⟨k, hixk, hirxk, h_smul⟩ := is_injective (f · · ·) (g₁ · ·) smul_eq
    simpa [Hg] using congr_arg (g₂ k) h_smul

@[simp]
theorem lift_of (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (Module.lift P₁ P₂ f g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift, IsDirectLimit.lift_of]
  exact IsDirectLimit.lift_of (f · · ·) P₁ P₂ (g₁ · ·) (g₂ · ·) Hg x

theorem lift_unique (F : P₁ →ₗ[R] P₂) (x) : F x = (Module.lift P₁ P₂ f g₁ (fun i ↦ F.comp <| g₁ i)
    (fun i j hij x ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact LinearMap.congr_arg (IsDirectLimit.compatibility (f := (f · · ·))
      (g := (g₁ · ·)) i j hij x))) x := by
  simp only [lift, IsDirectLimit.lift,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, image_preimage]

variable [h₂ : IsDirectLimit M P₂ (f · · ·) (g₂ · ·)]

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def linearEquiv : P₁ ≃ₗ[R] P₂ :=
  { IsDirectLimit.Equiv (f · · ·) P₁ P₂ (g₁ · ·) (g₂ · ·) with
    map_add' := (lift P₁ P₂ f g₁ g₂ h₂.compatibility).map_add'
    map_smul' := (lift P₁ P₂ f g₁ g₂ h₂.compatibility).map_smul'}

@[simp]
lemma linearEquiv_apply (i : ι) (x : M i) :
  linearEquiv P₁ P₂ f g₁ g₂ (g₁ i x) = g₂ i x :=
  IsDirectLimit.Equiv_apply (f · · ·) P₁ P₂ (g₁ · ·) (g₂ · ·) i x

@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) :
  (linearEquiv P₁ P₂ f g₁ g₂).symm (g₂ i x) = g₁ i x :=
  IsDirectLimit.linearEquiv_symm_apply (f · · ·) P₁ P₂ (g₁ · ·) (g₂ · ·) i x

end Module

end IsDirectLimit
