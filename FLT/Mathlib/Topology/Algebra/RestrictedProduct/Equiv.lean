/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
module

public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
--import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!

# Isomorphisms of restricted products

Restricted products of isomorphic things are isomorphic.

Restricted products of matrices/products/units are isomorphic to matrices/products/units
of the restricted product.

Restricted product over a principal filter is isomorphic to a product.

We don't allow topological isomorphisms; they have to go into TopologicalSpace because of imports.

-/

@[expose] public section

open RestrictedProduct

section pi_congr_right

variable {ι : Type*}
variable {R₁ : ι → Type*} {R₂ : ι → Type*} {S₁ : ι → Type*} {S₂ : ι → Type*}
  [(i : ι) → SetLike (S₁ i) (R₁ i)] [(i : ι) → SetLike (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → Set (R₁ i)} {A₂ : (i : ι) → Set (R₂ i)}
variable {𝓕 : Filter ι}

/-- The equivalence between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
@[simps]
def Equiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕] ≃ Πʳ i, [R₂ i, A₂ i]_[𝓕] where
  toFun := map (fun i ↦ φ i) (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo)
  invFun := map (fun i ↦ (φ i).symm)
    (by filter_upwards [hφ]; exact fun i ↦ Set.BijOn.mapsTo ∘ Set.BijOn.equiv_symm)
  left_inv x := by ext; simp
  right_inv x := by ext; simp

section add_mul_equiv

variable [(i : ι) → Monoid (R₁ i)] [(i : ι) → Monoid (R₂ i)]
  [(i : ι) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → SubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

/-- The `MulEquiv` between restricted products built from `MulEquiv`s on the factors. -/
@[to_additive (attr := simps! apply) /-- The `AddEquiv` between restricted products built from
  `AddEquiv`s on the factors. -/]
def MulEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := Equiv.restrictedProductCongrRight _ hφ
  map_mul' _ _ := by ext; simp

/-- The isomorphism between the units of a restricted product of monoids,
and the restricted product of the units of the monoids. -/
def MulEquiv.restrictedProductUnits {ι : Type*} {ℱ : Filter ι}
    {M : ι → Type*} [(i : ι) → Monoid (M i)]
    {S : ι → Type*} [∀ i, SetLike (S i) (M i)] [∀ i, SubmonoidClass (S i) (M i)]
    {A : Π i, S i} :
    (Πʳ i, [M i, A i]_[ℱ])ˣ ≃*
      Πʳ i, [(M i)ˣ, (Submonoid.ofClass (A i)).units]_[ℱ] where
        toFun u := ⟨fun i ↦ ⟨u.1 i, u⁻¹.1 i, congr($u.mul_inv i), congr($u.inv_mul i)⟩,
          by filter_upwards [u.val.2, u⁻¹.val.2] using fun i hi hi' ↦ ⟨hi, hi'⟩⟩
        invFun ui := ⟨⟨fun i ↦ ui i, by filter_upwards [ui.2] using fun i hi ↦ hi.1⟩,
          ⟨fun i ↦ ui⁻¹ i, by filter_upwards [ui⁻¹.2] using fun i hi ↦ hi.1⟩,
          by ext i; exact (ui i).mul_inv,
          by ext i; exact (ui i).inv_mul⟩
        left_inv u := by ext; rfl
        right_inv ui := by ext; rfl
        map_mul' u v := by ext; rfl

end add_mul_equiv

section ring_equiv

variable [(i : ι) → Semiring (R₁ i)] [(i : ι) → Semiring (R₂ i)]
  [(i : ι) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}

/-- The ring isomorphism between restricted products on the same index, when
each factor is equivalent, with compatibility on the restricted subsets. -/
@[simps! apply]
def RingEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃+* R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃+* (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext; simp [AddEquiv.restrictedProductCongrRight]

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι) → AddCommMonoid (R₁ i)] [(i : ι) → AddCommMonoid (R₂ i)]
variable [(i : ι) → Module T (R₁ i)] [(i : ι) → Module T (R₂ i)]
variable [(i : ι) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι) → S₁ i} {A₂ : (i : ι) → S₂ i}
variable [(i : ι) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι) → SMulMemClass (S₂ i) T (R₂ i)]

/-- The `LinearEquiv` between restricted products built from `LinearEquiv`s on the factors. -/
def LinearEquiv.restrictedProductCongrRight (φ : (i : ι) → R₁ i ≃ₗ[T] R₂ i)
    (hφ : ∀ᶠ i in 𝓕, Set.BijOn (φ i) (A₁ i) (A₂ i)) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕]) ≃ₗ[T] (Πʳ i, [R₂ i, A₂ i]_[𝓕]) where
  __ := AddEquiv.restrictedProductCongrRight (fun i ↦ (φ i).toAddEquiv)
    (by filter_upwards [hφ]; exact fun i ↦ id)
  map_smul' m x := by
    ext i
    apply map_smul

end linear_equiv

end pi_congr_right

section pi_congr_left

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply, simps -isSimp symm_apply]
def Equiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂] where
  toFun x := ⟨fun i ↦ e.piCongrLeft' _ x i, by
    have := x.eventually
    simp only [piCongrLeft'_apply, h, Filter.eventually_map]; grind⟩
  invFun y := ⟨fun j ↦ (e.piCongrLeft' _).symm y j, by
    have := y.eventually
    simp_rw [h] at this
    have := Filter.eventually_map.1 this
    simp only [piCongrLeft'_symm_apply]; grind⟩
  left_inv x := by
    ext i
    exact funext_iff.1 ((e.piCongrLeft' _).left_inv x) i
  right_inv y := by
    ext j
    exact funext_iff.1 ((e.piCongrLeft' _).right_inv y) j

@[simp]
theorem Equiv.restrictedProductCongrLeft'_symm_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e)
    (x : Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) (j : ι₂) :
    (restrictedProductCongrLeft' e h).symm x (e.symm j) = x j := by
  simp [restrictedProductCongrLeft'_symm_apply]

/-- The equivalence between restricted products on the same factors on different
indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def Equiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  ((e.symm).restrictedProductCongrLeft' (𝓕₂.map_equiv_symm _ ▸ h)).symm

@[simp]
theorem Equiv.restrictedProductCongrLeft_apply_apply (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (x : Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁]) (i : ι₁) :
    (restrictedProductCongrLeft e h) x (e i) = x i :=
  restrictedProductCongrLeft'_symm_apply_apply e.symm (𝓕₂.map_equiv_symm _ ▸ h) x _

#adaptation_note /-- to_additive started failing in 4.28.0 . This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes -/
section add_equiv

variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}
/-- The additive monoid isomorphism between restricted
products on the same factors on different indices, when the indices are equivalent, with
compatibility on the restriction filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def AddEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_add' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']

/-- The additive monoid isomorphism between restricted
products on the same factors on different indices, when the indices are equivalent, with
compatibility on the restriction filters. Applying the equivalence on the left-hand side. -/
def AddEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_add' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end add_equiv

section mul_equiv

variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

-- @[to_additive (attr := simps! apply)  should be re-added when we bump beyond 4.28.0; we want
-- to revert the changes in this file made in
-- https://github.com/ImperialCollegeLondon/FLT/pull/859/changes
/-- The multiplicative monoid isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
def MulEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := by ext; simp [Equiv.restrictedProductCongrLeft']

/-- The multiplicative monoid isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def MulEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := Equiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end mul_equiv

section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The ring isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def RingEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_mul' _ _ := rfl

/-- The ring isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
def RingEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃+* Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_mul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]
  [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]

/-- The linear isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the right-hand side. -/
@[simps! apply]
def LinearEquiv.restrictedProductCongrLeft' (e : ι₁ ≃ ι₂) (h : 𝓕₂ = 𝓕₁.map e) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₁ (e.symm j), A₁ (e.symm j)]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongrLeft' e h
  map_smul' _ _ := rfl

/-- The linear isomorphism between restricted products on the same factors on
different indices, when the indices are equivalent, with compatibility on the restriction
filters. Applying the equivalence on the left-hand side. -/
def LinearEquiv.restrictedProductCongrLeft (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e) :
    Πʳ i, [R₂ (e i), A₂ (e i)]_[𝓕₁] ≃ₗ[T] Πʳ j, [R₂ j, A₂ j]_[𝓕₂] where
  __ := AddEquiv.restrictedProductCongrLeft e h
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp [AddEquiv.restrictedProductCongrLeft]

end linear_equiv

end pi_congr_left

section pi_congr

variable {ι₁ ι₂ : Type*}
variable {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

/-- The equivalence between restricted products when the indices and factors are equivalent,
provided compatibility criteria on the restriction filters and factors. -/
def Equiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Πʳ i, [R₁ i, A₁ i]_[𝓕₁] ≃ Πʳ j, [R₂ j, A₂ j]_[𝓕₂] :=
  (Equiv.restrictedProductCongrRight φ hφ).trans
    (e.restrictedProductCongrLeft h)

@[simp]
theorem Equiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    e.restrictedProductCongr h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem Equiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃ R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (e.restrictedProductCongr h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

#adaptation_note /-- to_additive started failing in 4.28.0.
This should be fixed
in current mathlib; these lines to 200 can be deleted. See
https://github.com/ImperialCollegeLondon/FLT/pull/859/changes  -/
section add_equiv

variable [(i : ι₁) → AddMonoid (R₁ i)] [(i : ι₂) → AddMonoid (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The additive monoid isomorphism between restricted
products when the indices and factors are equivalent, provided compatibility criteria on the
restriction filters and factors. -/
@[simps! apply]
def AddEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+ R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+ (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_add' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

end add_equiv

section mul_equiv

variable [(i : ι₁) → Monoid (R₁ i)] [(i : ι₂) → Monoid (R₂ i)]
  [(i : ι₁) → SubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → SubmonoidClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The multiplicative monoid isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def MulEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := Equiv.restrictedProductCongr e h (fun _ ↦ (φ _).toEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

end mul_equiv

section ring_equiv

variable [(i : ι₁) → Semiring (R₁ i)] [(i : ι₂) → Semiring (R₂ i)]
  [(i : ι₁) → SubsemiringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubsemiringClass (S₂ i) (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

/-- The ring isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def RingEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃+* (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_mul' _ _ := by ext j; obtain ⟨i, rfl⟩ := e.surjective j; simp

@[simp]
theorem RingEquiv.restrictedProductCongr_apply_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ i, [R₁ i, A₁ i]_[𝓕₁]} {i : ι₁} :
    RingEquiv.restrictedProductCongr e h φ hφ x (e i) =
      φ i (x i) := by
  simp [restrictedProductCongr]

@[simp]
theorem RingEquiv.restrictedProductCongr_symm_apply {e : ι₁ ≃ ι₂} {h : 𝓕₁ = 𝓕₂.comap e}
    {φ : (i : ι₁) → R₁ i ≃+* R₂ (e i)}
    {hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))}
    {x : Πʳ j, [R₂ j, A₂ j]_[𝓕₂]} :
    (RingEquiv.restrictedProductCongr e h φ hφ).symm x = fun a => (φ a).symm (x (e a)) :=
  rfl

end ring_equiv

section linear_equiv

variable {T : Type*} [Semiring T]
variable [(i : ι₁) → AddCommMonoid (R₁ i)] [(i : ι₂) → AddCommMonoid (R₂ i)]
variable {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}
variable [(i : ι₁) → Module T (R₁ i)] [(i : ι₂) → Module T (R₂ i)]
  [(i : ι₁) → AddSubmonoidClass (S₁ i) (R₁ i)] [(i : ι₂) → AddSubmonoidClass (S₂ i) (R₂ i)]
  [(i : ι₁) → SMulMemClass (S₁ i) T (R₁ i)] [(i : ι₂) → SMulMemClass (S₂ i) T (R₂ i)]

/-- The linear isomorphism between restricted products when the indices and factors
are equivalent, provided compatibility criteria on the restriction filters and factors. -/
def LinearEquiv.restrictedProductCongr (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃ₗ[T] R₂ (e i))
    (hφ : ∀ᶠ i in 𝓕₁, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    (Πʳ i, [R₁ i, A₁ i]_[𝓕₁]) ≃ₗ[T] (Πʳ j, [R₂ j, A₂ j]_[𝓕₂]) where
  __ := AddEquiv.restrictedProductCongr e h (fun _ ↦ (φ _).toAddEquiv) hφ
  map_smul' _ _ := by
    ext j
    obtain ⟨i, rfl⟩ := e.surjective j
    simp

end linear_equiv

end pi_congr

section structure_map

variable {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {S₁ : ι₁ → Type*} {R₂ : ι₂ → Type*} {S₂ : ι₂ → Type*}
  [(i : ι₁) → SetLike (S₁ i) (R₁ i)] [(i : ι₂) → SetLike (S₂ i) (R₂ i)]
  {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂} {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable [(i : ι₁) → Ring (R₁ i)] [(i : ι₂) → Ring (R₂ i)]
  [(i : ι₁) → SubringClass (S₁ i) (R₁ i)] [(i : ι₂) → SubringClass (S₂ i) (R₂ i)]
  {A₁ : (i : ι₁) → S₁ i} {A₂ : (i : ι₂) → S₂ i}

theorem RingEquiv.restrictedProductCongr_bijOn_structureSubring (e : ι₁ ≃ ι₂) (h : 𝓕₁ = 𝓕₂.comap e)
    (φ : (i : ι₁) → R₁ i ≃+* R₂ (e i))
    (hφ : ∀ i, Set.BijOn (φ i) (A₁ i) (A₂ (e i))) :
    Set.BijOn (restrictedProductCongr e h φ (.of_forall hφ))
      (structureSubring R₁ A₁ 𝓕₁) (structureSubring R₂ A₂ 𝓕₂) := by
  have hm (i : _) := (hφ i).mapsTo
  have hs (i : _) := (hφ i).symm (φ i).toEquiv.invOn |>.mapsTo
  refine ⟨fun x hx ↦ ?_, (RingEquiv.injective _).injOn, fun y hy ↦ ?_⟩
  · refine mem_structureSubring_iff.2 fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    aesop
  · exact ⟨(restrictedProductCongr e h φ (.of_forall hφ)).symm y, by aesop⟩

end structure_map

section binary

variable {ι : Type*} {ℱ : Filter ι} {A B : ι → Type*}
  {C : (i : ι) → Set (A i)} {D : (i : ι) → Set (B i)}

/-- The bijection between a restricted product of binary products, and the binary product
of the restricted products. -/
@[simps]
def Equiv.restrictedProductProd :
    Πʳ i, [A i × B i, C i ×ˢ D i]_[ℱ] ≃ (Πʳ i, [A i, C i]_[ℱ]) × (Πʳ i, [B i, D i]_[ℱ]) where
  toFun x := (map (fun i (t : A i × B i) ↦ t.1) (by simp +contextual [Set.MapsTo]) x,
              map (fun i (t : A i × B i) ↦ t.2) (by simp +contextual [Set.MapsTo]) x)
  invFun yz :=
    ⟨fun i ↦ (yz.1 i, yz.2 i), by
    filter_upwards [yz.1.2, yz.2.2] with i using Set.mk_mem_prod⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

lemma Equiv.restrictedProductProd_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductProd.symm ∘ Prod.map (inclusion _ _ hℱ) (inclusion _ _ hℱ) =
      inclusion (fun i ↦ A i × B i) (fun i ↦ C i ×ˢ D i) hℱ ∘ Equiv.restrictedProductProd.symm :=
  rfl

end binary

section pi

variable {ι : Type*} {ℱ : Filter ι} {n : Type*} [Fintype n]
    {A : n → ι → Type*}
    {C : (j : n) → (i : ι) → Set (A j i)}

-- Q: Is there a mathlibism for `{f | ∀ j, f j ∈ C j i}`?
-- A: Yes, `Set.pi Set.univ`, except that it's defeq to `{f | ∀ j ∈ univ, f j ∈ C j i}`

/-- The bijection between a restricted product of finite products, and a finite product
of restricted products.
-/
def Equiv.restrictedProductPi :
    Πʳ i, [Π j, A j i, {f | ∀ j, f j ∈ C j i}]_[ℱ] ≃ Π j, Πʳ i, [A j i, C j i]_[ℱ] where
  toFun x j := map (fun i t ↦ t _) (by simp +contextual [Set.MapsTo]) x
  invFun y := .mk (fun i j ↦ y j i) (by simp)
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl

lemma Equiv.restrictedProductPi_symm_comp_inclusion {ℱ₁ ℱ₂ : Filter ι} (hℱ : ℱ₁ ≤ ℱ₂) :
    Equiv.restrictedProductPi.symm ∘ Pi.map (fun i ↦ inclusion (A i) (C i) hℱ) =
      inclusion _ _ hℱ ∘ Equiv.restrictedProductPi.symm :=
  rfl

/-- The bijection between a restricted product of m x n matrices, and m x n matrices
of restricted products.
-/
def Equiv.restrictedProductMatrix {ι : Type*} {m n : Type*} [Fintype m] [Fintype n]
    {A : ι → Type*}
    {C : (i : ι) → Set (A i)} :
    Πʳ i, [Matrix m n (A i), {f | ∀ a b, f a b ∈ C i}] ≃ Matrix m n (Πʳ i, [A i, C i]) :=
  Equiv.restrictedProductPi.trans (Equiv.piCongrRight fun _ ↦ Equiv.restrictedProductPi)

end pi

namespace RestrictedProduct

section flatten

variable {ι : Type*}
variable {ℱ : Filter ι}
    {G H : ι → Type*}
    {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)}
variable {ι₂ : Type*} {𝒢 : Filter ι₂} {f : ι → ι₂} (C)

variable (hf : Filter.Tendsto f ℱ 𝒢) in
/-- The canonical map from a restricted product of products over fibres of a map on indexing sets
to the restricted product over the original indexing set. -/
def flatten : Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] →
    Πʳ i, [G i, C i]_[ℱ] :=
  mapAlong _ G f hf (fun i x ↦ x ⟨i, rfl⟩) (by filter_upwards with x y hy using hy ⟨x, rfl⟩ trivial)

@[simp]
lemma flatten_apply (hf : Filter.Tendsto f ℱ 𝒢) (x) (i : ι) :
    flatten C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

variable (hf : Filter.comap f 𝒢 = ℱ)

/-- The canonical bijection from a restricted product of products over fibres of a map on indexing
sets to the restricted product over the original indexing set. -/
def flatten_equiv :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)]_[𝒢] ≃
    Πʳ i, [G i, C i]_[ℱ] where
  toFun := flatten C (by rw [Filter.tendsto_iff_comap]; exact hf.ge)
  invFun := fun ⟨x, hx⟩ ↦ ⟨fun _ i ↦ x i, by
    rw [← hf, Filter.eventually_comap] at hx
    filter_upwards [hx] with j hj ⟨i, hi⟩ _ using hj i hi⟩
  left_inv := by
    intro ⟨x, hx⟩
    ext _ ⟨i, rfl⟩
    rfl
  right_inv x := by ext i; rfl

@[simp]
lemma flatten_equiv_apply (x) (i : ι) :
    flatten_equiv C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv C hf).symm x i j = x j.1 :=
  rfl

variable (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite)

/-- The equivalence given by `flatten` when both restricted products are over the cofinite
filter. -/
def flatten_equiv' :
    Πʳ j, [Π (i : f ⁻¹' {j}), G i, Set.pi Set.univ (fun (i : f ⁻¹' {j}) => C i)] ≃
    Πʳ i, [G i, C i] :=
  flatten_equiv C <| le_antisymm (Filter.comap_cofinite_le f) (Filter.map_le_iff_le_comap.mp hf)

@[simp]
lemma flatten_equiv'_apply (x) (i : ι) :
    flatten_equiv' C hf x i = x (f i) ⟨i, rfl⟩ :=
  rfl

@[simp]
lemma flatten_equiv'_symm_apply (x) (i : ι₂) (j : f ⁻¹' {i}) :
    (flatten_equiv' C hf).symm x i j = x j.1 :=
  rfl

end flatten

section principal
/-!

## Principal filters

A restricted product over a principal filter is isomorphic to a product.

-/

variable {ι : Type*} (R : ι → Type*) (S : Set ι) [∀ i, Decidable (i ∈ S)] (A : (i : ι) → Set (R i))

open scoped Filter

section type

/-- The canonical isomorphism between `Πʳ i, [R i, A i]_[𝓟 S]` and
`(Π i ∈ S, R i) × (Π i ∉ S, A i)`
-/
def principalEquivProd : Πʳ i, [R i, A i]_[𝓟 S] ≃
    (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  toFun x := (fun i ↦ ⟨x i, x.2 i.2⟩, fun i ↦ x i)
  invFun y := ⟨fun i ↦ if hi : i ∈ S then y.1 ⟨i, hi⟩ else y.2 ⟨i, hi⟩,
  by aesop⟩
  left_inv x := by ext; simp
  right_inv x := by
    ext i
    · simp
    · simp [dif_neg i.2]

end type

variable {T : ι → Type*} [Π i, SetLike (T i) (R i)] {A : Π i, T i}

section monoid

-- TODO move to FLT/Mathlib
/-- Monoid equivalence version of `principalEquivProd`. -/
@[to_additive /-- Additive monoid equivalence of principalEquivProd. -/]
def principalMulEquivProd [Π i, Monoid (R i)] [∀ i, SubmonoidClass (T i) (R i)] :
    Πʳ i, [R i, A i]_[𝓟 S] ≃* (Π i : S, A i) × (Π i : (Sᶜ : Set ι), R i) where
  __ := principalEquivProd R S _
  map_mul' _ _ := rfl

end monoid

variable {ι : Type*} (R : ι → Type*) {ℱ : Filter ι} (A : Type*) [CommRing A]

open scoped RestrictedProduct

open Filter

section module

/-- Module equivalence version of `principalEquivProd`. -/
noncomputable def principalLinearEquivProd [Π i, AddCommGroup (R i)]
    [∀ i, Module A (R i)] {C : ∀ i, Submodule A (R i)}
    (S : Set ι) [∀ i, Decidable (i ∈ S)] :
    (Πʳ i, [R i, C i]_[𝓟 S]) ≃ₗ[A] ((Π i : S, C i) ×
      (Π i : (Sᶜ : Set ι), R i)) where
  __ := principalAddEquivSum R S (A := C)
  map_smul' _ _ := rfl

end module

end principal

end RestrictedProduct
