import Mathlib.Topology.Algebra.RestrictedProduct

-- All this is marthlib PR #24200
open Set Topology Filter

namespace RestrictedProduct

@[ext]
lemma ext {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i)) {𝓕 : Filter ι}
    {x y :  Πʳ i, [R i, A i]_[𝓕]} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext <| funext h

section instances

variable {ι : Type*}
variable (R : ι → Type*)
variable {𝓕 : Filter ι}
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

instance [Π i, AddMonoid (R i)] [∀ i, AddSubmonoidClass (S i) (R i)] :
    AddMonoid (Πʳ i, [R i, B i]_[𝓕]) :=
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Monoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.monoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end instances

section eval

variable {ι : Type*}
variable (R : ι → Type*)
variable {𝓕 : Filter ι}
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

def eval (j : ι) (x : Πʳ i, [R i, B i]_[𝓕]) : R j := x j

@[to_additive]
def evalMonoidHom (j : ι) [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →* R j where
      toFun := eval R j
      map_one' := rfl
      map_mul' _ _ := rfl

def evalRingHom (j : ι) [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →+* R j where
      __ := evalMonoidHom R j
      __ := evalAddMonoidHom R j

end eval

section map

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : 𝓕₂.Tendsto f 𝓕₁)

section set

variable (φ : ∀ j, R₁ (f j) → R₂ j) (hφ : ∀ᶠ j in 𝓕₂, φ j '' B₁ (f j) ⊆ B₂ j)

def map (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, B₂ j]_[𝓕₂] := ⟨fun j ↦ φ j (x (f j)), by
  apply mem_of_superset (𝓕₂.inter_mem hφ (hf x.2))
  simp only [image_subset_iff, SetLike.mem_coe, preimage_setOf_eq]
  rintro _ ⟨h1, h2⟩
  exact h1 h2
  ⟩
end set

section monoid

variable [Π i, Monoid (R₁ i)] [Π i, Monoid (R₂ i)] [∀ i, SubmonoidClass (S₁ i) (R₁ i)]
    [∀ i, SubmonoidClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, (φ j) '' (B₁ (f j)) ≤ B₂ j)

@[to_additive]
def mapMonoidHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  toFun := map R₁ R₂ f hf (fun j r ↦ φ j r) hφ
  map_one' := by
    ext i
    exact map_one (φ i)
  map_mul' x y := by
    ext i
    exact map_mul (φ i) _ _

end monoid

section ring

variable [Π i, Ring (R₁ i)] [Π i, Ring (R₂ i)] [∀ i, SubringClass (S₁ i) (R₁ i)]
    [∀ i, SubringClass (S₂ i) (R₂ i)] (φ : ∀ j, R₁ (f j) →+* R₂ j)
    (hφ : ∀ᶠ j in 𝓕₂, (φ j) '' (B₁ (f j)) ≤ B₂ j)

def mapRingHom : Πʳ i, [R₁ i, B₁ i]_[𝓕₁] →+* Πʳ j, [R₂ j, B₂ j]_[𝓕₂] where
  __ := mapMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ
  __ := mapAddMonoidHom R₁ R₂ f hf (fun j ↦ φ j) hφ

@[simp]
lemma mapRingHom_apply (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) (j : ι₂) :
    x.mapRingHom R₁ R₂ f hf φ hφ j = φ j (x (f j)) :=
  rfl

end ring

end map

end RestrictedProduct
