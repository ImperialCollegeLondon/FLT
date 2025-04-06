import Mathlib.Topology.Algebra.RestrictedProduct

open Set Topology Filter

namespace RestrictedProduct

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

section projection

variable {ι : Type*}
variable (R : ι → Type*)
variable {𝓕 : Filter ι}
variable {S : ι → Type*}
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

def projection (j : ι) (x : Πʳ i, [R i, B i]_[𝓕]) : R j := x j

@[to_additive]
def projectionMonoidHom (j : ι) [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →* R j where
      toFun := projection R j
      map_one' := rfl
      map_mul' _ _ := rfl

def projectionRingHom (j : ι) [Π i, Ring (R i)] [∀ i, SubringClass (S i) (R i)] :
    (Πʳ i, [R i, B i]_[𝓕]) →+* R j where
      __ := projectionMonoidHom R j
      __ := projectionAddMonoidHom R j

end projection

section map

variable {ι₁ ι₂ : Type*}
variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)
variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}
variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}
variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]
variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}
variable (f : ι₂ → ι₁) (hf : 𝓕₂.Tendsto f 𝓕₁)

section set

variable (φ : ∀ j, R₁ (f j) → R₂ j) (hφ : ∀ᶠ j in 𝓕₂, φ j '' B₁ (f j) ≤ B₂ j)

def map (x : Πʳ i, [R₁ i, B₁ i]_[𝓕₁]) : Πʳ j, [R₂ j, B₂ j]_[𝓕₂] := ⟨fun j ↦ φ j (x (f j)), by
  -- I know x(i)∈B₁(i) for an 𝓕₁-good set of i by definition of restricted product
  -- the preimage of an 𝓕₁-good set of i is an 𝓕₂-good set of j by hf
  -- So then x(f(j))∈B₁(f(j)) for an 𝓕₂-good set of j and I didn't use hφ
  have := x.2
  apply hf at this
  convert this
  simp
  have foo (S : Set ι₁) (hs : S ∈ 𝓕₁) : f ⁻¹' S ∈ 𝓕₂ := by
    exact hf hs
  sorry
  ⟩
end set

end map

/-
RestrictedProduct.projectionRingHom.{u_1, u_2, u_3} {ι : Type u_1} (R : ι → Type u_2) {𝓕 : Filter ι} {S : ι → Type u_3}
  [(i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i} (j : ι) [(i : ι) → Ring (R i)]
  [∀ (i : ι), SubringClass (S i) (R i)] : Πʳ (i : ι), [R i, ↑(B i)]_[𝓕] →+* R j
-/
--def map
end RestrictedProduct
