import Mathlib.Topology.Algebra.RestrictedProduct

open Set Topology Filter

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))
variable {𝓕 𝓖 : Filter ι} {S T : Set ι}

variable {S : ι → Type*} -- subobject type
variable [Π i, SetLike (S i) (R i)]
variable {B : Π i, S i}

namespace RestrictedProduct

instance [Π i, AddMonoid (R i)] [∀ i, AddSubmonoidClass (S i) (R i)] :
    AddMonoid (Πʳ i, [R i, B i]_[𝓕]) :=
  haveI : ∀ i, SMulMemClass (S i) ℕ (R i) := fun _ ↦ AddSubmonoidClass.nsmulMemClass
  DFunLike.coe_injective.addMonoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[to_additive existing]
instance [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)] :
    Monoid (Πʳ i, [R i, B i]_[𝓕]) :=
  DFunLike.coe_injective.monoid _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

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

end RestrictedProduct
