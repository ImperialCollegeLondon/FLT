/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.Algebra.Algebra.Equiv

/-!
# Algebra isomorphisms and the image of the base ring

Material for `Mathlib.Algebra.Algebra.Equiv`.
-/

@[expose] public section

/-- An algebra isomorphism identifies the images of the base ring: `e x` lies in the image of `F`
if and only if `x` does. -/
theorem AlgEquiv.apply_mem_range_algebraMap_iff {F A B : Type*} [CommSemiring F] [Semiring A]
    [Semiring B] [Algebra F A] [Algebra F B] (e : A ≃ₐ[F] B) {x : A} :
    e x ∈ Set.range (algebraMap F B) ↔ x ∈ Set.range (algebraMap F A) :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨c, e.injective (by rw [e.commutes, hc])⟩,
    fun ⟨c, hc⟩ ↦ ⟨c, by rw [← hc, e.commutes]⟩⟩

end
