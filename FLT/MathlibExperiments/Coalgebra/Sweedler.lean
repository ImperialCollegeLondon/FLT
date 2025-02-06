/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/

import Mathlib.RingTheory.Bialgebra.Basic

/-!

# "Sweedler notation"

Sweedler notation seems to be the practice of writing `comul x` (for `x` in a
coalgebra) as `∑ᵢ x₁ᵢ ⊗ x₂ᵢ` and then dropping the sum and instead writing
`x⁽¹⁾ ⊗ x⁽²⁾`. The axioms of a coalgebra/bialgebra/Hopf algebra can be
rewritten using Sweedler notation and look a little less cluttered this way.
Something which surprised me (KB): sometimes `ext` is not enough and one really
has to decompose elements in this way; so we take the time to write a small API for
this idea, although we do not attempt to remove the `∑` symbol. The finite
index set that `i` runs through is, somewhat arbitrarily, defined to be
a subset of `A ⊗ A` with `A` the coalgebra in question.

-/

open BigOperators TensorProduct

namespace Coalgebra

variable {R A : Type*} [CommSemiring R]
variable [AddCommMonoid A] [Module R A] [Coalgebra R A]

lemma exists_repr (x : A) :
    ∃ (I : Finset (A ⊗[R] A)) (x1 : A ⊗[R] A → A) (x2 : A ⊗[R] A → A),
    Coalgebra.comul x = ∑ i ∈ I, x1 i ⊗ₜ[R] x2 i := by
  classical
  have mem1 : comul x ∈ (⊤ : Submodule R (A ⊗[R] A)) := ⟨⟩
  rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem1
  obtain ⟨r, hr, (eq1 : ∑ i ∈ r.support, (_ • _) = _)⟩ := mem1
  choose a a' haa' using hr
  replace eq1 := calc _
    comul x = ∑ i ∈ r.support, r i • i := eq1.symm
    _ = ∑ i ∈ r.support.attach, (r i : R) • i.1 := Finset.sum_attach _ _ |>.symm
    _ = ∑ i ∈ r.support.attach, (r i • a i.2 ⊗ₜ[R] a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ congr(r i.1 • $(haa' i.2)).symm
    _ = ∑ i ∈ r.support.attach, ((r i • a i.2) ⊗ₜ[R] a' i.2) :=
        Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul' _ _ _
  refine ⟨r.support, fun i ↦ if h : i ∈ r.support then r i • a h else 0,
    fun i ↦ if h : i ∈ r.support then a' h else 0, eq1 ▸ ?_⟩
  conv_rhs => rw [← Finset.sum_attach]
  exact Finset.sum_congr rfl fun _ _ ↦ (by aesop)

/-- an arbitrarily chosen indexing set for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def ℐ (a : A) : Finset (A ⊗[R] A) := exists_repr a |>.choose

/-- an arbitrarily chosen first coordinate for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def Δ₁ (a : A) : A ⊗[R] A → A := exists_repr a |>.choose_spec.choose

/-- an arbitrarily chosen second coordinate for comul(a) = ∑ a₁ ⊗ a₂. -/
noncomputable def Δ₂ (a : A) : A ⊗[R] A → A :=
  exists_repr a |>.choose_spec.choose_spec.choose

lemma comul_repr (a : A) :
    Coalgebra.comul a = ∑ i ∈ ℐ a, Δ₁ a i ⊗ₜ[R] Δ₂ (R := R) a i :=
  exists_repr a |>.choose_spec.choose_spec.choose_spec

lemma sum_counit_tmul (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i ∈ s, x i ⊗ₜ[R] y i) :
    ∑ i ∈ s, counit (R := R) (x i) ⊗ₜ y i = 1 ⊗ₜ[R] a := by
  simpa [repr, map_sum] using congr($(rTensor_counit_comp_comul (R := R) (A := A)) a)

lemma sum_tmul_counit (a : A) {ι : Type*} (s : Finset ι) (x y : ι → A)
    (repr : comul a = ∑ i ∈ s, x i ⊗ₜ[R] y i) :
    ∑ i ∈ s, (x i) ⊗ₜ counit (R := R) (y i) = a ⊗ₜ[R] 1 := by
  simpa [repr, map_sum] using congr($(lTensor_counit_comp_comul (R := R) (A := A)) a)

end Coalgebra
