/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.PElementaryConstruction
public import FLT.Slop.BrauerInduction.Background.ClassFun.Zlocal

/-!
# Bernstein's prime-local ideal

This file defines the prime-local Bernstein span used in Steps 3--5 of the
proof.

For a fixed prime `p`, the basic generators are induced class functions

`Ind_E^G q`

where `E ≤ G` is `p`-elementary and `q ∈ Q(E)`.  We package these generators
as `JGen`, define their integral span `J p`, and define the localized span
`Jloc p` over the `p`-local integers `Zlocal p`.

The file also proves the structural properties needed later:

* generators restrict to global elements of the character system `Q`;
* `J p` absorbs multiplication by global `Q`-functions;
* `J p ≤ Jloc p`;
* `Jloc p` is closed under multiplication;
* Bernstein's Step 8 functions `fA` belong to `J p`, hence also to `Jloc p`.

The later file `PRegularSum` uses these results to construct the local
function supported on a chosen `p`-regular conjugacy class.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

namespace BrauerInduction

section IntegralIdeal

/-!
## The integral span `J_p`

This section defines the common generator set `JGen` and the integral span
`J p`.  It proves the elementary closure lemmas for `J`, the projection-formula
ideal property `mul_mem_J`, and the Step 8 membership result `f_a_mem_J`.
-/

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Fintype G]
variable (p : ℕ)

/-- The common generator set for both `J_p` and `Jloc_p`. -/
def JGen : Set (ClassFun k G) :=
  { f : ClassFun k G |
      ∃ (E : Subgroup G) (_ : IsPElementary p E)
        (q : ClassFun k E),
        q ∈ ClassFun.qSys k G E ∧
        f = ClassFun.ind (k := k) E q }

/-- Bernstein's integral prime-local span `J_p`. -/
def J : Submodule ℤ (ClassFun k G) := Submodule.span ℤ (JGen p)

/-- A generator of `J_p`: induction from a `p`-elementary subgroup. -/
lemma ind_mem_J
    (E : Subgroup G) (hE : IsPElementary p E)
    {q : ClassFun k E}
    (hq : q ∈ ClassFun.qSys k G E) :
    ClassFun.ind (k := k) E q ∈ J p := by
  exact Submodule.subset_span ⟨E, hE, q, hq, rfl⟩

/-- The zero function belongs to `J_p`. -/
lemma zero_mem_J :
    (0 : ClassFun k G) ∈ J p :=
  Submodule.zero_mem _

/-- `J_p` is closed under addition. -/
lemma add_mem_J
    {f g : ClassFun k G} (hf : f ∈ J p) (hg : g ∈ J p) :
    f + g ∈ J p :=
  Submodule.add_mem _ hf hg

/-- `J_p` is closed under integral scalar multiplication. -/
lemma zsmul_mem_J
    (n : ℤ) {f : ClassFun k G} (hf : f ∈ J p) :
    n • f ∈ J p :=
  Submodule.smul_mem _ n hf

/--
A generator restricts to a global element of the character system `Q`.
-/
lemma JGen_mem_Q_sys
    {y : ClassFun k G}
    (hy : y ∈ JGen p) :
    ClassFun.res (⊤ : Subgroup G) y
      ∈ ClassFun.qSys k G (⊤ : Subgroup G) := by
  rcases hy with ⟨E, hE, q, hq_Q, rfl⟩
  exact ClassFun.qSys.ind_mem (H := E) hq_Q

/-- The integral span `J_p` absorbs multiplication by global `Q`-functions. -/
lemma mul_mem_J [_hp : Fact p.Prime] [_hk : CharZero k]
    (f g : ClassFun k G)
    (hf : f ∈ J p)
    (hg : ClassFun.res (⊤ : Subgroup G) g ∈ ClassFun.qSys (k := k) (G := G) ⊤) :
    f * g ∈ J  p := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ J p) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨E, hE, q, ⟨hq_Lambda, hq_Z⟩, rfl⟩
    obtain ⟨hg_Lambda, hg_Z⟩ := hg
    rw [mul_comm, ClassFun.projection_formula]
    apply Submodule.subset_span (R := ℤ)
    use E, hE, (ClassFun.res E g * q)
    constructor
    · constructor
      · apply ClassFun.rLambda.mul_mem
        · exact ClassFun.rLambda.res_top_to_subgroup hg_Lambda
        · exact hq_Lambda
      · apply ClassFun.cZ.mul_mem
        · apply ClassFun.cZ.res
          intro x
          exact hg_Z ⟨x, Subgroup.mem_top x⟩
        · exact hq_Z
    · rfl
  · simp only [zero_mul, zero_mem]
  · intro x y _ _ hx_mem hy_mem
    rw [add_mul]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro n x _ hx_mem
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx_mem

/-- Bernstein Step 8: the induced function `fA` belongs to `J_p`. -/
lemma f_a_mem_J
    [Fact p.Prime] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    ClassFun.fA (k := k) p a ∈ J p := by
  unfold ClassFun.fA
  exact ind_mem_J p
    (eSubgroup p a)
    (E_isPElementary p ha)
    (ClassFun.phi_mem_Q (k := k) p a ha)

end IntegralIdeal

section LocalizedIdeal

/-!
## The localized span `Jloc_p`

This section extends the same generators from integral coefficients to
`p`-local coefficients. It proves `J_subset_Jloc`, the localized Step 8 result
`f_a_mem_Jloc`, and the multiplicative closure theorem `Jloc.mul_mem`.
-/

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [Fintype G]
variable (p : ℕ) [Fact p.Prime]

/-- The localized prime-local span `Jloc_p`. -/
noncomputable def Jloc : Submodule (Zlocal p) (ClassFun k G) :=
  Submodule.span (Zlocal p) (JGen p)

/-- A generator of `Jloc p`: induction from a `p`-elementary subgroup. -/
lemma ind_mem_Jloc
    (E : Subgroup G) (hE : IsPElementary p E) {q : ClassFun k E}
    (hq : q ∈ ClassFun.qSys k G E) :
    ClassFun.ind (k := k) E q ∈ Jloc p := by
  exact Submodule.subset_span ⟨E, hE, q, hq, rfl⟩

/-- The integral span `J_p` is contained in the localized span `Jloc_p`. -/
lemma J_subset_Jloc
    {f : ClassFun k G} (hf : f ∈ J p) :
    f ∈ Jloc p := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    exact Submodule.subset_span hx
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    have h_smul : n • x = (n : Zlocal p) • x := by
      exact Eq.symm (Int.cast_smul_eq_zsmul (Zlocal p) n x)
    rw [h_smul]
    exact Submodule.smul_mem _ (n : Zlocal p) hx

/-- Bernstein Step 8, localized form: `fA ∈ Jloc p`. -/
lemma f_a_mem_Jloc [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    ClassFun.fA (k := k) p a ∈ Jloc p := by
  unfold ClassFun.fA
  exact ind_mem_Jloc p
    (eSubgroup p a)
    (E_isPElementary p ha)
    (ClassFun.phi_mem_Q (k := k) p a ha)

/-- The localized span `Jloc_p` is closed under pointwise multiplication. -/
lemma Jloc.mul_mem [_hk : IsAlgClosed k]
    (x y : ClassFun k G) (hx : x ∈ Jloc p) (hy : y ∈ Jloc p) :
    x * y ∈ Jloc p := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro x_gen hx_gen
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro y_gen hy_gen
      have hx_J : x_gen ∈ J p := by
        apply Submodule.subset_span
        exact hx_gen
      have hx_J : x_gen ∈ J  p := by
        exact Submodule.subset_span hx_gen
      have hy_Q :
          ClassFun.res (⊤ : Subgroup G) y_gen
            ∈ ClassFun.qSys k G (⊤ : Subgroup G) := by
        exact JGen_mem_Q_sys  p hy_gen
      have hxy_J :
          x_gen * y_gen ∈ J  p := by
        exact mul_mem_J  p x_gen y_gen hx_J hy_Q
      exact J_subset_Jloc p hxy_J
    · rw [mul_zero]
      exact Submodule.zero_mem _
    · intro y1 y2 _ _ hy1 hy2
      rw [mul_add]
      exact Submodule.add_mem _ hy1 hy2
    · intro r y' _ hy'
      have h_comm : x_gen * (r • y') = r • (x_gen * y') := by
        ext g
        simp only [ClassFun.mul_apply, ClassFun.Zlocal.smul_apply]
        ring_nf
      rw [h_comm]
      exact Submodule.smul_mem _ r hy'
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x1 x2 _ _ hx1 hx2
    rw [add_mul]
    exact Submodule.add_mem _ hx1 hx2
  · intro r x' _ hx'
    have h_assoc : (r • x') * y = r • (x' * y) := by
      ext g
      simp only [ClassFun.mul_apply, ClassFun.Zlocal.smul_apply]
      ring
    rw [h_assoc]
    exact Submodule.smul_mem _ r hx'

end LocalizedIdeal
end BrauerInduction

end Slop
