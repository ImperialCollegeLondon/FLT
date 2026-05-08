/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import FLT.Patching.Ultraproduct

/-!
# Vanishing filters of ideals in product rings

For an ideal `p` of `Πᵢ R i`, we define the *vanishing filter*
`vanishingFilter p` of `p`: the filter of subsets `s` such that the
characteristic idempotent of `s` lies in `p`. Prime ideals give rise to
ultrafilters via this construction.
-/

@[expose] public section

set_option autoImplicit false
variable (R₀ : Type*) [CommRing R₀]
variable {ι : Type*} {R M : ι → Type*} [∀ i, CommRing (R i)] [∀ i, AddCommGroup (M i)]
variable [∀ i, Algebra R₀ (R i)] [∀ i, Module (R i) (M i)]
variable (I : ∀ i, Ideal (R i)) (N : ∀ i, Submodule (R i) (M i)) (F : Filter ι)

open Filter

open scoped Classical in
/-- The vanishing filter of an ideal `p` of the product ring `Πᵢ Rᵢ` over an index
set `ι`: a set `s ⊆ ι` is in the vanishing filter if the element of `Πᵢ Rᵢ` which
is `0` on `s` and `1` outside `s` lies in `p`. -/
def vanishingFilter (p : Ideal (Π i, R i)) : Filter ι where
  sets := { s | (if · ∈ s then 0 else 1) ∈ p }
  univ_sets := by simpa [-zero_mem] using zero_mem p
  sets_of_superset {s t} hs hst := by
    change _ ∈ p
    convert p.smul_mem (fun i ↦ if i ∈ t then 0 else 1) hs with i
    simp [← ite_or, or_iff_right_of_imp (@hst _)]
  inter_sets {s t} hs ht := by
    change _ ∈ p
    convert add_mem ht (sub_mem hs (mul_mem (s := p) hs ht)) with i
    simp only [Set.mem_inter_iff, ite_and, Pi.add_apply,
      Pi.sub_apply, Pi.mul_apply, mul_ite, mul_zero, mul_one]
    split_ifs <;> simp

open scoped Classical in
@[simp]
lemma mem_vanishingFilter {p : Ideal (Π i, R i)} {s} :
    s ∈ vanishingFilter p ↔ (if · ∈ s then 0 else 1) ∈ p :=
  Iff.rfl

/-- The vanishing ultrafilter of a prime ideal `p` of the product ring.
See `vanishingFilter` for definition of a vanishing filter of an ideal of `Πᵢ Rᵢ`;
if `p` is prime then this is an ultrafilter. -/
def vanishingUltrafilter (p : Ideal (Π i, R i)) [p.IsPrime] : Ultrafilter ι :=
  .ofComplNotMemIff (vanishingFilter p) <| by
    classical
    intro s
    simp only [vanishingFilter, Filter.mem_mk, Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro H
      refine (Ideal.IsPrime.mem_or_mem_of_mul_eq_zero ‹p.IsPrime› ?_).resolve_left H
      ext i
      simp only [ite_not, Pi.mul_apply, mul_ite, mul_zero, mul_one,
        Pi.zero_apply, ite_eq_left_iff, ite_eq_right_iff]
      exact fun a b ↦ (a b).elim
    · intro h₁ h₂
      refine ‹p.IsPrime›.ne_top (p.eq_top_iff_one.mpr ?_)
      convert p.add_mem h₁ h₂
      ext
      simp only [Pi.one_apply, ite_not, Pi.add_apply]
      split_ifs <;> simp

open scoped Classical in
@[simp]
lemma mem_vanishingUltrafilter {p : Ideal (Π i, R i)} [p.IsPrime] {s} :
    s ∈ vanishingUltrafilter p ↔ (fun i ↦ if i ∈ s then 0 else 1) ∈ p :=
  Iff.rfl

lemma eventually_vanishingFilter_not_isUnit
    (p : Ideal (Π i, R i)) {x} (hx : x ∈ p) :
    ∀ᶠ i in vanishingFilter p, ¬ IsUnit (x i) := by
  classical
  have : (fun i ↦ if IsUnit (x i) then 1 else 0) ∈ p := by
    convert p.mul_mem_left (fun i ↦ if h : IsUnit (x i) then (h.unit⁻¹ : _) else 0) hx with i
    aesop
  simp only [Filter.Eventually, mem_vanishingFilter, Set.mem_setOf_eq, Classical.ite_not]
  convert this

lemma vanishingFilter_le {p : Ideal (Π i, R i)} {F : Filter ι} :
    vanishingFilter p ≤ F ↔ eventuallyProd ⊥ F ≤ p := by
  constructor
  · rintro H v hv
    convert Ideal.mul_mem_left _ v (H hv)
    aesop
  · intro H s hs
    apply H
    filter_upwards [hs]
    aesop

lemma vanishingFilter_eventuallyProd (F : Filter ι) (hI : ∀ i, I i ≠ ⊤) :
    vanishingFilter (eventuallyProd I F) = F := by
  ext; simp[apply_ite, ← Ideal.eq_top_iff_one, hI]

open OrderDual in
lemma vanishingFilter_gc :
    GaloisConnection (vanishingFilter ∘ ofDual)
      (toDual ∘ eventuallyProd (⊥ : ∀ i, Ideal (R i))) :=
  fun _ _ ↦ vanishingFilter_le

open OrderDual in
/-- The Galois insertion between filters on `ι` and ideals of `Π i, R i` (for nontrivial `R i`)
formed by `vanishingFilter` and `eventuallyProd ⊥`. -/
def vanishingFilterGI [∀ i, Nontrivial (R i)] :
    GaloisInsertion (vanishingFilter ∘ ofDual)
      (toDual ∘ eventuallyProd (⊥ : ∀ i, Ideal (R i))) where
  gc := vanishingFilter_gc
  le_l_u x := (by simp [vanishingFilter_eventuallyProd])
  choice := _
  choice_eq _ _ := rfl

lemma vanishingFilter_antimono {p q : Ideal (Π i, R i)} (h : p ≤ q) :
    vanishingFilter q ≤ vanishingFilter p :=
  vanishingFilter_gc.monotone_l h

lemma eventuallyProd_vanishingFilter_le (p : Ideal (Π i, R i)) :
    eventuallyProd ⊥ (vanishingFilter p) ≤ p :=
  vanishingFilter_gc.le_u_l _
