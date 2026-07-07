/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.PElementaryConstruction
public import FLT.Slop.BrauerInduction.LocalIdeal
public import FLT.Slop.BrauerInduction.Background.ClassFun.Zlocal
public import FLT.Slop.BrauerInduction.Background.Group.PRegularClass

@[expose] public section

universe u v

/-!
# Bernstein Steps 5–7: the p-regular class sum

This file constructs the local class function used to prove that `1` belongs
to the localized Bernstein span `Jloc p`.

For each `p`-regular element `a`, the function `f_a` constructed in
`PElementaryConstruction` is normalized to a function `e_a` satisfying
`e_a(a) = 1`.  Summing these functions over representatives of `p`-regular
conjugacy classes gives the class function `E_p`.

The main result of the first part is the local congruence

`E_p(g) = 1 + p z`

for some `z : Zlocal p`, formalized as `E_p_congr`.

The second part uses the polynomial with roots `E_p(g)` to prove the final
local statement

`one_mem_Jloc : (1 : ClassFun k G) ∈ Jloc p`.
-/


namespace BrauerInduction

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable (p : ℕ) [Fact p.Prime]

section PRegularClassSum

/-!
## The normalized `p`-regular class sum

This section defines the normalized functions `e_a`, sums them over
`p`-regular conjugacy classes to obtain `E_p`, and proves the congruence
`E_p(g) = 1 + pz` in the `p`-local integers.
-/


/--
The `p`-local unit represented by the value `f_a(a)`.

Bernstein's function `f_a` takes a `p`-local unit value at the defining
`p`-regular element `a`; this definition chooses that unit so that `e_a`
can normalize `f_a`.
-/
noncomputable def e_a_unit
    [Fintype G] [CharZero k]
    {a : G} (ha : IsPRegular p a) : (Zlocal p)ˣ :=
  Classical.choose
    (ClassFun.f_a_apply_a_isUnit_Zlocal (k := k) p (a := a) ha)

/--
The chosen unit `e_a_unit` maps to the value `f_a(a)` under the canonical map
`Zlocal p → k`.
-/
lemma e_a_unit_spec
    [Fintype G] [CharZero k]
    {a : G} (ha : IsPRegular p a) :
    Zlocal.toK (k := k) p (e_a_unit (k := k) p ha : Zlocal p)
      =
    ClassFun.f_a (k := k) p a a :=
  Classical.choose_spec
    (ClassFun.f_a_apply_a_isUnit_Zlocal (k := k) p  ha)

/--
The normalized Bernstein function attached to a `p`-regular element `a`.

It is obtained from `f_a` by multiplying by the inverse of the `p`-local unit
`f_a(a)`, so that the resulting class function takes value `1` at `a`.
-/
noncomputable def e_a
    [Fintype G] [CharZero k]
    (a : G) (ha : IsPRegular p a) : ClassFun k G :=
  ((↑((e_a_unit (k := k) p ha)⁻¹) : Zlocal p) •
    ClassFun.f_a (k := k) p a)

/--
The normalized function `e_a` belongs to the localized Bernstein span `Jloc p`.
-/
lemma e_a_mem_Jloc
    {G : Type u} [Group G] [Fintype G] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    e_a (k := k) p a ha ∈ Jloc p := by
  unfold e_a
  apply Submodule.smul_mem
  exact f_a_mem_Jloc p a ha

/--
The normalized function `e_a` takes value `1` at its defining `p`-regular element `a`.
-/
lemma e_a_apply_self
    [Fintype G] [CharZero k]
    (a : G) (ha : IsPRegular p a) :
    (e_a (k := k) p a ha) a = 1 := by
  unfold e_a
  rw [ClassFun.Zlocal.smul_apply]
  rw [← e_a_unit_spec (k := k) p ha]
  rw [← map_mul]
  rw [Units.inv_mul]
  exact map_one _

/--
The normalized function `e_a` vanishes outside the `p`-section whose
`p`-regular part is conjugate to `a`.
-/
lemma e_a_apply_not_isConj
    [Fintype G] [CharZero k] {a x : G}
    (ha : IsPRegular p a) (hx : ¬ IsConj (Group.pRegular p x) a) :
    (e_a (k := k) p a ha) x = (0 : k) := by
  simp only [e_a, ClassFun.smul_apply, Units.isUnit, IsUnit.smul_eq_zero]
  exact ClassFun.f_a_apply_eq_zero_of_not_isConj p a x hx

/--
The Bernstein class sum `E_p`.

This is the sum of the normalized functions `e_a`, with one representative
chosen for each conjugacy class of `p`-regular elements.
-/
noncomputable def E_p
    [Fintype G] [CharZero k] : ClassFun k G :=
  ∑ C : PRegularClass p G, e_a p
    C.repr (PRegularClass.repr_isPRegular C)


open Classical in
/--
On `p`-regular elements, the summand indexed by a `p`-regular conjugacy class
is a Kronecker delta: it is `1` on that class and `0` on all other
`p`-regular classes.
-/
lemma e_a_apply_pRegular_delta
    [Fintype G] [CharZero k]
    (C : PRegularClass p G)
    (g : G) (hg : IsPRegular p g) :
    (e_a (k := k) p C.repr (PRegularClass.repr_isPRegular C)) g
      =
    if IsConj C.repr g then 1 else 0 := by
  by_cases h : IsConj C.repr g
  · simp only [h, if_pos]
    calc
      (e_a (k := k) p C.repr
          (PRegularClass.repr_isPRegular C)) g
          =
        (e_a (k := k) p C.repr
          (PRegularClass.repr_isPRegular C)) C.repr := by
            exact
              (e_a (k := k) p C.repr
                (PRegularClass.repr_isPRegular C)).map_conj
                  g C.repr h.symm
      _ = 1 := by
        exact e_a_apply_self (k := k) p C.repr (PRegularClass.repr_isPRegular C)
  · simp only [h, ↓reduceIte]
    apply e_a_apply_not_isConj (k := k) p
    rw [Group.pRegular_eq_self_of_isPRegular
      (hf := isOfFinOrder_of_finite g ) (hr := hg)]
    exact Not.imp h fun a ↦ id (IsConj.symm a)

/--
The class sum `E_p` takes value `1` on every `p`-regular element.
-/
lemma E_p_apply_of_pRegular
  [Fintype G] [CharZero k]
  (g : G) (hg : IsPRegular p g) :
  E_p (k := k) p g = 1 := by
  rcases PRegularClass.unique_of_isPRegular p g hg with ⟨C0, hC0, huniq⟩
  simp only [E_p, ClassFun.sum_apply]
  classical
  have h_sum :
      ∑ i : PRegularClass p G,
        (e_a (k := k) p i.repr (PRegularClass.repr_isPRegular i)) g =
      ∑ i : PRegularClass p G, if IsConj i.repr g then (1 : k) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    exact e_a_apply_pRegular_delta p i g hg
  rw[h_sum]
  rw [Finset.sum_eq_single C0 (M:= k)]
  · rw[if_pos hC0]
  · intro i _ hi_neq
    have h_not_conj : ¬ IsConj i.repr g := by
      intro h_conj
      exact hi_neq (huniq i h_conj)
    rw [if_neg h_not_conj]
  · intro h_not_mem
    exact (h_not_mem (Finset.mem_univ C0)).elim

open PElementary Subgroup in
/--
The normalized function `e_a` is congruent to `1` modulo `p` on elements of
the form `a * u`, where `u` is `p`-singular and commutes with `a`.

This is the local fixed-point congruence from Bernstein's Step 8, after
normalizing by the unit value `f_a(a)`.
-/
lemma e_a_congr_pSingular
    [CharZero k] [Fintype G]
    (p : ℕ) [Fact p.Prime]
    {a : G} (ha : IsPRegular p a)
    (s : G) (hs : IsPSingular p s) (h_comm : Commute a s) :
    ∃ z : Zlocal p, e_a (k := k) p a ha (a * s)
              = 1 + (Zlocal.toK p z) * (p : k) := by
  -- Use the same normalizing unit as the definition of `e_a`.
  let faa : (Zlocal p)ˣ := e_a_unit (k := k) (p := p) ha
  have hu0 :
      Zlocal.toK (k := k) p (faa : Zlocal p) =
        ClassFun.f_a (k := k) p a a := by
    dsimp [faa]
    exact e_a_unit_spec p ha
  have hf_fix := ClassFun.f_a_apply_mul_pSingular_eq_Nfix
      (k := k) p ha s hs h_comm
  let C : Subgroup G := centralizer ({a} : Set G)
  let H : Subgroup C := (P_in_Z p a : Subgroup C)
  let uC : C := ⟨s, by
    simpa [C, Subgroup.mem_centralizer_iff] using h_comm.eq⟩
  have huC : IsPSingular p (uC : C) := by
    dsimp [IsPSingular] at hs ⊢
    obtain ⟨n, hn⟩ := hs
    use n
    have h_ord : orderOf uC = orderOf s := (Subgroup.orderOf_coe uC).symm
    rw [h_ord]
    exact hn
  have hmodEq :
      Nat.card { c : C ⧸ H // uC • c = c } ≡
        Nat.card (C ⧸ H) [MOD p] := by
    exact card_fixedPoints_pSingular_modEq H (uC : C) huC
  have hdvd :
      (p : ℤ) ∣
        (Nat.card (C ⧸ H) : ℤ) -
          (Nat.card { c : C ⧸ H // uC • c = c } : ℤ) := by
    apply Int.ModEq.dvd
    exact Int.natCast_modEq_iff.mpr hmodEq
  -- `t` measures the difference between the quotient cardinality and the
  -- fixed-point cardinality.
  obtain ⟨t, ht⟩ := hdvd
  let z : Zlocal p := -↑(faa⁻¹) * (t : Zlocal p)
  use z
  unfold e_a
  rw [ClassFun.Zlocal.smul_apply, hf_fix]
  have h_card_rel :
      (Nat.card { c : C ⧸ H // uC • c = c } : k) =
        (Nat.card (C ⧸ H) : k) - (t : k) * (p : k) := by
    have ht_int :
        (Nat.card { c : C ⧸ H // uC • c = c } : ℤ) =
          (Nat.card (C ⧸ H) : ℤ) - (p : ℤ) * t := by
      omega
    have h_cast := congrArg (fun x : ℤ => (x : k)) ht_int
    push_cast at h_cast
    rw [h_cast]
    ring
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (P_of_Z p a) := Fintype.ofFinite (P_of_Z p a)
  have h_u0_val :
      Zlocal.toK (k := k) p (faa : Zlocal p) =
        (Nat.card (C ⧸ H) : k) := by
    rw [hu0, ClassFun.f_a_apply_a_eq_bernsteinIndex (k := k) p ha]
    unfold ClassFun.bernsteinIndex
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
    simp only [Nat.card_eq_fintype_card, Nat.cast_inj]
    have h_H_card : Fintype.card (P_of_Z p a) = Fintype.card H := by
      symm
      apply Fintype.card_congr
      exact (Subgroup.equivMapOfInjective _ _ Subtype.coe_injective).toEquiv
    rw [h_H_card]
    rw [Nat.mul_div_cancel]
    exact Fintype.card_pos
  rw [h_card_rel, ← h_u0_val]
  simp only [z, map_units_inv, map_neg, map_mul, neg_mul]
  rw [mul_sub]
  have h_inv_mul :
      ((Zlocal.toK (k := k) p) ↑faa)⁻¹ *
          (Zlocal.toK (k := k) p) ↑faa = 1 := by
    rw [← map_units_inv, ← map_mul, Units.inv_mul, map_one]
  rw [h_inv_mul]
  rw [map_intCast (Zlocal.toK (k := k) p)]
  ring

/--
The value of `e_a` at an arbitrary element `g` is congruent modulo `p` to
its value at the `p`-regular part of `g`.
-/
lemma e_a_congr_pRegularPart
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime]
    (a : G) (ha : IsPRegular p a) (g : G) :
    let r := Group.pRegular p g
    ∃ z : Zlocal p,
      e_a (k := k) p a ha g =
      e_a p a ha r + (Zlocal.toK p z) * (p : k) := by
  intro r
  let s := Group.pSingular p g
  let hfg := isOfFinOrder_of_finite g
  have h_decomp : g = r * s := by exact Eq.symm (Group.pDecomp' p hfg)
  have hs : IsPSingular p s := Group.isPSingular_pSingular p g
  have h_comm : Commute r s := Group.pRegular_pSingular_commute p rfl
  by_cases h_conj : IsConj a r
  · obtain ⟨x, hx⟩ := isConj_iff.mp h_conj
    let s' := x⁻¹ * s * x
    have hs' : IsPSingular p s' := by
      dsimp [s']
      exact IsPSingular.conj' p hs x
    have hu'_comm : Commute a s' := by
      have ha_eq : a = x⁻¹ * r * x := by
        calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
             _ = x⁻¹ * r * x := by rw [hx]
      rw [ha_eq]
      dsimp [s']
      calc (x⁻¹ * r * x) * (x⁻¹ * s * x)
        _ = x⁻¹ * (r * s) * x := by group
        _ = x⁻¹ * (s * r) * x := by rw [h_comm.eq]
        _ = (x⁻¹ * s * x) * (x⁻¹ * r * x) := by group
    obtain ⟨z_local, hz_local⟩ := e_a_congr_pSingular (k:=k) p ha s' hs' hu'_comm
    use z_local
    have h_conj_g : IsConj g (a * s') := by
      rw [isConj_iff]
      use x⁻¹
      simp only [inv_inv]
      rw [h_decomp, mul_assoc]
      group
      rw [← hx]
      dsimp [s']
      group
    have h_conj_s : IsConj r a := by
      rw[isConj_iff]
      use x⁻¹
      simp only [inv_inv]
      simp [← hx, mul_assoc]
    have h_eval_g :
        e_a (k := k) p a ha g =
          e_a p a ha (a * s') :=
      ClassFun.apply_eq_apply_of_isConj h_conj_g
    have h_eval_s :
        e_a (k := k) p a ha r =
          e_a p a ha a :=
      ClassFun.apply_eq_apply_of_isConj h_conj_s
    rw [h_eval_g, h_eval_s]
    rw [hz_local]
    rw [e_a_apply_self]
  · use (0 : Zlocal p)
    rw [e_a_apply_not_isConj p ha]
    · simp only [map_zero, zero_mul, add_zero]
      rw [e_a_apply_not_isConj p ha]
      intro h_contra
      apply h_conj
      symm
      have h_s: IsPRegular p r := Group.isPRegular_pRegular p hfg
      have h_idem : Group.pRegular p r = r :=
        Group.pRegular_eq_self_of_isPRegular p (isOfFinOrder_of_finite r) h_s
      rw [h_idem] at h_contra
      exact h_contra
    · dsimp [r] at h_conj
      exact Not.imp h_conj fun b ↦ id (IsConj.symm b)

/--
The class sum `E_p` is congruent to `1` modulo `p` at every group element.

Equivalently, for every `g : G`, there is some `Z : Zlocal p` such that
`E_p(g) = 1 + toK(Z) * p`.
-/
lemma E_p_congr
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] (g : G) :
    ∃ Z : Zlocal p,
      E_p (k := k) p g =
        1 + (Zlocal.toK p Z) * (p : k) := by
  let s := Group.pRegular p g
  have hfg : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hs_reg : IsPRegular p s := by
    dsimp [s]
    exact Group.isPRegular_pRegular p hfg
  let z_func (C : PRegularClass p G) : Zlocal p :=
    Classical.choose
      (e_a_congr_pRegularPart (k := k) p C.repr C.repr_isPRegular g)
  have hz_func : ∀ C : PRegularClass p G,
      e_a (k := k) p C.repr C.repr_isPRegular g =
        e_a p C.repr C.repr_isPRegular s
          + (Zlocal.toK p (z_func C)) * (p : k) := by
    intro C
    simpa [s, z_func] using
      Classical.choose_spec
        (e_a_congr_pRegularPart p C.repr C.repr_isPRegular g)
  let Z_total : Zlocal p := ∑ C : PRegularClass p G, z_func C
  refine ⟨Z_total, ?_⟩
  have h_error_terms :
      ∑ C : PRegularClass p G,
          (Zlocal.toK (k := k) p (z_func C)) * (p : k)
        =
      (Zlocal.toK p Z_total) * (p : k) := by
    dsimp [Z_total]
    rw [← Finset.sum_mul]
    congr 1
    exact (map_sum (Zlocal.toK p)
      (fun C : PRegularClass p G => z_func C) Finset.univ).symm
  have h_main :
      ∑ C : PRegularClass p G,
        e_a p C.repr C.repr_isPRegular s
      =
      (1 : k) := by
    have hEp :=
      E_p_apply_of_pRegular (k := k) p s hs_reg
    simpa [E_p, ClassFun.sum_apply, s] using hEp
  calc
    E_p (k := k) p g
        =
      (∑ C : PRegularClass p G,
        e_a (k := k) p C.repr C.repr_isPRegular) g := by
        rfl
    _ =
      ∑ C : PRegularClass p G,
        e_a (k := k) p C.repr C.repr_isPRegular g := by
        rw [ClassFun.sum_apply]
    _ =
      ∑ C : PRegularClass p G,
        (e_a (k := k) p C.repr C.repr_isPRegular s
          + (Zlocal.toK p (z_func C)) * (p : k)) := by
        apply Finset.sum_congr rfl
        intro C _
        exact hz_func C
    _ =
      (∑ C : PRegularClass p G,
        e_a (k := k) p C.repr C.repr_isPRegular s)
        +
      ∑ C : PRegularClass p G,
        (Zlocal.toK p (z_func C)) * (p : k) := by
        rw [Finset.sum_add_distrib]
    _ =
      1 + (Zlocal.toK (k := k) p Z_total) * (p : k) := by
        rw [h_error_terms, h_main]

/--
A `p`-local lift of the value of `E_p` at each group element.

The congruence `E_p(g) = 1 + pz` allows us to choose a value in `Zlocal p`
whose image in `k` is exactly `E_p(g)`.
-/
noncomputable def E_p_val
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] : G → Zlocal p :=
  fun g => 1 + (Classical.choose (E_p_congr (k:=k) p g)) * (p : Zlocal p)

/--
The value of `E_p` is the image of its chosen `p`-local lift `E_p_val`.
-/
lemma E_p_apply_eq_toK_E_p_val
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] (g : G) :
    E_p (k:=k) p g = Zlocal.toK p (E_p_val (k:=k) p g) := by
  unfold E_p_val
  simp only [map_add, map_one, map_mul, map_natCast]
  have h_congr := Classical.choose_spec (E_p_congr (k:=k) p g)
  exact h_congr

/--
The class sum `E_p` belongs to the localized Bernstein span `Jloc p`.
-/
lemma E_p_mem_Jloc
    {G : Type u} [Group G] [Fintype G] [CharZero k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] :
    E_p (G:= G) (k := k) p ∈ Jloc p := by
  dsimp [E_p]
  refine Submodule.sum_mem (Jloc p) ?_
  intro C hC
  exact e_a_mem_Jloc p (a := C.repr) (ha := C.repr_isPRegular)

end PRegularClassSum

section PolynomialArgument

/-!
## The polynomial argument

This section applies Bernstein's polynomial trick to `E_p`.  Since all values
of `E_p` are congruent to `1` modulo `p`, the constant term of the polynomial
with roots `E_p(g)` is a unit in `Zlocal p`.  Evaluating this polynomial at
`E_p` then expresses `1` as a `Zlocal p`-linear combination of positive powers
of `E_p`, hence as an element of `Jloc p`.
-/

open Polynomial

/--
The polynomial with roots the `p`-local values `E_p_val g`.

This is Bernstein's polynomial used to express `1` as a `Zlocal p`-linear
combination of positive powers of `E_p`.
-/
noncomputable def E_p_poly
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] : Polynomial (Zlocal p) :=
  ∏ g : G, (X - C (E_p_val (k:=k) p g))

/--
The polynomial `E_p_poly` vanishes at each of the values `E_p_val g`.
-/
lemma E_p_poly_eval_zero
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] (g : G) :
    (E_p_poly (G := G) (k:=k) p).eval (E_p_val (k:=k) p g) = 0 := by
  unfold E_p_poly
  rw [eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  simp only [eval_sub, eval_X, eval_C, sub_self]

/--
Each value `E_p_val g` is a unit in `Zlocal p`.

This follows from the congruence shape `E_p_val g = 1 + pz`.
-/
lemma E_p_val_isUnit
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] (g : G) :
    IsUnit (E_p_val (k:=k) p g) := by
  unfold E_p_val
  have h_comm : 1 + (Classical.choose (E_p_congr (k:=k) p g)) * (p : Zlocal p) =
                1 + (p : Zlocal p) * (Classical.choose (E_p_congr (k:=k) p g)) := by
    rw [mul_comm (Classical.choose _) (p : Zlocal p)]
  rw [h_comm]
  exact Zlocal.isUnit_one_add_p_mul _

/--
The constant coefficient of `E_p_poly` is a unit in `Zlocal p`.

Indeed, it is, up to sign, the product of the unit values `E_p_val g`.
-/
lemma E_p_poly_coeff_zero_isUnit
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] :
    IsUnit ((E_p_poly (G:=G) (k:=k) p).coeff 0) := by
  have h_coeff : (E_p_poly (G:=G) (k:=k) p).coeff 0 = (E_p_poly (G:=G) (k:=k) p).eval 0 := by
    exact coeff_zero_eq_eval_zero (E_p_poly p)
  rw [h_coeff]
  unfold E_p_poly
  rw [Polynomial.eval_prod]
  rw [IsUnit.prod_iff]
  intro g _
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  apply IsUnit.neg
  exact E_p_val_isUnit p g

/--
Every strictly positive power of `E_p` belongs to `Jloc p`.

This uses that `E_p ∈ Jloc p` and that `Jloc p` is closed under pointwise
multiplication.
-/
lemma E_p_pow_mem_Jloc
    {G : Type u} [Group G] [Fintype G] [CharZero k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    E_p (G:=G) (k:=k) p ^ n ∈ Jloc p := by
  induction n with
  | zero =>
    contradiction
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      simp only [zero_add, pow_succ, pow_zero, one_mul]
      exact E_p_mem_Jloc p
    · simp only [pow_succ]
      apply Jloc.mul_mem (k:=k) p
      · exact ih (Nat.pos_of_ne_zero hn0)
      · exact E_p_mem_Jloc p

/--
The constant coefficient of `E_p_poly` is nonzero.
-/
lemma E_p_poly_coeff_zero_ne_zero
    [Fintype G] [CharZero k]
    (p : ℕ) [Fact p.Prime] :
    (E_p_poly (G := G) (k := k) p).coeff 0 ≠ 0 := by
  haveI : Nontrivial (Zlocal p) := Zlocal.nontrivial (k:=k) p
  exact IsUnit.ne_zero (E_p_poly_coeff_zero_isUnit (k := k) p)

/--
Bernstein's local conclusion: the constant class function `1` belongs to the
localized Bernstein span `Jloc p`.

The proof applies the polynomial `E_p_poly` to the class function `E_p`.
Since the constant coefficient is a unit and all positive powers of `E_p`
belong to `Jloc p`, the resulting relation expresses `1` as an element of
`Jloc p`.
-/
lemma one_mem_Jloc
    {G : Type u} [Group G] [Fintype G] [CharZero k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] :
    (1 : ClassFun k G) ∈ Jloc p := by
  let P := E_p_poly (G:=G) (k:=k) p
  let u : Zlocal p := ↑(E_p_poly_coeff_zero_isUnit (G:= G) (k:=k) p).unit⁻¹
  have hu : u * P.coeff 0 = 1 := Units.inv_mul (E_p_poly_coeff_zero_isUnit p).unit
  let One_sum : ClassFun k G :=
    ∑ i ∈ P.support.erase 0,  ((-u * P.coeff i : Zlocal p) • (E_p  p ^ i))
  have h_One_sum_mem : One_sum ∈ Jloc p := by
    dsimp [One_sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    have hi_pos : 0 < i := Nat.pos_of_ne_zero (Finset.mem_erase.mp hi).1
    exact E_p_pow_mem_Jloc p i hi_pos
  have h_one_eq : (1 : ClassFun k G) = One_sum := by
    ext g
    simp only [ClassFun.one_apply]
    have h_eval := E_p_poly_eval_zero (k:=k) p g
    rw [Polynomial.eval_eq_sum] at h_eval
    change ∑ i ∈ P.support, P.coeff i * E_p_val p g ^ i = 0 at h_eval
    have h_mem_zero : 0 ∈ P.support := by
      apply Polynomial.mem_support_iff.mpr
      exact E_p_poly_coeff_zero_ne_zero (k := k) p
    rw [← Finset.insert_erase h_mem_zero] at h_eval
    rw [Finset.sum_insert (Finset.notMem_erase 0 _)] at h_eval
    simp only [pow_zero, mul_one] at h_eval
    have h_eq_neg :
      (∑ i ∈ P.support.erase 0, P.coeff i * (E_p_val (k:=k) p g) ^ i) = - P.coeff 0 := by
      calc (∑ i ∈ P.support.erase 0, P.coeff i * (E_p_val p g) ^ i)
        _ = -P.coeff 0 + (P.coeff 0 + ∑ i ∈ P.support.erase 0, P.coeff i * (E_p_val p g) ^ i) := by
              ring
        _ = -P.coeff 0 + 0 := by rw [h_eval]
        _ = -P.coeff 0 := by ring
    calc (1 : k) = Zlocal.toK p 1 := by simp only [map_one]
      _ = Zlocal.toK p (u * P.coeff 0) := by rw [hu]
      _ = Zlocal.toK p (-u * -P.coeff 0) := by congr 1; ring
      _ = Zlocal.toK p (-u * ∑ i ∈ P.support.erase 0, P.coeff i * (E_p_val p g) ^ i) := by
            rw [← h_eq_neg]
      _ = Zlocal.toK p (∑ i ∈ P.support.erase 0, -u * P.coeff i * (E_p_val p g) ^ i) := by
            rw [Finset.mul_sum]
            simp only [← mul_assoc]
            congr
      _ = ∑ i ∈ P.support.erase 0, Zlocal.toK p (-u * P.coeff i * (E_p_val p g) ^ i) :=
            map_sum (Zlocal.toK p) _ _
      _ = ∑ i ∈ P.support.erase 0,
            Zlocal.toK p (-u * P.coeff i) * Zlocal.toK p (E_p_val p g) ^ i := by
            simp only [neg_mul, map_neg, map_mul, map_pow, Finset.sum_neg_distrib, neg_inj]
            rfl
      _ = ∑ i ∈ P.support.erase 0, Zlocal.toK p (-u * P.coeff i) * (E_p p g) ^ i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← E_p_apply_eq_toK_E_p_val p g]
      _ = ∑ i ∈ P.support.erase 0, Zlocal.toK p (-u * P.coeff i) * (E_p p g) ^ i := by
            congr
      _ = One_sum g := by
            simp only [One_sum, ClassFun.finset_sum_apply,
              ClassFun.Zlocal.smul_apply, ClassFun.pow_apply]
  rw [h_one_eq]
  exact h_One_sum_mem

end PolynomialArgument

end BrauerInduction
