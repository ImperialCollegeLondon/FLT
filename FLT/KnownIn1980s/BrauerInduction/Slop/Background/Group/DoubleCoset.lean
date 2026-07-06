/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.Coset

@[expose] public section

/-!
# Double-coset helper lemmas

This file contains auxiliary lemmas for double-coset representatives, fibre
cardinality computations, and decomposing finite sums over a group into sums over
double cosets.
-/

universe u v

variable {G : Type u} [Group G]

namespace DoubleCoset

/--
A double coset representative `g` defines the identity double coset iff
`g = h * k` for some `h ∈ H` and `k ∈ K`.
-/
lemma mk_eq_one_iff {H K : Subgroup G} {g : G} :
    DoubleCoset.mk H K g = DoubleCoset.mk H K 1 ↔ ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  rw [DoubleCoset.eq] --
  constructor
  · rintro ⟨h, hh, k, hk, h_inv⟩
    have hg : g = h⁻¹ * k⁻¹ := by
      have h1 : k⁻¹ = h * g := by
        apply_fun (fun x => x * k⁻¹) at h_inv
        simp only [one_mul, mul_inv_cancel_right] at h_inv
        exact h_inv
      rw [h1, inv_mul_cancel_left]
    exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, hg⟩
  · rintro ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [← mul_assoc, mul_inv_cancel, one_mul, inv_mul_cancel]

/--
A finite group has finitely many double cosets.

This is a named local-instance provider for
`Fintype (DoubleCoset.Quotient H K)`.
-/
@[reducible]
noncomputable def quotientFintype
    [Finite G] (H K : Subgroup G) :
    Fintype (DoubleCoset.Quotient (G := G) H K) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact Quotient.fintype (DoubleCoset.setoid (H : Set G) (K : Set G))

/-- The identity double coset in `I \ G / I`. -/
abbrev oneDC (I : Subgroup G) : DoubleCoset.Quotient (G:=G) I I :=
  DoubleCoset.mk (G := G) I I (1 : G)

/--
If a double coset in `I \ G / I` is not the identity double coset, then its
chosen representative is not an element of `I`.
-/
lemma out_not_mem_of_ne_one
    (I : Subgroup G) (d : DoubleCoset.Quotient (G := G) I I)
      (hd : d ≠ DoubleCoset.oneDC (G := G) I) :
    Quotient.out d ∉ I := by
  intro hout
  apply hd
  have hmk : DoubleCoset.mk (G := G) I I (Quotient.out d) =
    DoubleCoset.mk (G := G) I I (1 : G) := by
    refine (DoubleCoset.eq (G := G) I I (Quotient.out d) (1 : G)).2 ?_
    refine ⟨(Quotient.out d)⁻¹, I.inv_mem hout, 1, I.one_mem, ?_⟩
    simp
  calc
    d = DoubleCoset.mk (G := G) I I (Quotient.out d) := by
      exact Eq.symm (DoubleCoset.out_eq' I I d)
    _ = DoubleCoset.mk (G := G) I I (1 : G) := hmk

/--
The chosen representative of the identity double coset belongs to `I`.
-/
lemma out_oneDC_mem
    (I : Subgroup G) :
    Quotient.out (DoubleCoset.oneDC (G := G) I) ∈ I := by
  have hmk :
      DoubleCoset.mk (G := G) I I
        (Quotient.out (DoubleCoset.oneDC (G := G) I))
        =
      DoubleCoset.mk (G := G) I I (1 : G) := by
    calc
      DoubleCoset.mk (G := G) I I
          (Quotient.out (DoubleCoset.oneDC (G := G) I))
          = DoubleCoset.oneDC (G := G) I := by
              exact DoubleCoset.out_eq' (G := G) I I
                (DoubleCoset.oneDC (G := G) I)
      _ = DoubleCoset.mk (G := G) I I (1 : G) := rfl
  obtain ⟨h, hh, k, hk, hout⟩ :=
    (mk_eq_one_iff (H := I) (K := I)
      (g := Quotient.out (DoubleCoset.oneDC (G := G) I))).mp hmk
  rw [hout]
  exact I.mul_mem hh hk

/--
The parametrisation of the double coset `I g I` used in the fibre-counting
argument. It sends `(u, v)` to `u⁻¹ * g * v⁻¹`.
-/
def parameterization (I : Subgroup G) (g : G) : I × I → G :=
  fun p => (p.1 : G)⁻¹ * g * (p.2 : G)⁻¹

/--
For fixed `u v : I`, the fibre of `parameterization I g` over
`(u : G) * g * (v : G)` is equivalent to `I ⊓ I.map (MulAut.conj g)`.

This is the fibre computation underlying the double-coset summation formula.
-/
noncomputable def fiberEquiv
    (I : Subgroup G) (g : G) (u v : I) :
     (↥(I ⊓ I.map (MulAut.conj g).toMonoidHom)) ≃
        {p : I × I // (parameterization I g p = (u : G) * g * (v : G))} := by
  let Ig : Subgroup G := I.map (MulAut.conj g).toMonoidHom
  let H : Subgroup G := I ⊓ Ig
  let φ : I × I → G := parameterization I g
  refine
  { toFun := ?_
    invFun := ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro h
    let uinv : I := ⟨(u : G)⁻¹, I.inv_mem u.2⟩
    let vinv : I := ⟨(v : G)⁻¹, I.inv_mem v.2⟩
    have hg_memI : g⁻¹ * (h.1 : G) * g ∈ I := by
      have hhIg : (h.1 : G) ∈ Ig := h.2.2
      have : (MulAut.conj g).symm (h.1 : G) ∈ I :=
        (Subgroup.mem_map_equiv (f := MulAut.conj g) (K := I) (x := (h.1 : G))).1
          (by simpa [Ig] using hhIg)
      simpa [MulAut.conj_symm_apply] using this
    refine
      ⟨ ( ⟨(h.1 : G)⁻¹ * (uinv : G), I.mul_mem (I.inv_mem h.2.1) uinv.2⟩
        , ⟨(vinv : G) * (g⁻¹ * (h.1 : G) * g), I.mul_mem vinv.2 hg_memI⟩ ),
        ?_ ⟩
    dsimp [φ, parameterization, uinv, vinv]
    group
  · rintro ⟨⟨a, b⟩, hab⟩
    let hG : G := (u : G)⁻¹ * (a : G)⁻¹
    have hI : hG ∈ I := I.mul_mem (I.inv_mem u.2) (I.inv_mem a.2)
    have h_conj : hG = g * ((v : G) * (b : G)) * g⁻¹ := by
      have h1 :
          (u : G)⁻¹ * ((a : G)⁻¹ * g * (b : G)⁻¹) =
            (u : G)⁻¹ * ((u : G) * g * (v : G)) := by
        exact congrArg (fun t => (u : G)⁻¹ * t) hab
      have h1' : (u : G)⁻¹ * (a : G)⁻¹ * g * (b : G)⁻¹ = g * (v : G) := by
        simpa [mul_assoc] using h1
      have h2 :
          ((u : G)⁻¹ * (a : G)⁻¹ * g * (b : G)⁻¹) * (b : G) =
            (g * (v : G)) * (b : G) := by
        simpa using congrArg (fun t => t * (b : G)) h1'
      have h2' : (u : G)⁻¹ * (a : G)⁻¹ * g = g * (v : G) * (b : G) := by
        simpa [mul_assoc] using h2
      have h3 :
          ((u : G)⁻¹ * (a : G)⁻¹ * g) * g⁻¹ =
            (g * (v : G) * (b : G)) * g⁻¹ := by
        simpa using congrArg (fun t => t * g⁻¹) h2'
      simpa [hG, mul_assoc] using h3
    have hIg : hG ∈ I.map (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.mem_map).2 ?_
      refine ⟨(v : G) * (b : G), I.mul_mem v.2 b.2, ?_⟩
      simpa [MulAut.conj_apply, MonoidHom.coe_coe, mul_assoc] using h_conj.symm
    exact ⟨hG, ⟨hI, hIg⟩⟩
  · intro h
    apply Subtype.ext
    dsimp [parameterization]
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_left]
  · rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · dsimp [parameterization]
      simp only [mul_inv_rev, inv_inv, mul_inv_cancel_right]
    · dsimp [parameterization]
      have hab' : (a : G)⁻¹ * g * (b : G)⁻¹ = (u : G) * g * (v : G) := by
        simpa [parameterization] using hab
      have h1 :
        (u : G)⁻¹ * ((a : G)⁻¹ * g * (b : G)⁻¹)
          = (u : G)⁻¹ * ((u : G) * g * (v : G)) := congrArg (fun t => (u : G)⁻¹ * t) hab'
      have h1' :
        (u : G)⁻¹ * (a : G)⁻¹ * g * (b : G)⁻¹
          = g * (v : G) := by simpa [mul_assoc] using h1
      have h2 :
        ((u : G)⁻¹ * (a : G)⁻¹ * g * (b : G)⁻¹) * (b : G)
          = (g * (v : G)) * (b : G) := congrArg (fun t => t * (b : G)) h1'
      have h2' :
        (u : G)⁻¹ * (a : G)⁻¹ * g
          = g * (v : G) * (b : G) := by simpa [mul_assoc] using h2
      have h3 :
        g⁻¹ * ((u : G)⁻¹ * (a : G)⁻¹ * g)
          = g⁻¹ * (g * (v : G) * (b : G)) := congrArg (fun t => g⁻¹ * t) h2'
      have h3' :
        g⁻¹ * ((u : G)⁻¹ * (a : G)⁻¹) * g
          = (v : G) * (b : G) := by simpa [mul_assoc] using h3
      calc
        (v : G)⁻¹ * (g⁻¹ * ((u : G)⁻¹ * (a : G)⁻¹) * g)
          =
            (v : G)⁻¹ * ((v : G) * (b : G))
            := by exact congrArg (fun t => (v : G)⁻¹ * t) h3'
        _ = (b : G)
            := by simp only [inv_mul_cancel_left]

/-- The fibres of `parameterization I g` all have cardinality
  `Nat.card (I ⊓ I.map (MulAut.conj g))`. -/
lemma natCard_fiber_parameterization
    [Finite G] (I : Subgroup G) (g : G) (u v : I) :
    Nat.card {p : I × I // parameterization I g p = (u : G) * g * (v : G)}
      =
    Nat.card ↥(I ⊓ I.map (MulAut.conj g).toMonoidHom) := by
  simpa using (Nat.card_congr (fiberEquiv I g u v)).symm

open Classical in
/--
Summing `F` over the double coset `I g I` equals `1 / |I ⊓ I^g|` times the sum
over `I × I` through the parametrisation `(u, v) ↦ u⁻¹ * g * v⁻¹`.

Here `I^g` is represented as `I.map (MulAut.conj g).toMonoidHom`.
-/
lemma sum_eq_sum_over_product
    {k : Type v} [Field k] [CharZero k] [Fintype G]
    (I : Subgroup G)
    (g : G) (F : G → k) :
    ∑ x ∈ (DoubleCoset.doubleCoset g I I).toFinset, F x =
      (Nat.card ↥(I ⊓ I.map (MulAut.conj g).toMonoidHom) : k)⁻¹ *
        ∑ p : I × I, F (parameterization I g p) := by
  let D := DoubleCoset.doubleCoset g I I
  let Ig := I.map (MulAut.conj g).toMonoidHom
  let H := I ⊓ Ig
  let Dfin : Finset G := D.toFinset
  have mem_Dfin (x : G) : x ∈ Dfin ↔ x ∈ D := by simp [Dfin, Set.mem_toFinset]
  let φ : I × I → G := parameterization I g
  have hφ_maps : ∀ p : I × I, φ p ∈ D := by
    intro p
    refine DoubleCoset.mem_doubleCoset.mpr ?_
    refine ⟨(p.1.1 : G)⁻¹, I.inv_mem p.1.2, (p.2.1 : G)⁻¹, I.inv_mem p.2.2, ?_⟩
    simp [φ, parameterization, mul_assoc]
  have card_filter_eq_natCard (x : G) :
      ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)).card
        = Nat.card {p : I × I // φ p = x} := by
    let s : Finset (I × I) :=
      (Finset.univ : Finset (I × I)).filter (fun p => φ p = x)
    let e : ({p : I × I // φ p = x} ≃ ↥s) :=
    { toFun := fun t =>
        ⟨t.1, by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ _, t.2⟩⟩
      invFun := fun q =>
        ⟨q.1, (Finset.mem_filter.mp q.2).2⟩
      left_inv := by rintro ⟨p, hp⟩; rfl
      right_inv := by rintro ⟨p, hp⟩; rfl }
    have h₁ : Nat.card {p : I × I // φ p = x} = Nat.card (↥s) := Nat.card_congr e
    have h₂ : Nat.card (↥s) = s.card := by simp only [Nat.card_eq_fintype_card,
      Fintype.card_coe]
    exact (h₁.trans h₂).symm
  have fiber_card_eq (x : G) (hx : x ∈ D) :
      ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)).card
        = Nat.card H := by
    rcases DoubleCoset.mem_doubleCoset.mp hx with ⟨u0, hu0, v0, hv0, rfl⟩
    let uI : I := ⟨u0, hu0⟩
    let vI : I := ⟨v0, hv0⟩
    have hNat :
        Nat.card {p : I × I // φ p = (u0 : G) * g * (v0 : G)}
          = Nat.card H := by
      simpa [φ, parameterization, H, Ig] using
        (natCard_fiber_parameterization (I := I) (g := g) (u := uI) (v := vI))
    exact (card_filter_eq_natCard ((u0 : G) * g * (v0 : G))).trans hNat
  have sum_pairs_eq :
      (∑ p : I × I, F (φ p))
        =
      ∑ x ∈ Dfin, (Nat.card H : k) * F x := by
    have h_univ :
        (∑ p : I × I, F (φ p))
          =
        ∑ p ∈ (Finset.univ : Finset (I × I)), F (φ p) := by
      simp
    have hfib :
        (∑ p ∈ (Finset.univ : Finset (I × I)), F (φ p))
          =
        ∑ x ∈ Dfin,
          ∑ p ∈ (Finset.univ : Finset (I × I)) with φ p = x, F (φ p) := by
      simpa using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (I × I)))
          (t := Dfin)
          (g := φ)
          (f := fun p => F (φ p))
          (by
            intro p hp
            have : φ p ∈ D := hφ_maps p
            exact (mem_Dfin (φ p)).2 (hφ_maps p)
          )).symm
    have hinner :
        (∑ x ∈ Dfin,
            ∑ p ∈ (Finset.univ : Finset (I × I)) with φ p = x, F (φ p))
          =
        ∑ x ∈ Dfin, (Nat.card H : k) * F x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxD : x ∈ D :=  (mem_Dfin x).1 hx
      change
        (∑ p ∈ ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)), F (φ p))
          =
        (Nat.card H : k) * F x
      have hconst :
          (∑ p ∈ ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)), F (φ p))
            =
          ∑ p ∈ ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)), F x := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have hp' : φ p = x := (Finset.mem_filter.mp hp).2
        simp only [hp']
      have hcard :
          ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)).card = Nat.card H :=
        fiber_card_eq x hxD
      calc
        (∑ p ∈ ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)), F (φ p))
            =
          ∑ p ∈ ((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)), F x := hconst
        _ =
          (((Finset.univ : Finset (I × I)).filter (fun p => φ p = x)).card : k) * F x := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = (Nat.card H : k) * F x := by
          simp only [hcard]
    calc
      (∑ p : I × I, F (φ p))
          = ∑ p ∈ (Finset.univ : Finset (I × I)), F (φ p) := h_univ
      _ = ∑ x ∈ Dfin,
            ∑ p ∈ (Finset.univ : Finset (I × I)) with φ p = x, F (φ p) := hfib
      _ = ∑ x ∈ Dfin, (Nat.card H : k) * F x := hinner
  have hH0' : Nat.card H ≠ 0 := by
    refine (Nat.card_ne_zero).2 ?_
    refine ⟨?_, ?_⟩
    · exact ⟨⟨1, by simp⟩⟩
    · infer_instance
  have hH0 : (Nat.card H : k) ≠ 0 := Nat.cast_ne_zero.mpr hH0'
  have h_main :
      (Nat.card H : k)⁻¹ * (∑ p : I × I, F (φ p)) = ∑ x ∈ Dfin, F x := by
    rw [sum_pairs_eq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp only [Nat.card_eq_fintype_card, ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
      not_false_eq_true, inv_mul_cancel_left₀]
  have hDfin_goal : Dfin = D.toFinset := by ext x; simp [Dfin, Set.mem_toFinset]
  have h_main_toFinset :
      (Nat.card H : k)⁻¹ * (∑ p : I × I, F (φ p)) = ∑ x ∈ D.toFinset, F x := by
    have h := h_main
    rw [hDfin_goal] at h
    exact h
  simpa [φ, D, H, Ig] using h_main_toFinset.symm

open Classical in
/--
Decompose a finite sum over `G` into a sum over double cosets.

Each double coset contributes the sum of `f` over the corresponding subset of
`G`.
-/
lemma sum_over_G_eq_sum_double_cosets
    {k : Type v} [AddCommMonoid k]
    [Finite G] [Fintype G] (I : Subgroup G) (f : G → k) :
    letI : Fintype (DoubleCoset.Quotient (I : Set G) I) :=
       Quotient.fintype (DoubleCoset.setoid (I : Set G) (I : Set G))
    ∑ x : G, f x =
      ∑ d : DoubleCoset.Quotient (I : Set G) I,
      ∑ x ∈ (DoubleCoset.quotToDoubleCoset I I d).toFinset, f x := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext g
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    let d := DoubleCoset.mk I I g
    use d
    constructor
    · exact True.intro
    · rw [Set.mem_toFinset]
      convert DoubleCoset.mem_doubleCoset_self I I g
      apply @Quotient.exact _ (DoubleCoset.setoid (I : Set G) I)
      exact Quotient.out_eq d
  · intro d₁ _ d₂ _ h_neq
    have h_disj := DoubleCoset.disjoint_out (H := I) (K := I) h_neq
    exact Set.disjoint_toFinset.mpr h_disj


open Classical in
/--
Regroup a finite sum over right cosets by double cosets.

This is `Fintype.sum_fiberwise` for the map sending a right coset `q` to the
double coset represented by `q.out`.
-/
lemma sum_rightCosets_by_doubleCoset
    {k : Type v} [AddCommMonoid k]
    [Finite G] (I : Subgroup G)
    [Fintype (_root_.Quotient (QuotientGroup.rightRel I))]
    [Fintype (Quotient (G := G) I I)]
    (F : _root_.Quotient (QuotientGroup.rightRel I) → k) :
    (∑ q : _root_.Quotient (QuotientGroup.rightRel I), F q)
      =
    ∑ d : Quotient (G := G) I I,
      (∑ q :
            {q : _root_.Quotient (QuotientGroup.rightRel I) // DoubleCoset.mk I I q.out = d},
          F q.1) := by
  let φ : _root_.Quotient (QuotientGroup.rightRel I) → Quotient (G := G) I I :=
    fun q => DoubleCoset.mk I I q.out
  simpa [φ] using (Fintype.sum_fiberwise φ (fun q => F q)).symm


open Classical in
/--
The set associated to a double-coset quotient element is the double coset of its
chosen representative.
-/
@[simp]
lemma quotToDoubleCoset_eq_doubleCoset_out
    (I J : Subgroup G)
    (d : DoubleCoset.Quotient (G := G) I J) :
    DoubleCoset.quotToDoubleCoset I J d =
      DoubleCoset.doubleCoset (Quotient.out d) I J := by
  rfl

end DoubleCoset
