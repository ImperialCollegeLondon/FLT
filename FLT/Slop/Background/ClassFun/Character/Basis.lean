/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.FDRep.Character.Basis
public import FLT.Slop.Background.FDRep.Character.Orthogonality
public import FLT.Slop.Background.ClassFun.Orthogonality
public import FLT.Slop.Background.ClassFun.Character.Span
public import FLT.Slop.Background.ClassFun.ConjClasses

@[expose] public section

/-!

# Bases of class functions from irreducible characters

This file proves that the irreducible characters of a finite group form a basis
of its space of class functions over an algebraically closed field of
characteristic zero.

Linear independence follows from Schur orthogonality. Spanning is proved by
duality. A linear functional vanishing on the span of the irreducible characters
is represented, via the nondegenerate character pairing, by pairing with a class
function `f`. The vanishing of the functional on all irreducible characters says
that `f` is orthogonal to every irreducible character; the theorem
`classFun_eq_zero_of_orthogonal_simples` then gives `f = 0`. Thus the dual
annihilator of the span is zero, and finite-dimensionality implies that the span
is the whole space.

The file then constructs a basis consisting of irreducible characters, shows
that the associated simple representations form a complete set of
isomorphism-class representatives, and deduces that the dimension of the
class-function space equals the number of irreducible representations.
-/

universe u v w z

namespace ClassFun

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} {G : Type v}
variable [Field k] [Group G]

open Classical in
/--
Irreducible characters of pairwise nonisomorphic simple representations are
linearly independent.

This version does not require the field to be algebraically closed. The
diagonal pairing terms are `|G| * finrank k (End(V i))`.
-/
lemma irreducible_characters_linearIndependent
    [Finite G] [CharZero k]
    {ι : Type*} [Finite ι]
    (V : ι → FDRep k G)
    [hSimple : ∀ i, Simple (V i)]
    (hNonIso : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j)) :
    LinearIndependent k
      (fun i => ClassFun.character (V i)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hpair :
      (∑ i : ι, c i * ((Fintype.card G : k) * (Module.finrank k (V j ⟶ V i) : k)))
        =
      0 := by
    have h :=
      congrArg
        (fun φ : ClassFun k G =>
          characterPairingLeft k G φ
            (ClassFun.character (V j)))
        hc
    simpa only [
      map_sum, map_smul, map_zero,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      RingHom.id_apply, smul_eq_mul,
      characterPairingLeft_character_eq_card_mul_finrank_hom
    ] using h
  have hcollapse :
      (∑ i : ι,
          c i * ((Fintype.card G : k) * (Module.finrank k (V j ⟶ V i) : k)))
        =
      c j * ((Fintype.card G : k) * (Module.finrank k (V j ⟶ V j) : k)) := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      have hfinrank :
          Module.finrank k (V j ⟶ V i) = 0 := by
        exact FDRep.finrank_hom_eq_zero_of_not_iso_simple
          (S := V j) (T := V i)
          (hNonIso j i (Ne.symm hij))
      simp [hfinrank]
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  rw [hcollapse] at hpair
  have hcard : (Fintype.card G : k) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hend :
      (Module.finrank k (V j ⟶ V j) : k) ≠ 0 :=
    FDRep.finrank_end_cast_ne_zero_of_simple (V j)
  have hdiag :
      (Fintype.card G : k) * (Module.finrank k (V j ⟶ V j) : k) ≠ 0 := by
    exact mul_ne_zero hcard hend
  exact (mul_eq_zero.mp hpair).resolve_right hdiag

/--
The annihilator in the linear dual of the span of the irreducible characters
is zero.
-/
private lemma irreducibleCharacterSpan_dualAnnihilator_eq_bot
    {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k] :
    (Submodule.span k
      (irreducibleCharacterSet k G)
    ).dualAnnihilator = ⊥ := by
  apply eq_bot_iff.mpr
  intro ℓ hℓ
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨f, rfl⟩ :=
    characterPairingLeft_surjective ℓ
  have h_ortho :
      ∀ (S : FDRep k G),
        Simple S →
          ∑ x : G, f x * S.character x⁻¹ = 0 := by
    intro S hS
    have hmem :
        ClassFun.character S ∈
          Submodule.span k
            (irreducibleCharacterSet k G) :=
      Submodule.subset_span ⟨S, hS, rfl⟩
    have hvanish :=
      (Submodule.mem_dualAnnihilator
        (characterPairingLeft k G f)).mp hℓ
        (ClassFun.character S) hmem
    simpa only [
      characterPairingLeft_apply,
      char_apply
    ] using hvanish
  have hf : f = 0 :=
    classFun_eq_zero_of_orthogonal_simples f h_ortho
  simp only [hf, map_zero, zero_mem]

/--
The irreducible characters span the space of class functions.
-/
theorem irreducibleCharacterSpan_eq_top
    {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k] :
    Submodule.span k
      (irreducibleCharacterSet k G) = ⊤ := by
  let W : Submodule k (ClassFun k G) :=
    Submodule.span k (irreducibleCharacterSet k G)
  have hAnn : W.dualAnnihilator = ⊥ := by
    simpa [W] using
      irreducibleCharacterSpan_dualAnnihilator_eq_bot (k := k) (G := G)
  have hfin :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq
      (K := k) (V := ClassFun k G) W
  rw [hAnn] at hfin
  have htop : W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using hfin
  simpa [W] using htop

/--
There exists a finite basis of the class-function space whose vectors are
characters of simple representations.
-/
lemma exists_basis_of_irreducibleCharacters
    {G : Type u} [Group G]
    [Finite G] [CharZero k] [IsAlgClosed k] :
    ∃ (ι : Type u) (_ : Fintype ι)
      (b : Module.Basis ι k (ClassFun k G)),
        ∀ i, b i ∈ irreducibleCharacterSet k G := by
  let S : Set (ClassFun k G) := irreducibleCharacterSet k G
  have hspan : ⊤ ≤ Submodule.span k S := by
    rw [irreducibleCharacterSpan_eq_top (k := k) (G := G)]
  let b := Module.Basis.ofSpan (K := k) (V := ClassFun k G) (s := S) hspan
  refine ⟨_, ?_, b, ?_⟩
  · exact Fintype.ofFinite _
  · intro i
    apply Module.Basis.ofSpan_subset hspan (Set.mem_range_self i)

/--
If a basis of the class-function space consists of characters of simple
representations, then those representations exhaust all isomorphism classes
of simple representations.
-/
lemma complete_of_basis_irreducibleCharacters
    [Finite G] [CharZero k]
    {ι : Type (max u v)} [Finite ι]
    (b : Module.Basis ι k (ClassFun k G))
    (V : ι → FDRep k G)
    (hSimple : ∀ i, Simple (V i))
    (hb_eq : ∀ i, b i = ClassFun.character (V i)) :
    ∀ S : FDRep k G,
      Simple S → ∃ i, Nonempty (S ≅ V i) := by
  intro S hS
  by_contra hnone
  push Not at hnone
  have hNonIsoV : ∀ i j, i ≠ j → IsEmpty (V i ≅ V j) := by
    intro i j hij
    refine ⟨?_⟩
    intro e
    have hbij : b i = b j := by
      calc
        b i = ClassFun.character (V i) := hb_eq i
        _   = ClassFun.character (V j) := ClassFun.char_eq_of_iso e
        _   = b j := (hb_eq j).symm
    exact hij (b.injective hbij)
  let W : Option ι → FDRep k G
    | none => S
    | some i => V i
  haveI : ∀ o : Option ι, Simple (W o) := by
    intro o
    cases o with
    | none =>
        exact hS
    | some i =>
        exact hSimple i
  have hNonIsoW :
      ∀ a b, a ≠ b → IsEmpty (W a ≅ W b) := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none =>
            exact False.elim (hab rfl)
        | some j =>
            refine ⟨?_⟩
            intro e
            exact IsEmpty.false e
    | some i =>
        cases b with
        | none =>
            refine ⟨?_⟩
            intro e
            exact IsEmpty.false (id e.symm)
        | some j =>
            exact hNonIsoV i j (by
              intro hij
              apply hab
              simp [hij])
  have hLI :
      LinearIndependent k (fun o : Option ι => ClassFun.character (W o)) :=
    ClassFun.irreducible_characters_linearIndependent
      (V := W) hNonIsoW
  let χS : ClassFun k G := ClassFun.character S
  haveI : Fintype ι := Fintype.ofFinite ι
  have hexpand : χS = ∑ i : ι, (b.repr χS i) • b i := by
    simp only [Module.Basis.sum_repr]
  have hexpand' :
      χS =
        ∑ i : ι,
          (b.repr χS i) • ClassFun.character (V i) := by
    simpa [hb_eq] using hexpand
  let c : Option ι → k
    | none => 1
    | some i => - b.repr χS i
  have hrel :
      ∑ o : Option ι, c o • ClassFun.character (W o) = 0 := by
    rw [Fintype.sum_option]
    simp only [c, W, one_smul]
    calc
      χS + ∑ x : ι, (-(b.repr χS x)) • ClassFun.character (V x)
          =
        (∑ x : ι, (b.repr χS x) • ClassFun.character (V x))
          + ∑ x : ι, (-(b.repr χS x)) • ClassFun.character (V x) := by
            rw [← hexpand']
      _ =
        ∑ x : ι,
          ((b.repr χS x) • ClassFun.character (V x)
            + (-(b.repr χS x)) • ClassFun.character (V x)) := by
            rw [Finset.sum_add_distrib]
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            rw [← add_smul]
            simp
  rw [Fintype.linearIndependent_iff] at hLI
  have hnone_coeff : c none = 0 := hLI c hrel none
  simp [c] at hnone_coeff

/--
A basis of the class-function space consisting of characters of simple
representations.
-/
structure IrrepCharBasis
    (k : Type u) (G : Type v)
    [Field k] [Group G] where
  /-- The index type of the chosen basis. -/
  ι : Type (max u v)

  /-- The index type is finite. -/
  [fintype : Fintype ι]
  /-- The simple representations indexing the basis. -/
  V : ι → FDRep k G

  /-- Each representation in the family is simple. -/
  simple : ∀ i, Simple (V i)

  /-- The corresponding basis of class functions. -/
  b : Module.Basis ι k (ClassFun k G)

  /-- Each basis vector is the character of its corresponding representation. -/
  b_eq : ∀ i, b i = ClassFun.character (V i)

attribute [instance] IrrepCharBasis.fintype

/--
The representations indexing an irreducible-character basis exhaust all
isomorphism classes of simple representations.
-/
lemma IrrepCharBasis.is_exhaustive
    [Finite G] [CharZero k]
    (B : IrrepCharBasis k G) :
    ∀ S : FDRep k G,
      Simple S → ∃ i, Nonempty (S ≅ B.V i) :=
  complete_of_basis_irreducibleCharacters
     B.b B.V B.simple B.b_eq

/--
There exists a basis of the class-function space consisting of characters of
simple representations.
-/
theorem nonempty_irrepCharBasis
    {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k] :
    Nonempty (IrrepCharBasis k G) := by
  obtain ⟨ι, hι, b, hb⟩ := exists_basis_of_irreducibleCharacters (k := k) (G := G)
  letI : Fintype ι := hι
  choose V hSimple hb_eq using hb
  exact ⟨{
    ι := ι
    V := V
    simple := hSimple
    b := b
    b_eq := hb_eq
  }⟩

/--
The representations underlying an irreducible character basis form a complete
set of simple representations.
-/
lemma IrrepCharBasis.isCompleteSetOfSimples
    {k : Type u} [Field k] [CharZero k]
    {G : Type v} [Finite G] [Group G]
    (B : ClassFun.IrrepCharBasis k G) :
    FDRep.IsCompleteSetOfSimples B.V where
  is_simple := B.simple
  is_exhaustive := complete_of_basis_irreducibleCharacters B.b B.V B.simple B.b_eq
  is_distinct := by
    intro i j h
    rcases h with ⟨e⟩
    apply B.b.injective
    calc
      B.b i = ClassFun.character (B.V i) := B.b_eq i
      _ = ClassFun.character (B.V j) := ClassFun.char_eq_of_iso e
      _ = B.b j := (B.b_eq j).symm


lemma span_characters_eq_top_of_complete
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {G : Type u} [Group G] [Finite G]
    {ι : Type*}
    (S : ι → FDRep k G)
    (hS : FDRep.IsCompleteSetOfSimples S) :
    Submodule.span k (Set.range (fun i => ClassFun.character (S i))) = ⊤ := by
  rw [← irreducibleCharacterSpan_eq_top (k := k) (G := G)]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro χ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨S i, hS.is_simple i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro χ ⟨T, hT, rfl⟩
    rcases hS.is_exhaustive T hT with ⟨i, ⟨e⟩⟩
    rw [ClassFun.char_eq_of_iso e]
    exact Submodule.subset_span ⟨i, rfl⟩

/--
The dimension of the class-function space equals the number of representations
in any complete set of simple representations.
-/
lemma finrank_classFun_eq_card_of_complete
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι]
    (S : ι → FDRep k G)
    (hS : FDRep.IsCompleteSetOfSimples (k := k) (G := G) S) :
    Module.finrank k (ClassFun k G) = Fintype.card ι := by
  let χ : ι → ClassFun k G := fun i => ClassFun.character (S i)
  letI : ∀ i, Simple (S i) := hS.is_simple
  have hLI : LinearIndependent k χ := by
    exact
      ClassFun.irreducible_characters_linearIndependent
        (k := k) (G := G)
        (V := S)
        (hNonIso := fun i j hij => hS.isEmpty_iso_of_ne hij)
  have hspan :
      Submodule.span k (Set.range χ) = ⊤ :=
    span_characters_eq_top_of_complete
      (k := k) (G := G) S hS
  have hdim :
      Module.finrank k (Submodule.span k (Set.range χ)) = Fintype.card ι := by
    exact finrank_span_eq_card hLI
  rw [← hdim]
  rw [hspan]
  simp

open Classical in
/--
A noncanonical equivalence between the index type of a finite complete set of
simple representations and the conjugacy classes of `G`.
-/
noncomputable def completeSetEquivConjClasses
    {k : Type u} [Field k] {G : Type u} [Group G] {κ : Type z} [Fintype κ]
    [Finite G] [CharZero k] [IsAlgClosed k]
    (S : κ → FDRep k G)
    (hS : FDRep.IsCompleteSetOfSimples S) :
    κ ≃ ConjClasses G := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Quotient.fintype (IsConj.setoid G)
  have h_card_eq : Fintype.card κ = Fintype.card (ConjClasses G) := by
    have h1 :
        Module.finrank k (ClassFun k G) =
          Fintype.card (ConjClasses G) := by
      rw [LinearEquiv.finrank_eq (linearEquivConjClasses (k := k) (G := G))]
      exact Module.finrank_pi k
    have h2 :
        Module.finrank k (ClassFun k G) = Fintype.card κ := by
      simpa [Nat.card_eq_fintype_card] using
        ClassFun.finrank_classFun_eq_card_of_complete
          (k := k) (G := G) S hS
    rw [← h2, h1]
  exact Fintype.equivOfCardEq h_card_eq

/--
A chosen basis of the class-function space consisting of characters of simple
representations.
-/
noncomputable def irrepCharBasis
    {G : Type u} [Group G] [Finite G] [CharZero k] [IsAlgClosed k] :
    IrrepCharBasis k G := Classical.choice (nonempty_irrepCharBasis (k := k) (G := G))

/--
The coordinates of a character in an irreducible-character basis are integers.

The integer is the multiplicity with which the corresponding irreducible
representation occurs in a semisimple decomposition of the representation.
-/
lemma char_coeffs_int
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k]
    (B : ClassFun.IrrepCharBasis k G)
    (U : FDRep k G) (i : B.ι) :
    ∃ m : ℤ, B.b.repr (ClassFun.character U) i = (m : k) := by
  classical
  haveI : NeZero (Nat.card G) := ⟨One.natCard_ne_zero_of_finite G⟩
  obtain ⟨κ, f, hFintype, hSimple_f, hSum⟩ :=
    ClassFun.char_eq_sum_simples U
  letI : Fintype κ := hFintype
  have h_repr_sum :
      B.b.repr (ClassFun.character U) =
        ∑ j : κ, B.b.repr (ClassFun.character (f j)) := by
    rw [hSum, map_sum]
  have h_repr_eval :
      B.b.repr (ClassFun.character U) i =
        ∑ j : κ, B.b.repr (ClassFun.character (f j)) i := by
    rw [h_repr_sum]
    simp
  have h_iso :
      ∀ j : κ, ∃ idx : B.ι, Nonempty (f j ≅ B.V idx) := by
    intro j
    exact IrrepCharBasis.is_exhaustive B (f j) (hSimple_f j)
  choose idx h_idx using h_iso
  have h_char_fj :
      ∀ j : κ, ClassFun.character (f j) = B.b (idx j) := by
    intro j
    calc
      ClassFun.character (f j)
          = ClassFun.character (B.V (idx j)) := by
              exact ClassFun.char_eq_of_iso (Classical.choice (h_idx j))
      _   = B.b (idx j) := by
              exact (B.b_eq (idx j)).symm
  have h_repr_eval2 :
      ∀ j : κ,
        B.b.repr (ClassFun.character (f j)) i =
          if idx j = i then (1 : k) else 0 := by
    intro j
    rw [h_char_fj j]
    by_cases hji : idx j = i
    · subst hji
      simp
    · have hcoord :
          B.b.repr (B.b (idx j)) i = 0 := by
        have hrepr :
            B.b.repr (B.b (idx j)) =
              Finsupp.single (idx j) (1 : k) := by
          simp
        rw [hrepr]
        simp [hji]
      rw [hcoord]
      simp [hji]
  have h_sum_ones :
      (∑ j : κ, B.b.repr (ClassFun.character (f j)) i)
        =
      Finset.sum (Finset.univ.filter (fun j : κ => idx j = i))
         (fun _ => (1 : k)) := by
    have h_rewrite :
        (∑ j : κ, B.b.repr (ClassFun.character (f j)) i)
          =
        ∑ j : κ, if idx j = i then (1 : k) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact h_repr_eval2 j
    rw [h_rewrite, Finset.sum_filter]
  rw [h_repr_eval, h_sum_ones, Finset.sum_const, nsmul_eq_mul]
  refine ⟨((Finset.univ.filter (fun j : κ => idx j = i)).card : ℤ), ?_⟩
  simp only [mul_one, Int.cast_natCast]

end ClassFun

namespace FDRep

/--
There exists a finite complete set of simple finite-dimensional representations,
and the number of such representatives equals the dimension of the space of
class functions.
-/
theorem finrank_classFun_eq_num_irreps
    (G : Type u) [Group G] [Finite G]
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] :
    ∃ (κ : Type u) (_ : Fintype κ)
      (S : κ → FDRep k G),
        FDRep.IsCompleteSetOfSimples (k := k) (G := G) S ∧
        Module.finrank k (ClassFun k G) = Fintype.card κ := by
  let B : ClassFun.IrrepCharBasis k G := ClassFun.irrepCharBasis (k := k) (G := G)
  letI : Fintype B.ι := B.fintype
  refine ⟨B.ι, inferInstance, B.V, ?_, ?_⟩
  · exact ClassFun.IrrepCharBasis.isCompleteSetOfSimples (k:= k) (G := G) B
  · exact ClassFun.finrank_classFun_eq_card_of_complete B.V
      (ClassFun.IrrepCharBasis.isCompleteSetOfSimples (k:= k) (G := G) B)

end FDRep
