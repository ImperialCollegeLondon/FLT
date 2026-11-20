/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Biproducts
public import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Simple decompositions of finite-dimensional representations

This file contains Maschke-style decomposition results for `FDRep`.

Over a field `k`, for a finite group `G` whose order is nonzero in `k`, every
object of `FDRep k G` decomposes as a finite biproduct of simple
representations.

The proof is by induction on the dimension of the representation. For a
nonzero representation we first construct a simple subobject. Maschke's theorem,
via Mathlib's injectivity result for finite-dimensional representations, shows
that this monomorphism splits. The representation is then isomorphic to a
biproduct of the simple subobject and the cokernel, and the induction continues
on the lower-dimensional summand.

Because the Mathlib Maschke/injectivity instance for `FDRep` currently has the
coefficient field and group in the same universe, the main decomposition theorem
in this file uses a single universe for `k` and `G`.

## Main results

* `FDRep.splitMonoOfMono`: every monomorphism of finite-dimensional
  representations splits under the Maschke hypotheses.
* `FDRep.exists_simple_subobject`: every nonzero finite-dimensional
  representation contains a simple subobject.
* `FDRep.exists_simple_decomposition`: every finite-dimensional representation
  is isomorphic to a finite biproduct of simple representations.
-/

@[expose] public section

namespace Slop
open Slop

namespace FDRep

open CategoryTheory
open CategoryTheory.Limits
open BigOperators
open scoped MonoidAlgebra

universe u v w

section SplitMono

variable {k : Type u} [CommRing k]

/--
A split monomorphism realizes its codomain as a binary biproduct of its source
and its cokernel.
-/
lemma exists_iso_biprod_of_splitMono
    {G : Type v} [Monoid G]
    {S V : FDRep k G} (f : S ⟶ V) (sf : SplitMono f) :
    Nonempty (V ≅ S ⊞ cokernel f) := by
  haveI : IsSplitMono f := ⟨⟨sf⟩⟩
  have i₀ :
      IsColimit
        (Cofork.ofπ (cokernel.π f)
          ((cokernel.condition f).trans zero_comp.symm)) :=
    cokernelIsCokernel (f := f)
  have i : IsColimit
      (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) := by
    simpa [CokernelCofork.ofπ] using i₀
  let b := binaryBiconeOfIsSplitMonoOfCokernel (f := f) i
  have hb : b.IsBilimit :=
    isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (f := f) i
  refine ⟨?_⟩
  simpa [b] using
    (biprod.uniqueUpToIso (X := S) (Y := cokernel f) hb)


/-- A monomorphism of finite-dimensional representations over a field of characteristic
coprime to the group order is a split monomorphism. -/
noncomputable def splitMonoOfMono
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    [Finite G] [hne : NeZero (Nat.card G : k)]
    {V W : FDRep k G} (f : V ⟶ W) [Mono f] :
    SplitMono f := by
  letI : Fintype G := Fintype.ofFinite G
  haveI : NeZero (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    exact hne
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (show (Fintype.card G : k) ≠ 0 from NeZero.ne _)
  -- 1. Map to Rep k G where the Injective instances exist
  let F := forget₂ (FDRep k G) (Rep k G)
  haveI : Mono (F.map f) := CategoryTheory.Functor.map_mono F f
  -- 2. Synthesize the Injective instance for the underlying representation
  haveI : CategoryTheory.Injective (F.obj V) := by
    infer_instance
  let hfac : ∃ r_rep : F.obj W ⟶ F.obj V, F.map f ≫ r_rep = 𝟙 (F.obj V) :=
    CategoryTheory.Injective.factors
      (J := F.obj V)
      (f := F.map f)
      (g := 𝟙 (F.obj V))
  let r_rep : F.obj W ⟶ F.obj V := Classical.choose hfac
  have hr_rep : F.map f ≫ r_rep = 𝟙 (F.obj V) := Classical.choose_spec hfac
  -- 3. Pull the retraction back to FDRep k G
  let r : W ⟶ V := F.preimage r_rep
  have hr : f ≫ r = 𝟙 V := by
    apply F.map_injective
    change F.map f ≫ F.map (F.preimage r_rep) = 𝟙 (F.obj V)
    rw [F.map_preimage]
    exact hr_rep
  exact ⟨r, hr⟩

end SplitMono

open CategoryTheory
/--
Assume `G` is finite and `char k ∤ |G|`.
Then every nontrivial finite-dimensional `k`-representation of `G`
(i.e. object of `FDRep k G`) contains a simple subrepresentation.
-/
theorem exists_simple_subobject
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    [Finite G] [hne : NeZero (Nat.card G : k)]
    (V : FDRep k G) (hV : ¬ IsZero V) :
    ∃ (S : FDRep k G) (f : S ⟶ V), Simple S ∧ Mono f := by
  -- Explicitly define the induction motive
  have h_nz : Nontrivial V := by
    by_contra hnt
    have hsub : Subsingleton V :=
      not_nontrivial_iff_subsingleton.mp hnt
    exact hV ((isZero_iff_subsingleton V).mpr hsub)
  let P : ℕ → Prop := fun n =>
    ∀ (V' : FDRep k G), Nontrivial V' → Module.finrank k V' ≤ n →
      ∃ (S : FDRep k G) (f : S ⟶ V'), Simple S ∧ Mono f
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro m ih V' h_nz' hn'
    by_cases h_simp : Simple V'
    · exact ⟨V', 𝟙 V', h_simp, inferInstance⟩
    · haveI : Nontrivial V' := h_nz'
      have h_not_simp :
          ¬ (∀ (W : FDRep k G) (f : W ⟶ V') [Mono f],
              IsIso f ∨ f = 0) := by
        intro h
        apply h_simp
        refine ⟨?_⟩
        intro W f hf_mono
        haveI : Mono f := hf_mono
        constructor
        · intro hf_iso
          haveI : IsIso f := hf_iso
          exact isIso_hom_ne_zero_of_nontrivial
              (k := k) (G := G) (W := W) (V := V') f
        · intro hf_ne
          rcases h W f with hf_iso | hf_zero
          · exact hf_iso
          · exact False.elim (hf_ne hf_zero)
      push Not at h_not_simp
      rcases h_not_simp with ⟨W, f, h_mono, h_not_iso, hf_ne_zero⟩
      haveI : Mono f := h_mono
      -- 1. Split the monomorphism using Maschke's theorem
      haveI sm : SplitMono f := splitMonoOfMono f
      let Q : FDRep k G := CategoryTheory.Limits.cokernel f
      have h_iso : Nonempty (V' ≅ W ⊞ Q) := by
        simpa [Q] using exists_iso_biprod_of_splitMono f sm
      let iso : V' ≅ W ⊞ Q := h_iso.some
      have h_dim_sum :
          Module.finrank k V' =
            Module.finrank k W + Module.finrank k Q := by
        have e1 : V' ≃ₗ[k] (W ⊞ Q : FDRep k G) :=
          FDRep.isoToLinearEquiv iso
        have e2 : (W ⊞ Q : FDRep k G) ≃ₗ[k] W × Q :=
          linearEquivBiprod W Q
        have e : V' ≃ₗ[k] W × Q :=
          e1.trans e2
        calc
          Module.finrank k V'
              = Module.finrank k (W × Q) :=
                  LinearEquiv.finrank_eq e
          _ = Module.finrank k W + Module.finrank k Q :=
                  Module.finrank_prod
      have h_pos_coker : 0 < Module.finrank k Q := by
        apply Nat.pos_of_ne_zero
        intro h_zero_dim
        have h_zero : IsZero Q :=
          (finrank_eq_zero_iff_IsZero Q).mp h_zero_dim
        haveI : Epi f := by
          dsimp [Q] at h_zero
          exact (Preadditive.epi_iff_isZero_cokernel f).mpr h_zero
        haveI : IsIso f := isIso_of_mono_of_epi f
        exact h_not_iso inferInstance
      -- 4. Dimension of W is strictly less than V'
      have h_dim_W : Module.finrank k W < Module.finrank k V' := by
        rw [h_dim_sum]
        exact lt_add_of_pos_right _ h_pos_coker
      have h_nz_W : Nontrivial W := by
        by_contra hc
        have h_sub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hc
        have h_zero : IsZero W := (isZero_iff_subsingleton W).mpr h_sub
        exact hf_ne_zero (h_zero.eq_of_src f 0)
      -- 5. Invoke the induction hypothesis on W
      have h_lt : Module.finrank k W < m := lt_of_lt_of_le h_dim_W hn'
      rcases ih (Module.finrank k W) h_lt W h_nz_W le_rfl with ⟨S, g, hS_simp, hg_mono⟩
      -- 6. S ⟶ W ⟶ V' is our target simple monomorphism
      exact ⟨S, g ≫ f, hS_simp, inferInstance⟩
  -- Finally, evaluate the proven motive P on our initial V
  exact hP (Module.finrank k V) V h_nz le_rfl

/--
Maschke-style decomposition: every finite-dimensional representation is a finite
biproduct of simple finite-dimensional representations.

The coefficient field and group are kept in the same universe because the
Mathlib `FDRep` Maschke/injectivity instance currently has this universe shape.
-/
theorem exists_simple_decomposition
    {k : Type u} [Field k]
    {G : Type u} [Group G]
    [Finite G] [NeZero (Nat.card G : k)] (V : FDRep k G) :
    ∃ (ι : Type) (f : ι → FDRep k G) (_ : Fintype ι)
      (_ : ∀ i, Simple (f i)), Nonempty (V ≅ ⨁ f) := by
  let P : ℕ → Prop :=
    fun n =>
      ∀ V : FDRep k G,
        finrank V = n →
        ∃ (ι : Type) (f : ι → FDRep k G) (_ : Fintype ι)
          (_ : ∀ i, Simple (f i)), Nonempty (V ≅ ⨁ f)
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?step
    intro n IH V h_dim
    cases n with
    | zero =>
        have hV0 : IsZero V := by
          exact (finrank_eq_zero_iff_IsZero V).mp h_dim
        let ι : Type := PEmpty
        let f : ι → FDRep k G := fun i => PEmpty.elim i
        letI : Fintype ι := Fintype.ofFinite ι
        have hB0 : IsZero (⨁ f) :=
          IsZero_biproduct_empty f
        have h_simples : ∀ i : ι, Simple (f i) := by
          intro i
          cases i
        have hIso : V ≅ ⨁ f :=
          hV0.iso hB0
        exact ⟨ι, f, inferInstance, h_simples, ⟨hIso⟩⟩
    | succ n =>
        have hV_not_IsZero : ¬ IsZero V := by
          intro hzero
          have hz : finrank V = 0 :=
            (finrank_eq_zero_iff_IsZero V).mpr hzero
          have hsucc : Nat.succ n = 0 := by
            simp [h_dim] at hz
          exact Nat.succ_ne_zero n hsucc
        obtain ⟨S, f, hS_simple, hf_mono⟩ :=
          exists_simple_subobject V hV_not_IsZero
        haveI : Mono f := hf_mono
        let sf : SplitMono f :=
          splitMonoOfMono f
        let K := cokernel f
        obtain ⟨iso_split⟩ :=
          exists_iso_biprod_of_splitMono f sf
        have hsum :
            finrank (S ⊞ K) = finrank S + finrank K := finrank_biprod S K
        have hV_eq :
            finrank (S ⊞ K) = Nat.succ n := by
          simpa [K] using (finrank_congr iso_split.symm).trans h_dim
        have hS_pos : 0 < finrank S := by
          have hnot : ¬ IsZero S := Simple.not_isZero S
          have hne : finrank S ≠ 0 := by
            intro hz
            exact hnot ((finrank_eq_zero_iff_IsZero S).mp hz)
          exact Nat.pos_of_ne_zero hne
        have hSK : finrank S + finrank K = Nat.succ n := by
          simpa [hsum] using hV_eq
        have hK_lt : finrank K < Nat.succ n := by
          have hlt : finrank K < finrank S + finrank K :=
            Nat.lt_add_of_pos_left hS_pos
          exact hlt.trans_eq hSK
        rcases IH (finrank K) hK_lt K rfl with
          ⟨ι, g, hι, hg_simple, ⟨isoK⟩⟩
        have iso₀ : V ≅ S ⊞ (⨁ g) :=
          iso_split ≪≫ (biprod.mapIso (Iso.refl S) isoK)
        let ι' := Option ι
        let f' : ι' → FDRep k G := fun t => Option.rec S g t
        haveI : Fintype ι' := inferInstance
        have hf'_simple : ∀ i', Simple (f' i') := by
          intro i'
          cases i' with
          | none =>
              simpa [f'] using hS_simple
          | some i =>
              simpa [f'] using hg_simple i
        have iso₁ : S ⊞ (⨁ g) ≅ ⨁ f' := by
          simpa [f'] using (FDRep.biproductOptionIso (S := S) (K := g))
        exact ⟨ι', f', inferInstance, hf'_simple, ⟨iso₀ ≪≫ iso₁⟩⟩
  exact hP (finrank V) V rfl

end FDRep

end Slop
