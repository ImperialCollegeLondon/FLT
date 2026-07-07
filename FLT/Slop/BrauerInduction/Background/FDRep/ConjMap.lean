/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Basic

/-!
# Conjugating finite-dimensional representations of subgroups

This file defines two ways to conjugate a finite-dimensional representation of a
subgroup.

* `FDRep.conj` conjugates a representation of a normal subgroup `A ⊆ G` by an
  element `g : G`; since `A` is normal, the result is again a representation of
  `A`.

* `FDRep.conjMap` conjugates a representation of an arbitrary subgroup `I ⊆ G`
  to a representation of the conjugate subgroup
  `I.map (MulAut.conj g).toMonoidHom`.

The file also contains helper lemmas for comparing the action of the conjugated
representation on elements of a normal subgroup contained in `I`.
-/

@[expose] public section

namespace Slop
open Slop

universe u v w

open CategoryTheory

namespace FDRep

/--
Conjugate a representation of a normal subgroup by an element of the ambient
group.

If `A ⊆ G` is normal and `σ` is a representation of `A`, then `conjNormal A σ g`
is the representation of `A` obtained by precomposing `σ` with the automorphism
of `A` induced by conjugation by `g`.
-/
noncomputable def conjNormal {k : Type u} [CommRing k] {G : Type v} [Group G]
  (A : Subgroup G) [A.Normal] (σ : FDRep k A) (g : G) : FDRep k A :=
  FDRep.of (σ.ρ.comp (MulAut.conjNormal (H := A) g).toMonoidHom)

@[simp]
lemma conjNormal_rho_apply {k : Type u} [CommRing k] {G : Type v} [Group G]
    (A : Subgroup G) [A.Normal] (σ : FDRep k A) (g : G) (a : A) :
    (conjNormal (A := A) σ g).ρ a = σ.ρ ((MulAut.conjNormal (H := A) g) a) := rfl

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
Conjugate a representation of a subgroup to a representation of the conjugate
subgroup.

If `σ` is a representation of `I`, then `conjMap I g σ` is a representation of
`g I g⁻¹`, represented here as `I.map (MulAut.conj g).toMonoidHom`.
The action is obtained by transporting back along the subgroup equivalence
induced by `MulAut.conj g`.
-/
noncomputable def conjMap
    (I : Subgroup G) (g : G) (σ : FDRep k I) :
    FDRep k (I.map (MulAut.conj g).toMonoidHom) := by
  let e : I ≃* I.map (MulAut.conj g).toMonoidHom :=
    (MulAut.conj g).subgroupMap I
  exact FDRep.of (σ.ρ.comp e.symm.toMonoidHom)

@[simp]
lemma conjMap_rho_apply
    (I : Subgroup G) (g : G)
    (σ : FDRep k I)
    (x : I.map (MulAut.conj g).toMonoidHom)
    (v : (FDRep.conjMap (k := k) I g σ)) :
    (FDRep.conjMap (k := k) I g σ).ρ x v =
      σ.ρ (((MulAut.conj g).subgroupMap I).symm x) v :=
  rfl


/--
If `A` is normal and `A ≤ I`, then `A` is contained in the conjugate subgroup
`I.map (MulAut.conj g).toMonoidHom`.
-/
lemma le_conjMap_of_normal
    (A I : Subgroup G) [haN : A.Normal] (hAI : A ≤ I) (g : G) :
    A ≤ I.map (MulAut.conj g).toMonoidHom := by
  intro a haA
  refine ⟨(MulAut.conj g).symm a, ?_, ?_⟩
  · apply hAI
    have hmem : (g⁻¹ : G) * (a : G) * g ∈ A :=
      Subgroup.Normal.conj_mem' haN a haA g
    simpa [MulAut.conj_symm_apply] using hmem
  · simpa using (MulAut.conj g).apply_symm_apply a

/--
Evaluate `conjMap I g σ` on an element of a normal subgroup contained in `I`.

If `A` is normal in `G`, `A ≤ I`, and `a : A`, then the element `a`, viewed as
an element of the conjugate subgroup `I.map (MulAut.conj g).toMonoidHom`, acts
in `conjMap I g σ` as the original representation `σ` evaluated at
`g⁻¹ * a * g`, viewed as an element of `I`.
-/
lemma conjMap_rho_apply_of_mem_normal
    (A I : Subgroup G) [haN : A.Normal] (hAI : A ≤ I)
    (g : G) (σ : FDRep k I)
    (a : A)
    (v : (FDRep.conjMap (k := k) I g σ)) :
    let Ig : Subgroup G := I.map (MulAut.conj g).toMonoidHom
    let hAIg : A ≤ Ig := FDRep.le_conjMap_of_normal A I hAI g
    let aIg : Ig := ⟨(a : G), hAIg a.2⟩
    let a_conj_val : G := g⁻¹ * (a : G) * g
    let h_mem_A : a_conj_val ∈ A := by
      simpa [a_conj_val] using
         Subgroup.Normal.conj_mem' haN (a : G) a.2 g
    let aI : I := ⟨a_conj_val, hAI h_mem_A⟩
    (FDRep.conjMap (k := k) I g σ).ρ aIg v =
      σ.ρ aI v := by
  intro Ig hAIg aIg a_conj_val h_mem_A aI
  rw [FDRep.conjMap_rho_apply]
  congr

end FDRep

end Slop
