/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.FDRep.Character.Basic
public import FLT.Slop.Background.FDRep.Res

@[expose] public section

/-!

Linear characters

In this project, a linear character of a group or monoid `G` over `k` is
represented directly by a monoid homomorphism

`ψ : G →* kˣ`.

There is no separate `LinearChar` type. The construction `FDRep.ofLinearChar ψ`
is the associated one-dimensional representation: its underlying `k`-module is
`k`, and an element `g : G` acts by scalar multiplication by `ψ g`.

This file proves the basic API for these representations, including their
action on vectors, their characters, their finrank, and compatibility with
transport along group isomorphisms.
-/

universe u v

variable {k : Type u} [CommRing k]

namespace FDRep

open Module

section Monoid

variable {G : Type v} [Monoid G]

/--
The one-dimensional representation associated to a linear character
`ψ : G →* kˣ`.

The underlying `k`-module is `k`, and `g : G` acts by scalar multiplication by
`ψ g`.
-/
noncomputable def ofLinearChar (ψ : G →* kˣ) : FDRep k G :=
  let ρ : Representation k G k :=
  { toFun := fun g => (ψ g : k) • LinearMap.id,
    map_one' := by
      ext
      simp only [map_one, Units.val_one, one_smul, LinearMap.id_coe, id_eq, Module.End.one_apply]
    map_mul' := by
      intro x y
      ext
      simp only [map_mul, Units.val_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul,
        mul_one, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Module.End.mul_apply]
      apply CommMonoid.mul_comm
  }
  FDRep.of ρ


@[simp] lemma ofLinearChar_rho_apply (ψ : G →* kˣ) (g : G) (x : k) :
    (ofLinearChar (k := k) ψ).ρ g x = (ψ g : k) * x := by
  simp only [ofLinearChar]
  change ↑(ψ g) * LinearMap.id x = ↑(ψ g) * x
  simp only [LinearMap.id_coe, id_eq]


@[simp]
lemma char_ofLinearChar {k : Type u} [Field k]
    (ψ : G →* kˣ) (g : G) :
    (ofLinearChar ψ).character g = (ψ g : k) := by
  simp only [character, ofLinearChar]
  change
    (LinearMap.trace k k)
        ((ψ g : k) • (LinearMap.id : k →ₗ[k] k))
      =
    (ψ g : k)
  rw [LinearMap.trace_eq_matrix_trace
    (b := Module.Basis.singleton Unit k)]
  simp only [Matrix.trace, Finset.univ_unique, PUnit.default_eq_unit,
    Matrix.diag_apply, LinearMap.toMatrix_singleton, Finset.sum_const,
    Finset.card_singleton, one_smul]
  change
    (((ψ g : k) • (LinearMap.id : k →ₗ[k] k)) 1)
      =
    (ψ g : k)
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    smul_eq_mul, mul_one]

@[simp]
theorem finrank_ofLinearChar
    {k : Type u} [Field k]
    (ψ : G →* kˣ) :
    (FDRep.ofLinearChar ψ).finrank = 1 := by
  change Module.finrank k k = 1
  simp only [finrank_self]

end Monoid

end FDRep

section Group

variable {G : Type v} [Group G]

open CategoryTheory
/--
Transporting `ofLinearChar` along an isomorphism `e : G ≃* H`.
If `ψ` is a character on `G`, then `Transport(e, ofLinearChar ψ) ≅ ofLinearChar (ψ ∘ e⁻¹)`.
-/
noncomputable def FDRep.transport_ofLinearChar_iso
    {H : Type v} [Group H] (e : G ≃* H) (ψ : G →* kˣ) :
    transport e (ofLinearChar ψ) ≅
    ofLinearChar (ψ.comp e.symm.toMonoidHom) := Iso.refl (transport e (ofLinearChar ψ))

/--
If two linear characters differ, they differ at some element.
-/
lemma LinearChar.exists_apply_ne
    {A : Subgroup G} {χ χ' : A →* kˣ} (hχ : χ ≠ χ') :
    ∃ a : A, (χ a : k) ≠ (χ' a : k) := by
  by_contra h
  apply hχ
  ext a
  have hnne : ¬ (χ a : k) ≠ (χ' a : k) := (not_exists.mp h) a
  exact not_ne_iff.mp hnne

open Classical in
@[simp]
lemma LinearChar.char_ofTop_ulift_of
    {k : Type u} [Field k] [Finite G]
    (ψ : (⊤ : Subgroup G) →* kˣ) (g : G) :
    (FDRep.ofTop
        (FDRep.ofLinearChar (k := k) ψ)).character g
      =
    (ψ ⟨g, Subgroup.mem_top g⟩ : k) := by
  change
    (FDRep.ofLinearChar ψ).character
        (Subgroup.topEquiv.symm g)
      =
    (ψ ⟨g, Subgroup.mem_top g⟩ : k)
  have htop :
      Subgroup.topEquiv.symm g =
        (⟨g, Subgroup.mem_top g⟩ : (⊤ : Subgroup G)) := by
    rfl
  rw [htop]
  exact FDRep.char_ofLinearChar
    ψ
    ⟨g, Subgroup.mem_top g⟩


/--
Transporting the representation attached to a linear character along a group
equivalence gives the representation attached to the character precomposed with
the inverse equivalence.
-/
noncomputable def FDRep.ofLinearChar_transportEquiv_iso
    {H : Type v} [Group H]
    (e : G ≃* H)
    (θ : G →* kˣ) :
    ((FDRep.transportEquiv (k := k) e).functor.obj
        (FDRep.ofLinearChar θ))
      ≅
    FDRep.ofLinearChar (θ.comp e.symm.toMonoidHom) := by
  rfl

end Group
