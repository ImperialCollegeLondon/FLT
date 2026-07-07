/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.LinearChar.Basic
public import FLT.Slop.Background.FDRep.ConjMap

@[expose] public section

/-!
# Inertia groups of linear characters

Let `H` be a normal subgroup of a group `G`, and let `ψ : H →* kˣ` be a linear
character. This file defines the conjugate character `conj ψ g` and its inertia
subgroup.

Our convention is

`(conj ψ g)(h) = ψ(g * h * g⁻¹)`.

With this convention, conjugation satisfies

`conj ψ (g₁ * g₂) = conj (conj ψ g₁) g₂`,

so it behaves as a right action. The left action of `G` on linear characters is
therefore defined by

`g • ψ = conj ψ g⁻¹`.

With respect to this left action, the inertia subgroup is exactly the stabilizer
of `ψ`.

## Main definitions

* `LinearChar.conj`: the conjugate of a linear character.
* `LinearChar.inertia`: the subgroup of elements of `G` fixing a linear
  character under conjugation.

## Main results

* `LinearChar.conj_ofLinearChar_iso`: conjugating the representation attached
  to a linear character agrees with conjugating the character.
* `LinearChar.inertia_eq_stabilizer`: the inertia subgroup is the stabilizer
  for the conjugation action.
* `LinearChar.le_inertia_of_isMulCommutative`: a commutative normal subgroup
  is contained in the inertia subgroup of each of its linear characters.
* `LinearChar.exists_mem_of_conj_ne`: an element outside the inertia subgroup
  changes the value of the character at some element of the normal subgroup.
-/

universe u v

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

namespace LinearChar

variable {H : Subgroup G} [H.Normal]

open CategoryTheory

/--
The conjugate of a linear character `ψ : H →* kˣ` by an element `g : G`. The
convention is `(conj ψ g)(h) = ψ(g * h * g⁻¹)`. Normality of `H` ensures
 that conjugation by `g` restricts to an automorphism of `H`.
-/
def conj (ψ : H →* kˣ) (g : G) :  H →* kˣ :=
  ψ.comp ((MulAut.conjNormal (H := H) g).toMonoidHom)

@[simp] lemma conj_apply (ψ : H →* kˣ) (g : G) (h : H) :
    conj ψ g h = ψ (((MulAut.conjNormal g) : H ≃* H) h) := rfl

@[simp] lemma conj_one (ψ : H →* kˣ) :
    conj (H := H) ψ (1 : G) = ψ := by
  ext h
  simp [conj]


/--
Conjugation of linear characters reverses multiplication in the acting
variable: `conj ψ (g₁ * g₂) = conj (conj ψ g₁) g₂`.
-/
lemma conj_mul (ψ : H →* kˣ) (g₁ g₂ : G) :
    conj ψ (g₁ * g₂) = conj (conj ψ g₁) g₂ := by
  ext h
  simp [conj, map_mul]

/--
Conjugating the one-dimensional representation associated to `ψ` is isomorphic
to the one-dimensional representation associated to the
conjugate character `conj ψ g`.
-/
noncomputable def conj_ofLinearChar_iso
    (ψ : H →* kˣ) (g : G) :
    FDRep.conjNormal H (FDRep.ofLinearChar (k := k) ψ) g
      ≅ FDRep.ofLinearChar (k := k) (LinearChar.conj (H := H) ψ g) := by
  exact Iso.refl _

section Inertia

/--
The inertia subgroup of a linear character `ψ : H →* kˣ`. It consists of the
elements `g : G` for which conjugation by `g` fixes `ψ`.
-/
def inertia (ψ : H →* kˣ) : Subgroup G where
  carrier := { g : G | conj (H := H) ψ g = ψ }
  one_mem' := by simp [conj_one]
  mul_mem' := by
    intro g₁ g₂ hg₁ hg₂
    have h₁ : conj (H := H) ψ g₁ = ψ := hg₁
    have h₂ : conj (H := H) ψ g₂ = ψ := hg₂
    simp [conj_mul, h₁, h₂]
  inv_mem' := by
    intro g hg
    have hg' : conj (H := H) ψ g = ψ := hg
    have h1 : conj (H := H) (conj (H := H) ψ g) g⁻¹ = conj (H := H) ψ g⁻¹ := by
      simpa using congrArg (fun χ => conj (H := H) χ g⁻¹) hg'
    rw [← conj_mul (H := H) ψ g g⁻¹] at h1
    have : ψ = conj (H := H) ψ g⁻¹ := by
      simpa [mul_inv_cancel, conj_one] using h1
    exact this.symm

@[simp] lemma mem_inertia_iff (ψ : H →* kˣ) (g : G) :
    g ∈ inertia (H := H) ψ ↔ conj (H := H) ψ g = ψ := Iff.rfl

/--
The left conjugation action of `G` on the linear characters of `H`. Since
`conj ψ (g₁ * g₂) = conj (conj ψ g₁) g₂`, the inverse is inserted in the
definition: `g • ψ = conj ψ g⁻¹`.
-/
instance : MulAction G (H →* kˣ) where
  smul g ψ := conj (H := H) ψ g⁻¹
  one_smul ψ := by
    change conj (H := H) ψ ((1 : G)⁻¹) = ψ
    simp [conj_one (H := H) (ψ := ψ)]
  mul_smul g₁ g₂ ψ := by
    change
      conj (H := H) ψ ((g₁ * g₂)⁻¹) =
        conj (H := H) (conj (H := H) ψ (g₂⁻¹)) (g₁⁻¹)
    have hinv : (g₁ * g₂)⁻¹ = g₂⁻¹ * g₁⁻¹ := by simp
    simpa [hinv] using (conj_mul (H := H) (ψ := ψ) (g₁ := g₂⁻¹) (g₂ := g₁⁻¹))

/--
The inertia subgroup of `ψ` is its stabilizer under the left conjugation
action of `G` on the linear characters of `H`.
-/
lemma inertia_eq_stabilizer (ψ : H →* kˣ) :
    inertia (H := H) ψ = MulAction.stabilizer G ψ := by
  ext g
  change
    conj (H := H) ψ g = ψ ↔
      conj (H := H) ψ g⁻¹ = ψ
  constructor
  · intro hg
    have hg_mem : g ∈ inertia (H := H) ψ := hg
    exact
      (mem_inertia_iff (H := H) ψ g⁻¹).1
        (Subgroup.inv_mem _ hg_mem)
  · intro hg
    have hginv_mem : g⁻¹ ∈ inertia (H := H) ψ := hg
    have := Subgroup.inv_mem (inertia (H := H) ψ) hginv_mem
    simpa using this

/--
Every element of a commutative normal subgroup `A` fixes each linear
character of `A` under conjugation. Consequently, `A` is contained in the
inertia subgroup of any linear character of `A`.
-/
lemma le_inertia_of_isMulCommutative
    {A : Subgroup G} [A.Normal] [IsMulCommutative A]
    (ψ : A →* kˣ) :
    A ≤ LinearChar.inertia (H := A) ψ := by
  intro a ha
  rw [mem_inertia_iff]
  ext x
  let aA : A := ⟨a, ha⟩
  have hx : ((MulAut.conjNormal (H := A) a) x) = x := by
    apply Subtype.ext
    have hcomm : aA * x = x * aA := by exact mul_comm' aA x
    have hcommG : (a : G) * (x : G) = (x : G) * (a : G) :=
      congrArg (fun y : A => (y : G)) hcomm
    calc
      (a : G) * (x : G) * (a : G)⁻¹
          = ((x : G) * (a : G)) * (a : G)⁻¹ := by simp [mul_assoc, hcommG]
      _   = (x : G) * ((a : G) * (a : G)⁻¹) := by simp [mul_assoc]
      _   = (x : G) := by simp
  rw [conj_apply, hx]

/--
Membership in the inertia subgroup is equivalent to fixing the character under
the left conjugation action.
-/
@[simp] lemma mem_inertia_iff_smul_eq (ψ : H →* kˣ) (g : G) :
    g ∈ LinearChar.inertia (H := H) ψ ↔ g • ψ = ψ := by
  simp [LinearChar.inertia_eq_stabilizer,
      MulAction.mem_stabilizer_iff (G := G) (a := ψ) (g := g)]

/--
If `g` does not belong to the inertia subgroup of `ψ`, then conjugation by `g`
changes the value of `ψ` at some element of the normal subgroup.
-/
lemma exists_conj_coe_apply_ne_of_not_mem_inertia
    {A : Subgroup G} [A.Normal]
    (ψ : A →* kˣ) {g : G}
    (hg : g ∉ LinearChar.inertia ψ) :
    ∃ a : A,
      ((LinearChar.conj ψ g) a : k) ≠ (ψ a : k) := by
  apply LinearChar.exists_apply_ne
  intro h
  exact hg ((LinearChar.mem_inertia_iff (H := A) ψ g).2 h)

end Inertia

end LinearChar
