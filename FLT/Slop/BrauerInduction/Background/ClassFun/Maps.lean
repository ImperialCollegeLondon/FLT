/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.ClassFun.Basic

public import FLT.Slop.BrauerInduction.Background.ClassFun.Basic

@[expose] public section

/-!
# Maps of class functions

This file defines the basic functorial operations on class functions:

* precomposition with a group homomorphism;
* postcomposition with a map between coefficient types;
* restriction to a subgroup;
* inflation from a quotient group.

It also packages the linear forms of these constructions when the coefficient
types carry suitable module structures.
-/

namespace ClassFun

universe u v w x

variable {k : Type u} {l : Type v}
variable {G : Type w} {H : Type x}
variable [Group G] [Group H]

section Composition

/--
Precompose a class function with a group homomorphism.

This is the pullback of class functions along the homomorphism.
-/
def comp (f : ClassFun k G) (φ : H →* G) : ClassFun k H where
  toFun h := f (φ h)
  map_conj := by
    intro x y hxy
    exact f.map_conj _ _ (MonoidHom.map_isConj φ hxy)

@[simp]
lemma comp_apply
    (f : ClassFun k G) (φ : H →* G) (h : H) :
    f.comp φ h = f (φ h) :=
  rfl

@[simp]
lemma comp_id (f : ClassFun k G) :
    f.comp (MonoidHom.id G) = f := by
  ext g
  rfl

@[simp]
lemma comp_comp
    {L : Type*} [Group L]
    (f : ClassFun k G) (φ : H →* G) (ψ : L →* H) :
    (f.comp φ).comp ψ = f.comp (φ.comp ψ) := by
  ext x
  rfl

@[simp]
lemma comp_zero [Zero k] (φ : H →* G) :
    (0 : ClassFun k G).comp φ = 0 := by
  ext h
  rfl

@[simp]
lemma comp_add [Add k]
    (f g : ClassFun k G) (φ : H →* G) :
    (f + g).comp φ = f.comp φ + g.comp φ := by
  ext h
  rfl

@[simp]
lemma comp_smul
    {R : Type*} [SMul R k]
    (a : R) (f : ClassFun k G) (φ : H →* G) :
    (a • f).comp φ = a • f.comp φ := by
  ext h
  rfl

/--
Precomposition with a group homomorphism, as a linear map on class functions.
-/
def compLinearMap
    {R : Type*}
    [Semiring R] [AddCommMonoid k] [Module R k]
    (φ : H →* G) :
    ClassFun k G →ₗ[R] ClassFun k H where
  toFun f := f.comp φ
  map_add' f g := by
    ext h
    rfl
  map_smul' r f := by
    ext h
    rfl

@[simp]
lemma compLinearMap_apply
    {R : Type*}
    [Semiring R] [AddCommMonoid k] [Module R k]
    (φ : H →* G) (f : ClassFun k G) :
    compLinearMap (k := k) (R := R) φ f = f.comp φ :=
  rfl

end Composition

section Postcomposition

/--
Postcompose a class function with a map between coefficient types.
-/
def postcomp (f : ClassFun k G) (F : k → l) :
    ClassFun l G where
  toFun g := F (f g)
  map_conj := by
    intro x y hxy
    exact congrArg F (f.map_conj x y hxy)

@[simp]
lemma postcomp_apply
    (f : ClassFun k G) (F : k → l) (g : G) :
    f.postcomp F g = F (f g) :=
  rfl

@[simp]
lemma postcomp_id (f : ClassFun k G) :
    f.postcomp id = f := by
  ext g
  rfl

lemma postcomp_comp
    {m : Type*}
    (f : ClassFun k G) (F : k → l) (Q : l → m) :
    (f.postcomp F).postcomp Q =
      f.postcomp (Q ∘ F) := by
  ext g
  rfl

/--
Postcomposition with a linear map, as a linear map between spaces of class
functions.
-/
def postcompLinearMap
    {R : Type*}
    [Semiring R]
    [AddCommMonoid k] [AddCommMonoid l]
    [Module R k] [Module R l]
    (F : k →ₗ[R] l) :
    ClassFun k G →ₗ[R] ClassFun l G where
  toFun f := f.postcomp F
  map_add' f g := by
    ext x
    exact F.map_add (f x) (g x)
  map_smul' r f := by
    ext x
    exact F.map_smul r (f x)

@[simp]
lemma postcompLinearMap_apply
    {R : Type*}
    [Semiring R]
    [AddCommMonoid k] [AddCommMonoid l]
    [Module R k] [Module R l]
    (F : k →ₗ[R] l) (f : ClassFun k G) :
    postcompLinearMap (G := G) F f = f.postcomp F :=
  rfl

end Postcomposition

section Restriction

/-- Restriction of a class function to a subgroup. -/
def res (K : Subgroup G) (f : ClassFun k G) :
    ClassFun k K :=
  f.comp K.subtype

@[simp]
lemma res_apply
    (K : Subgroup G) (f : ClassFun k G) (x : K) :
    res K f x = f (x : G) :=
  rfl

@[simp]
lemma res_zero [Zero k] (K : Subgroup G) :
    res K (0 : ClassFun k G) = 0 :=
  comp_zero K.subtype

@[simp]
lemma res_add [Add k]
    (K : Subgroup G) (f g : ClassFun k G) :
    res K (f + g) = res K f + res K g :=
  comp_add f g K.subtype

@[simp]
lemma res_smul
    {R : Type*} [SMul R k]
    (K : Subgroup G) (a : R) (f : ClassFun k G) :
    res K (a • f) = a • res K f :=
  comp_smul a f K.subtype

/-- Restriction to a subgroup, as a linear map. -/
def resLinearMap
    {R : Type*}
    [Semiring R] [AddCommMonoid k] [Module R k]
    (K : Subgroup G) :
    ClassFun k G →ₗ[R] ClassFun k K :=
  compLinearMap K.subtype

end Restriction

section Inflation

/--
Inflate a class function on a quotient group to the original group.
-/
def inflate
    {K : Subgroup G} [K.Normal]
    (f : ClassFun k (G ⧸ K)) :
    ClassFun k G :=
  f.comp (QuotientGroup.mk' K)

@[simp]
lemma inflate_apply
    {K : Subgroup G} [K.Normal]
    (f : ClassFun k (G ⧸ K)) (g : G) :
    inflate f g = f (QuotientGroup.mk' K g) :=
  rfl

end Inflation

section MulEquiv

/--
A multiplicative equivalence of groups induces an equivalence of their spaces
of class functions.
-/
def equivOfMulEquiv (e : H ≃* G) :
    ClassFun k G ≃ ClassFun k H where
  toFun f := f.comp e.toMonoidHom
  invFun f := f.comp e.symm.toMonoidHom
  left_inv f := by
    ext g
    change f (e (e.symm g)) = f g
    rw [e.apply_symm_apply]
  right_inv f := by
    ext h
    change f (e.symm (e h)) = f h
    rw [e.symm_apply_apply]

@[simp]
lemma equivOfMulEquiv_apply
    (e : H ≃* G) (f : ClassFun k G) (h : H) :
    equivOfMulEquiv (k := k) e f h = f (e h) :=
  rfl

@[simp]
lemma equivOfMulEquiv_symm_apply
    (e : H ≃* G) (f : ClassFun k H) (g : G) :
    (equivOfMulEquiv (k := k) e).symm f g = f (e.symm g) :=
  rfl

end MulEquiv

end ClassFun
