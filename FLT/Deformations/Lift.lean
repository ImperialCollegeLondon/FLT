import FLT.Deformations.Basic
import FLT.Deformations.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.Algebra.Module.Equiv.Defs

universe u

open CategoryTheory Function
open scoped TensorProduct

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type u}
  [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : Representation (𝓴 𝓞) G V)

variable (A : 𝓒 𝓞)
variable [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
variable [Module A V] [IsScalarTower A (𝓴 A) V]

variable {W: Type u} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

variable (reduction : LinearEquiv
  (algebraMap (𝓴 A) (𝓴 𝓞))
  ((𝓴 A) ⊗[A] W)
  V)

variable (ρ: Representation A G W)

section Definition

variable (W V) in
noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

variable (V W) in
noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V where
  toFun kaw := reduction kaw
  map_add' := by simp
  map_smul' := by
    simp
    rintro m x
    sorry -- TODO: why is rw [LinearEquiv.map_smulₛₗ reduction] not matching?

variable (W V) in
noncomputable def representation_mod : W →ₗ[A] V :=
  (mod_ctts V A W reduction).comp (extend_ctts A W)

omit W reduction in
structure Lift : Type _ where
  W: Type _
  [addCommMonoid : AddCommMonoid W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  reduction : LinearEquiv (algebraMap (𝓴 A) (𝓴 𝓞)) ((𝓴 A) ⊗[A] W) V
  -- The following 4 instances are just a LEAN specification pattern.
  -- What we really want is for any A : 𝓒 𝓞
  -- to have module structure on V with the natural scalar product, but we cannot define this
  -- as a dependent instance as it further depends on 𝓞, which is not the scope of "Module A V"
  -- To solve this: assume there is *some* structure, and further assume that structre coincides
  -- the natural one by IsScalarTower
  [module_A : Module A V]
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [isScalarTower_A : IsScalarTower A (𝓴 A) V]
  ρ: Representation A G W
  is_lift: ∀ g : G, ∀ w : W, ρbar g (representation_mod V A W reduction w)
      = representation_mod V A W reduction (ρ g w)

attribute [instance] Lift.addCommMonoid Lift.module Lift.free Lift.finite

def Lift.isIso : Setoid (Lift ρbar A) where
  r l l' := Representation.IsRepresentationEquiv l.ρ l'.ρ
  iseqv := {
    refl := by
      unfold Representation.IsRepresentationEquiv
      rintro l
      use LinearEquiv.id l.W
      rintro g
      unfold LinearEquiv.id
      aesop
    symm := by
      unfold Representation.IsRepresentationEquiv
      rintro x y ⟨φ, φ_prop⟩
      use φ.symm
      rintro g
      sorry
    trans := by
      unfold Representation.IsRepresentationEquiv
      rintro x y z ⟨φ, φ_prop⟩ ⟨φ', φ'_prop⟩
      use LinearEquiv.comp' φ φ'
      sorry
  }

end Definition

section UnrestrictedFunctor

omit A in
def Lift.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) (l : Lift ρbar A) : Lift ρbar B where
  W :=
    letI : Algebra A B := f.hom.toAlgebra
    l.W ⊗[A] B
  addCommMonoid := sorry
  module := sorry
  free := sorry
  finite := sorry
  reduction := sorry
  module_A := sorry
  module_𝓴A := sorry
  isScalarTower_𝓴A := sorry
  isScalarTower_A := sorry
  ρ := sorry
  is_lift := sorry

variable (𝓞) in
def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Lift ρbar A
  map f l := Lift.functor_onMap ρbar f l
  map_id := sorry
  map_comp := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

section UnrestrictedFunctor

section G_finite -- Section 3.1 Smit & Lenstra

open Matrix Set MvPolynomial
variable [Finite G]

variable (𝓞 G) in
abbrev smitLenstraRingRelations (ι : Type u) [Fintype ι] : Ideal (MvPolynomial (ι × ι × G) 𝓞) :=
  let rel1 := {X (i, i, (1:G)) - C (1 : 𝓞) | (i : ι)}
  let rel2 := {X (i, i, g) | (i : ι) (g : G)}
  let rel3 := { X (i, j, g)
      - ∑ᶠ (l : ι), (X (i, l, g)) * (X (l, j, h))  | (i : ι) (j : ι) (g : G) (h : G)}
  Ideal.span (rel1 ∪ rel2 ∪ rel3)

-- SmitLenstraRing is the ring 𝓞[G, n] given by Smit&Lenstra
variable (𝓞 G) in
abbrev smitLenstraRing (ι : Type u) [Fintype ι] : Type u :=
  (MvPolynomial (ι × ι × G) 𝓞) ⧸ smitLenstraRingRelations 𝓞 G ι

local notation3:max 𝓞 "[" G ", " α "]" => smitLenstraRing 𝓞 G α
local notation3:max "GL(" α ", " R ")" => (GeneralLinearGroup α R)
local notation3:max "Hom_grp(" G₁ ", " G₂ ")" => (G₁ →* G₂)
local notation3:max "Hom_alg(" O "; " A "," A' ")" => (A →ₗ[O] A')

-- Choose any basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
noncomputable def pbar' := Representation.gl_map_of_basis ρbar 𝓫

variable (A : 𝓒 𝓞)

noncomputable def smitLenstraMap : Hom_alg(𝓞; 𝓞[G, ι], A) ≃ Hom_grp(G, GL(ι, A)) where
  toFun f := {
    toFun := fun g : G => .mk' (.of (fun i j : ι =>
            f (Ideal.Quotient.mk (smitLenstraRingRelations 𝓞 G ι) (X (i, j, g)))))
          (by sorry)
    map_one' := sorry
    map_mul' := sorry
  }
  invFun ρ := {
    toFun := fun φ : 𝓞[G, ι] => sorry
    map_add' := sorry
    map_smul' := sorry
  }
  left_inv := sorry
  right_inv := sorry

-- Proposition 2.5 in G Finite
theorem Lift.functor_isCorepresentable_finite : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end G_finite

section G_profinite -- Section 3.2 Smit & Lenstra

end G_profinite
