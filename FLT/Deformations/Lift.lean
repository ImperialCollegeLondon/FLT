import Mathlib

universe u

open CategoryTheory Function
open scoped TensorProduct

section ToMathlib
def GL_map_of_representation_of_basis {R V G ι: Type u} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* Matrix.GeneralLinearGroup ι R :=
  sorry
end ToMathlib

-- Initial Setting
variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)
variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable {G : Type u}
  [Group G] [TopologicalSpace G] [TopologicalGroup G]
variable (ρbar : Representation (𝓴 𝓞) G V)

section Definitions

variable (𝓞) in
abbrev CommAlgCat := Under (CommRingCat.of 𝓞)

instance : CoeOut (CommAlgCat 𝓞) (CommRingCat) where coe A := A.right

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
def modMap (A : CommAlgCat 𝓞) [IsLocalRing A] := RingHom.comp (IsLocalRing.residue A) A.hom

variable (𝓞) in
class IsResidueAlgebra (A : CommAlgCat 𝓞) [IsLocalRing A] : Prop where
  isSurjective : Surjective (modMap 𝓞 A)

variable (𝓞) in
noncomputable def IsResidueAlgebra.toRingEquiv (A : CommAlgCat 𝓞) [IsLocalRing A] [IsLocalHom A.hom]
  [IsResidueAlgebra 𝓞 A] : (𝓴 A) ≃+* (𝓴 𝓞) where
    toFun ka := IsLocalRing.residue (R := 𝓞) (surjInv (f := modMap 𝓞 A)
      (IsResidueAlgebra.isSurjective (A := A)) ka)
    invFun ko := by
      let mp := (RingHom.comp (IsLocalRing.residue (R := A)) A.hom)
      simp only [Functor.const_obj_obj, CommRingCat.coe_of] at mp
      exact IsLocalRing.ResidueField.lift mp ko
    left_inv := sorry
    right_inv := sorry
    map_mul' := by
      simp [modMap]
      intro x y
      rw [← map_mul, eq_of_surj]



    map_add' := sorry

variable (𝓞) in
class IsProartinian (A : CommAlgCat 𝓞) : Prop where
  pro_artin : True

variable (𝓞) in
def 𝓒_filter : CommAlgCat 𝓞 → Prop := fun A =>
  ∃ (_ : IsLocalRing A),
  ∃ (_ : IsLocalHom A.hom),
  IsResidueAlgebra 𝓞 A ∧
  IsProartinian 𝓞 A

variable (𝓞) in
def 𝓒 := FullSubcategory (𝓒_filter 𝓞)

instance : Category (𝓒 𝓞) := by unfold 𝓒; infer_instance

instance : CoeOut (𝓒 𝓞) (CommAlgCat 𝓞) where coe A := A.obj

variable (A : 𝓒 𝓞)
instance : Algebra 𝓞 A := by unfold 𝓒 at A; exact A.obj.hom.toAlgebra
instance : IsLocalRing A := by unfold 𝓒 at A; exact A.property.1
instance : IsLocalHom A.obj.hom := by unfold 𝓒 at A; exact A.property.2.1
instance : IsResidueAlgebra 𝓞 A := by unfold 𝓒 at A; exact A.property.2.2.1
noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A)

instance : IsProartinian 𝓞 A := by unfold 𝓒 at A; exact A.property.2.2.2
variable [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
variable [Module A V] [IsScalarTower A (𝓴 A) V]

variable {W: Type u} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]
variable (ρ: Representation A G W)

variable (W V) in
noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) :=
  (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

variable (V W) in
noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V := by
  refine TensorProduct.lift ?_
  sorry

variable (W V) in
noncomputable def representation_mod : W →ₗ[A] V :=
  LinearMap.comp (mod_ctts V A W) (extend_ctts A W)

omit W in
structure Lift : Type (u+1) where
  W: Type u
  [addCommMonoid : AddCommMonoid W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  -- The following 4 instances are just a weird LEAN pattern. What we really want is for any A : 𝓒 𝓞
  -- to have module structure on V with the natural scalar product, but we cannot define this
  -- as a dependent instance as it further depends on 𝓞, which is not the scope of "Module A V"
  -- To solve this: assume there is *some* structure, and further assume that structre coincides
  -- the natural one by IsScalarTower
  [module_A : Module A V]
  [module_𝓴A : Module (𝓴 A) V]
  [isScalarTower_𝓴A : IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [isScalarTower_A : IsScalarTower A (𝓴 A) V]
  ρ: Representation A G W
  is_lift: ∀ g : G, ∀ w : W, ρbar g (representation_mod V W (A := A) w)
      = representation_mod V W (A := A) (ρ g w)

def Lift.isIso : Setoid (Lift ρbar A) where
  r W W' := sorry
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry
  }

omit A in
def Lift.functor_onMap {A B : 𝓒 𝓞} (f : A ⟶ B) : Lift ρbar A → Lift ρbar B :=
  sorry

variable (𝓞) in
def Lift.functor : CategoryTheory.Functor (𝓒 𝓞) (Type (u+1)) where
  obj A := Lift ρbar A
  map f := sorry -- Lift.functor_onMap ρbar f

end Definitions

section G_finite -- Section 3.1 Smit & Lenstra

open Matrix Set MvPolynomial
variable [Finite G]

variable (𝓞 G) in
abbrev SLRingRelations (ι : Type u) [Fintype ι] : Ideal (MvPolynomial (ι × ι × G) 𝓞) :=
  let rel1 := {X (i, i, (1:G)) - C (1 : 𝓞) | (i : ι)}
  let rel2 := {X (i, i, g) | (i : ι) (g : G)}
  let rel3 := { X (i, j, g)
      - ∑ᶠ (l : ι), (X (i, l, g)) * (X (l, j, h))  | (i : ι) (j : ι) (g : G) (h : G)}
  Ideal.span (rel1 ∪ rel2 ∪ rel3)

-- SLRing is the ring 𝓞[G, n] given by Smit&Lenstra
variable (𝓞 G) in
abbrev SLRing (ι : Type u) [Fintype ι] : Type u :=
  (MvPolynomial (ι × ι × G) 𝓞) ⧸ SLRingRelations 𝓞 G ι

local notation3:max O "[" G' ", " α "]" => SLRing O G' α
local notation3:max "GL(" α ", " R ")" => (GeneralLinearGroup α R)
local notation3:max "Hom_grp(" G₁ ", " G₂ ")" => (G₁ →* G₂)
local notation3:max "Hom_alg(" O "; " A "," A' ")" => (A →ₗ[O] A')

-- Choose any basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
def pbar' := GL_map_of_representation_of_basis ρbar 𝓫

variable (A : 𝓒 𝓞)

def SLMap : Hom_alg(𝓞; 𝓞[G, ι], A) ≃ Hom_grp(G, GL(ι, A)) where
  toFun f := _
  invFun ρ := _
  left_inv := sorry
  right_inv := sorry

theorem Lift.functor_isCorepresentable : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end G_finite

section G_profinite -- Section 3.2 Smit & Lenstra

end G_profinite
