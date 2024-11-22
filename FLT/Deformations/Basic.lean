import Mathlib

universe u

open CategoryTheory Function
open scoped TensorProduct

section Definitions

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (𝓞) in
abbrev CommAlgCat := Under (CommRingCat.of 𝓞)

instance : CoeOut (CommAlgCat 𝓞) (CommRingCat) where coe A := A.right

variable (𝓞) in
class IsResidueAlgebra (A : CommAlgCat 𝓞) [IsLocalRing A] : Prop where
  surjective_residue : Surjective (RingHom.comp (IsLocalRing.residue A) A.hom)

def IsResidueAlgebra.toRingEquiv (A : CommAlgCat 𝓞) [IsLocalRing A] [IsResidueAlgebra 𝓞 A] :
  (𝓴 A) ≃+* (𝓴 𝓞) := sorry


variable (𝓞) in
class IsProartinian (A : CommAlgCat 𝓞) : Prop where
  pro_artin : True

variable (𝓞) in
def 𝓒_filter : CommAlgCat 𝓞 → Prop := fun A =>
  ∃ (_ : IsLocalRing A), IsResidueAlgebra 𝓞 A ∧ IsLocalHom A.hom ∧ IsProartinian 𝓞 A

variable (𝓞) in
def 𝓒 := FullSubcategory (𝓒_filter 𝓞)

instance : Category (𝓒 𝓞) := by unfold 𝓒; infer_instance

instance : CoeOut (𝓒 𝓞) (CommAlgCat 𝓞) where coe A := A.obj

variable (A : 𝓒 𝓞)
instance : Algebra 𝓞 A := by unfold 𝓒 at A; exact A.obj.hom.toAlgebra
instance : IsLocalRing A := by unfold 𝓒 at A; exact A.property.1
instance : IsResidueAlgebra 𝓞 A := by unfold 𝓒 at A; exact A.property.2.1
instance : IsLocalHom A.obj.hom := by unfold 𝓒 at A; exact A.property.2.2.1
instance : IsProartinian 𝓞 A := by unfold 𝓒 at A; exact A.property.2.2.2

instance [IsResidueAlgebra 𝓞 A] : Algebra (𝓴 A) (𝓴 𝓞) := sorry

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]
variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
  [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
  [Module A V] [IsScalarTower A (𝓴 A) V]

variable (ρbar : Representation (𝓴 𝓞) G V)

variable {W: Type u} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]
variable (ρ: Representation A G W)

variable (W V) in
noncomputable def extend_ctts : W →ₗ[A] ((𝓴 A) ⊗[A] W) := (TensorProduct.mk A (𝓴 A) W) (1 : (𝓴 A))

variable (W V) in
noncomputable def mod_ctts : ((𝓴 A) ⊗[A] W) →ₗ[A] V := by
  refine TensorProduct.lift ?_
  sorry

variable (W V) in
noncomputable def representation_mod : W →ₗ[A] V :=
  LinearMap.comp (mod_ctts A V W) (extend_ctts A W)

omit W in
structure Lift where
  W: Type u
  [addCommMonoid : AddCommMonoid W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  ρ: Representation A G W
  is_lift: ∀ g : G, ∀ w : W, ρbar g (representation_mod V W (A := A) w)
      = representation_mod V W (A := A) (ρ g w)

def Lift.isIso : Setoid (Lift A ρbar) where
  r W W' := sorry
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry
  }

def Deformation := Quotient <| Lift.isIso A ρbar

variable (𝓞) in
def Lift.functor : Functor (𝓒 𝓞) (Type u) where
  obj a := sorry--(Lift a ρbar)
  map := sorry

end Definitions

theorem Lift.functor_representable : (Lift.functor 𝓞).IsRepresentable  := sorry
