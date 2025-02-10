import FLT.Deformation.Algebra.Category.AlgebraCat.CommAlgebraCat
import FLT.Deformation.Proartinian
import FLT.Deformation.ResidueAlgebra
import FLT.Mathlib.Algebra.Group.Units.Hom

universe u

open CategoryTheory Function
open scoped TensorProduct

namespace Deformation

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable (𝓞) in
def BaseCat_filter (A : CommAlgebraCat 𝓞) : Prop :=
  ∃ (_ : IsLocalRing A),
  ∃ (_ : IsLocalHom (algebraMap 𝓞 A)),
  IsResidueAlgebra 𝓞 A ∧
  IsProartinian A

variable (𝓞) in
def BaseCat := FullSubcategory (BaseCat_filter 𝓞)

notation3:max "𝓒" 𝓞 => BaseCat 𝓞

namespace BaseCat

instance : Category (𝓒 𝓞) := by unfold BaseCat; infer_instance

instance : CoeOut (𝓒 𝓞) (CommAlgebraCat 𝓞) where coe A := A.obj

variable (A : 𝓒 𝓞)

instance : IsLocalRing A := by unfold BaseCat at A; exact A.property.1
instance : IsLocalHom (algebraMap 𝓞 A) := by unfold BaseCat at A; exact A.property.2.1
instance : IsResidueAlgebra 𝓞 A := by unfold BaseCat at A; exact A.property.2.2.1
noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) := by unfold BaseCat at A; infer_instance
noncomputable instance : Algebra (𝓴 𝓞) (𝓴 A) := by unfold BaseCat at A; infer_instance
instance : IsProartinian A := by unfold BaseCat at A; exact A.property.2.2.2

instance : ConcreteCategory (𝓒 𝓞) (· →ₐ[𝓞] ·) := by unfold BaseCat; infer_instance

variable {A} in
def quotient (a : Ideal A) : 𝓒 𝓞 where
  obj := CommAlgebraCat.of 𝓞 (A ⧸ a)
  property := by
    unfold BaseCat_filter
    simp only [exists_and_left, exists_prop, exists_and_right]
    split_ands
    . use isLocalRing_of_quotient a
      infer_instance
    . have h := isLocalHom_of_quotient (algebraMap 𝓞 A) a
      simp at h
      exact h
    . infer_instance

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable (A : 𝓒 𝓞) [IsNoetherianRing A]

instance noetherian_topology
    : IsAdic (IsLocalRing.maximalIdeal A) := by
  exact IsProartinian.noetherian_topology ↑A.obj

instance noetherian_isAdic
    : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
  exact IsProartinian.noetherian_isAdic ↑A.obj

lemma noetherian_continuous (A' : 𝓒 𝓞) (f : A →ₐ[𝓞] A')
    : Continuous f := by
  exact IsProartinian.noetherian_continuous ↑A.obj ↑A'.obj f

end Noetherian

end BaseCat

end Deformation
