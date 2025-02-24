import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.CategoryTheory.Widesubcategory

import FLT.Mathlib.Algebra.InverseLimit

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

variable (𝓞) in
abbrev CommAlgCat := Under (CommRingCat.of 𝓞)

instance : CoeOut (CommAlgCat 𝓞) (CommRingCat) where coe A := A.right

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
abbrev modMap (A : CommAlgCat 𝓞) [IsLocalRing A] : 𝓞 →+* 𝓴 A :=
   (IsLocalRing.residue ↑A.right).comp A.hom

variable (𝓞) in
class IsResidueAlgebra (A : CommAlgCat 𝓞) [IsLocalRing A] : Prop where
  isSurjective : Surjective (modMap 𝓞 A)

variable (𝓞) in
noncomputable def IsResidueAlgebra.toRingEquiv (A : CommAlgCat 𝓞) [IsLocalRing A] [IsLocalHom A.hom]
  [IsResidueAlgebra 𝓞 A] : (𝓴 A) ≃+* (𝓴 𝓞) where
    toFun ka := IsLocalRing.residue (R := 𝓞) (surjInv (f := modMap 𝓞 A)
      (IsResidueAlgebra.isSurjective (A := A)) ka)
    invFun ko := IsLocalRing.ResidueField.lift (modMap 𝓞 A) ko
    left_inv := by
      simp [LeftInverse]
      rintro x
      rw [← RingHom.comp_apply]
      change (⇑(IsLocalRing.residue ↑A.right) ∘ ⇑A.hom) (surjInv _ x) = x
      rw [Function.surjInv_eq (f := (⇑(IsLocalRing.residue ↑A.right) ∘ ⇑A.hom))]
    right_inv := by
      simp [RightInverse, LeftInverse]
      rintro x
      let y := (IsLocalRing.ResidueField.lift (modMap 𝓞 A)) x
      let z := surjInv (IsResidueAlgebra.isSurjective (A := A)) y
      let X := surjInv (IsLocalRing.residue_surjective) x
      have hX_to_x : IsLocalRing.residue 𝓞 X = x := by
        unfold X
        exact surjInv_eq (f := IsLocalRing.residue 𝓞) _ _
      have hy : y = (modMap 𝓞 A) X := by
        unfold y
        rw [← hX_to_x]
        simp
      suffices h : (IsLocalRing.residue 𝓞) z = (IsLocalRing.residue 𝓞) X by
        change (IsLocalRing.residue 𝓞) z = x
        unfold X at h
        rw [surjInv_eq (f := IsLocalRing.residue 𝓞)] at h
        exact h
      sorry
    map_mul' := by
      simp [modMap]
      rintro x y
      rw [← map_mul]
      sorry
    map_add' := by
      simp [modMap]
      rintro x y
      sorry

abbrev ArtinianQuotientIdeal (A : Type*) [CommRing A]
  := {a : Ideal A // IsArtinianRing (A ⧸ a)}

instance {A : Type*} [CommRing A] : Coe (ArtinianQuotientIdeal A) (Ideal A) where
  coe a := a.1

abbrev proartinianCompletion_obj {A : Type*} [CommRing A] (a : ArtinianQuotientIdeal A) :=
  A ⧸ (a : Ideal A)

def proartinianCompletion_map {A : Type*} [CommRing A] {a b : ArtinianQuotientIdeal A} (h : a ≤ b) :
  proartinianCompletion_obj b →+* proartinianCompletion_obj a := sorry

abbrev proartinianCompletion (A : Type*) [CommRing A] :=
  Ring.InverseLimit
  (fun (a : ArtinianQuotientIdeal A) => proartinianCompletion_obj a)
  (fun (a b : ArtinianQuotientIdeal A) (h : a ≤ b)
    => proartinianCompletion_map (A := A) h)

def diagonalMap (A : Type*) [CommRing A] : A →+* proartinianCompletion A := sorry

def diagonalMap_toComponent (A : Type*) [CommRing A] (a : ArtinianQuotientIdeal A) :
  A →+* proartinianCompletion_obj a := algebraMap _ _

variable (𝓞) in
class IsProartinian (A : Type*) [CommRing A] : Prop where
  pro_artin : Function.Bijective (diagonalMap A)

instance (A : CommAlgCat 𝓞) [IsProartinian A] : TopologicalSpace A := .generateFrom
  {U | ∃ a : ArtinianQuotientIdeal A, ∃ V : Set (proartinianCompletion_obj a),
    U = (diagonalMap_toComponent A a) ⁻¹' V}

instance (A : CommAlgCat 𝓞) [IsProartinian A] : TopologicalRing A where
  continuous_add := sorry
  continuous_mul := sorry
  continuous_neg := sorry

variable (𝓞) in
def 𝓒_filter : CommAlgCat 𝓞 → Prop := fun A =>
  ∃ (_ : IsLocalRing A),
  ∃ (_ : IsLocalHom A.hom),
  IsResidueAlgebra 𝓞 A ∧
  IsProartinian A

variable (𝓞) in
def 𝓒_full := FullSubcategory (𝓒_filter 𝓞)

instance : Category (𝓒_full 𝓞) := by unfold 𝓒_full; infer_instance

instance : CoeOut (𝓒_full 𝓞) (CommAlgCat 𝓞) where coe A := A.obj

abbrev ContinuousHoms :=
  (fun {A B : 𝓒_full 𝓞} => fun (f : A ⟶ B) => Continuous f)

instance : CategoryTheory.MorphismProperty.IsMultiplicative

def 𝓒 := WideSubcategory
  (fun {A B : 𝓒_full 𝓞} => fun (f : A ⟶ B) => Continuous f)
  (IsMultiplicative := sorry)


variable (A : 𝓒 𝓞)

instance : Algebra 𝓞 A := by unfold 𝓒 at A; exact A.obj.hom.toAlgebra
instance : IsLocalRing A := by unfold 𝓒 at A; exact A.property.1
instance : IsLocalHom A.obj.hom := by unfold 𝓒 at A; exact A.property.2.1
instance : IsResidueAlgebra 𝓞 A := by unfold 𝓒 at A; exact A.property.2.2.1
noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A)
instance : IsProartinian A := by unfold 𝓒 at A; exact A.property.2.2.2
