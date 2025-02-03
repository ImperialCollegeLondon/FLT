import FLT.Deformations.Algebra.Category.AlgebraCat.CommAlgebraCat
import FLT.Deformations.Algebra.InverseLimit
import FLT.Mathlib.RingTheory.Ideal.Quotient.Defs
import FLT.Mathlib.RingTheory.LocalRing.Defs
import FLT.Mathlib.Algebra.Group.Units.Hom
import FLT.Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

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

section IsResidueAlgebra

variable (A : CommAlgebraCat 𝓞) [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]

-- modMap : O --Under.hom-> A --IsLocalRing.residue-> k A
variable (𝓞) in
abbrev modMap : 𝓞 →+* 𝓴 A :=
   (IsLocalRing.residue A).comp (algebraMap 𝓞 A)

variable (𝓞) in
class IsResidueAlgebra : Prop where
  isSurjective : Surjective (modMap 𝓞 A)

variable [IsResidueAlgebra 𝓞 A]

variable (𝓞) in
noncomputable def IsResidueAlgebra.toRingEquiv : (𝓴 A) ≃+* (𝓴 𝓞) where
    toFun ka := IsLocalRing.residue (R := 𝓞) (surjInv (f := modMap 𝓞 A)
      (IsResidueAlgebra.isSurjective (A := A)) ka)
    invFun ko := IsLocalRing.ResidueField.lift (modMap 𝓞 A) ko
    left_inv := by
      simp [LeftInverse]
      rintro x
      rw [← RingHom.comp_apply]
      change ((IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)) (surjInv _ x) = x
      rw [Function.surjInv_eq (f := (⇑(IsLocalRing.residue A) ∘ (algebraMap 𝓞 A)))]
    right_inv := by
      simp [Function.RightInverse, LeftInverse]
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

noncomputable instance : Algebra (𝓴 𝓞) (𝓴 A) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A).symm

noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) :=
  RingHom.toAlgebra (IsResidueAlgebra.toRingEquiv 𝓞 A)

instance : RingHomInvPair
  (algebraMap (𝓴 A) (𝓴 𝓞))
  (algebraMap (𝓴 𝓞) (𝓴 A)) where
    comp_eq := sorry
    comp_eq₂ := sorry

instance : RingHomInvPair
  (algebraMap (𝓴 𝓞) (𝓴 A))
  (algebraMap (𝓴 A) (𝓴 𝓞)) where
    comp_eq := sorry
    comp_eq₂ := sorry

end IsResidueAlgebra

section IsProartinian

variable {A : Type*} [CommRing A]

variable (A) in
def ArtinianQuotientIdeal := {a : Ideal A // IsArtinianRing (A ⧸ a)}

instance : Coe (ArtinianQuotientIdeal A) (Ideal A) where
  coe a := a.1

instance : Preorder (ArtinianQuotientIdeal A) where
  le a b := (a : Ideal A) ≥ (b : Ideal A)
  lt a b := (a : Ideal A) > (b : Ideal A)
  le_refl := by simp
  le_trans := by
    rintro a b c hab hbc
    simp_all
    exact le_trans hbc hab

abbrev proartinianCompletion_obj {A : Type*} [CommRing A] (a : ArtinianQuotientIdeal A) :=
  A ⧸ (a : Ideal A)

def ideal_le_of_artinianQuotientIdeal_le {A : Type*} [CommRing A] {a b : ArtinianQuotientIdeal A}
    (h : a ≤ b) : (b : Ideal A) ≤ (a : Ideal A) :=
  by
    simp [LE.le] at h
    exact h

def proartinianCompletion_map {A : Type*} [CommRing A] {a b : ArtinianQuotientIdeal A}
    (h : a ≤ b) :
  (proartinianCompletion_obj b) →+* (proartinianCompletion_obj a) :=
    Ideal.ringHomOfQuot_of_le (ideal_le_of_artinianQuotientIdeal_le h)

abbrev proartinianCompletion (A : Type*) [CommRing A] :=
  Ring.InverseLimit
    (fun (a : ArtinianQuotientIdeal A) => proartinianCompletion_obj a)
    proartinianCompletion_map

noncomputable def diagonalMap (A : Type*) [CommRing A] : A →+* proartinianCompletion A :=
  Ring.InverseLimit.map_of_maps
    proartinianCompletion_map
    (fun a ↦ Ideal.Quotient.mk (a : Ideal A))
    (by
      rintro a b h
      unfold proartinianCompletion_map
      aesop
    )

def diagonalMap_toComponent (A : Type*) [CommRing A] (a : ArtinianQuotientIdeal A) :
  A →+* proartinianCompletion_obj a := algebraMap _ _

variable (𝓞) in
class IsProartinian (A : Type*) [CommRing A] : Prop where
  pro_artin : Function.Bijective (diagonalMap A)

instance (A : Type*) [CommRing A] [IsProartinian A] : TopologicalSpace A := .generateFrom
  {U | ∃ a : ArtinianQuotientIdeal A, ∃ V : Set (proartinianCompletion_obj a),
    U = (diagonalMap_toComponent A a) ⁻¹' V}

instance (A : Type*) [CommRing A] [IsProartinian A] : TopologicalRing A where
  continuous_add := sorry
  continuous_mul := sorry
  continuous_neg := sorry

end IsProartinian
section 𝓒

variable (𝓞) in
def 𝓒_filter (A : CommAlgebraCat 𝓞) : Prop :=
  ∃ (_ : IsLocalRing A),
  ∃ (_ : IsLocalHom (algebraMap 𝓞 A)),
  IsResidueAlgebra 𝓞 A ∧
  IsProartinian A

variable (𝓞) in
def 𝓒 := FullSubcategory (𝓒_filter 𝓞)

instance : Category (𝓒 𝓞) := by unfold 𝓒; infer_instance

instance : CoeOut (𝓒 𝓞) (CommAlgebraCat 𝓞) where coe A := A.obj

variable (A : 𝓒 𝓞)

instance : IsLocalRing A := by unfold 𝓒 at A; exact A.property.1
instance : IsLocalHom (algebraMap 𝓞 A) := by unfold 𝓒 at A; exact A.property.2.1
instance : IsResidueAlgebra 𝓞 A := by unfold 𝓒 at A; exact A.property.2.2.1
noncomputable instance : Algebra (𝓴 A) (𝓴 𝓞) := by unfold 𝓒 at A; infer_instance
noncomputable instance : Algebra (𝓴 𝓞) (𝓴 A) := by unfold 𝓒 at A; infer_instance
instance : IsProartinian A := by unfold 𝓒 at A; exact A.property.2.2.2

instance : ConcreteCategory (𝓒 𝓞) (· →ₐ[𝓞] ·) := by unfold 𝓒; infer_instance

variable {A} in
def 𝓒.quotient (a : Ideal A) : 𝓒 𝓞 where
  obj := CommAlgebraCat.quotient a
  property := by
    unfold 𝓒_filter
    sorry -- We need 1) quotient of local is local, 2) quotient of localhom is localhom
          -- 3) quotient of residue algebra is residue algebra, 4) quotient of proartinian is proartinian

end 𝓒

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable (A : 𝓒 𝓞)

instance noetherian_deformationCat_topology [IsNoetherianRing A] :
  IsAdic (IsLocalRing.maximalIdeal A) := sorry

instance noetherian_deformationCat_isAdic [IsNoetherianRing A] :
  IsAdicComplete (IsLocalRing.maximalIdeal A) A := sorry

lemma noetherian_deformationCat_continuous {A A' : 𝓒 𝓞} [IsNoetherianRing A]
  (f : A →ₐ[𝓞] A') : Continuous f := sorry

end Noetherian
