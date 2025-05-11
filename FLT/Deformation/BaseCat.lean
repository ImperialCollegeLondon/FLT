import FLT.Deformation.IsProartinianRing
import FLT.Deformation.IsResidueAlgebra
import FLT.Mathlib.Algebra.Group.Units.Hom
import FLT.Deformation.Topology.Algebra.OpenIdeal

universe v u

#exit

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u)
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [IsProartinianRing 𝓞]

scoped notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

structure BaseCat where
  carrier : Type v
  [isCommRing : CommRing carrier]
  [isAlgebra : Algebra 𝓞 carrier]
  [isLocalRing : IsLocalRing carrier]
  [isLocalHom : IsLocalHom (algebraMap 𝓞 carrier)]
  [isResidueAlgebra : IsResidueAlgebra 𝓞 carrier]
  [isProartinianRing : IsProartinianRing carrier]

scoped notation3:max "𝓒" 𝓞 => BaseCat 𝓞

-- Porting note: typemax hack to fix universe complaints
/-- An alias for `BaseCat.{max u₁ u₂}`, to deal around unification issues.
Since the universe the ring lives in can be inferred, we put that last. -/
@[nolint checkUnivs]
abbrev BaseCatMax.{v₁, v₂, u₁} (𝓞 : Type u₁) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] :=
  BaseCat.{max v₁ v₂} 𝓞

attribute [instance] BaseCat.isCommRing BaseCat.isAlgebra BaseCat.isLocalRing BaseCat.isLocalHom
  BaseCat.isResidueAlgebra BaseCat.isProartinianRing

initialize_simps_projections BaseCat (-isCommRing, -isAlgebra, -isLocalRing, -isLocalHom,
  -isResidueAlgebra, -isProartinianRing)

namespace BaseCat

instance : CoeSort (BaseCat 𝓞) (Type v) :=
  ⟨BaseCat.carrier⟩

attribute [coe] BaseCat.carrier

abbrev of (X : Type v) [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinianRing X] : BaseCat.{v} 𝓞 :=
  ⟨X⟩

lemma coe_of (X : Type v) [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinianRing X] : (of 𝓞 X : Type v) = X := rfl

variable {𝓞} in
/-- The type of morphisms in `BaseCat 𝓞`. -/
@[ext]
structure Hom (A B : BaseCat.{v} 𝓞) where
  /-- The underlying algebra map. -/
  hom : A →A[𝓞] B
  [isLocalHom : IsLocalHom hom.toRingHom]

attribute [instance] Hom.isLocalHom

-- TODO(jlcontreras): find home
instance ContinuousAlgHom.isLocalHom_id {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [TopologicalSpace A] [IsTopologicalRing A]:
    IsLocalHom (ContinuousAlgHom.id R A).toRingHom :=
  sorry

-- TODO(jlcontreras): find home
instance ContinuousAlgHom.isLocalHom_comp {R A B C : Type*}
    [CommRing R] [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {g : B →A[R] C} {f : A →A[R] B}
    [IsLocalHom g.toRingHom] [IsLocalHom f.toRingHom] :
    IsLocalHom (ContinuousAlgHom.comp g f).toRingHom :=
  sorry

instance : Category (BaseCat.{v} 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨ContinuousAlgHom.comp g.hom f.hom⟩

variable {𝓞} in
/-- Typecheck an `ContinuousAlgHom` as a morphism in `BaseCat`. -/
abbrev ofHom {A B : Type v}
  [CommRing A] [Algebra 𝓞 A] [IsLocalRing A] [IsLocalHom (algebraMap 𝓞 A)]
  [IsResidueAlgebra 𝓞 A] [IsProartinianRing A]
  [CommRing B] [Algebra 𝓞 B] [IsLocalRing B] [IsLocalHom (algebraMap 𝓞 B)]
  [IsResidueAlgebra 𝓞 B] [IsProartinianRing B]
  (f : A →A[𝓞] B) [IsLocalHom f.toRingHom]:
    of 𝓞 A ⟶ of 𝓞 B := ⟨f⟩

instance {A B : BaseCat.{v} 𝓞} : CoeFun (A ⟶ B) fun _ ↦ (A → B) where
  coe f := f.hom

------------------------------------------------------------
variable {𝓞}

variable {X Y Z : Type v}
  [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinianRing X]
  [CommRing Y] [Algebra 𝓞 Y] [IsLocalRing Y] [IsLocalHom (algebraMap 𝓞 Y)]
  [IsResidueAlgebra 𝓞 Y] [IsProartinianRing Y]
  [CommRing Z] [Algebra 𝓞 Z] [IsLocalRing Z] [IsLocalHom (algebraMap 𝓞 Z)]
  [IsResidueAlgebra 𝓞 Z] [IsProartinianRing Z]

variable {A B C : BaseCat.{v} 𝓞}

@[simp]
lemma hom_id : (𝟙 A : A ⟶ A).hom = ContinuousAlgHom.id 𝓞 A := rfl

/- Provided for rewriting. -/
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[ext]
lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
lemma hom_ofHom (f : X →A[𝓞] Y) [IsLocalHom f.toRingHom] : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id : ofHom (ContinuousAlgHom.id 𝓞 X) = 𝟙 (of 𝓞 X) := rfl

@[simp]
lemma ofHom_comp (f : X →A[𝓞] Y) (g : Y →A[𝓞] Z) [IsLocalHom f.toRingHom] [IsLocalHom g.toRingHom]:
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply (f : X →A[𝓞] Y) [IsLocalHom f.toRingHom] (x : X) : ofHom f x = f x := rfl

@[simp]
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

@[simp]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso : of 𝓞 A ≅ A where
  hom := 𝟙 A
  inv := 𝟙 A

variable {X Y : Type u}
  [CommRing X] [Algebra 𝓞 X] [IsLocalRing X] [IsLocalHom (algebraMap 𝓞 X)]
  [IsResidueAlgebra 𝓞 X] [IsProartinianRing X]
  [CommRing Y] [Algebra 𝓞 Y] [IsLocalRing Y] [IsLocalHom (algebraMap 𝓞 Y)]
  [IsResidueAlgebra 𝓞 Y] [IsProartinianRing Y]
variable {A B : BaseCat 𝓞}

/-- Build an isomorphism in the category `BaseCat R` from a `ContinuousAlgEquiv` between `Algebra`s. -/
@[simps]
def _root_.ContinuousAlgEquiv.toContinuousAlgebraIso (e : X ≃A[𝓞] Y)
  [IsLocalHom e.toContinuousAlgHom.toRingHom] [IsLocalHom e.symm.toContinuousAlgHom.toRingHom] : BaseCat.of 𝓞 X ≅ BaseCat.of 𝓞 Y where
  hom := BaseCat.ofHom (e : X →A[𝓞] Y)
  inv := BaseCat.ofHom (e.symm : Y →A[𝓞] X)

/-- Build a `ContinuousAlgEquiv` from an isomorphism in the category `BaseCat R`. -/
@[simps]
def _root_.CategoryTheory.Iso.toContinuousAlgEquiv (i : A ≅ B) : A ≃A[𝓞] B :=
  {i.hom.hom  with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
    continuous_toFun := by continuity}

variable {R : BaseCat 𝓞}

lemma exists_sub_mem_maximalIdeal (r : R.carrier) : ∃ (a : 𝓞), r - algebraMap _ _ a ∈ maximalIdeal _ := by
  obtain ⟨a, ha⟩ := R.isResidueAlgebra.surjective 𝓞 R.carrier (residue _ r)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact ha.symm

noncomputable
def preimage (r : R.carrier) : 𝓞 := (exists_sub_mem_maximalIdeal r).choose

lemma preimage_spec (r : R.carrier) : r - algebraMap _ _ (preimage r) ∈ maximalIdeal _ :=
  (exists_sub_mem_maximalIdeal r).choose_spec

lemma residue_preimage (r : R.carrier) : residue _ (algebraMap _ _ (preimage r)) = residue _ r :=
  (Ideal.Quotient.eq.mpr (preimage_spec r)).symm

lemma residue_preimage_eq_iff {r : R.carrier} {a} :
    residue _ (preimage r) = a ↔ residue _ r = ResidueField.map (algebraMap 𝓞 R.carrier) a := by
  rw [← (R.isResidueAlgebra.bijective 𝓞).1.eq_iff]
  erw [ResidueField.map_residue]
  rw [residue_preimage]
  rfl

def self : 𝓒 𝓞 where
  carrier := 𝓞
  isCommRing := by infer_instance
  isAlgebra := by infer_instance
  isLocalRing := by infer_instance
  isLocalHom := ⟨fun _ ↦ id⟩
  isResidueAlgebra := .mk (by change Surjective (residue 𝓞); exact residue_surjective)
  isProartinianRing := by infer_instance

instance : Inhabited (BaseCat 𝓞) := ⟨self⟩

def fromSelf (R : 𝓒 𝓞) : self ⟶ R :=
  BaseCat.Hom.mk ⟨(Algebra.ofId 𝓞 R.carrier), by sorry⟩  (isLocalHom := ⟨R.isLocalHom.1⟩)

def residueField : 𝓒 𝓞 where
  carrier := ResidueField 𝓞
  isCommRing := by infer_instance
  isAlgebra := by infer_instance
  isLocalRing := by infer_instance
  isLocalHom := .of_surjective _ (by change Surjective (residue 𝓞); exact residue_surjective)
  isResidueAlgebra := sorry
  isProartinianRing := sorry

noncomputable
def toResidueField (R : 𝓒 𝓞) : R ⟶ residueField :=
  BaseCat.Hom.mk
    ⟨
      ⟨(RingEquiv.ofBijective _ R.isResidueAlgebra.bijective).symm.toRingHom.comp (residue _), fun _ ↦
        (R.isResidueAlgebra.bijective 𝓞).1
        ((RingEquiv.ofBijective _ R.isResidueAlgebra.bijective).apply_symm_apply _)⟩,
      by sorry
    ⟩
    (isLocalHom := .of_surjective _ ((RingEquiv.ofBijective _ R.isResidueAlgebra.bijective).symm.surjective.comp residue_surjective))

lemma to_residueField_apply {R : 𝓒 𝓞} (f : R ⟶ residueField) (r : R.carrier) : f.hom r = residue _ (preimage r)  := by
  trans f.hom (algebraMap _ _ (preimage r))
  · rw [← sub_eq_zero, ← map_sub, ← not_ne_iff,
      ← @isUnit_iff_ne_zero _ (inferInstanceAs (GroupWithZero (ResidueField 𝓞)))]
    change ¬IsUnit (f.hom.toRingHom _)
    rw [isUnit_map_iff f.hom.toRingHom, ← mem_nonunits_iff, ← mem_maximalIdeal]
    exact preimage_spec _
  · sorry

lemma to_residueField_ext {R : 𝓒 𝓞} (f₁ f₂ : R ⟶ residueField) : f₁ = f₂ := by
  refine BaseCat.Hom.ext ?_
  ext r
  rw [to_residueField_apply, to_residueField_apply]

def quotient (a : OpenIdeal A) [Nontrivial (A ⧸ a.1)] : BaseCat.{v} 𝓞 where
  carrier := A ⧸ a.1
  isCommRing := by infer_instance
  isAlgebra := by infer_instance
  isLocalRing := by infer_instance
  isLocalHom := by
    have h := IsLocalHom.of_quotient (algebraMap 𝓞 A) a.1
    simp only [Ideal.Quotient.mk_comp_algebraMap] at h
    exact h
  isResidueAlgebra := by infer_instance
  isProartinianRing :=
    IsProartinianRing.instQuotientIdealOfNontrivialOfIsOpenCarrier a.1 a.2

def toQuotient (a : OpenIdeal A) [Nontrivial (A ⧸ a.1)] : A ⟶ (quotient a) where
  hom := {
    toFun := Ideal.Quotient.mkₐ A a.1
    map_one' := by simp
    map_mul' := by simp
    map_zero' := by simp
    map_add' := by simp
    commutes' r := by simp; rfl
    cont := sorry
  }
  isLocalHom := sorry

end BaseCat

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable (A : 𝓒 𝓞) [IsNoetherianRing A]

instance noetherian_topology
    : IsAdic (IsLocalRing.maximalIdeal A) := by
  exact IsProartinianRing.noetherian_topology A

instance noetherian_isAdic
    : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
  exact IsProartinianRing.noetherian_isAdic A

lemma noetherian_continuous (A' : 𝓒 𝓞) (f : A →ₐ[𝓞] A')
    : Continuous f := by
  exact IsProartinianRing.noetherian_continuous A A' f

end Noetherian

end Deformation
