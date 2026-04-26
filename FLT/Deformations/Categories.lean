module

public import FLT.Deformations.IsProartinian
public import FLT.Deformations.IsResidueAlgebra
public import Mathlib.Topology.Algebra.Algebra.Equiv

@[expose] public section

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]

/-- A local proartinian algebra is a topological ring that is local and proartinian,
and that the induced map on the residue fields is bijective. -/
class IsLocalProartinianAlgebra
    (R : Type u) [CommRing R] [TopologicalSpace R] [Algebra 𝓞 R] : Prop extends
  IsTopologicalRing R, IsLocalRing R, IsProartinian R,
  IsLocalHom (algebraMap 𝓞 R), IsResidueAlgebra 𝓞 R

section 𝓞_is_local

-- if 𝓞 admits a local proartinian algebra then 𝓞 is itself local.
example (𝓞 : Type u) [CommRing 𝓞]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝓞 R] [IsLocalProartinianAlgebra 𝓞 R] : IsLocalRing 𝓞 := by
  let φ : 𝓞 →+* R := algebraMap 𝓞 R
  have hφ : IsLocalHom φ := IsLocalProartinianAlgebra.toIsLocalHom
  have hR : Nontrivial R := IsLocalRing.toNontrivial
  haveI : Nontrivial 𝓞 := RingHom.domain_nontrivial φ
  apply of_nonunits_add
  intros a b ha hb
  rw [mem_nonunits_iff, ← isUnit_map_iff φ, ← mem_nonunits_iff] at ha hb ⊢
  rw [map_add]
  -- maximalIdeal R = nonunits R is rfl as sets
  exact Ideal.add_mem (IsLocalRing.maximalIdeal R) ha hb

-- If 𝓞 is a local ring complete wrt m-adic topology
-- then 𝓞 → R is continuous.
example (𝓞 : Type u) [CommRing 𝓞] [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞]
    [IsLocalRing 𝓞] [IsAdicTopology 𝓞]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝓞 R] [IsLocalProartinianAlgebra 𝓞 R] : Continuous (algebraMap 𝓞 R) :=
  isContinuous_of_isProartinian_of_isLocalHom _

end 𝓞_is_local

/-- The category of local proartinian algebras over `𝓞` with fixed residue field `𝕜`. -/
structure ProartinianCat where
  /-- Underlying set of a `ProartinianCat` -/
  carrier : Type u
  /-- ring structure of a `ProartinianCat` -/
  [commRing : CommRing carrier]
  /-- topological space structure of a `ProartinianCat` -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- algebra structure of a `ProartinianCat` -/
  [algebra : Algebra 𝓞 carrier]
  [isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 carrier]

local notation3:max "𝓒" 𝓞 => ProartinianCat 𝓞

namespace ProartinianCat

attribute [instance] commRing algebra topologicalSpace isLocalProartinianAlgebra

initialize_simps_projections ProartinianCat (-commRing, -algebra, -topologicalSpace)

instance : CoeSort (ProartinianCat 𝓞) (Type u) := ⟨carrier⟩

attribute [coe] ProartinianCat.carrier

/-- Make a `ProartinianCat` from an unbundled algebra. -/
abbrev of (X : Type u) [CommRing X] [Algebra 𝓞 X]
    [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X] :
    ProartinianCat 𝓞 :=
  ⟨X⟩

lemma coe_of (X : Type u) [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X]
    [IsLocalProartinianAlgebra 𝓞 X] :
    of 𝓞 X = X := rfl

variable {𝓞} in
/-- The type of morphisms in `ProartinianCat 𝓞`. -/
@[ext]
structure Hom (A B : ProartinianCat 𝓞) where
  /-- The underlying algebra map. -/
  hom : A →A[𝓞] B

instance : Category (ProartinianCat 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance (A B : ProartinianCat 𝓞) (f : A ⟶ B) : IsLocalHom f.hom := by
  convert isLocalHom_of_isContinuous_of_isProartinian f.hom.toRingHom f.hom.cont
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

variable {𝓞} in
/-- Typecheck an `ContinuousAlgHom` as a morphism in `ProartinianCat`. -/
abbrev ofHom {A B : Type u}
    [CommRing A] [Algebra 𝓞 A] [TopologicalSpace A] [IsLocalProartinianAlgebra 𝓞 A]
    [CommRing B] [Algebra 𝓞 B] [TopologicalSpace B] [IsLocalProartinianAlgebra 𝓞 B]
    (f : A →A[𝓞] B) :
    of 𝓞 A ⟶ of 𝓞 B := ⟨f⟩

variable {𝓞}

variable {X Y Z : Type u}
  [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X]
  [CommRing Y] [Algebra 𝓞 Y] [TopologicalSpace Y] [IsLocalProartinianAlgebra 𝓞 Y]
  [CommRing Z] [Algebra 𝓞 Z] [TopologicalSpace Z] [IsLocalProartinianAlgebra 𝓞 Z]

variable {A B C : ProartinianCat 𝓞}

@[simp]
lemma hom_id : (𝟙 A :).hom = ContinuousAlgHom.id 𝓞 A := rfl

lemma id_apply (x) : (𝟙 A :).hom x = x := rfl

@[simp]
lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (x) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[ext]
lemma hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

lemma hom_ofHom (f : X →A[𝓞] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id : ofHom (ContinuousAlgHom.id 𝓞 X) = 𝟙 (of 𝓞 X) := rfl

@[simp]
lemma ofHom_comp (f : X →A[𝓞] Y) (g : Y →A[𝓞] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/-- Build an isomorphism in the category `ProartinianCat R` from a
  `ContinuousAlgEquiv` between `Algebra`s. -/
@[simps]
def ofEquiv (e : X ≃A[𝓞] Y) : of 𝓞 X ≅ of 𝓞 Y where
  hom := ofHom (e : X →A[𝓞] Y)
  inv := ofHom (e.symm : Y →A[𝓞] X)

/-- Build a `ContinuousAlgEquiv` from an isomorphism in the category `ProartinianCat R`. -/
def _root_.CategoryTheory.Iso.toContinuousAlgEquiv (i : A ≅ B) : A ≃A[𝓞] B where
  __ := i.hom.hom
  invFun := i.inv.hom
  left_inv _ := by simp [← comp_apply]
  right_inv _ := by simp [← comp_apply]
  continuous_toFun := i.hom.hom.cont
  continuous_invFun := i.inv.hom.2

section self

variable [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]

/-- `𝓞` as a proartinian local algebra. -/
def self : 𝓒 𝓞 where
  carrier := 𝓞
  topologicalSpace := (maximalIdeal 𝓞).adicTopology
  isLocalProartinianAlgebra :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : CompactSpace 𝓞 := compactSpace_of_finite_residueField
    ⟨⟩

instance : IsAdicTopology (self (𝓞 := 𝓞)) := ⟨rfl⟩

/-- The structure map of a proartinian local algebra as a morphism in the category. -/
def fromSelf (R : ProartinianCat 𝓞) : self ⟶ R where
  hom :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : IsAdicTopology 𝓞 := ⟨rfl⟩
    ⟨Algebra.ofId _ _, isContinuous_of_isProartinian_of_isLocalHom (algebraMap 𝓞 R)⟩

instance (R : ProartinianCat 𝓞) : Unique (self ⟶ R) := by
  refine ⟨⟨fromSelf R⟩, fun f ↦ ?_⟩
  ext : 1
  apply ContinuousAlgHom.coe_inj.mp
  ext

/-- `𝓞` is initial in `ProartinianCat`. -/
def isInitialSelf : IsInitial (self (𝓞 := 𝓞)) := .ofUnique _

end self

section residueField

variable [IsLocalRing 𝓞]

set_option backward.isDefEq.respectTransparency false in
/-- The residue field `𝕜` as a proartinian local algebra. -/
def residueField : 𝓒 𝓞 where
  carrier := ResidueField 𝓞
  topologicalSpace := ⊥
  isLocalProartinianAlgebra :=
    letI : TopologicalSpace (ResidueField 𝓞) := ⊥
    letI : DiscreteTopology (ResidueField 𝓞) := ⟨rfl⟩
    letI : IsResidueAlgebra 𝓞 (ResidueField 𝓞) := by delta ResidueField; infer_instance
    ⟨⟩

instance : DiscreteTopology (residueField (𝓞 := 𝓞)) := ⟨rfl⟩

noncomputable
instance : Field (residueField (𝓞 := 𝓞)) := inferInstanceAs (Field (ResidueField 𝓞))

set_option backward.isDefEq.respectTransparency false in
/-- The quotient map of a `ProartinianCat` to the residue field. -/
noncomputable
def toResidueField (R : ProartinianCat 𝓞) : R ⟶ residueField where
  hom := ⟨(IsResidueAlgebra.algEquiv 𝓞 R).symm.toAlgHom.comp (IsScalarTower.toAlgHom 𝓞 R _), by
    refine (RingHom.continuous_iff_isOpen_ker (β := residueField) (f := AlgHom.toRingHom _)).mpr ?_
    dsimp [residueField]
    rw [AlgHom.comp_toRingHom, RingHom.ker_comp_of_injective]
    · simp only [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq, residue]
      rw [Ideal.mk_ker]
      exact isOpen_maximalIdeal_of_isProartinian
    · exact (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective⟩

lemma toResidueField_surjective (R : ProartinianCat 𝓞) :
    Function.Surjective (toResidueField R).hom :=
  (IsResidueAlgebra.algEquiv 𝓞 R).symm.surjective.comp Ideal.Quotient.mk_surjective

lemma ker_toResidueField (R : ProartinianCat 𝓞) :
    RingHom.ker (toResidueField R).hom = maximalIdeal R :=
  (RingHom.ker_comp_of_injective _ (f := (IsResidueAlgebra.algEquiv 𝓞 R).symm.toRingHom)
    (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective).trans Ideal.mk_ker

lemma to_residueField_apply {R : 𝓒 𝓞} (f : R ⟶ residueField) (r : R.carrier) :
    f.hom r = residue _ (IsResidueAlgebra.preimage 𝓞 r)  := by
  trans f.hom (algebraMap _ _ (IsResidueAlgebra.preimage 𝓞 r))
  · rw [← sub_eq_zero, ← map_sub, ← not_ne_iff,
      ← @isUnit_iff_ne_zero _ _ (f.hom (r - (algebraMap 𝓞 ↑R) (IsResidueAlgebra.preimage 𝓞 r)))]
    change ¬IsUnit (f.hom.toRingHom _)
    rw [isUnit_map_iff f.hom.toRingHom, ← mem_nonunits_iff, ← mem_maximalIdeal]
    exact IsResidueAlgebra.preimage_spec _ _
  · erw [AlgHom.commutes]; rfl

noncomputable
instance (R : ProartinianCat 𝓞) : Unique (R ⟶ residueField) := by
  refine ⟨⟨toResidueField R⟩, fun f ↦ ?_⟩
  ext
  simp [to_residueField_apply]

/-- `𝕜` is initial in `ProartinianCat`. -/
noncomputable
def isTerminalResidueField : IsTerminal (residueField (𝓞 := 𝓞)) := .ofUnique _

end residueField

end ProartinianCat

end Deformation
