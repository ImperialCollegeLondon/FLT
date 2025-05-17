import FLT.Deformations.Subfunctor
import Mathlib
import FLT.Deformations.Categories

open CategoryTheory IsLocalRing

namespace Deformation

universe u

variable {n : Type} [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

variable (n) in
/-- `repnFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)`. -/
def repnFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := G →ₜ* GL n R
  map {R S} f ρ := .comp (Units.mapₜ f.hom.mapMatrix.toContinuousMonoidHom) ρ

omit [IsLocalRing 𝓞] in
@[simp]
lemma repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl

variable {G 𝓞} in
/-- Turn an element in `repnFunctor` into an actual `Representation`. -/
def toRepresentation {R} (ρ : (repnFunctor n G 𝓞).obj R) :
    Representation R G (n → R) :=
  (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ.toMonoidHom)

variable (n)

/-- `repnQuotFunctor n G 𝓞` is the functor taking `R` to continuous reps `G → GLₙ(R)` up to
conjucation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def repnQuotFunctor : ProartinianCat 𝓞 ⥤ Type u where
  obj R := MulAction.orbitRel.Quotient ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))
    (G →ₜ* GL n R)
  map {R S} f := Quotient.map ((repnFunctor n G 𝓞).map f) (by
    rintro _ ρ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨.toConjAct (Matrix.GeneralLinearGroup.map f.hom.toRingHom g.ofConjAct), ?_⟩, ?_⟩
    · simpa [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
        ← AlgHom.comp_toRingHom, ← ContinuousAlgHom.coe_comp, ← ProartinianCat.hom_comp,
        Subsingleton.elim _ R.toResidueField]
    · obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
      ext1 γ
      simp [ConjAct.toConjAct_smul, ← map_inv, -ConjAct.ofConjAct_inv, ← map_mul])
  map_id _ := by ext ⟨_⟩; rfl
  map_comp _ _ := by ext ⟨_⟩; rfl

/-- The quotient map taking representations to "representations up to equivalence". -/
noncomputable
def toRepnQuot : repnFunctor n G 𝓞 ⟶ repnQuotFunctor n G 𝓞 where
  app _ := Quotient.mk''
  naturality _ _ _ := rfl

/-- `liftFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`. -/
noncomputable
def liftFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) : Subfunctor (repnFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {ρ}

/-- `deformationFunctor n G 𝓞` is the functor taking `R` to lifts `G → GLₙ(R)` of `ρ : G → GLₙ(𝕜)`,
up to conjucation by some `γ` in the kernel of `GLₙ(R) → GLₙ(𝕜)`. -/
noncomputable
def deformationFunctor (ρ : (repnFunctor n G 𝓞).obj .residueField) :
    Subfunctor (repnQuotFunctor n G 𝓞) :=
  .ofIsTerminal _ ProartinianCat.isTerminalResidueField {(toRepnQuot n G 𝓞).app _ ρ}

end Deformation
