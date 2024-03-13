/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.CommAlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits

#align_import algebra.category.Algebra.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace CommAlgebraCat

variable {R : Type u} [CommRing R]

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ CommAlgebraCatMax.{v, w} R) (j) :
    Semiring ((F ⋙ forget (CommAlgebraCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
#align Algebra.semiring_obj CommAlgebraCat.semiringObj

instance algebraObj (F : J ⥤ CommAlgebraCatMax.{v, w} R) (j) :
    Algebra R ((F ⋙ forget (CommAlgebraCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)
#align Algebra.algebra_obj CommAlgebraCat.algebraObj

/-- The flat sections of a functor into `CommAlgebraCat R` form a submodule of all sections.
-/
def sectionsSubalgebra (F : J ⥤ CommAlgebraCatMax.{v, w} R) : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (CommAlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCatMax.{v, w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).commutes r }
#align Algebra.sections_subalgebra CommAlgebraCat.sectionsSubalgebra

instance limitSemiring (F : J ⥤ CommAlgebraCatMax.{v, w} R) :
    Ring.{max v w} (Types.limitCone.{v, w} (F ⋙ forget (CommAlgebraCatMax.{v, w} R))).pt :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)
#align Algebra.limit_semiring CommAlgebraCat.limitSemiring

instance limitAlgebra (F : J ⥤ CommAlgebraCatMax.{v, w} R) :
    Algebra R (Types.limitCone (F ⋙ forget (CommAlgebraCatMax.{v, w} R))).pt :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)
#align Algebra.limit_algebra CommAlgebraCat.limitAlgebra

/-- `limit.π (F ⋙ forget (CommAlgebraCat R)) j` as a `AlgHom`. -/
def limitπAlgHom (F : J ⥤ CommAlgebraCatMax.{v, w} R) (j) :
    (Types.limitCone (F ⋙ forget (CommAlgebraCat R))).pt →ₐ[R]
      (F ⋙ forget (CommAlgebraCatMax.{v, w} R)).obj j :=
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (CommAlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCat.{max v w}) j with
    commutes' := fun _ => rfl }
#align Algebra.limit_π_alg_hom CommAlgebraCat.limitπAlgHom

-- namespace HasLimits

-- -- The next two definitions are used in the construction of `HasLimits (CommAlgebraCat R)`.
-- -- After that, the limits should be constructed using the generic limits API,
-- -- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
-- /-- Construction of a limit cone in `CommAlgebraCat R`.
-- (Internal use only; use the limits API.)
-- -/
-- def limitCone (F : J ⥤ CommAlgebraCatMax.{v, w} R) : Cone F where
--   pt := CommAlgebraCat.of R (Types.limitCone (F ⋙ forget _)).pt
--   π :=
--     { app := limitπAlgHom F
--       naturality := fun _ _ f =>
--         AlgHom.coe_fn_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
-- #align Algebra.has_limits.limit_cone CommAlgebraCat.HasLimits.limitCone

-- /-- Witness that the limit cone in `CommAlgebraCat R` is a limit cone.
-- (Internal use only; use the limits API.)
-- -/
-- def limitConeIsLimit (F : J ⥤ CommAlgebraCatMax.{v, w} R) : IsLimit (limitCone.{v, w} F) := by
--   refine'
--     IsLimit.ofFaithful (forget (CommAlgebraCat R)) (Types.limitConeIsLimit.{v, w} _)
--       -- Porting note: in mathlib3 the function term
--       -- `fun v => ⟨fun j => ((forget (CommAlgebraCat R)).mapCone s).π.app j v`
--       -- was provided by unification, and the last argument `(fun s => _)` was `(fun s => rfl)`.
--       (fun s => ⟨⟨⟨⟨fun v => ⟨fun j => ((forget (CommAlgebraCat R)).mapCone s).π.app j v, _⟩,
--          _⟩, _⟩, _, _⟩, _⟩)
--       (fun s => _)
--   · intro j j' f
--     exact DFunLike.congr_fun (Cone.w s f) v
--   · -- Porting note: we could add a custom `ext` lemma here.
--     apply Subtype.ext
--     ext j
--     simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
--       forget_map_eq_coe]
--     -- This used to be as below but we need `erw` after leanprover/lean4#2644
--     -- simp [forget_map_eq_coe, AlgHom.map_one, Functor.mapCone_π_app]
--     erw [map_one]
--     rfl
--   · intro x y
--     apply Subtype.ext
--     ext j
--     simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
--       forget_map_eq_coe]
--     -- This used to be as below, but we need `erw` after leanprover/lean4#2644
--     -- simp [forget_map_eq_coe, AlgHom.map_mul, Functor.mapCone_π_app]
--     erw [map_mul]
--     rfl
--   · simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
--       forget_map_eq_coe]
--     -- The below `simp` was enough before leanprover/lean4#2644
--     -- simp [forget_map_eq_coe, AlgHom.map_zero, Functor.mapCone_π_app]
--     apply Subtype.ext
--     dsimp
--     funext u
--     erw [map_zero]
--     rfl
--   · intro x y
--     simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
--       forget_map_eq_coe]
--     -- The below `simp` was enough before leanprover/lean4#2644
--     -- simp [forget_map_eq_coe, AlgHom.map_add, Functor.mapCone_π_app]
--     apply Subtype.ext
--     dsimp
--     funext u
--     erw [map_add]
--     rfl
--   · intro r
--     apply Subtype.ext
--     ext j
--     exact (s.π.app j).commutes r
--   · rfl
-- #align Algebra.has_limits.limit_cone_is_limit CommAlgebraCat.HasLimits.limitConeIsLimit

-- end HasLimits

-- open HasLimits

-- -- Porting note: mathport translated this as `irreducible_def`, but as `HasLimitsOfSize`
-- -- is a `Prop`, declaring this as `irreducible` should presumably have no effect
-- /-- The category of R-algebras has all limits. -/
-- lemma hasLimitsOfSize : HasLimitsOfSize.{v, v} (CommAlgebraCatMax.{v, w} R) :=
--   { has_limits_of_shape := fun _ _ =>
--     { has_limit := fun F => HasLimit.mk
--         { cone := limitCone F
--           isLimit := limitConeIsLimit F } } }
-- #align Algebra.has_limits_of_size CommAlgebraCat.hasLimitsOfSize

-- instance hasLimits : HasLimits (CommAlgebraCat.{w} R) :=
--   CommAlgebraCat.hasLimitsOfSize.{w, w, u}
-- #align Algebra.has_limits CommAlgebraCat.hasLimits

-- /-- The forgetful functor from R-algebras to rings preserves all limits.
-- -/
-- instance forget₂RingPreservesLimitsOfSize :
--     PreservesLimitsOfSize.{v, v} (forget₂ (CommAlgebraCatMax.{v, w} R) RingCatMax.{v, w}) where
--   preservesLimitsOfShape :=
--     { preservesLimit :=
--         preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
--           (RingCat.limitConeIsLimit.{v, w}
--             (_ ⋙ forget₂ (CommAlgebraCatMax.{v, w} R) RingCatMax.{v, w})) }
-- #align Algebra.forget₂_Ring_preserves_limits_of_size CommAlgebraCat.forget₂RingPreservesLimitsOfSize

-- instance forget₂RingPreservesLimits : PreservesLimits (forget₂ (CommAlgebraCat R) RingCat.{w}) :=
--   CommAlgebraCat.forget₂RingPreservesLimitsOfSize.{w, w}
-- #align Algebra.forget₂_Ring_preserves_limits CommAlgebraCat.forget₂RingPreservesLimits

-- /-- The forgetful functor from R-algebras to R-modules preserves all limits.
-- -/
-- instance forget₂ModulePreservesLimitsOfSize : PreservesLimitsOfSize.{v, v}
--     (forget₂ (CommAlgebraCatMax.{v, w} R) (ModuleCatMax.{v, w} R)) where
--   preservesLimitsOfShape :=
--     { preservesLimit :=
--         preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
--           (ModuleCat.HasLimits.limitConeIsLimit
--             (_ ⋙ forget₂ (CommAlgebraCatMax.{v, w} R) (ModuleCatMax.{v, w} R))) }
-- #align Algebra.forget₂_Module_preserves_limits_of_size CommAlgebraCat.forget₂ModulePreservesLimitsOfSize

-- instance forget₂ModulePreservesLimits :
--     PreservesLimits (forget₂ (CommAlgebraCat R) (ModuleCat.{w} R)) :=
--   CommAlgebraCat.forget₂ModulePreservesLimitsOfSize.{w, w}
-- #align Algebra.forget₂_Module_preserves_limits CommAlgebraCat.forget₂ModulePreservesLimits

-- /-- The forgetful functor from R-algebras to types preserves all limits.
-- -/
-- instance forgetPreservesLimitsOfSize :
--     PreservesLimitsOfSize.{v, v} (forget (CommAlgebraCatMax.{v, w} R)) where
--   preservesLimitsOfShape :=
--     { preservesLimit :=
--        preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
--           (Types.limitConeIsLimit (_ ⋙ forget _)) }
-- #align Algebra.forget_preserves_limits_of_size CommAlgebraCat.forgetPreservesLimitsOfSize

-- instance forgetPreservesLimits : PreservesLimits (forget (CommAlgebraCat.{w} R)) :=
--   CommAlgebraCat.forgetPreservesLimitsOfSize.{w, w}
-- #align Algebra.forget_preserves_limits CommAlgebraCat.forgetPreservesLimits

-- end CommAlgebraCat
