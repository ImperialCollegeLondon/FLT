import Mathlib

universe u

open CategoryTheory Function Ring Topology
open scoped TensorProduct

section Definitions

-- Kevin thinks this could WLOG be 𝓞 = WittVectors(𝓴)
-- TODO(jlcontreras): Is it true that
--   Any topological local algebra A ≃ₜ limproj (its artinian quotients with discrete topology)
--   with residue field k (by the canonical map),
--   has a natural algebra structure over WittVectors(𝓴)
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (𝓞) in
def CommAlgCat := Under (CommRingCat.of 𝓞)

variable (𝓞) in
instance : Coe (CommAlgCat 𝓞) (CommRingCat) where
  coe A := A.right

def IsResidueAlgebra (A : CommAlgCat 𝓞) [IsLocalRing A.right] : Prop :=
  Surjective (RingHom.comp (IsLocalRing.residue A.right) A.hom)

def IsProartinian (_ : CommAlgCat 𝓞) : Prop := True

variable (𝓞) in
def 𝓒 := FullSubcategory (fun (A : CommAlgCat 𝓞) => by
  exact IsLocalRing A.right
  ∧ IsLocalHom A.hom
  -- ∧ IsResidueAlgebra A How to make typeclass inference synthesize IsLocalRing A.right, when its
  -- inside the and!
  ∧ IsProartinian A)


variable (A : 𝓒 𝓞)
variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable {V : Type u} [AddCommMonoid V]
variable [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

structure Lift where
  W: Type*
  [addCommMonoid : AddCommMonoid W]
  [module : Module A W]
  [free : Module.Free A W]
  [finite : Module.Finite A W]
  ρ: Representation A G W
  is_lift: Bijective (fun (w : W ⊗[A] (𝓴 𝓞)) => (0: V))


end Definitions

#min_imports
