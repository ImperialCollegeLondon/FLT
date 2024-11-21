import Mathlib

universe u
open Matrix Function
open scoped TensorProduct


def GL_map_of_representation_of_basis {R V G ι: Type u} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* GeneralLinearGroup ι R :=
  sorry

instance module_of_extension_of_constants (R T M : Type u) [CommRing R] [CommRing T]
  [AddCommGroup M] [Module R M] [Algebra R T]: Module T (M ⊗[R] T) := by
  sorry

section G_finite

variable {G : Type u} [Group G] [Finite G]

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u} [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

variable {A : Type u} [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]
variable (match_residue: (𝓴 𝓞) ≃+* (𝓴 A))
variable (match_residue_by: RingHom.comp (IsLocalRing.residue A) (algebraMap 𝓞 A) =
  RingHom.comp match_residue (IsLocalRing.residue 𝓞))

variable {W : Type u} [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
variable (ρ : Representation A G W)

instance : Module (𝓴 A) V := sorry

variable (W) in
def extend_ctts : W →+ (W ⊗[A] (𝓴 A)) := sorry
variable (W V) in
def mod_ctts : (W ⊗[A] (𝓴 A)) →+[𝓴 A] V  := sorry
variable (W V) in
def representation_mod : W →+ V :=
  AddMonoidHom.comp (mod_ctts V W (A := A)) (extend_ctts W (A := A))

variable (is_lift : Bijective (mod_ctts V W (A := A)))
variable (is_lift_ρ : ∀ g : G, ∀ w : W, ρbar g (representation_mod V W (A := A) w)
  = representation_mod V W (A := A) (ρ g w))


-- Choose a basis of V and, by Nakayama, this gives you a compatible base of W
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓑 : Basis ι (𝓴 𝓞) V)
def pbar' :=  GL_map_of_representation_of_basis ρbar 𝓑


end G_finite

section G_profinite


end G_profinite
