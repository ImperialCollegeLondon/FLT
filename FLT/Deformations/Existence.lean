import Mathlib

universe u
open Matrix Function TensorProduct RingHom

section G_finite

def GL_map_of_representation_of_basis {R V G ι: Type u} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* GeneralLinearGroup ι R :=
  sorry

variable {G : Type u} [Group G] [Finite G]

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u} [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

variable {A : Type u} [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]
variable (match_residue: (𝓴 𝓞) ≃+* (𝓴 A))
variable (match_residue_by: comp (algebraMap 𝓞 A) (A.residue) = comp matching_residue (𝓞.residue))

variable (matching_residue : IsIso )

variable {W : Type u} [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
variable (ρ : Representation A G W)

def modulo_map_on_reps : W ⊗[A] (𝓴 A) →[𝓴 A] V  := by
  sorry

variable (is_lift_ρ : ∀ g : G, ρ g = 1)

-- Choose a basis of V and, by Nakayama, this gives you a compatible base of W
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓑 : Basis ι (𝓴 𝓞) V)
def pbar' :=  GL_map_of_representation_of_basis ρbar 𝓑


end G_finite

section G_profinite


end G_profinite
