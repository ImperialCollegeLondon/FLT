import Mathlib
import FLT.Deformations.Basic

universe u

open Function
open scoped TensorProduct



section G_finite

variable {G : Type u} [Group G] [Finite G]

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable (V : Type u) [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

variable {A : Type u} [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]
variable (match_residue: (𝓴 A) ≃+* (𝓴 𝓞))
variable (match_residue_by: RingHom.comp match_residue
  (RingHom.comp (IsLocalRing.residue A) (algebraMap 𝓞 A)) = IsLocalRing.residue 𝓞)

variable (W : Type u) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
variable (ρ : Representation A G W)

--instance match_residue_module : Module (𝓴 A) V := Module.compHom V match_residue.toRingHom


variable (is_lift : Bijective (mod_ctts V W (A := A)))
variable (is_lift_ρ : ∀ g : G, ∀ w : W, )

-- Choose a basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
def pbar' :=  GL_map_of_representation_of_basis ρbar 𝓫

-- (W ⊗[A] (𝓴 A)) = W ⊗ A/mA = W/mW ≃+* V means there is a w_i A-basis of W such
-- that w_i ↦ v_i by representation_mod
def nakayama_basis : Basis ι A W := sorry
-- lemma nakayama_basis_lift : Basis ι A W → Basis ι (𝓴 A) V := sorry
-- lemma nakayama_basis_lift_eq_mod : ∀ w : (nakayama_basis W (ι := ι) (A := A)),
--   nakayama_basis_lift w = representation_mod w := sorry

def ρ' :=  GL_map_of_representation_of_basis ρ (nakayama_basis W (ι := ι) (A := A))

-- This is the ring 𝓞[G, n] given by Smit&Lenstra
local notation 𝓞 "[" G ", " ι"]" => 𝓞
local notation3 "GL_" ι "(" 𝓞 ")" => (GeneralLinearGroup ι 𝓞)
local notation3 "Hom_g(" G ", " G' ")" => (G →* G')

def map_of_lenstraRing : 𝓞[G,n]  → Hom_g(G, GL_ ι(𝓞)) := sorry

theorem bijection_lenstraRing : Bijective (map_of_lenstraRing 𝓞 G ι) := by sorry


end G_finite

section G_profinite


end G_profinite
