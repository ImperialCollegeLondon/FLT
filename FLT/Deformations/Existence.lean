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

variable (V : Type u) [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]
variable (ρbar : Representation (𝓴 𝓞) G V)

variable {A : Type u} [CommRing A] [Algebra 𝓞 A] [IsLocalRing A]
variable (match_residue: (𝓴 𝓞) ≃+* (𝓴 A))
variable (match_residue_by: RingHom.comp (IsLocalRing.residue A) (algebraMap 𝓞 A) =
  RingHom.comp match_residue (IsLocalRing.residue 𝓞))

variable (W : Type u) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
variable (ρ : Representation A G W)

instance match_residue_module : Module (𝓴 A) V := sorry
  -- smul ka v := (match_residue.invFun ka) • v

noncomputable def extend_ctts : W →ₗ[𝓴 A] (W ⊗[A] (𝓴 A)) where
  toFun w := w ⊗ₜ[A] (1 : (𝓴 A))
  map_add' := by
    simp [TensorProduct.add_tmul]
  map_smul' := sorry

noncomputable def mod_ctts : (W ⊗[A] (𝓴 A)) →ₗ[𝓴 A] V where
  toFun t := sorry
  map_add' := sorry
  map_smul' := sorry

noncomputable def representation_mod : W →ₗ[𝓴 A] V :=
  LinearMap.comp (mod_ctts V W (A := A)) (extend_ctts W (A := A))

variable (is_lift : Bijective (mod_ctts V W (A := A)))
variable (is_lift_ρ : ∀ g : G, ∀ w : W, ρbar g (representation_mod V W (A := A) w)
  = representation_mod V W (A := A) (ρ g w))

-- Choose a basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
def pbar' :=  GL_map_of_representation_of_basis ρbar 𝓫

-- (W ⊗[A] (𝓴 A)) = W ⊗ A/mA = W/mW ≃+* V means there is a w_i A-basis of W such
-- that w_i ↦ v_i by representation_mod
def nakayama_compatible_basis : Basis ι A W := by
  sorry

def ρ' :=  GL_map_of_representation_of_basis ρ (nakayama_compatible_basis W (ι := ι) (A := A))

-- This is the ring 𝓞[G, n] given by Smit&Lenstra
local notation "LenstraRing" G 𝓞 ι => 𝓞

local notation "GL_" ι "(" R ")" => (GeneralLinearGroup ι R)
local notation 𝓞 "[" G "," ι "]" => FreeModule
local notation "Hom[" G "," G' "]" => (G →* G')

def map_of_lenstraRing : 𝓞[G, ι] → Type u := sorry

theorem bijection_lenstraRing : IsBijective map_of_lenstraRing := by sorry


end G_finite

section G_profinite


end G_profinite
