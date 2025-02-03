import FLT.Deformations.BaseCategory
import FLT.Deformations.Lift

universe u

open CategoryTheory Function
open scoped TensorProduct

variable {𝓞 : Type u}
  [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {V : Type u}
  [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type u} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : Representation (𝓴 𝓞) G V)

variable (A : 𝓒 𝓞)
variable [Module (𝓴 A) V] [IsScalarTower (𝓴 A) (𝓴 𝓞) V]
variable [Module A V] [IsScalarTower A (𝓴 A) V]

variable {W: Type u} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

variable {ι : Type*} [Fintype ι]

variable (reduction : LinearEquiv
  (algebraMap (𝓴 A) (𝓴 𝓞))
  ((𝓴 A) ⊗[A] W)
  V)

variable (ρ: Representation A G W)
section G_finite -- Section 3.1 Smit & Lenstra

open Matrix Set MvPolynomial
variable [Finite G]

variable (𝓞 G) in
abbrev smitLenstraRingRelations (ι : Type u) [Fintype ι] : Ideal (MvPolynomial (ι × ι × G) 𝓞) :=
  let rel1 := {X (i, i, (1:G)) - C (1 : 𝓞) | (i : ι)}
  let rel2 := {X (i, j, (1:G)) | (i : ι) (j : ι) (_ : i ≠ j)}
  let rel3 := { X (i, j, g * h)
      - ∑ᶠ (l : ι), (X (i, l, g)) * (X (l, j, h))  | (i : ι) (j : ι) (g : G) (h : G)}
  Ideal.span (rel1 ∪ rel2 ∪ rel3)

-- SmitLenstraRing is the ring 𝓞[G, n] given by Smit&Lenstra
variable (𝓞 G) in
abbrev smitLenstraRing (ι : Type u) [Fintype ι] : Type u :=
  (MvPolynomial (ι × ι × G) 𝓞) ⧸ smitLenstraRingRelations 𝓞 G ι

local notation3:max 𝓞 "[" G ", " α "]" => smitLenstraRing 𝓞 G α
local notation3:max "GL(" α ", " R ")" => (GeneralLinearGroup α R)

-- Choose any basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
noncomputable def pbar' := Representation.gl_map_of_basis ρbar 𝓫

variable (A : 𝓒 𝓞)

def eval_smitLenstraPoly (ρ' : G →* GL(ι, A)) (F : MvPolynomial (ι × ι × G) 𝓞) : A.obj :=
  F.eval₂ (algebraMap 𝓞 A) (fun ⟨i, j, g⟩  ↦ (ρ' g).val i j)

noncomputable def smitLenstraMap : (𝓞[G, ι] →ₗ[𝓞] A) ≃ (G →* GL(ι, A)) where
  toFun f := {
    toFun := fun g : G ↦
      .mk' (.of
        (fun i j : ι ↦
          f (Ideal.Quotient.mk (smitLenstraRingRelations 𝓞 G ι) (X (i, j, g)))
        )
      )
      (by sorry)
    map_one' := sorry
    map_mul' := sorry
  }
  invFun ρ' := {
    toFun := fun mpoly : 𝓞[G, ι] ↦
      let mpoly' := mpoly.out
      eval_smitLenstraPoly A ρ' mpoly'
    map_add' := sorry
    map_smul' := sorry
  }
  left_inv := sorry
  right_inv := sorry

-- Proposition 2.5 in G Finite
theorem Lift.functor_isCorepresentable_finite : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end G_finite
