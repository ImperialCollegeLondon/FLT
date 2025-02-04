import FLT.Deformations.BaseCategory
import FLT.Deformations.Lift
import FLT.Mathlib.Algebra.MvPolynomial.Eval

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
noncomputable abbrev smitLenstraRingRelations1 (i : ι) : MvPolynomial (ι × ι × G) 𝓞 :=
  X (i, i, (1:G)) - C (1 : 𝓞)

variable (𝓞 G) in
noncomputable abbrev smitLenstraRingRelations2 (i j : ι) (_ : i ≠ j) : MvPolynomial (ι × ι × G) 𝓞 :=
  X (i, j, (1:G))

variable (𝓞 G) in
noncomputable abbrev smitLenstraRingRelations3 (i j : ι) (g h : G) : MvPolynomial (ι × ι × G) 𝓞 :=
    X (i, j, g * h) - ∑ᶠ (l : ι), (X (i, l, g)) * (X (l, j, h))

variable (𝓞 G) in
noncomputable abbrev smitLenstraRingRelations (ι : Type u) [Fintype ι] : Ideal (MvPolynomial (ι × ι × G) 𝓞) :=
  let rel1 := {smitLenstraRingRelations1 𝓞 G i | (i : ι)}
  let rel2 := {smitLenstraRingRelations2 𝓞 G i j hneq | (i : ι) (j : ι) (hneq : i ≠ j)}
  let rel3 := {smitLenstraRingRelations3 𝓞 G i j g h | (i : ι) (j : ι) (g : G) (h : G)}
  Ideal.span (rel1 ∪ rel2 ∪ rel3)

-- SmitLenstraRing is the ring 𝓞[G, n] given by Smit&Lenstra
variable (𝓞 G) in
noncomputable abbrev smitLenstraRing (ι : Type u) [Fintype ι] : Type u :=
  (MvPolynomial (ι × ι × G) 𝓞) ⧸ smitLenstraRingRelations 𝓞 G ι

local notation3:max 𝓞 "[" G ", " α "]" => smitLenstraRing 𝓞 G α
local notation3:max "GL(" α ", " R ")" => (GeneralLinearGroup α R)

-- Choose any basis of V, this makes ρbar into a G →* GL_ι(𝓴 A)
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable (𝓫 : Basis ι (𝓴 𝓞) V)
noncomputable def pbar' := Representation.gl_map_of_basis ρbar 𝓫

variable {A : 𝓒 𝓞}

noncomputable abbrev smitLenstraMap_mvpoly_to_matrix (f : 𝓞[G, ι] →ₐ[𝓞] A) (g : G) : Matrix ι ι A :=
  fun i j : ι ↦ f (Ideal.Quotient.mk _ (X (i, j, g)))

@[simp]
lemma smitLenstraMap_map_one_elementwise_ii {f : 𝓞[G, ι] →ₐ[𝓞] A} {i : ι} :
    f (Ideal.Quotient.mk _ (X (i, i, 1))) = (1 : A.obj) := by
  sorry

@[simp]
lemma smitLenstraMap_map_one_elementwise_ij {f : 𝓞[G, ι] →ₐ[𝓞] A} {i j : ι} (h : i ≠ j) :
    f (Ideal.Quotient.mk _ (X (i, j, 1))) = (0 : A.obj) := by
  sorry

@[simp]
lemma smitLenstraMap_map_one (f : 𝓞[G, ι] →ₐ[𝓞] A) :
    smitLenstraMap_mvpoly_to_matrix f (1 : G) = 1 := by
  unfold smitLenstraMap_mvpoly_to_matrix
  ext i j
  by_cases h : i ≠ j
  . simp [h]
  . simp only [ne_eq, Decidable.not_not] at h
    rw [h]
    simp

@[simp]
lemma smitLenstraMap_map_mul (f : 𝓞[G, ι] →ₐ[𝓞] A) (g h : G) :
    (smitLenstraMap_mvpoly_to_matrix f g) * (smitLenstraMap_mvpoly_to_matrix f h) =
    smitLenstraMap_mvpoly_to_matrix f (g * h) := by
  ext i j
  simp only [mul_apply]
  sorry

def inverseSmitLenstraMap_eval_on_choice (ρ : G →* GL(ι, A)) : MvPolynomial (ι × ι × G) 𝓞 →ₐ[𝓞] A.obj where
  toFun F := F.eval₂ (algebraMap 𝓞 A) (fun ⟨i, j, g⟩ ↦ (ρ g).val i j)
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop
  commutes' := by aesop

lemma inverseSmitLenstraMap_eval_independent_of_choice {ρ : G →* GL(ι, A)} :
    ∀ F ∈ smitLenstraRingRelations 𝓞 G ι, inverseSmitLenstraMap_eval_on_choice ρ F = 0 := by
  sorry

noncomputable def inverseSmitLenstraMap_eval (ρ : G →* GL(ι, A)) : 𝓞[G, ι] →ₐ[𝓞] A.obj :=
  Ideal.Quotient.liftₐ
    (smitLenstraRingRelations 𝓞 G ι)
    (inverseSmitLenstraMap_eval_on_choice ρ)
    (inverseSmitLenstraMap_eval_independent_of_choice (ρ := ρ))

noncomputable def smitLenstraMap : (𝓞[G, ι] →ₐ[𝓞] A) ≃ (G →* GL(ι, A)) where
  toFun φ := {
    toFun := fun g : G ↦ ⟨
      smitLenstraMap_mvpoly_to_matrix φ g,
      smitLenstraMap_mvpoly_to_matrix φ g⁻¹,
      by simp,
      by simp⟩
    map_one' := by aesop
    map_mul' := by aesop
  }
  invFun ρ' := inverseSmitLenstraMap_eval ρ'
  left_inv := by
    unfold Function.LeftInverse
    unfold smitLenstraMap_mvpoly_to_matrix
    intro φ
    ext F
    simp_all only
    sorry
  right_inv := by
    unfold Function.RightInverse
    unfold Function.LeftInverse
    unfold smitLenstraMap_mvpoly_to_matrix
    intro ρ
    ext g i j
    simp_all only [MonoidHom.coe_mk, OneHom.coe_mk]
    sorry

-- Proposition 2.5 in G Finite
theorem Lift.functor_isCorepresentable_finite : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry

end G_finite
