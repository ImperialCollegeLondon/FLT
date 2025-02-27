/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.DivisionAlgebra.Finiteness

/-

# Definition of automorphic forms on a totally definite quaternion algebra

-/

suppress_compilation

variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] --[IsCentralSimple F D] [FiniteDimensional F D]

namespace TotallyDefiniteQuaternionAlgebra

-- noncomputable example : D →+* (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
--   Algebra.TensorProduct.includeLeftRingHom

open scoped TensorProduct NumberField

open DedekindDomain

abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ

variable {F D} in
noncomputable abbrev incl₁ : Dˣ →* Dfx F D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 F) F)ˣ →* Dfx F D :=
  Units.map Algebra.TensorProduct.rightAlgebra.algebraMap.toMonoidHom

/-!
This definition is made in mathlib-generality but is *not* the definition of an automorphic
form unless Dˣ is compact mod centre at infinity. This hypothesis will be true if `D` is a
totally definite quaternion algebra.
-/
structure AutomorphicForm
  -- defined over R
  (R : Type*) [CommRing R]
  -- of weight W
  (W : Type*) [AddCommGroup W] [Module R W] [MulAction Dˣ W]
  -- and level U
  (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
  -- and character χ
  (χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* R) where
  -- definition
  toFun : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ → W
  left_invt : ∀ (δ : Dˣ) (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    toFun (incl₁ δ * g) = δ • (toFun g)
  has_character : ∀ (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (z : (FiniteAdeleRing (𝓞 F) F)ˣ),
    toFun (g * incl₂ F D z) = χ z • toFun g
  right_invt : ∀ (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    ∀ u ∈ U, toFun (g * u) = toFun g

namespace AutomorphicForm

-- defined over R
variable  (R : Type*) [CommRing R]
  -- weight
  (W : Type*) [AddCommGroup W] [Module R W] [DistribMulAction Dˣ W]
  -- NB actions of Dˣ and R should commute
  -- level
  (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) -- subgroup should be compact and open
  -- character
  (χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* R)

variable {F D R W U χ}

instance : CoeFun (AutomorphicForm F D R W U χ) (fun _ ↦ Dfx F D → W) where
  coe := toFun

attribute [coe] AutomorphicForm.toFun

@[ext]
theorem ext (φ ψ : AutomorphicForm F D R W U χ) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

def zero : (AutomorphicForm F D R W U χ) where
  toFun := 0
  left_invt δ _ := by simp
  has_character _ z := by simp
  right_invt _ u _ := by simp

instance : Zero (AutomorphicForm F D R W U χ) where
  zero := zero

@[simp]
theorem zero_apply (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (0 : AutomorphicForm F D R W U χ) x = 0 := rfl

def neg (φ : AutomorphicForm F D R W U χ) : AutomorphicForm F D R W U χ where
  toFun x := - φ x
  left_invt δ g := by simp [left_invt]
  has_character g z := by simp [has_character]
  right_invt g u hu := by simp_all [right_invt]

instance : Neg (AutomorphicForm F D R W U χ) where
  neg := neg

@[simp, norm_cast]
theorem neg_apply (φ : AutomorphicForm F D R W U χ) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (-φ : AutomorphicForm F D R W U χ) x = -(φ x) := rfl

def add (φ ψ : AutomorphicForm F D R W U χ) : AutomorphicForm F D R W U χ where
  toFun x := φ x + ψ x
  left_invt := by simp [left_invt]
  has_character := by simp [has_character]
  right_invt := by simp_all [right_invt]

instance : Add (AutomorphicForm F D R W U χ) where
  add := add

@[simp, norm_cast]
theorem add_apply (φ ψ : AutomorphicForm F D R W U χ) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (φ + ψ) x = (φ x) + (ψ x) := rfl

instance addCommGroup : AddCommGroup (AutomorphicForm F D R W U χ) where
  add := (· + ·)
  add_assoc := by intros; ext; simp [add_assoc];
  zero := 0
  zero_add := by intros; ext; simp
  add_zero := by intros; ext; simp
  nsmul := nsmulRec
  neg := (-·)
  zsmul := zsmulRec
  neg_add_cancel := by intros; ext; simp
  add_comm := by intros; ext; simp [add_comm]

-- from this point we need the Dˣ-action on W to be R-linear
variable [SMulCommClass R Dˣ W]

def smul (r : R) (φ : AutomorphicForm F D R W U χ) :
    AutomorphicForm F D R W U χ where
      toFun g := r • φ g
      left_invt := by simp [left_invt, smul_comm]
      has_character g z := by simp only [has_character, smul_comm r]
      right_invt := by simp_all [right_invt]

instance : SMul R (AutomorphicForm F D R W U χ) where
  smul := smul

lemma smul_apply (r : R) (φ : AutomorphicForm F D R W U χ) (g : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) :
    (r • φ) g = r • (φ g) := rfl

instance module : Module R (AutomorphicForm F D R W U χ) where
  one_smul g := by ext; simp [smul_apply]
  mul_smul r s g := by ext; simp [smul_apply, mul_smul]
  smul_zero r := by ext; simp [smul_apply]
  smul_add r f g := by ext; simp [smul_apply]
  add_smul r s g := by ext; simp [smul_apply, add_smul]
  zero_smul g := by ext; simp [smul_apply]

end TotallyDefiniteQuaternionAlgebra.AutomorphicForm
