/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.DivisionAlgebra.Finiteness
import FLT.Mathlib.Algebra.IsQuaternionAlgebra

/-

# Definition of automorphic forms on a totally definite quaternion algebra

-/

suppress_compilation

variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] --[IsCentralSimple F D] [FiniteDimensional F D]

namespace TotallyDefiniteQuaternionAlgebra

open scoped TensorProduct NumberField

open DedekindDomain

abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ

variable {F D} in
noncomputable abbrev incl₁ : Dˣ →* Dfx F D :=
  Units.map Algebra.TensorProduct.includeLeftRingHom.toMonoidHom

noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 F) F)ˣ →* Dfx F D :=
  Units.map Algebra.TensorProduct.rightAlgebra.algebraMap.toMonoidHom

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : TopologicalSpace (D ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :=
  moduleTopology (FiniteAdeleRing (𝓞 F) F) _

/-!
This definition is made in mathlib-generality but is *not* the definition of a
weight 2 automorphic form unless Dˣ is compact mod centre at infinity.
This hypothesis will be true if `D` is a totally definite quaternion algebra.
-/
structure WeightTwoAutomorphicForm
  -- defined over R
  (R : Type*) [AddCommMonoid R] where
  -- definition
  toFun : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ → R
  left_invt : ∀ (δ : Dˣ) (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    toFun (incl₁ δ * g) = (toFun g)
--  (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
  right_invt : ∃ (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    IsOpen (U : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) ∧
    ∀ (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ),
    ∀ u ∈ U, toFun (g * u) = toFun g
  trivial_central_char (z : (FiniteAdeleRing (𝓞 F) F)ˣ)
      (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
      toFun (g * incl₂ F D z) = toFun g

variable {F D}

namespace WeightTwoAutomorphicForm

section add_comm_group

variable {R : Type*} [AddCommGroup R]

instance : CoeFun (WeightTwoAutomorphicForm F D R) (fun _ ↦ Dfx F D → R) where
  coe := toFun

attribute [coe] WeightTwoAutomorphicForm.toFun

@[ext]
theorem ext (φ ψ : WeightTwoAutomorphicForm F D R) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

def zero : (WeightTwoAutomorphicForm F D R) where
  toFun := 0
  left_invt δ _ := by simp
  right_invt := ⟨⊤, by simp⟩
  trivial_central_char _ z := by simp

instance : Zero (WeightTwoAutomorphicForm F D R) where
  zero := zero

@[simp]
theorem zero_apply (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (0 : WeightTwoAutomorphicForm F D R) x = 0 := rfl

def neg (φ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := - φ x
  left_invt δ g := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    simp_all [right_invt]
  trivial_central_char g z := by simp [trivial_central_char]

instance : Neg (WeightTwoAutomorphicForm F D R) where
  neg := neg

@[simp, norm_cast]
theorem neg_apply (φ : WeightTwoAutomorphicForm F D R) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (-φ : WeightTwoAutomorphicForm F D R) x = -(φ x) := rfl

def add (φ ψ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := φ x + ψ x
  left_invt := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    obtain ⟨V, hV⟩ := ψ.right_invt
    use U ⊓ V
    simp_all [right_invt, IsOpen.inter]
  trivial_central_char := by simp [trivial_central_char]

instance : Add (WeightTwoAutomorphicForm F D R) where
  add := add

@[simp, norm_cast]
theorem add_apply (φ ψ : WeightTwoAutomorphicForm F D R) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (φ + ψ) x = (φ x) + (ψ x) := rfl

instance addCommGroup : AddCommGroup (WeightTwoAutomorphicForm F D R) where
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

def group_smul (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) (φ : WeightTwoAutomorphicForm F D R) :
    WeightTwoAutomorphicForm F D R where
  toFun x := φ (x * g)
  left_invt δ x := by simp [left_invt, mul_assoc]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    -- use g * U * g⁻¹
    sorry
  trivial_central_char z x := by
    simp only [mul_assoc]
    sorry -- are we sure we only ever need trivial central character?

instance : SMul  (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ (WeightTwoAutomorphicForm F D R) where
  smul := group_smul

@[simp]
lemma group_smul_apply (g : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
    (φ : WeightTwoAutomorphicForm F D R) (x : (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ) :
    (g • φ) x = φ (x * g) := rfl

instance : DistribMulAction (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ (WeightTwoAutomorphicForm F D R) where
  smul := group_smul
  one_smul φ := by ext; simp
  mul_smul g h φ := by ext; simp [mul_assoc]
  smul_zero g := by ext; simp
  smul_add g φ ψ := by ext; simp

end add_comm_group

section comm_ring

variable {R : Type*} [CommRing R]

def ring_smul (r : R) (φ : WeightTwoAutomorphicForm F D R) :
    WeightTwoAutomorphicForm F D R where
      toFun g := r • φ g
      left_invt := by simp [left_invt, smul_comm]
      right_invt := by
        obtain ⟨U, hU⟩ := φ.right_invt
        use U
        simp_all [right_invt]
      trivial_central_char g z := by simp only [trivial_central_char, smul_comm r]

instance : SMul R (WeightTwoAutomorphicForm F D R) where
  smul := ring_smul

@[simp] -- maybe? ASK?
lemma smul_apply (r : R) (φ : WeightTwoAutomorphicForm F D R)
    (g : (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) :
    (r • φ) g = r • (φ g) := rfl

instance module : Module R (WeightTwoAutomorphicForm F D R) where
  one_smul g := by ext; simp [smul_apply]
  mul_smul r s g := by ext; simp [smul_apply, mul_smul, mul_assoc]
  smul_zero r := by ext; simp [smul_apply]
  smul_add r f g := by ext; simp [smul_apply, mul_add]
  add_smul r s g := by ext; simp [smul_apply, add_mul]
  zero_smul g := by ext; simp [smul_apply]

end comm_ring

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm
