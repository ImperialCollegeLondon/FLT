/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Definitions for automorphic forms on quaternion algebras

Let `D` be a totally definite quaternion algebra over a totally real
number field `F`. We set up notation and basic definitions for the spaces of
weight-2 automorphic forms on `D` (functions on the double-coset space
`D^× \\ (D ⊗ 𝔸_F^∞)^× / U` for an open compact subgroup `U`).

## Main definitions

* `TotallyDefiniteQuaternionAlgebra.Dfx`: the units of `D ⊗_F 𝔸_F^∞`.
* `TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm`: the space of
  weight-2 automorphic forms with values in a coefficient ring `R`.
-/

@[expose] public section

/-

# Definition of automorphic forms on a totally definite quaternion algebra

## Main definitions

In the `TotallyDefiniteQuaternionAlgebra` namespace:

* `WeightTwoAutomorphicForm F D R` -- weight 2
  R-valued automorphic forms for the totally definite quaternion algebra `D` over
  the totally real field `F`. Defined as locally-constant functions
  `φ : Dˣ \ (D ⊗ 𝔸_F^∞)ˣ → R` which are right-invariant by some compact open subgroup
  (i.e. ∃ U_φ such that `φ(gu)=φ(g)` for all `u ∈ U`) and have trivial central character
  (i.e. `φ(zg)=φ(g)` for all `z ∈ (𝔸_F^∞)ˣ`).

* `WeightTwoAutomorphicFormOfLevel U R` -- weight 2 R-valued automorphic forms of
  level `U`, i.e. `U`-invariant elements of `WeightTwoAutomorphicForm F D R`.
  It is a nontrivial theorem that if `U` is open and `R` is Noetherian then this space
  is a finitely-generated `R`-module; this follows from Fujisaki's lemma.

-/

suppress_compilation


variable (F : Type*) [Field F] [NumberField F] -- if F isn't totally real all the definitions
-- below are garbage mathematically but they typecheck.

variable (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D]
  -- If D isn't totally definite then all the
  -- definitions below are garbage mathematically but they typecheck.

namespace TotallyDefiniteQuaternionAlgebra

open scoped TensorProduct NumberField

open IsDedekindDomain

instance : CommRing (FiniteAdeleRing (𝓞 F) F) := inferInstance
instance : Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F) := inferInstance

/-- `Dfx` is an abbreviation for $(D\otimes_F\mathbb{A}_F^\infty)^\times.$ -/
abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ

/-- incl₁ is an abbreviation for the inclusion
$D^\times\to(D\otimes_F\mathbb{A}_F^\infty)^\times.$ Remark: I wrote the `incl₁`
docstring in LaTeX and the `incl₂` one in unicode. Which is better? -/
noncomputable abbrev incl₁ : Dˣ →* Dfx F D :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom.toMonoidHom)

/-- `incl₂` is he inclusion `𝔸_F^∞ˣ → (D ⊗ 𝔸_F^∞ˣ)`. Remark: I wrote the `incl₁`
docstring in LaTeX and the `incl₂` one in unicode. Which is better? -/
noncomputable abbrev incl₂ : (FiniteAdeleRing (𝓞 F) F)ˣ →* Dfx F D :=
  Units.map (Algebra.TensorProduct.includeRight.toRingHom.toMonoidHom)

omit [FiniteDimensional F D] in
lemma includeRight_mul_comm
    (y : FiniteAdeleRing (𝓞 F) F) (z : D ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z * Algebra.TensorProduct.includeRight y =
      Algebra.TensorProduct.includeRight y * z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [Algebra.TensorProduct.includeRight_apply]
  · intro d a
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    rw [add_mul, mul_add, hz₁, hz₂]

-- it's actually equal but ⊆ is all we need, and equality is harder
omit [FiniteDimensional F D] in
lemma range_incl₂_le_center : MonoidHom.range (incl₂ F D) ≤ Subgroup.center (Dfx F D) := by
  rintro x ⟨y, rfl⟩
  refine Subgroup.mem_center_iff.mpr fun g ↦ Units.ext ?_
  simpa [incl₂] using includeRight_mul_comm (F := F) (D := D) (↑y) (↑g)

noncomputable local instance : SMul (FiniteAdeleRing (𝓞 F) F)
    (D ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  smul a x := TensorProduct.comm _ _ _ (a • (TensorProduct.comm _ _ _ x))

omit [FiniteDimensional F D] in
@[simp]
private lemma tensor_right_smul_def (a : FiniteAdeleRing (𝓞 F) F)
    (x : D ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    a • x = (TensorProduct.comm _ _ _).symm (a • (TensorProduct.comm _ _ _ x)) := rfl

local instance : Module (FiniteAdeleRing (𝓞 F) F)
    (D ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  one_smul x := by
    simp_rw [tensor_right_smul_def, one_smul, (TensorProduct.comm F D _).symm_apply_apply]
  mul_smul a b x := by
    simp_rw [tensor_right_smul_def, mul_smul, (TensorProduct.comm F D _).apply_symm_apply]
  smul_zero := by simp
  smul_add := by simp
  add_smul := by simp [add_smul]
  zero_smul := by simp

noncomputable local instance : Algebra (FiniteAdeleRing (𝓞 F) F)
    (D ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' a x := by
    induction x with
    | zero =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_zero, zero_mul]
    | tmul d b =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, mul_comm]
    | add x y hx hy =>
        simp_all only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_add, add_mul]
  smul_def' a x := by
    induction x with
    | zero =>
        simp only [smul_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, mul_zero]
    | tmul d b =>
        simp only [tensor_right_smul_def, TensorProduct.comm_tmul, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [TensorProduct.smul_tmul']
        simp only [smul_eq_mul, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [tensor_right_smul_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, smul_add, mul_add]

private def tensorCommRightLinearEquiv :
    (FiniteAdeleRing (𝓞 F) F ⊗[F] D) ≃ₗ[FiniteAdeleRing (𝓞 F) F]
      (D ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  __ := (_root_.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) D).toAddEquiv
  map_smul' a x := by
    induction x with
    | zero =>
        simp only [smul_zero, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_zero,
          RingHom.id_apply]
    | tmul b d =>
        simp only [TensorProduct.smul_tmul', AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, TensorProduct.comm_tmul, RingHom.id_apply,
          tensor_right_smul_def, TensorProduct.comm_symm_tmul]
    | add x y hx hy =>
        simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          RingHom.id_apply, tensor_right_smul_def, smul_add, map_add]

local instance : Module.Finite (FiniteAdeleRing (𝓞 F) F)
    (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  Module.Finite.equiv
    (tensorCommRightLinearEquiv (F := F) (D := D))

noncomputable local instance : TopologicalSpace (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  moduleTopology (FiniteAdeleRing (𝓞 F) F) _

local instance : IsModuleTopology (FiniteAdeleRing (𝓞 F) F)
    (D ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

local instance : IsTopologicalRing (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _

local instance : TopologicalSpace (Dfx F D) := inferInstance

local instance : IsTopologicalGroup (Dfx F D) := inferInstance

/--
This definition is made in mathlib-generality but is *not* the definition of a
weight 2 automorphic form unless `Dˣ` is compact mod centre at infinity.
This hypothesis will be true if `D` is a totally definite quaternion algebra
over a totally real field.
-/
structure WeightTwoAutomorphicForm
  -- defined over R
  (R : Type*) [AddCommMonoid R] where
  /-- The function underlying an automorphic form. -/
  toFun : Dfx F D → R
  left_invt : ∀ (δ : Dˣ) (g : Dfx F D),
    toFun (incl₁ F D δ * g) = (toFun g)
  right_invt : ∃ (U : Subgroup (Dfx F D)),
    IsOpen (U : Set (Dfx F D)) ∧
    ∀ (g : Dfx F D),
    ∀ u ∈ U, toFun (g * u) = toFun g
  trivial_central_char (z : (FiniteAdeleRing (𝓞 F) F)ˣ)
      (g : Dfx F D) :
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

/-- The zero automorphic form for a totally definite quaterion algebra. -/
def zero : (WeightTwoAutomorphicForm F D R) where
  toFun := 0
  left_invt δ _ := by simp
  -- this used to be `by simp` but now it times out doing some crazy typeclass search for
  -- `DiscreteTopology (D ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ`
  right_invt := ⟨⊤, by simp only [Subgroup.coe_top, isOpen_univ, Subgroup.mem_top,
    Pi.zero_apply, imp_self, implies_true, and_self]⟩
  trivial_central_char _ z := by simp

instance : Zero (WeightTwoAutomorphicForm F D R) where
  zero := zero

@[simp]
theorem zero_apply (x : Dfx F D) :
    (0 : WeightTwoAutomorphicForm F D R) x = 0 := rfl

/-- Negation on the space of automorphic forms over a totally definite quaternion algebra. -/
def neg (φ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := - φ x
  left_invt δ g := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    simp_all only [neg_inj, right_invt]
  trivial_central_char g z := by simp [trivial_central_char]

instance : Neg (WeightTwoAutomorphicForm F D R) where
  neg := neg

@[simp, norm_cast]
theorem neg_apply (φ : WeightTwoAutomorphicForm F D R) (x : Dfx F D) :
    (-φ : WeightTwoAutomorphicForm F D R) x = -(φ x) := rfl

/-- Addition on the space of automorphic forms over a totally definite quaternion algebra. -/
def add (φ ψ : WeightTwoAutomorphicForm F D R) : WeightTwoAutomorphicForm F D R where
  toFun x := φ x + ψ x
  left_invt := by simp [left_invt]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    obtain ⟨V, hV⟩ := ψ.right_invt
    use U ⊓ V
    simp_all only [Subgroup.coe_inf, IsOpen.inter, Subgroup.mem_inf, implies_true, and_self]
  trivial_central_char := by simp [trivial_central_char]

instance : Add (WeightTwoAutomorphicForm F D R) where
  add := add

@[simp, norm_cast]
theorem add_apply (φ ψ : WeightTwoAutomorphicForm F D R) (x : Dfx F D) :
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

open scoped Pointwise

-- these two should be in mathlib
instance {G} [TopologicalSpace G] [DivInvMonoid G] [ContinuousMul G] :
    ContinuousConstSMul (ConjAct G) G where
  continuous_const_smul _ := IsTopologicalGroup.continuous_conj _

lemma _root_.ConjAct.isOpen_smul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {U : Subgroup G} (hU : IsOpen (U : Set G)) (g : ConjAct G) :
    IsOpen ((g • U : Subgroup G) : Set G) :=
  (Homeomorph.smul g).isOpen_image.mpr hU

open ConjAct

/-- The adelic group action on the space of automorphic forms over a totally definite
quaternion algebra. -/
def groupSmul (g : Dfx F D) (φ : WeightTwoAutomorphicForm F D R) :
    WeightTwoAutomorphicForm F D R where
  toFun x := φ (x * g)
  left_invt δ x := by simp [left_invt, mul_assoc]
  right_invt := by
    obtain ⟨U, hU⟩ := φ.right_invt
    refine ⟨(toConjAct g) • U, ?_, ?_⟩
    · replace hU := hU.1
      exact isOpen_smul hU (toConjAct g)
    · rintro k x ⟨u, hu, rfl⟩
      simp only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
        smul_def, ofConjAct_toConjAct, ← hU.2 (k * g) u hu]
      group
  trivial_central_char z x := by
    simp only [mul_assoc]
    have := range_incl₂_le_center F D ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff] at this
    rw [← this, ← mul_assoc, trivial_central_char]

instance : SMul (Dfx F D) (WeightTwoAutomorphicForm F D R) where
  smul := groupSmul

@[simp]
lemma group_smul_apply (g : Dfx F D)
    (φ : WeightTwoAutomorphicForm F D R) (x : Dfx F D) :
    (g • φ) x = φ (x * g) := rfl

attribute [instance low] Units.instMulAction

instance mulAction :
    MulAction (Dfx F D) (WeightTwoAutomorphicForm F D R) where
  smul := groupSmul
  one_smul φ := by ext; simp only [group_smul_apply, mul_one]
  mul_smul g h φ := by ext; simp only [group_smul_apply, mul_assoc]

instance distribMulAction : DistribMulAction (Dfx F D)
    (WeightTwoAutomorphicForm F D R) where
  __ := mulAction
  smul_zero g := by ext; simp only [group_smul_apply, zero_apply]
  smul_add g φ ψ := by ext; simp only [group_smul_apply, add_apply]

end add_comm_group

section comm_ring

variable {R : Type*} [CommRing R]

/-- The scalar action on the space of weight 2 automorphic forms on a totally definite
quaternion algebra. -/
def ringSmul (r : R) (φ : WeightTwoAutomorphicForm F D R) :
    WeightTwoAutomorphicForm F D R where
      toFun g := r • φ g
      left_invt := by simp [left_invt]
      right_invt := by
        obtain ⟨U, hU⟩ := φ.right_invt
        use U
        simp_all only [smul_eq_mul, implies_true, and_self]
      trivial_central_char g z := by simp only [trivial_central_char]

instance : SMul R (WeightTwoAutomorphicForm F D R) where
  smul := ringSmul

lemma smul_apply (r : R) (φ : WeightTwoAutomorphicForm F D R)
    (g : Dfx F D) :
    (r • φ) g = r • (φ g) := rfl

instance module : Module R (WeightTwoAutomorphicForm F D R) where
  one_smul g := by ext; simp [smul_apply]
  mul_smul r s g := by ext; simp [smul_apply, mul_assoc]
  smul_zero r := by ext; simp [smul_apply]
  smul_add r f g := by ext; simp [smul_apply, mul_add]
  add_smul r s g := by ext; simp [smul_apply, add_mul]
  zero_smul g := by ext; simp [smul_apply]

instance : SMulCommClass (Dfx F D) R (WeightTwoAutomorphicForm F D R) where
  smul_comm r g φ := by
    ext x
    simp [smul_apply]

end comm_ring

end WeightTwoAutomorphicForm

section finite_level

/--
`WeightTwoAutomorphicFormOfLevel U R` is the `R`-valued weight 2 automorphic forms of a fixed
level `U` for a totally definite quaternion algebra over a totally real field.
-/
def WeightTwoAutomorphicFormOfLevel (U : Subgroup (Dfx F D))
    (R : Type*) [CommRing R] : Type _ :=
  FixedPoints.addSubgroup U (WeightTwoAutomorphicForm F D R)

namespace WeightTwoAutomorphicFormOfLevel

variable {U : Subgroup (Dfx F D)} {R : Type*} [CommRing R]

/--
Enables coercion of automorphic forms to functions.
-/
@[coe]
def toFun (f : WeightTwoAutomorphicFormOfLevel U R)
    (x : Dfx F D) : R := f.1.toFun x

instance : CoeFun (WeightTwoAutomorphicFormOfLevel U R) (fun _ ↦ Dfx F D → R) where
  coe := toFun

@[ext]
lemma ext ⦃f g : WeightTwoAutomorphicFormOfLevel U R⦄ (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext <| WeightTwoAutomorphicForm.ext _ _ h

lemma left_invt (f : WeightTwoAutomorphicFormOfLevel U R) (δ : Dˣ) (g : Dfx F D) :
    f ((incl₁ F D) δ * g) = f g :=
  f.1.left_invt δ g

lemma right_invt (f : WeightTwoAutomorphicFormOfLevel U R) (g : Dfx F D) (u : U) :
    f (g * u) = f g :=
  congr($(f.2 u) g)

instance : AddCommGroup (WeightTwoAutomorphicFormOfLevel U R) := inferInstanceAs <|
  AddCommGroup (FixedPoints.addSubgroup U (WeightTwoAutomorphicForm F D R))

instance : Module R (WeightTwoAutomorphicFormOfLevel U R) where
  smul r f := ⟨r • f.1, fun u ↦ by simp [smul_comm, f.2 u]⟩
  one_smul f := by
    ext x
    exact one_smul R (f x)
  mul_smul r s f := by
    ext x
    exact mul_smul r s (f x)
  smul_zero r := by
    ext x
    exact smul_zero r
  smul_add r f g := by
    ext x
    exact smul_add r (f x) (g x)
  add_smul r s f := by
    ext x
    exact add_smul r s (f x)
  zero_smul f := by
    ext x
    exact zero_smul R (f x)

end WeightTwoAutomorphicFormOfLevel

end finite_level

end TotallyDefiniteQuaternionAlgebra
