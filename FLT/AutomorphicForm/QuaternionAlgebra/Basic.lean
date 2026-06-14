/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang
-/
module

public import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import FLT.QuaternionAlgebra.NumberField
public import FLT.AutomorphicForm.GroupTheoryStuff
public import FLT.AutomorphicForm.Stuff
public import FLT.Assumptions.KnownIn1980s
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!

# Definition of automorphic forms on a totally definite quaternion algebra

## Main definitions

In the `TotallyDefiniteQuaternionAlgebra` namespace:

* `WeightTwoAutomorphicForm F D R` -- weight 2
  R-valued automorphic forms for the totally definite quaternion algebra `D` over
  the totally real field `F`. Defined as locally-constant functions
  `φ : Dˣ \ (D ⊗ 𝔸_F^∞)ˣ → R` which are right-invariant by some compact open subgroup
  (i.e. ∃ U_φ such that `φ(gu)=φ(g)` for all `u ∈ U`) and have trivial central character
  (i.e. `φ(zg)=φ(g)` for all `z ∈ (𝔸_F^∞)ˣ`).

* `LevelStruct F R`: A structure containing a compact open and a character on it.
* `LevelStruct.form ℒ D`: The submodule `S(U, χ)` of `WeightTwoAutomorphicForm F D R`.

* `LocalLevelStruct F R`: A structure containing a compact open and a character on it.

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

attribute [-simp] RingHom.toMonoidHom_eq_coe

suppress_compilation

open IsQuaternionAlgebra.NumberField

open scoped FLT

variable (F : Type*) [Field F] [NumberField F] -- if F isn't totally real all the definitions
-- below are garbage mathematically but they typecheck.

variable (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D]
  -- If D isn't totally definite then all the
  -- definitions below are garbage mathematically but they typecheck.

namespace TotallyDefiniteQuaternionAlgebra

open scoped TensorProduct NumberField Adele

local notation "𝓓ˣ" => MonoidHom.range (WithRigidification.unitsIncl F D)
local notation "𝓕ˣ" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap F M₂(𝔸ᶠ[F]))))
local notation "𝔸ˣ" F =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F]))))

variable {F} in
lemma range_unitsMap_finiteAdeleRing_le_center : (𝔸ˣ F) ≤ .center _ := by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes]

open IsDedekindDomain

instance : CommRing (FiniteAdeleRing (𝓞 F) F) := inferInstance
instance : Ring (D ⊗[F] FiniteAdeleRing (𝓞 F) F) := inferInstance

/-- `Dfx` is an abbreviation for $(D\otimes_F\mathbb{A}_F^\infty)^\times.$ -/
abbrev Dfx := (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ

open scoped TensorProduct.RightActions in
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
  toFun : GL₂(𝔸ᶠ[F]) → R
  left_invt (δ : Dˣ) (g : GL₂(𝔸ᶠ[F])) : toFun (WithRigidification.unitsIncl _ _ δ * g) = (toFun g)
  right_invt : ∃ (U : Subgroup GL₂(𝔸ᶠ[F])), IsOpen (U : Set GL₂(𝔸ᶠ[F])) ∧
    ∀ g, ∀ u ∈ U, toFun (g * u) = toFun g
  trivial_central_char (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) : toFun (z • g) = toFun g

attribute [simp] WeightTwoAutomorphicForm.left_invt WeightTwoAutomorphicForm.trivial_central_char

variable {F D}

namespace WeightTwoAutomorphicForm

section add_comm_group

variable {R : Type*} [AddCommGroup R]

instance : CoeFun (WeightTwoAutomorphicForm F D R) (fun _ ↦ GL₂(𝔸ᶠ[F]) → R) where
  coe := toFun

attribute [coe] WeightTwoAutomorphicForm.toFun

@[ext]
theorem ext (φ ψ : WeightTwoAutomorphicForm F D R) (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; simp only [mk.injEq]; ext; apply h

@[simp]
lemma left_invt' (f : WeightTwoAutomorphicForm F D R)
    (δ : MonoidHom.range (WithRigidification.unitsIncl F D)) (g : GL₂(𝔸ᶠ[F])) :
    f (δ * g) = f g := by obtain ⟨_, δ, rfl⟩ := δ; simp

@[simp]
lemma trivial_central_char' (f : WeightTwoAutomorphicForm F D R)
    (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) :
    f (z.map (algebraMap _ _).toMonoidHom * g) = f g := by
  convert f.trivial_central_char z g using 2; ext1; simp [Units.smul_def, Algebra.smul_def]

@[simp]
lemma trivial_central_char_right (f : WeightTwoAutomorphicForm F D R)
    (z : (𝔸ᶠ[F])ˣ) (g : GL₂(𝔸ᶠ[F])) :
    f (g * z.map (algebraMap _ _).toMonoidHom) = f g := by
  rw [← f.trivial_central_char' z g]; congr 1; ext1; simp [Algebra.commutes]

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
theorem zero_apply (x : GL₂(𝔸ᶠ[F])) : (0 : WeightTwoAutomorphicForm F D R) x = 0 := rfl

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
theorem neg_apply (φ : WeightTwoAutomorphicForm F D R) (x : GL₂(𝔸ᶠ[F])) :
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
theorem add_apply (φ ψ : WeightTwoAutomorphicForm F D R) (x : GL₂(𝔸ᶠ[F])) :
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

open ConjAct

open scoped TensorProduct.RightActions in
/-- The adelic group action on the space of automorphic forms over a totally definite
quaternion algebra. -/
def groupSMul (g : GL₂(𝔸ᶠ[F])) (φ : WeightTwoAutomorphicForm F D R) :
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
  trivial_central_char z x := by simp [smul_mul_assoc]

instance : SMul GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D R) where
  smul := groupSMul

@[simp]
lemma groupSMul_apply (g : GL₂(𝔸ᶠ[F]))
    (φ : WeightTwoAutomorphicForm F D R) (x : GL₂(𝔸ᶠ[F])) :
    (g • φ) x = φ (x * g) := rfl

attribute [instance low] Units.instMulAction

instance mulAction :
    MulAction GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D R) where
  smul := groupSMul
  one_smul φ := by ext; simp only [groupSMul_apply, mul_one]
  mul_smul g h φ := by ext; simp only [groupSMul_apply, mul_assoc]

instance distribMulAction : DistribMulAction GL₂(𝔸ᶠ[F])
    (WeightTwoAutomorphicForm F D R) where
  __ := mulAction
  smul_zero g := by ext; simp only [groupSMul_apply, zero_apply]
  smul_add g φ ψ := by ext; simp only [groupSMul_apply, add_apply]

open IsDedekindDomain.FiniteAdeleRing

noncomputable
instance (v : HeightOneSpectrum (𝓞 F)) :
    DistribMulAction GL₂(v.adicCompletion F) (WeightTwoAutomorphicForm F D R) :=
  .compHom _ (GL2.finiteAdeleIncl v)

lemma adicCompletion_smul_def (v : HeightOneSpectrum (𝓞 F)) (g : GL₂(v.adicCompletion F))
    (x : WeightTwoAutomorphicForm F D R) : g • x = GL2.finiteAdeleIncl v g • x := rfl

end add_comm_group

section comm_ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The scalar action on the space of weight 2 automorphic forms on a totally definite
quaternion algebra. -/
def ringSMul (r : R) (φ : WeightTwoAutomorphicForm F D M) :
    WeightTwoAutomorphicForm F D M where
      toFun g := r • φ g
      left_invt := by simp [left_invt]
      right_invt := by
        obtain ⟨U, hU⟩ := φ.right_invt
        use U
        simp_all only [implies_true, and_self]
      trivial_central_char g z := by simp only [trivial_central_char]

instance : SMul R (WeightTwoAutomorphicForm F D M) where
  smul := ringSMul

@[simp]
lemma smul_apply (r : R) (φ : WeightTwoAutomorphicForm F D M)
    (g : GL₂(𝔸ᶠ[F])) :
    (r • φ) g = r • (φ g) := rfl

instance module : Module R (WeightTwoAutomorphicForm F D M) where
  one_smul g := by ext; simp [smul_apply]
  mul_smul r s g := by ext; simp [smul_apply, mul_smul]
  smul_zero r := by ext; simp [smul_apply]
  smul_add r f g := by ext; simp [smul_apply, smul_add]
  add_smul r s g := by ext; simp [smul_apply, add_smul]
  zero_smul g := by ext; simp [smul_apply]

instance : SMulCommClass GL₂(𝔸ᶠ[F]) R (WeightTwoAutomorphicForm F D M) where
  smul_comm r g φ := by ext; simp [smul_apply]

instance : SMulCommClass R GL₂(𝔸ᶠ[F]) (WeightTwoAutomorphicForm F D M) := .symm _ _ _

instance (v : HeightOneSpectrum (𝓞 F)) :
    SMulCommClass GL₂(v.adicCompletion F) R (WeightTwoAutomorphicForm F D R) where
  smul_comm _ _ _ := by rw [adicCompletion_smul_def, adicCompletion_smul_def, smul_comm]

instance (v : HeightOneSpectrum (𝓞 F)) :
    SMulCommClass R GL₂(v.adicCompletion F) (WeightTwoAutomorphicForm F D R) := .symm _ _ _

end comm_ring

end WeightTwoAutomorphicForm

variable (R : Type*) [CommRing R]

local notation "ιD" => WithRigidification.unitsIncl F D
local notation "ι𝔸" => Units.map (RingHom.toMonoidHom (algebraMap (𝔸ᶠ[F]) M₂(𝔸ᶠ[F])))
local notation "ℙ(" K ")" => HeightOneSpectrum (𝓞 K)
local notation "𝒪_[" K ", " v "]" => HeightOneSpectrum.adicCompletionIntegers K v

instance : (𝔸ˣ F).Normal := Subgroup.normal_of_le_center _ <| by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, (Algebra.commute_algebraMap_left ..).eq]

open ConjAct Pointwise

variable {R} {M : Type*} [AddCommGroup M] [Module R M]

namespace WeightTwoAutomorphicForm

variable (F R) in
/-- The structure of an compact open `U`,
and a continuous character on `U` that is trivial on `𝔸ᶠˣ`. -/
structure LevelStruct where
  /-- The open compact subgroup. -/
  U : Subgroup GL₂(𝔸ᶠ[F])
  isCompact_U : IsCompact (X := GL₂(𝔸ᶠ[F])) U
  isOpen_U : IsOpen (X := GL₂(𝔸ᶠ[F])) U
  /-- The character on the open compact. -/
  χ : U →* R
  range_unitsMap_le_ker_χ : (𝔸ˣ F).subgroupOf U ≤ χ.ker
  isOpen_ker : IsOpen (X := U) χ.ker

namespace LevelStruct

variable (ℒ : LevelStruct F R)

/-- `U 𝔸ᶠˣ` -/
abbrev UA : Subgroup GL₂(𝔸ᶠ[F]) := ℒ.U ⊔ 𝔸ˣ F

def χA : ℒ.UA →* R :=
  MonoidHom.liftOfSurjective' (Subgroup.prodToSupOfRight _ _
    ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)))
    (Subgroup.prodToSupOfRight_surjective _ _ _)
    ⟨ℒ.χ.coprod 1, by
      rintro ⟨x, ⟨_, y, rfl⟩⟩ hx
      replace hx : x.1 * y.map (algebraMap _ _).toMonoidHom = 1 := by
        simpa [Subtype.ext_iff] using hx
      simp only [MonoidHom.mem_ker, MonoidHom.coprod_apply, MonoidHom.one_apply, mul_one]
      refine ℒ.range_unitsMap_le_ker_χ ⟨y⁻¹, ?_⟩
      simpa [← mul_eq_one_iff_inv_eq']⟩

@[simp]
lemma χA_inclusion_left (x) : ℒ.χA (Subgroup.inclusion le_sup_left x) = ℒ.χ x := by
  trans ℒ.χA ((Subgroup.prodToSupOfRight _ _ ((range_unitsMap_finiteAdeleRing_le_center ..).trans
    (Subgroup.center_le_centralizer _))) (x, 1))
  · congr 1; ext; simp
  · simp [χA]

@[simp]
lemma χA_inclusion_right (x) : ℒ.χA (Subgroup.inclusion le_sup_right x) = 1 := by
  trans ℒ.χA ((Subgroup.prodToSupOfRight _ _ ((range_unitsMap_finiteAdeleRing_le_center ..).trans
    (Subgroup.center_le_centralizer _))) (1, x))
  · congr 1; ext; simp
  · simp [χA]

variable (D) in
/-- `Δ_g := U 𝔸ˣ ∩ g Dˣ g⁻¹` -/
def Δ (g : GL₂(𝔸ᶠ[F])) : Subgroup GL₂(𝔸ᶠ[F]) :=
  ℒ.UA ⊓ toConjAct g • 𝓓ˣ

/-- `Fˣ ≤ Δ_g` -/
lemma range_units_le_range (g : GL₂(𝔸ᶠ[F])) : 𝓕ˣ ≤ ℒ.Δ D g := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Subgroup.mem_sup_right ⟨x.map (algebraMap _ _).toMonoidHom, ?_⟩, _,
    ⟨x.map (algebraMap _ _).toMonoidHom, rfl⟩, ?_⟩
  · simp [Units.ext_iff, ← IsScalarTower.algebraMap_apply, RingHom.toMonoidHom_eq_coe]
  · ext1
    simp [toConjAct_smul, ← Algebra.commutes, RingHom.toMonoidHom_eq_coe]

/--
`[Δ_g : Fˣ]` is finite.
Since `g⁻¹ U g` is compact open, `g⁻¹ U g ⊆ x⁻¹GL₂(∏ 𝒪_{Fᵥ})x` for some `x`.
Let `𝒪 := x⁻¹M₂(∏ 𝒪_{Fᵥ})x ∩ D`.
Then `𝒪` is an order (why?) and `Δ_g/Fˣ ↪ 𝒪¹ := { x ∈ 𝒪 | N(x) = 1 }`,
where the latter is finite because it is discrete and bounded in `D ⊗_{ℚ} ℝ = ∏ ℍ`
(See Lemma 17.7.13 in Voight).
-/
lemma isFiniteRelIndex_Δ [NumberField.IsTotallyReal F] [IsQuaternionAlgebra F D]
    [IsQuaternionAlgebra.IsTotallyDefinite F D] (ℒ : LevelStruct F R) (g : GL₂(𝔸ᶠ[F])) :
    Subgroup.IsFiniteRelIndex 𝓕ˣ (ℒ.Δ D g) := by
  knownin1980s

variable (D) in
abbrev ΔIndex (g : GL₂(𝔸ᶠ[F])) : ℕ :=
  𝓕ˣ.relIndex (ℒ.Δ D g)

instance : 𝓕ˣ.Normal := Subgroup.normal_of_le_center _ (by
  rintro _ ⟨x, rfl⟩
  simp [Subgroup.mem_center_iff, Units.ext_iff, Algebra.commutes])

lemma isOpen_map_ker : IsOpen (X := GL₂(𝔸ᶠ[F])) (ℒ.χ.ker.map ℒ.U.subtype) :=
  ℒ.isOpen_U.isOpenEmbedding_subtypeVal.isOpenMap _ ℒ.isOpen_ker

variable (D M) in
def form : Submodule R (WeightTwoAutomorphicForm F D M) where
  carrier := { f | ∀ x : ℒ.U, x • f = ℒ.χ x • f }
  add_mem' {f g} hf hg x := by simp only [Set.mem_setOf_eq] at hf hg; simp [hf, hg]
  zero_mem' := by simp
  smul_mem' r f hf x := by
    simp only [Set.mem_setOf_eq] at hf
    rw [smul_comm, hf, smul_comm]

/-- A constructor for forms in `S(U, χ)`. -/
@[simps]
def mkForm
    (f : GL₂(𝔸ᶠ[F]) → M)
    (left_invt : ∀ d g, f (ιD d * g) = f g)
    (right_invt : ∀ g, ∀ u : ℒ.U, f (g * ↑u) = ℒ.χ u • f g)
    (trivial_central_char : ∀ z : 𝔸ᶠ[𝓞 F, F]ˣ, ∀ g, f (z • g) = f g) :
    ℒ.form D M where
  val.toFun := f
  val.left_invt := left_invt
  val.right_invt := ⟨_, ℒ.isOpen_map_ker, by rintro g _ ⟨x, hx, rfl⟩; simp_all⟩
  val.trivial_central_char := trivial_central_char
  property g := by ext; exact right_invt _ _

scoped[FLT] notation D "ˣ＼GL₂(𝔸 " F ")／" U:max =>
  DoubleCoset.Quotient (G := GL₂(𝔸ᶠ[F])) (MonoidHom.range <| WithRigidification.unitsIncl F D) U

lemma apply_mul_eq_χA_smul
    (f) (hf : f ∈ ℒ.form D M) (u : ℒ.UA) (g) : f (g * u) = ℒ.χA u • f g := by
  obtain ⟨⟨u, _, ⟨z, rfl⟩⟩, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _
    ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)) u
  have := fun g ↦ congr($(hf u) g)
  simp_all [LevelStruct.χA, Subgroup.smul_def, ← mul_assoc]

/-- A constructor for forms in `S(U, χ)` which instead asks for behaviour on `U 𝔸ˣ`. -/
abbrev mkFormA
    (f : GL₂(𝔸ᶠ[F]) → M)
    (left_invt : ∀ d g, f (ιD d * g) = f g)
    (right_invt : ∀ g, ∀ u : ℒ.UA, f (g * ↑u) = ℒ.χA u • f g) :
    ℒ.form D M :=
  ℒ.mkForm f left_invt (fun g u ↦ by simpa using right_invt g (Subgroup.inclusion le_sup_left u))
    (fun z g ↦ by
      convert right_invt g (Subgroup.inclusion le_sup_right ⟨_, z, rfl⟩) using 2
      · ext1
        simp [Algebra.smul_def, Units.smul_def, Algebra.commutes]
      · simp [-Subgroup.inclusion_mk])

open scoped Pointwise

variable (D) in
class IsSufficientlySmall (ℒ : LevelStruct F R) where
  coprime_ΔIndex : ∀ g, (orderOf ℒ.χ).Coprime (ℒ.ΔIndex D g)

export LevelStruct.IsSufficientlySmall (coprime_ΔIndex)

lemma toConjAct_smul_le_ker_χA [ℒ.IsSufficientlySmall D] (g : GL₂(𝔸ᶠ[F])) :
    (toConjAct g • 𝓓ˣ).subgroupOf ℒ.UA ≤ ℒ.χA.ker := by
  refine Subgroup.le_ker_of_le_ker_of_coprime_relIndex _ (orderOf ℒ.χ)
    (K₁ := 𝓕ˣ.subgroupOf _) ?_ ?_ ?_
  · ext x
    obtain ⟨⟨u, _, ⟨z, rfl⟩⟩, rfl⟩ := Subgroup.prodToSupOfRight_surjective _ _
      ((range_unitsMap_finiteAdeleRing_le_center ..).trans (Subgroup.center_le_centralizer _)) x
    simpa [LevelStruct.χA, -pow_orderOf_eq_one] using
      congr($(pow_orderOf_eq_one ℒ.χ) u)
  · simp only [Subgroup.subgroupOf, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
      Subgroup.range_subtype]
    exact ℒ.coprime_ΔIndex g
  · rintro ⟨x, hx⟩ ⟨u, rfl⟩
    exact ℒ.χA_inclusion_right ⟨_, u.map (algebraMap _ _).toMonoidHom, rfl⟩

lemma χA_eq_of_exists_mul_mul_eq [ℒ.IsSufficientlySmall D] (u v : ℒ.UA)
    (huv : ∃ g d d', ιD d * g * u = ιD d' * g * v) : ℒ.χA u = ℒ.χA v := by
  apply ((Group.isUnit v⁻¹).map ℒ.χA).mul_right_cancel
  simp only [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨g, d, d', e⟩ := huv
  refine ℒ.toConjAct_smul_le_ker_χA (D := D) g⁻¹ ?_
  suffices ∃ x, ιD x = g * u * v⁻¹ * g⁻¹ by
    simpa [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        toConjAct_smul, mul_assoc, Subgroup.mem_sup_of_normal_right]
  refine ⟨d⁻¹ * d', ?_⟩
  simp [eq_mul_inv_iff_mul_eq]
  simpa [mul_assoc, inv_mul_eq_iff_eq_mul] using e.symm

/-- Given a section to the projection `Dˣ＼GL₂(𝔸ᶠ[F])／U → GL₂(𝔸ᶠ[F])`,
`S(U, χ)` is isomorphic to the finite free module with basis `Dˣ＼GL₂(𝔸ᶠ[F])／U`. -/
def formEquivOfSection [ℒ.IsSufficientlySmall D]
    (σ : Dˣ＼GL₂(𝔸 F)／ℒ.UA → GL₂(𝔸ᶠ[F])) (δ : GL₂(𝔸ᶠ[F]) → Dˣ)
    (u : GL₂(𝔸ᶠ[F]) → ℒ.UA)
    (H : ∀ g : GL₂(𝔸ᶠ[F]), σ (DoubleCoset.mk 𝓓ˣ ℒ.UA g) = ιD (δ g) * g * u g) :
    ℒ.form D M ≃ₗ[R] ((Dˣ＼GL₂(𝔸 F)／ℒ.UA) → M) where
  toFun f x := f.1 (σ x)
  map_add' f g := by ext x; simp [-MonoidHom.coe_range]
  map_smul' r f := by ext x; simp [-MonoidHom.coe_range]
  invFun f :=
    ℒ.mkFormA (fun g ↦ ℒ.χA (u g)⁻¹ • f (DoubleCoset.mk _ _ g)) (fun d g ↦ by
    dsimp
    congr 1
    · refine map_inv_eq_iff.mpr ?_
      refine ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨g, δ (ιD d * g) * d, δ g, ?_⟩
      rw [map_mul, mul_assoc _ (ιD d) g, ← H, ← H]
      congr 1
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨d, rfl⟩, 1, by simp, by simp⟩
    · congr 1; exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨d, rfl⟩, 1, by simp, by simp⟩) (by
    intro g a
    dsimp [Subgroup.smul_def]
    rw [← mul_smul, mul_comm (ℒ.χA _) (ℒ.χA _), ← map_mul]
    congr 1
    · rw [map_inv_eq_map_comm, mul_inv_rev, inv_inv]
      refine ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨g * a, δ g, δ (g * a), ?_⟩
      rw [← H]
      simp only [← mul_assoc, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_cancel_right, ← H]
      congr 1
      exact (DoubleCoset.eq ..).mpr ⟨1, by simp, a, a.2, by simp⟩
    · congr 1
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨1, by simp, a, a.2, by simp⟩)
  left_inv f := by
    ext v
    trans ℒ.χA (u v)⁻¹ • ℒ.χA (u v) • f.1 v
    · have := ℒ.apply_mul_eq_χA_smul _ f.2
      simp_all [mul_assoc]
    · rw [← mul_smul, ← map_mul, inv_mul_cancel]; simp
  right_inv f := by
    ext x
    have : DoubleCoset.mk 𝓓ˣ ℒ.UA (σ x) = x := by
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
      exact .symm <| (DoubleCoset.eq ..).mpr ⟨_, ⟨_, rfl⟩, _, by simp, H ..⟩
    trans ℒ.χA 1 • f x; swap; · simp
    dsimp
    congr 1
    · rw [map_inv_eq_map_comm, inv_one]
      exact ℒ.χA_eq_of_exists_mul_mul_eq _ _ ⟨σ x, 1, (δ (σ x)), by simp [← H, this]⟩
    · simp [this]

/-- If `U` is sufficiently small,
`S(U, χ)` is isomorphic to the finite free module with basis `Dˣ＼GL₂(𝔸ᶠ[F])／U`. -/
def formEquiv [ℒ.IsSufficientlySmall D] :
    ℒ.form D M ≃ₗ[R] ((Dˣ＼GL₂(𝔸 F)／ℒ.UA) → M) :=
  formEquivOfSection _ Quotient.out
    (fun g ↦ (DoubleCoset.mk_out_eq_mul 𝓓ˣ ℒ.UA g).choose_spec.choose_spec.1.choose)
    (fun g ↦ ⟨_, (DoubleCoset.mk_out_eq_mul 𝓓ˣ ℒ.UA g).choose_spec.choose_spec.2.1⟩)
    fun g ↦ (DoubleCoset.mk_out_eq_mul _ _ g).choose_spec.choose_spec.2.2.trans <| by
      rw [(DoubleCoset.mk_out_eq_mul 𝓓ˣ ℒ.UA g).choose_spec.choose_spec.1.choose_spec]

variable (D) in
/-- Actually true for all totally definite quaternion algebra `D` but the instance
is provided elsewhere. -/
abbrev IsFinite (ℒ : LevelStruct F R) : Prop := Finite (Dˣ＼GL₂(𝔸 F)／ℒ.UA)

instance [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D] [Module.Finite R M] :
    Module.Finite R (ℒ.form D M) :=
  .of_surjective _ ℒ.formEquiv.symm.surjective

instance [ℒ.IsSufficientlySmall D] [ℒ.IsFinite D] [Module.Free R M] :
    Module.Free R (ℒ.form D M) :=
  .of_equiv ℒ.formEquiv.symm

instance : PartialOrder (LevelStruct F R) where
  le ℒ ℒ' := ∃ h : (ℒ.U ≤ ℒ'.U), ℒ.χ = ℒ'.χ.comp (Subgroup.inclusion h)
  le_refl _ := ⟨le_rfl, rfl⟩
  le_trans | ℒ₁, ℒ₂, ℒ₃, ⟨h₁₂, e₁₂⟩, ⟨h₂₃, e₂₃⟩ => ⟨h₁₂.trans h₂₃, by rw [e₁₂, e₂₃]; rfl⟩
  le_antisymm
  | ⟨U, _, _, _, _, _⟩, ⟨U', _, _, _, _, _⟩, ⟨h, e⟩, ⟨h', e'⟩ => by
    obtain rfl : U = U' := le_antisymm h h'; congr

lemma U_mono : Monotone fun ℒ : LevelStruct F R ↦ ℒ.U :=
  fun _ _ h ↦ h.1

lemma form_anti : Antitone (form (F := F) (D := D) (R := R) M) :=
  fun _ _ h _ hf x ↦ h.2 ▸ hf ⟨x.1, h.1 x.2⟩

/-- `(U, χ)` is normal in `(U', χ')` if `U ≤ U'` is normal and `χ'|_U = χ`. -/
class Normal (ℒ ℒ' : LevelStruct F R) : Prop extends (ℒ.U.subgroupOf ℒ'.U).Normal where
  le : ℒ ≤ ℒ'

instance (ℒ : LevelStruct F R) : ℒ.Normal ℒ where
  le := le_rfl
  toNormal := by simp

lemma le_normalizer (ℒ ℒ' : LevelStruct F R) [ℒ.Normal ℒ'] :
    ℒ'.U ≤ Subgroup.normalizer ℒ.U :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (U_mono Normal.le)).mp inferInstance

instance {ℒ ℒ' : LevelStruct F R} [ℒ.Normal ℒ'] : DistribMulAction ℒ'.U (ℒ.form D M) where
  smul u m := ⟨u • m, by
    intro v
    ext x
    have H₁ := congr($(m.2 ⟨_, ((inv_mem (le_normalizer ℒ ℒ' u.2)) _).mp v.2⟩) (x * u))
    have H₂ : ℒ'.χ ⟨(↑u)⁻¹ * ↑v * ↑u, mul_mem (mul_mem (inv_mem u.2)
      (Normal.le.1 v.2)) u.2⟩ = ℒ'.χ (Subgroup.inclusion Normal.le.1 v) := by
      change ℒ'.χ (u⁻¹ * (Subgroup.inclusion Normal.le.1 v) * u) = _
      simp_rw [map_mul, mul_right_comm _ _ (ℒ'.χ u), ← map_mul, inv_mul_cancel, one_mul]
    simp_all [Subgroup.smul_def, mul_assoc, (Normal.le (self := ‹_›)).2]⟩
  mul_smul x y m := Subtype.ext (mul_smul x y m.1)
  one_smul m := Subtype.ext (one_smul _ m.1)
  smul_zero x := Subtype.ext (smul_zero x)
  smul_add x m n := Subtype.ext (smul_add x m.1 n.1)

end LevelStruct

open IsDedekindDomain.FiniteAdeleRing

variable (F R) in
/-- A way to construct `LevelStruct` via a family of local level structs on finitely many finite
places. -/
structure LocalLevelStruct where
  /-- The set of finite places. -/
  S : Finset ℙ(F)
  /-- The open compacts at the given finite places. -/
  US : Π v : ℙ(F), Subgroup GL₂(v.adicCompletion F)
  isCompact_US_of_mem : ∀ v ∈ S, IsCompact (X := GL₂(v.adicCompletion F)) (US v)
  isOpen_US_of_mem: ∀ v ∈ S, IsOpen (X := GL₂(v.adicCompletion F)) (US v)
  US_eq_of_notMem : ∀ v ∉ S, US v = GL2.localFullLevel v
  /-- The characters at the given finite places. -/
  χ : Π v : ℙ(F), US v →* R
  χ_eq_of_notMem : ∀ v ∉ S, χ v = 1
  range_unitsMap_le_ker_χ : ∀ v ∈ S, (Units.map (algebraMap (v.adicCompletion F)
      M₂(v.adicCompletion F)).toMonoidHom).range.subgroupOf (US v) ≤ (χ v).ker
  isOpen_ker_χ_of_mem : ∀ v ∈ S, IsOpen ((χ v).ker : Set (US v))

namespace LocalLevelStruct

variable (ℒ : LocalLevelStruct F R) (v : ℙ(F))

lemma isOpen_US : IsOpen (X := GL₂(v.adicCompletion F)) (ℒ.US v) := by
  if h : v ∈ ℒ.S then exact ℒ.isOpen_US_of_mem _ h else
    exact ℒ.US_eq_of_notMem _ h ▸ GL2.localFullLevel.isOpen v

lemma isCompact_US : IsCompact (X := GL₂(v.adicCompletion F)) (ℒ.US v) := by
  if h : v ∈ ℒ.S then exact ℒ.isCompact_US_of_mem _ h else
    exact ℒ.US_eq_of_notMem _ h ▸ GL2.localFullLevel.isCompact v

/-- The `LevelStruct` constructed via a `LocalLevelStruct`. -/
@[simps -isSimp]
def toStruct : LevelStruct F R where
  U :=
  { carrier := { x | ∀ v, GL2.toAdicCompletion v x ∈ ℒ.US v }
    mul_mem' := by simp +contextual only [Set.mem_setOf_eq, map_mul, mul_mem, implies_true]
    one_mem' := by dsimp; simp only [map_one, one_mem, implies_true]
    inv_mem' := by dsimp; simp only [map_inv, inv_mem_iff, imp_self, implies_true] }
  isCompact_U := by
    classical
    rw [← GL2.restrictedProduct.toHomeomorph.symm.isCompact_preimage]
    convert RestrictedProduct.isCompact_forall_mem_of_eventually_subset ?_ ℒ.US
      ℒ.isCompact_US ?_
    · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v
    · exact Filter.eventually_of_mem ℒ.S.finite_toSet.compl_mem_cofinite fun v hv ↦
        M2.units_localFullLevel v ▸ (ℒ.US_eq_of_notMem v hv).le
  isOpen_U := by
    classical
    rw [← GL2.restrictedProduct.toHomeomorph.symm.isOpen_preimage]
    convert RestrictedProduct.isOpen_forall_mem_of_eventually_eq ?_ ℒ.US
      ℒ.isOpen_US ?_ using 1
    · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v
    · exact Filter.eventually_of_mem ℒ.S.finite_toSet.compl_mem_cofinite fun v hv ↦
        M2.units_localFullLevel v ▸ (ℒ.US_eq_of_notMem v hv).symm
  χ := ∏ v ∈ ℒ.S, (ℒ.χ v).comp (((GL2.toAdicCompletion v).comp
    (Subgroup.subtype _)).codRestrict _ (by rintro ⟨x, hx⟩; exact hx v))
  range_unitsMap_le_ker_χ := by
    rintro ⟨_, hg⟩ ⟨g, rfl⟩
    simp only [MonoidHom.mem_ker, MonoidHom.finsetProd_apply, MonoidHom.coe_comp,
      Function.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_subtype]
    refine Finset.prod_eq_one fun v hv ↦ ℒ.range_unitsMap_le_ker_χ v hv
      ⟨g.map (FiniteAdeleRing.toAdicCompletion v).toMonoidHom, ?_⟩
    ext1
    simp [GL2.toAdicCompletion, Matrix.algebraMap_eq_diagonal]
  isOpen_ker := by
    let : TopologicalSpace R := ⊥
    have : DiscreteTopology R := ⟨rfl⟩
    have := ℒ.isOpen_ker_χ_of_mem
    simp only [← MonoidHom.continuous_iff_isOpen_ker] at this ⊢
    eta_expand
    simp only [MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.codRestrict_apply, Subgroup.coe_subtype]
    refine continuous_finsetProd _ fun v hv ↦ (this v hv).comp ?_
    exact continuous_induced_rng.mpr
      ((GL2.continuous_toAdicCompletion _).comp continuous_subtype_val)

open scoped Classical in
noncomputable
def incl : ℒ.US v →* ℒ.toStruct.U :=
  ((GL2.finiteAdeleIncl v).comp (Subgroup.subtype _)).codRestrict _ <| by
  rintro ⟨x, hx⟩ w
  obtain rfl | h := eq_or_ne w v
  · simpa
  · simp [h]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma χ_incl (x) : ℒ.toStruct.χ (ℒ.incl v x) = ℒ.χ v x := by
  simp only [toStruct_χ, MonoidHom.finsetProd_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.codRestrict_apply]
  refine (Finset.prod_eq_single v ?_ ?_).trans ?_
  · intro w hw hvw
    convert (ℒ.χ w).map_one
    exact GL2.toAdicCompletion_finiteAdeleIncl_of_ne _ _ _ hvw
  · intro hv; simp [ℒ.χ_eq_of_notMem v hv]
  · congr 1
    ext1
    exact GL2.toAdicCompletion_finiteAdeleIncl_same _ _

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.LocalLevelStruct
