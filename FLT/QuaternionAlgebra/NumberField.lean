/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Bryan Wang Peng Jun
-/
module

public import FLT.Mathlib.Algebra.IsQuaternionAlgebra
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import FLT.Hacks.RightActionInstances
public import FLT.AutomorphicForm.GroupTheoryStuff
public import FLT.AutomorphicForm.Stuff
public import FLT.NumberField.Completion.Finite
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.Topology.Algebra.IsOpenUnits
public import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.Flat.Basic

/-!

# Definitions of various compact open subgrups of Dˣ and GL₂(𝔸_F^∞)

We define U₁(v) as a subgroup of GL₂(Fᵥ), and U₁(S) as a subgroup
of GL₂(𝔸_F^∞). We introduce the concept
of a rigidification `r : (D ⊗[F] 𝔸_F^∞) ≅ M₂(𝔸_F^∞)` in order
to push U₁(S) over to a subgroup of `(D ⊗[F] 𝔸_F^∞)ˣ`.

-/

@[expose] public section
variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

open IsDedekindDomain

open scoped NumberField TensorProduct

-- `adicCompletion` is now a one-field structure whose `@[ext]` lemma peels an extra
-- `.toCompletion` step; disable it locally so componentwise `ext` proofs stay in `adicCompletion`.
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext

namespace IsQuaternionAlgebra.NumberField

-- local notation "𝔸 " F:max => FiniteAdeleRing (𝓞 F) F

/-- `GL₂(F)` is notation for `GL (Fin 2) F`. -/
scoped[FLT] notation "GL₂(" F ")" => GL (Fin 2) F

/-- `M₂(F)` is notation for `Matrix (Fin 2) (Fin 2) F`. -/
scoped[FLT] notation "M₂(" F ")" => Matrix (Fin 2) (Fin 2) F

open scoped FLT Adele

/--
A rigidification of a quaternion algebra D over a number field F
is a fixed choice of `𝔸_F^∞`-algebra isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`. In other
words, it is a choice of splitting of `D ⊗[F] Fᵥ` (i.e. an isomorphism to `M₂(Fᵥ)`)
for all finite places `v` together with a guarantee that the isomorphism works
on the integral level at all but finitely many places. Such a rigidification exists
if and only if F is unramified at all finite places.
-/
class WithRigidification where
  /-- the inclusion `D ↪ M₂(𝔸ᶠ)` of a rigidification.
  This becomes an iso after lifting to `D ⊗ 𝔸ᶠ`. -/
  incl : D →ₐ[F] M₂(𝔸ᶠ[F])
  cond : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId 𝔸ᶠ[F] _) incl
    fun _ _ ↦ Algebra.commute_algebraMap_left ..)

section

variable [WithRigidification F D]

open scoped TensorProduct.RightActions in
/-- Given a rigidification of `D`, `D ⊗ 𝔸ᶠ` is isomorphic to `M₂(𝔸ᶠ)`. -/
noncomputable def WithRigidification.algEquiv :
    D ⊗[F] 𝔸ᶠ[F] ≃ₐ[𝔸ᶠ[F]] M₂(𝔸ᶠ[F]) :=
  .trans { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl } <|
    .ofBijective _ WithRigidification.cond

omit [IsQuaternionAlgebra F D] in
@[simp]
lemma WithRigidification.algEquiv_tmul (a b) :
    algEquiv F D (a ⊗ₜ b) = b • incl a := by
  simp [algEquiv, Algebra.smul_def]

/-- Given a rigidification, we get an embedding `Dˣ ↪ GL₂(𝔸_F)`. -/
noncomputable abbrev WithRigidification.unitsIncl : Dˣ →* GL₂(𝔸ᶠ[F]) :=
  Units.map (WithRigidification.incl.toMonoidHom)

noncomputable
instance : Module D M₂(𝔸ᶠ[F]) :=
  .compHom _ (WithRigidification.incl (F := F).toRingHom)

omit [IsQuaternionAlgebra F D] in
lemma WithRigidification.smul_def (d : D) (x : M₂(𝔸ᶠ[F])) : d • x = incl d * x := rfl

instance : IsScalarTower F D M₂(𝔸ᶠ[F]) :=
  .of_algebraMap_smul fun r x ↦ by simp [WithRigidification.smul_def, Algebra.smul_def]

instance : IsScalarTower D D M₂(𝔸ᶠ[F]) where
  smul_assoc a b m := by simp [WithRigidification.smul_def, mul_assoc]

instance : IsScalarTower D M₂(𝔸ᶠ[F]) M₂(𝔸ᶠ[F]) where
  smul_assoc a b m := by simp [WithRigidification.smul_def, mul_assoc]

lemma HeightOneSpectrum.nonempty {R : Type*} [CommRing R] (hR : ¬ IsField R) [Nontrivial R] :
    Nonempty (HeightOneSpectrum R) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  exact ⟨⟨I, inferInstance, by rintro rfl; exact hR (Ring.isField_iff_maximal_bot.mpr hI)⟩⟩

open scoped TensorProduct.RightActions in
lemma WithRigidification.incl_injective (F : Type*)
    [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D] :
    Function.Injective (WithRigidification.incl (F := F) (D := D)) := by
  refine .of_comp (f := (WithRigidification.algEquiv F D).symm) ?_
  convert Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := D)
    (B := FiniteAdeleRing (𝓞 F) F) ?_
  · ext x; apply (WithRigidification.algEquiv F D).injective; simp
  · exact (algebraMap F _).injective

lemma WithRigidification.unitsIncl_injective (F : Type*)
    [Field F] [NumberField F] (D : Type*) [Ring D] [Algebra F D] [WithRigidification F D] :
    Function.Injective (WithRigidification.unitsIncl F D) := by
  refine Units.map_injective (WithRigidification.incl_injective F D)

open scoped TensorProduct.RightActions in
lemma WithRigidification.det_incl_sq (F : Type*)
    [Field F] [NumberField F] {D : Type*} [Ring D] [Algebra F D]
    [WithRigidification F D] [Module.Finite F D]
    (d : D) : (WithRigidification.incl (F := F) d).det ^ 2 =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (Algebra.norm F d) := by
  classical
  have := Algebra.norm_one_tmul F (FiniteAdeleRing (𝓞 F) F) d
  rw [← Algebra.norm_eq_of_algEquiv (.ofBijective _ (WithRigidification.cond (F := F) (D := D)))]
    at this
  dsimp at this
  simpa only [map_one, one_mul, Algebra.norm_eq_det] using! this

lemma WithRigidification.unitsIncl_algebraMap (F : Type*)
    [Field F] [NumberField F] {D : Type*} [Ring D] [Algebra F D] [WithRigidification F D]
    (x : Fˣ) : WithRigidification.unitsIncl F D (x.map (algebraMap F D).toMonoidHom) =
      x.map (algebraMap _ _).toMonoidHom := by
  ext1; simp

end

/--
A quaternion algebra over a number field is unramified if it is split
at all finite places. This is implemented as the existence of a rigidification
of `D`, that is, an isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`.
-/
abbrev IsUnramified : Prop := Nonempty (WithRigidification F D)

end IsQuaternionAlgebra.NumberField

open IsQuaternionAlgebra.NumberField IsDedekindDomain

variable {F}

open scoped FLT

namespace IsDedekindDomain

/-- `M_2(O_v)` as a subring of `M_2(F_v)`. -/
noncomputable def M2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subring M₂(v.adicCompletion F) :=
  (v.adicCompletionIntegers F).matrix

/-- `GL₂(𝒪ᵥ)` as a subgroup of `GL₂(Fᵥ)`. -/
noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup GL₂(v.adicCompletion F) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

theorem M2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (X := M₂(v.adicCompletion F)) (M2.localFullLevel v) :=
  (NumberField.isOpenAdicCompletionIntegers F v).matrix

theorem M2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (X := M₂(v.adicCompletion F)) (M2.localFullLevel v) :=
  (isCompact_iff_compactSpace.mpr (NumberField.instCompactSpaceAdicCompletionIntegers F v)).matrix

@[simp]
lemma M2.units_localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    (M2.localFullLevel v).units = GL2.localFullLevel v := by
  simp only [M2.localFullLevel, ← Units.range_map_subtype, GL2.localFullLevel]
  rw [← MonoidHom.range_comp_mulEquiv
    (Units.mapEquiv (Subring.matrixEquiv
      (v.adicCompletionIntegers F).toSubring (n := Fin 2)).toMulEquiv)]
  rfl

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (X := GL₂(v.adicCompletion F)) (GL2.localFullLevel v) :=
  M2.units_localFullLevel v ▸ Submonoid.isOpen_units (M2.localFullLevel.isOpen _)

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (X := GL₂(v.adicCompletion F)) (GL2.localFullLevel v) :=
  M2.units_localFullLevel v ▸ Submonoid.units_isCompact (M2.localFullLevel.isCompact _)

lemma GL2.mem_localFullLevel {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F),
      Units.map ((v.adicCompletionIntegers F).subtype.mapMatrix.toMonoidHom) x' = x :=
  hx

lemma GL2.mem_localFullLevel' {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F), ∀ i j, x' i j = x i j := by
  refine (mem_localFullLevel hx).imp ?_
  simp only [RingHom.toMonoidHom_eq_coe, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply]
  rintro y hy
  simp [← hy]

-- shortcut instances for next theorem: needed after mathlib #34045
variable (v : HeightOneSpectrum (𝓞 F)) in
noncomputable instance : Ring (HeightOneSpectrum.adicCompletion F v) := inferInstance
variable (v : HeightOneSpectrum (𝓞 F)) in
noncomputable instance : CommRing (HeightOneSpectrum.adicCompletion F v) := inferInstance

set_option backward.isDefEq.respectTransparency false in
lemma GL2.v_det_val_mem_localFullLevel_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} (hx : x ∈ localFullLevel v) :
    Valued.v x.val.det = 1 := by
  obtain ⟨y, hy⟩ := mem_localFullLevel hx
  have hd : IsUnit y.det.val := by simp
  rw [Valued.isUnit_valuationSubring_iff] at hd
  simpa [← hy, Matrix.det_fin_two] using hd

lemma GL2.v_le_one_of_mem_localFullLevel (v : HeightOneSpectrum (𝓞 F)) {x}
    (hx : x ∈ localFullLevel v) (i j) : Valued.v (x i j) ≤ 1 := by
  simp only [localFullLevel, Units.map, RingHom.mapMatrix, Matrix.map, ValuationSubring.subtype,
    Subring.subtype, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_monoidHom_mk, Units.inv_eq_val_inv, Matrix.coe_units_inv, MonoidHom.mem_range,
    MonoidHom.mk'_apply, Matrix.GeneralLinearGroup.ext_iff, Matrix.of_apply] at hx
  obtain ⟨x', hx'⟩ := hx
  simp only [← hx', ← HeightOneSpectrum.mem_adicCompletionIntegers, SetLike.coe_mem]

lemma GL2.mem_localFullLevel_iff_v {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} :
    x ∈ localFullLevel v ↔ (∀ (i j), Valued.v (x i j) ≤ 1) ∧ Valued.v x.val.det = 1 :=
  ⟨fun h ↦ ⟨GL2.v_le_one_of_mem_localFullLevel _ h, GL2.v_det_val_mem_localFullLevel_eq_one h⟩, by
    intro ⟨h₁, h₂⟩
    let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x i j, h₁ i j⟩
    have det_eq : M.det = x.val.det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp [M]
    have isUnit_M :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Valued.isUnit_valuationSubring_iff.mpr (det_eq ▸ h₂)))
    use isUnit_M.unit
    ext i j; fin_cases i; all_goals fin_cases j
    all_goals simp [M]⟩

open Valued FLT

/-- local `U₀(v)`, defined as a subgroup of `GL₂(Fᵥ)` given by
matrices in `GL₂(𝒪ᵥ)` congruent to `(* *;0 *) mod v`. -/
noncomputable def GL2.localIwahoriLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := { x ∈ localFullLevel v | Valued.v (x.val 1 0) < 1 }
  mul_mem' {a b} ha hb := by
    simp_all only [Set.mem_setOf_eq, Units.val_mul]
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_⟩
    simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    apply Valuation.map_add_lt _
    · rw [map_mul]
      apply mul_lt_one_of_lt_of_le ha.2
      apply v_le_one_of_mem_localFullLevel _ hb.1
    · rw [map_mul, mul_comm]
      apply mul_lt_one_of_lt_of_le hb.2
      apply v_le_one_of_mem_localFullLevel _ ha.1
  one_mem' := by simp [one_mem]
  inv_mem' {a} ha := by
    simp_all [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
      v_det_val_mem_localFullLevel_eq_one ha.1]

lemma GL2.mem_localIwahoriLevel {v : HeightOneSpectrum (𝓞 F)} {g : GL₂(v.adicCompletion F)} :
    g ∈ localIwahoriLevel v ↔ g ∈ localFullLevel v ∧ Valued.v (g.val 1 0) < 1 := .rfl

lemma GL2.mem_localIwahoriLevel_iff_v {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} :
    x ∈ localIwahoriLevel v ↔ Valued.v (x 0 0) = 1 ∧ Valued.v (x 0 1) ≤ 1 ∧ Valued.v (x 1 0) < 1 ∧
      Valued.v (x 1 1) = 1 := by
  trans Valued.v x.val.det = 1 ∧ Valued.v (x 0 0) ≤ 1 ∧
      Valued.v (x 0 1) ≤ 1 ∧ Valued.v (x 1 0) < 1 ∧ Valued.v (x 1 1) ≤ 1
  · simp [GL2.mem_localIwahoriLevel, GL2.mem_localFullLevel_iff_v]
    grind
  trans 1 ≤ Valued.v (x 0 0) ∧ 1 ≤ Valued.v (x 1 1) ∧ Valued.v (x 0 0) ≤ 1 ∧
      Valued.v (x 0 1) ≤ 1 ∧ Valued.v (x 1 0) < 1 ∧ Valued.v (x 1 1) ≤ 1; swap
  · simp only [le_antisymm_iff]; grind
  · simp only [← and_assoc, and_congr_left_iff]
    intro h₁ h₂ h₃ h₄
    trans Valued.v (x 0 0 * x 1 1) = 1
    · rw [Matrix.det_fin_two]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · rw [← sub_add_cancel (_ * _) (x 0 1 * x 1 0), Valuation.map_add_eq_of_lt_left, h]
        rw [h, map_mul, ← one_mul (1 : WithZero _)]
        exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₃ h₂ zero_le zero_lt_one
      · rw [Valuation.map_sub_eq_of_lt_left, h]
        rw [h, ← one_mul (1 : WithZero _), map_mul]
        exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₃ h₂ zero_le zero_lt_one
    · simp only [map_mul]
      refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ ↦ (H₁.antisymm h₄) ▸ (H₂.antisymm h₁) ▸ one_mul _⟩
      · exact (mul_le_mul_iff_left₀ (by simp [pos_iff_ne_zero]; aesop)).mp
          (.trans_eq (by simpa) h.symm)
      · exact (mul_le_mul_iff_right₀ (by simp [pos_iff_ne_zero]; aesop)).mp
          (.trans_eq (by simpa) h.symm)

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localIwahoriLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (X := GL₂(v.adicCompletion F)) (GL2.localIwahoriLevel v) := by
  convert (GL2.localFullLevel.isOpen v).inter
      ((Valued.isOpen_ball _ 1).preimage (Continuous.matrix_elem Units.continuous_val 1 0))
  ext x
  refine and_congr .rfl Valued.v.restrict_lt_one_iff.symm

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localIwahoriLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (X := GL₂(v.adicCompletion F)) (GL2.localIwahoriLevel v) := by
  convert (GL2.localFullLevel.isCompact v).inter_right
      ((Valued.isClosed_ball _ 1).preimage (Continuous.matrix_elem Units.continuous_val 1 0))
  ext x
  refine and_congr .rfl Valued.v.restrict_lt_one_iff.symm

open scoped FLT

/-- `GL₂(𝒪ᵥ)` as a subgroup of `GL₂(Fᵥ)` is isomorpic to `GL₂(𝒪ᵥ)` as a type. -/
noncomputable
def GL2.localFullLevelEquiv (v : HeightOneSpectrum (𝓞 F)) :
    GL2.localFullLevel v ≃* GL₂(v.adicCompletionIntegers F) :=
  .symm <| .ofBijective
    (Units.map ((v.adicCompletionIntegers F).subtype.mapMatrix
      (m := Fin 2)).toMonoidHom).rangeRestrict ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (Units.map_injective (Matrix.map_injective Subtype.val_injective)),
        MonoidHom.rangeRestrict_surjective _⟩

@[simp]
lemma GL2.localFullLevelEquiv_symm_apply (v : HeightOneSpectrum (𝓞 F))
    (g : GL₂(v.adicCompletionIntegers F)) :
    ((GL2.localFullLevelEquiv v).symm g).1 = g.map (v.adicCompletionIntegers F).subtype := rfl

@[simp]
lemma GL2.localFullLevelEquiv_apply (v : HeightOneSpectrum (𝓞 F))
    (g : GL2.localFullLevel v) (i j) : (GL2.localFullLevelEquiv v g i j).1 = g.1 i j := by
  have : (GL2.localFullLevelEquiv v g).1 = Matrix.of fun i j ↦ ⟨g.1 i j,
      GL2.v_le_one_of_mem_localFullLevel v g.2 _ _⟩ := by
    apply Matrix.map_injective Subtype.val_injective
    change ((GL2.localFullLevelEquiv v).symm (GL2.localFullLevelEquiv v g)).1.1 = _
    simp only [MulEquiv.symm_apply_apply]
    ext; simp
  simp [this]

lemma GL2.localIwahoriLevel_le_localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    GL2.localIwahoriLevel v ≤ GL2.localFullLevel v := fun _ hg ↦ hg.1

open IsDedekindDomain HeightOneSpectrum

/-- The map from the Iwahori subgroup `(*, *; 0, *) mod v`
sending `(a, b; c, d)` to `a/d mod v` in `k(v)ˣ` as a monoid hom. -/
noncomputable
def GL2.localIwahoriLevel.char (v : HeightOneSpectrum (𝓞 F)) :
    GL2.localIwahoriLevel v →* (IsLocalRing.ResidueField (v.adicCompletionIntegers F))ˣ :=
  MonoidHom.toHomUnits
  { toFun g :=
      IsLocalRing.residue _ (GL2.localFullLevelEquiv v
        (Subgroup.inclusion (GL2.localIwahoriLevel_le_localFullLevel v) g) 0 0) /
      IsLocalRing.residue _ (GL2.localFullLevelEquiv v
        (Subgroup.inclusion (GL2.localIwahoriLevel_le_localFullLevel v) g) 1 1)
    map_one' := by simp
    map_mul' x y := by
      rw [div_mul_div_comm]
      congr 1
      · simp [Matrix.mul_apply, adicCompletionIntegers.isUnit_iff_valued_eq_one, y.2.2.ne]
      · simp [Matrix.mul_apply, adicCompletionIntegers.isUnit_iff_valued_eq_one, x.2.2.ne] }

lemma GL2.v_zero_zero_eq_one_of_mem_localIwahoriLevel
    (v : HeightOneSpectrum (𝓞 F)) {x : GL (Fin 2) (adicCompletion F v)}
    (hx : x ∈ GL2.localIwahoriLevel v) : Valued.v (x 0 0) = 1 := by
  have := (GL2.localIwahoriLevel.char v ⟨x, hx⟩).ne_zero
  simp_all [-Units.ne_zero, GL2.localIwahoriLevel.char,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]

lemma GL2.v_one_one_eq_one_of_mem_localIwahoriLevel
    (v : HeightOneSpectrum (𝓞 F)) {x : GL (Fin 2) (adicCompletion F v)}
    (hx : x ∈ GL2.localIwahoriLevel v) : Valued.v (x 1 1) = 1 := by
  have := (GL2.localIwahoriLevel.char v ⟨x, hx⟩).ne_zero
  simp_all [-Units.ne_zero, GL2.localIwahoriLevel.char,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]

lemma GL2.localIwahoriLevel.char_eq_one_iff {v : HeightOneSpectrum (𝓞 F)} {g} :
    char v g = 1 ↔ Valued.v (g.val 0 0 - g.val 1 1) < 1 := by
  simp only [char, Fin.isValue, Units.ext_iff, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk,
    OneHom.coe_mk, Units.val_one]
  rw [div_eq_one_iff_eq, ← sub_eq_zero]
  · have : Valued.v (g.1 0 0 - g.1 1 1) ≤ 1 :=
      (v.adicCompletionIntegers F).sub_mem (GL2.v_le_one_of_mem_localFullLevel _ g.2.1 _ _)
      (GL2.v_le_one_of_mem_localFullLevel _ g.2.1 _ _)
    simpa [← map_sub, adicCompletionIntegers.isUnit_iff_valued_eq_one]
  · simp [adicCompletionIntegers.isUnit_iff_valued_eq_one,
      GL2.v_one_one_eq_one_of_mem_localIwahoriLevel]

/-- local U_1(v), defined as a subgroup of GL₂(Fᵥ) given by
matrices in GL₂(𝒪ᵥ) congruent to (a *;0 a) mod v. -/
noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup GL₂(v.adicCompletion F) :=
  .copy ((localIwahoriLevel.char v).ker.map (Subgroup.subtype _))
    { x ∈ localIwahoriLevel v | Valued.v (x 0 0 - x 1 1) < 1 } <| by
    ext x
    by_cases hx : x ∈ localIwahoriLevel v <;> simp [hx, GL2.localIwahoriLevel.char_eq_one_iff]

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (X := GL₂(v.adicCompletion F)) (GL2.localTameLevel v) := by
  refine (GL2.localIwahoriLevel.isOpen v).inter (t := { x | Valued.v (x 0 0 - x 1 1) < 1 }) ?_
  simp_rw [← Valued.v.restrict_lt_one_iff]
  exact (Valued.isOpen_ball _ _).preimage
    (.sub (Units.continuous_val.matrix_elem _ _) (Units.continuous_val.matrix_elem _ _))

lemma GL2.localIwahoriLevel.ker_char {v : HeightOneSpectrum (𝓞 F)} :
    (char v).ker = (GL2.localTameLevel v).subgroupOf _ := by
  rw [GL2.localTameLevel, Subgroup.copy_eq]
  exact (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm

/-- local U_1(v), defined as a subgroup of GL₂(Fᵥ) given by
matrices in GL₂(𝒪ᵥ) congruent to `(a *;0 b) mod v` with `p ∤ ord_{k(v)}(a/b)`. -/
noncomputable def GL2.localPTameLevel (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  (((MaximalPQuotient.mk _ p).comp (localIwahoriLevel.char v)).ker.map (Subgroup.subtype _))

lemma GL2.localTameLevel_le_localPTameLevel
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    GL2.localTameLevel v ≤ GL2.localPTameLevel v p := by
  rw [GL2.localTameLevel, Subgroup.copy_eq]
  exact Subgroup.map_mono (MonoidHom.ker_le_ker_comp _ _)

lemma GL2.localPTameLevel_le_localIwahoriLevel
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    GL2.localPTameLevel v p ≤ GL2.localIwahoriLevel v :=
  (Subgroup.map_le_range _ _).trans (by simp)

theorem GL2.localPTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    IsOpen (X := GL₂(v.adicCompletion F)) (GL2.localPTameLevel v p) :=
  Subgroup.isOpen_mono (GL2.localTameLevel_le_localPTameLevel ..)
    (GL2.localTameLevel.isOpen v)

theorem GL2.localPTameLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    IsCompact (X := GL₂(v.adicCompletion F)) (GL2.localPTameLevel v p) :=
  (GL2.localIwahoriLevel.isCompact v).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (GL2.localPTameLevel.isOpen v p))
      (localPTameLevel_le_localIwahoriLevel _ _)

/-- The subgroup of `Fᵥˣ` consisting of elements in `𝒪ᵥˣ` whose order mod `v` is prime to `p`.
In particular it contains `1+v𝒪ᵥ`. -/
noncomputable
def GL2.localPTameLevelSubgroup (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    Subgroup (v.adicCompletion F)ˣ :=
  ((MaximalPQuotient.mk _ p).comp (Units.map (IsLocalRing.residue
    (v.adicCompletionIntegers F)).toMonoidHom)).ker.map (Units.map (algebraMap _ _).toMonoidHom)

lemma GL2.localIwahoriLevel.ker_char_comp (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    ((MaximalPQuotient.mk _ p).comp (char v)).ker = (GL2.localPTameLevel v p).subgroupOf _ :=
  (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _).symm

instance (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    ((GL2.localPTameLevel v p).subgroupOf (GL2.localIwahoriLevel v)).Normal := by
  rw [← GL2.localIwahoriLevel.ker_char_comp]; infer_instance

lemma GL2.mem_localPTameLevel
    {v : HeightOneSpectrum (𝓞 F)} {p : ℕ} {x : GL₂(v.adicCompletion F)} :
    x ∈ localPTameLevel v p ↔ x ∈ localIwahoriLevel v ∧
      ∃ h, Units.mk0 (x 0 0 / x 1 1) h ∈ GL2.localPTameLevelSubgroup v p := by
  refine ⟨fun h ↦ ⟨GL2.localPTameLevel_le_localIwahoriLevel _ _ h, ?_⟩, ?_⟩
  · have H := GL2.mem_localIwahoriLevel_iff_v.mp (GL2.localPTameLevel_le_localIwahoriLevel _ _ h)
    refine ⟨?_, ?_⟩
    · simp only [Fin.isValue, ne_eq, div_eq_zero_iff, not_or]
      exact ⟨fun h' ↦ by simp [h'] at H, fun h' ↦ by simp [h'] at H⟩
    · obtain ⟨x, hx, rfl⟩ := h
      dsimp at H
      have := GL2.localIwahoriLevel.char v x
      refine ⟨IsUnit.unit (a := ⟨x.1 0 0 / x.1 1 1, ?_⟩) ?_, ?_, ?_⟩
      · simp [mem_adicCompletionIntegers, H]
      · simp [adicCompletionIntegers.isUnit_iff_valued_eq_one, H]
      · simp only [SetLike.mem_coe, MonoidHom.mem_ker,
          MonoidHom.coe_comp, Function.comp_apply] at hx ⊢
        convert hx
        ext1
        dsimp [localIwahoriLevel.char]
        rw [eq_div_iff (by simp [adicCompletionIntegers.isUnit_iff_valued_eq_one, H]), ← map_mul]
        congr
        ext; simpa using div_mul_cancel₀ _ (fun h' ↦ by simp [h'] at H)
      · ext1; simp
  · rintro ⟨h₁, h₂, a, ha0, ha⟩
    have H := GL2.mem_localIwahoriLevel_iff_v.mp h₁
    refine ⟨⟨_, h₁⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply] at ha0 ⊢
    convert ha0
    ext1
    dsimp [localIwahoriLevel.char]
    rw [div_eq_iff (by simp [adicCompletionIntegers.isUnit_iff_valued_eq_one, H]), ← map_mul]
    congr
    have : x.1 1 1 ≠ 0 := fun h' ↦ by simp [h'] at H
    ext1
    simp [show a.1.1 = _ from congr(($ha).1), this]

lemma GL2.localIwahoriLevel_le_normalizer_localPTameLevel
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) :
    GL2.localIwahoriLevel v ≤ .normalizer (GL2.localPTameLevel v p) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (GL2.localPTameLevel_le_localIwahoriLevel ..)]
  infer_instance

end IsDedekindDomain

open RestrictedProduct

/-- The canonical F-algebra morphism from `𝔸_F^∞` (the finite adeles of a number field F) to
the local component `F_v` for `v` a finite place of `𝓞 F`. -/
noncomputable
def IsDedekindDomain.FiniteAdeleRing.toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v where
  __ := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

open scoped Adele

namespace IsDedekindDomain.FiniteAdeleRing

/-- The canonical group homomorphism from `GL_2(𝔸_F^∞)` to the local component `GL_2(F_v)` for `v`
a finite place. -/
noncomputable def GL2.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin 2) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (FiniteAdeleRing.toAdicCompletion v)).toMonoidHom

lemma GL2.continuous_toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) : Continuous (GL2.toAdicCompletion v) :=
  Units.continuous_map (continuous_id.matrix_map (RestrictedProduct.continuous_eval _))

open scoped RestrictedProduct in
/-- `RestrictedProduct.mulSingle` as a `MonoidHom`. -/
def _root_.RestrictedProduct.mulSingleHom {ι : Type*} {S : ι → Type*} {G : ι → Type*}
    [(i : ι) → SetLike (S i) (G i)] (A : (i : ι) → S i) [DecidableEq ι] [(i : ι) → Monoid (G i)]
    [∀ (i : ι), SubmonoidClass (S i) (G i)] (i : ι) :
    (G i) →* Πʳ i, [G i, A i] where
  toFun := RestrictedProduct.mulSingle _ _
  map_one' := by simp
  map_mul' _ _ := RestrictedProduct.mulSingle_mul ..

/-- The inclusion `GL₂(Fᵥ) → GL₂(𝔸ᶠ)` sending `g` to `(1, ..., g, ..., 1)`. -/
noncomputable
def GL2.finiteAdeleIncl (v : HeightOneSpectrum (𝓞 F)) : GL₂(v.adicCompletion F) →* GL₂(𝔸ᶠ[F]) :=
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  (ContinuousMulEquiv.restrictedProductMatrixUnits
    fun v ↦ Valued.isOpen_integer _).symm.toMonoidHom.comp
      ((RestrictedProduct.mulSingleHom _ v).comp (by exact .id _))

@[simp]
lemma GL2.toAdicCompletion_finiteAdeleIncl_of_ne
    (v w : HeightOneSpectrum (𝓞 F)) (x) (H : v ≠ w) :
    GL2.toAdicCompletion v (GL2.finiteAdeleIncl w x) = 1 := by
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  ext i j
  change (Pi.mulSingle
    (M := fun v : HeightOneSpectrum (𝓞 F) ↦ GL₂(v.adicCompletion F)) w x v).1 i j = _
  simp [H]

@[simp]
lemma GL2.toAdicCompletion_finiteAdeleIncl_same (v : HeightOneSpectrum (𝓞 F)) (x) :
    GL2.toAdicCompletion v (GL2.finiteAdeleIncl v x) = x := by
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.typeDecidableEq _
  ext i j
  change (Pi.mulSingle
    (M := fun v : HeightOneSpectrum (𝓞 F) ↦ GL₂(v.adicCompletion F)) v x v).1 i j = _
  simp

/-- `GL_2(𝔸_F^∞)` is isomorphic and homeomorphic to the
restricted product of the local components `GL_2(F_v)`.
-/
noncomputable def GL2.restrictedProduct :
    GL₂(𝔸ᶠ[F]) ≃ₜ*
    Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [GL₂(v.adicCompletion F), (M2.localFullLevel v).units] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits (NumberField.isOpenAdicCompletionIntegers F)

@[simp]
lemma GL2.restrictedProduct_apply (x : GL₂(𝔸ᶠ[F])) (v : HeightOneSpectrum (𝓞 F)) :
    (GL2.restrictedProduct x v) = GL2.toAdicCompletion v x := rfl

lemma GL2.ext (a b : GL₂(𝔸ᶠ[F])) (H : ∀ v, GL2.toAdicCompletion v a = GL2.toAdicCompletion v b) :
    a = b := by
  apply GL2.restrictedProduct.injective
  ext1 v
  simp [H]

lemma GL2.mul_comm_of_toAdicCompletion_eq_one
    (v : HeightOneSpectrum (𝓞 F)) (a b) (ha : GL2.toAdicCompletion v a = 1) :
    a * GL2.finiteAdeleIncl v b = GL2.finiteAdeleIncl v b * a := by
  apply GL2.ext _ _ fun w ↦ ?_
  obtain rfl | h := eq_or_ne w v
  · simp [ha]
  · simp [h]

variable (F) in
/-- A maximal compact of `GL₂(𝔸ᶠ[F])` given by `∏ GL₂(𝒪ᵥ)`. -/
noncomputable
def GL2.maximalCompact : Subgroup GL₂(𝔸ᶠ[F]) :=
  ⨅ v, (GL2.localFullLevel v).comap (GL2.toAdicCompletion v)

lemma GL2.maximalCompact.isOpen : IsOpen (X := GL₂(𝔸ᶠ[F])) (GL2.maximalCompact F) := by
  classical
  rw [← GL2.restrictedProduct.toHomeomorph.symm.isOpen_preimage]
  convert! RestrictedProduct.isOpen_forall_mem _ using 1
  · ext; simp [maximalCompact, ← GL2.restrictedProduct_apply]; rfl
  · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v

lemma GL2.maximalCompact.isCompact : IsCompact (X := GL₂(𝔸ᶠ[F])) (GL2.maximalCompact F) := by
  classical
  rw [← GL2.restrictedProduct.toHomeomorph.symm.isCompact_preimage]
  convert! RestrictedProduct.isCompact_forall_mem_of_eventually_subset _
    (GL2.localFullLevel (F := F)) GL2.localFullLevel.isCompact _ using 1
  · ext; simp [maximalCompact, ← GL2.restrictedProduct_apply]
  · exact fun v ↦ M2.units_localFullLevel v ▸ GL2.localFullLevel.isOpen v
  · simp [M2.units_localFullLevel]

end IsDedekindDomain.FiniteAdeleRing
