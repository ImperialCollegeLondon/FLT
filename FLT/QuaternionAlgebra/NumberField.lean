module

public import FLT.Mathlib.Algebra.IsQuaternionAlgebra
public import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
public import FLT.Mathlib.Topology.Instances.Matrix
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Compact
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import FLT.Hacks.RightActionInstances
public import FLT.NumberField.Completion.Finite
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

namespace IsQuaternionAlgebra.NumberField

open scoped TensorProduct.RightActions in
/--
A rigidification of a quaternion algebra D over a number field F
is a fixed choice of `𝔸_F^∞`-algebra isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`. In other
words, it is a choice of splitting of `D ⊗[F] Fᵥ` (i.e. an isomorphism to `M₂(Fᵥ)`)
for all finite places `v` together with a guarantee that the isomorphism works
on the integral level at all but finitely many places. Such a rigidification exists
if and only if F is unramified at all finite places.
-/
abbrev Rigidification :=
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F) ≃ₐ[FiniteAdeleRing (𝓞 F) F]
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))

/--
A quaternion algebra over a number field is unramified if it is split
at all finite places. This is implemented as the existence of a rigidification
of `D`, that is, an isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`.
-/
def IsUnramified : Prop := Nonempty (Rigidification F D)

end IsQuaternionAlgebra.NumberField

open IsQuaternionAlgebra.NumberField IsDedekindDomain

variable {F}

namespace IsDedekindDomain

/-- `M_2(O_v)` as a subring of `M_2(F_v)`. -/
noncomputable def M2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
  (v.adicCompletionIntegers F).matrix

/-- `GL₂(𝒪ᵥ)` as a subgroup of `GL₂(Fᵥ)`. -/
noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

theorem M2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (M2.localFullLevel v).carrier :=
  (NumberField.isOpenAdicCompletionIntegers F v).matrix

theorem M2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (M2.localFullLevel v).carrier :=
  (isCompact_iff_compactSpace.mpr (NumberField.instCompactSpaceAdicCompletionIntegers F v)).matrix

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localFullLevel_eq_units (v : HeightOneSpectrum (𝓞 F)) :
    GL2.localFullLevel v = (M2.localFullLevel v).toSubmonoid.units := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, rfl⟩
    rw [Submonoid.mem_units_iff]
    constructor
    · let m : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) := u
      have hm : m.map (v.adicCompletionIntegers F).subtype ∈
          (v.adicCompletionIntegers F).matrix := by
        change m.map Subtype.val ∈ Set.matrix
          (↑(v.adicCompletionIntegers F) : Set (v.adicCompletion F))
        rw [Set.mem_matrix]
        intro i j
        exact (m i j).2
      simpa [m, Units.map] using hm
    · let m : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) := u⁻¹
      have hm : m.map (v.adicCompletionIntegers F).subtype ∈
          (v.adicCompletionIntegers F).matrix := by
        change m.map Subtype.val ∈ Set.matrix
          (↑(v.adicCompletionIntegers F) : Set (v.adicCompletion F))
        rw [Set.mem_matrix]
        intro i j
        exact (m i j).2
      simpa [m, Units.map] using hm
  · intro hx
    rw [Submonoid.mem_units_iff] at hx
    rcases hx with ⟨hx, hxinv⟩
    have hx_set : (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈
        Set.matrix (↑(v.adicCompletionIntegers F) : Set (v.adicCompletion F)) := by
      simpa [Subring.matrix] using hx
    have hxinv_set : ((x⁻¹ : Units (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) ∈
        Set.matrix (↑(v.adicCompletionIntegers F) : Set (v.adicCompletion F)) := by
      simpa [Subring.matrix] using hxinv
    have hx' : ∀ i j, (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        (v.adicCompletionIntegers F) := by
      simpa [Set.mem_matrix] using hx_set
    have hxinv' : ∀ i j, ((x⁻¹ : Units (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ (v.adicCompletionIntegers F) := by
      simpa [Set.mem_matrix] using hxinv_set
    let a : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x i j, hx' i j⟩
    let b : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨(x⁻¹ : Units (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) i j,
        hxinv' i j⟩
    have ha : a.map (v.adicCompletionIntegers F).subtype = x := by
      ext i j
      simp [a]
    have hb : b.map (v.adicCompletionIntegers F).subtype = x⁻¹ := by
      ext i j
      simp [b]
    have hmul : (a * b).map (v.adicCompletionIntegers F).subtype = 1 := by
      have h0 : (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
          (x⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
        simpa using x.mul_inv
      rw [Matrix.map_mul, ha, hb]
      simpa using h0
    have hmul' : a * b = 1 := by
      have hmulmap : (a * b).map (v.adicCompletionIntegers F).subtype =
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F)).map
            (v.adicCompletionIntegers F).subtype := by
        simpa using hmul
      exact Matrix.map_injective
        (show Function.Injective (v.adicCompletionIntegers F).subtype from Subtype.val_injective)
        hmulmap
    refine ⟨Units.mkOfMulEqOne a b hmul', ?_⟩
    ext i j
    simp [Units.map, a]

theorem GL2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localFullLevel v).carrier :=
  by
    simpa [GL2.localFullLevel_eq_units] using
      (Submonoid.isOpen_units (U := (M2.localFullLevel v).toSubmonoid)
        (M2.localFullLevel.isOpen v))

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localFullLevel v).carrier :=
  by
    simpa [GL2.localFullLevel_eq_units] using
      (Submonoid.units_isCompact (S := (M2.localFullLevel v).toSubmonoid)
        (M2.localFullLevel.isCompact v))

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

lemma GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one {v : HeightOneSpectrum (𝓞 F)}
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
    all_goals simp [M]
  ⟩

open Valued

/-- local U_1(v), defined as a subgroup of GL₂(Fᵥ) given by
matrices in GL₂(𝒪ᵥ) congruent to (a *;0 a) mod v. -/
noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {x ∈ localFullLevel v |
    Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
  mul_mem' {a b} ha hb := by
    simp_all only [Set.mem_setOf_eq, Units.val_mul]
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.isValue, Fin.sum_univ_two]
      convert_to Valued.v ((a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) +
        (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) < 1
      · ring_nf
      suffices Valued.v (a.val 0 1 * b.val 1 0) < 1 ∧
                Valued.v (a.val 1 0 * b.val 0 1) < 1 ∧
                Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) < 1 by
        apply Valuation.map_add_lt _ this.2.2 ?_
        apply Valuation.map_sub_lt _ this.1 this.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · convert_to Valued.v (a.val 0 0 * (b.val 0 0 - b.val 1 1) +
          (a.val 0 0 - a.val 1 1) * b.val 1 1) < 1
        · ring_nf
        apply Valuation.map_add_lt _
        · rw [map_mul, mul_comm]
          apply mul_lt_one_of_lt_of_le hb.2.1
          apply v_le_one_of_mem_localFullLevel _ ha.1
        · rw [map_mul]
          apply mul_lt_one_of_lt_of_le ha.2.1
          apply v_le_one_of_mem_localFullLevel _ hb.1
    · simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
      apply Valuation.map_add_lt _
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
  one_mem' := by simp [one_mem]
  inv_mem' {a} ha := by
    simp_all only [Set.mem_setOf_eq, inv_mem_iff, Matrix.coe_units_inv, true_and,
      Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one,
      ← mul_sub, map_mul, map_inv₀, mul_neg, Valuation.map_neg]
    rw [Valuation.map_sub_swap, v_det_val_mem_localFullLevel_eq_one ha.1]
    simp [ha.2]

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localTameLevel v).carrier :=
  by
    have hL : IsOpen (GL2.localFullLevel v : Set (GL (Fin 2) (v.adicCompletion F))) :=
      GL2.localFullLevel.isOpen v
    have hS : IsOpen ({x : v.adicCompletion F | Valued.v x < 1} : Set (v.adicCompletion F)) := by
      let U : Set (v.adicCompletionIntegers F) := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
      have hU : IsOpen U := IsLocalRing.isOpen_maximalIdeal (R := v.adicCompletionIntegers F)
      have hsub : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
        NumberField.isOpenAdicCompletionIntegers F v
      have himg :
          IsOpen ((Subtype.val : v.adicCompletionIntegers F → v.adicCompletion F) '' U :
            Set (v.adicCompletion F)) :=
        hsub.isOpenEmbedding_subtypeVal.isOpenMap _ hU
      have hEq :
          ((Subtype.val : v.adicCompletionIntegers F → v.adicCompletion F) '' U :
              Set (v.adicCompletion F)) =
            {x : v.adicCompletion F | Valued.v x < 1} := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := y)).mp hy
        · intro hx
          have hxsub : x ∈ (v.adicCompletionIntegers F) := by
            exact (Valuation.mem_integer_iff (v := Valued.v) x).2 (le_of_lt hx)
          refine ⟨⟨x, hxsub⟩, ?_, rfl⟩
          exact (Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := ⟨x, hxsub⟩)).2 hx
      simpa [hEq] using himg
    have hmat :
        Continuous fun x : GL (Fin 2) (v.adicCompletion F) =>
          ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :=
      Units.continuous_val
    have h00 :
        Continuous fun x : GL (Fin 2) (v.adicCompletion F) =>
          (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0)) :=
      (continuous_apply (i := (0 : Fin 2))).comp
        ((continuous_apply (i := (0 : Fin 2))).comp hmat)
    have h11 :
        Continuous fun x : GL (Fin 2) (v.adicCompletion F) =>
          (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) :=
      (continuous_apply (i := (1 : Fin 2))).comp
        ((continuous_apply (i := (1 : Fin 2))).comp hmat)
    have h10 :
        Continuous fun x : GL (Fin 2) (v.adicCompletion F) =>
          (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)) :=
      (continuous_apply (i := (0 : Fin 2))).comp
        ((continuous_apply (i := (1 : Fin 2))).comp hmat)
    have hcond1 :
        IsOpen {x : GL (Fin 2) (v.adicCompletion F) |
          Valued.v (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) -
            ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) < 1} := by
      exact hS.preimage (h00.sub h11)
    have hcond2 :
        IsOpen {x : GL (Fin 2) (v.adicCompletion F) |
          Valued.v (((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)) < 1} := by
      exact hS.preimage h10
    simpa [GL2.localTameLevel, Set.mem_setOf_eq, and_left_comm, and_assoc] using
      hL.inter (hcond1.inter hcond2)

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localTameLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localTameLevel v).carrier :=
  by
    let L := GL2.localFullLevel v
    have hLc : IsCompact (L : Set (GL (Fin 2) (v.adicCompletion F))) :=
      GL2.localFullLevel.isCompact v
    haveI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
    have hopen : IsOpen (GL2.localTameLevel v).carrier := GL2.localTameLevel.isOpen v
    have hsubopen : IsOpen ((GL2.localTameLevel v).subgroupOf L : Set L) :=
      Subgroup.subgroupOf_isOpen (U := L) (K := GL2.localTameLevel v) hopen
    let U : OpenSubgroup L := ⟨(GL2.localTameLevel v).subgroupOf L, hsubopen⟩
    have hclosed : IsClosed (U : Set L) := OpenSubgroup.isClosed U
    have hcomp : IsCompact (U : Set L) := hclosed.isCompact
    have hEq : ((Subtype.val : L → GL (Fin 2) (v.adicCompletion F)) '' (U : Set L)) =
        (GL2.localTameLevel v).carrier := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hy
      · intro hx
        rcases hx with ⟨hxL, hxcond⟩
        refine ⟨⟨x, hxL⟩, ?_, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨hxL, hxcond⟩
    simpa [hEq] using
      hcomp.image (continuous_subtype_val : Continuous (Subtype.val : L →
        GL (Fin 2) (v.adicCompletion F)))

end IsDedekindDomain

open RestrictedProduct

/-- The canonical F-algebra morphism from `𝔸_F^∞` (the finite adeles of a number field F) to
the local component `F_v` for `v` a finite place of `𝓞 F`. -/
noncomputable
def IsDedekindDomain.FiniteAdeleRing.toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v where
  __ := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

namespace IsDedekindDomain.FiniteAdeleRing

/-- The canonical group homomorphism from `GL_2(𝔸_F^∞)` to the local component `GL_2(F_v)` for `v`
a finite place. -/
noncomputable def GL2.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →*
    GL (Fin 2) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (FiniteAdeleRing.toAdicCompletion v)).toMonoidHom

/-- `GL_2(𝔸_F^∞)` is isomorphic and homeomorphic to the
restricted product of the local components `GL_2(F_v)`.
-/
noncomputable def GL2.restrictedProduct :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
    Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits (NumberField.isOpenAdicCompletionIntegers F)

-- Adapted from `polyproof/FLT`, PR #38, to expose the restricted-product evaluation
-- lemmas needed by the Hecke operator proofs.

/-- The "value" form of the bridging computation: at every entry `(i,j)` and place `w`,
the matrix entry of `GL2.toAdicCompletion w (rp.symm x)` equals the corresponding
entry of `(x w).val`. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_val_apply
    (w : HeightOneSpectrum (𝓞 F))
    (x : Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units])
    (i j : Fin 2) :
    ((GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm x)).val i j) = (x w).val i j := by
  rfl

/-- The unit-level version of `toAdicCompletion_restrictedProduct_symm_val_apply`:
applying `GL2.toAdicCompletion w` to the inverse image of `x` under the restricted-
product equivalence yields `x w` directly. Useful for transporting global statements
about `GL₂(𝔸_F^∞)` to local statements at each place. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_apply
    (w : HeightOneSpectrum (𝓞 F))
    (x : Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units]) :
    GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm x) = x w := by
  ext i j
  exact GL2.toAdicCompletion_restrictedProduct_symm_val_apply w x i j

/-- Bridging lemma: applying `GL2.toAdicCompletion w` to the embedding of a single
local element `g_loc` at place `v` via the restricted product isomorphism gives
`g_loc` if `w = v` and `1` otherwise. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_same
    [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (v : HeightOneSpectrum (𝓞 F)) (g_loc : GL (Fin 2) (v.adicCompletion F)) :
    GL2.toAdicCompletion v
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v g_loc)) = g_loc := by
  ext i j
  rw [GL2.toAdicCompletion_restrictedProduct_symm_val_apply,
    RestrictedProduct.mulSingle_eq_same]

lemma GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_ne
    [DecidableEq (HeightOneSpectrum (𝓞 F))]
    {w v : HeightOneSpectrum (𝓞 F)} (hwv : w ≠ v)
    (g_loc : GL (Fin 2) (v.adicCompletion F)) :
    GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v g_loc)) = 1 := by
  ext i j
  rw [GL2.toAdicCompletion_restrictedProduct_symm_val_apply,
    RestrictedProduct.mulSingle_eq_of_ne _ _ hwv]

end IsDedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

/-- If `F` is a number field and `S` is a finite set of finite places of `𝓞 F` then
`GL2.TameLevel S` is the subgroup of `GL₂(𝔸_F^∞)` consisting of things in `GL₂(𝓞ᵥ)` for
all places, and furthermore in the local "`U₁(v)`" subgroup `(a *;0 a) mod v` for all `v ∈ S`.
-/
noncomputable def GL2.TameLevel (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
    carrier := {x | (∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v) ∧
      (∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v)}
    mul_mem' {a b} ha hb := by simp_all [mul_mem]
    one_mem' := by simp_all [one_mem]
    inv_mem' {x} hx := by simp_all

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem GL2.TameLevel.isOpen : IsOpen (GL2.TameLevel S).carrier :=
  by
    classical
    let RP :=
      Πʳ (v : HeightOneSpectrum (𝓞 F)),
        [GL (Fin 2) (v.adicCompletion F), ↑(M2.localFullLevel v).units]_[Filter.cofinite]
    have hK0_open : IsOpen {x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} := by
      exact
        RestrictedProduct.isOpen_forall_mem
          (R := fun v : HeightOneSpectrum (𝓞 F) => GL (Fin 2) (v.adicCompletion F))
          (A := fun v => (M2.localFullLevel v).units)
          (fun v =>
            Submonoid.isOpen_units
              (U := (M2.localFullLevel v).toSubmonoid)
              (M2.localFullLevel.isOpen v))
    have hK0_compact : IsCompact {x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} := by
      have hf :
          Continuous
            (RestrictedProduct.structureMap
              (fun v : HeightOneSpectrum (𝓞 F) => GL (Fin 2) (v.adicCompletion F))
              (fun v => ((M2.localFullLevel v).units : Set (GL (Fin 2) (v.adicCompletion F))))
              Filter.cofinite) :=
        (RestrictedProduct.isOpenEmbedding_structureMap
          (fun v =>
            Submonoid.isOpen_units
              (U := (M2.localFullLevel v).toSubmonoid)
              (M2.localFullLevel.isOpen v))).continuous
      letI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace ((M2.localFullLevel v).units) :=
        fun v =>
          isCompact_iff_compactSpace.mp <|
            Submonoid.units_isCompact
              (S := (M2.localFullLevel v).toSubmonoid)
              (M2.localFullLevel.isCompact v)
      letI : Nonempty ((i : HeightOneSpectrum (𝓞 F)) → (M2.localFullLevel i).units) :=
        ⟨fun v => 1⟩
      have hRange :
          ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} : Set RP) =
            Set.range
              (RestrictedProduct.structureMap
                (fun v : HeightOneSpectrum (𝓞 F) => GL (Fin 2) (v.adicCompletion F))
                (fun v => ((M2.localFullLevel v).units : Set (GL (Fin 2) (v.adicCompletion F))))
                Filter.cofinite) := by
        ext x
        constructor
        · intro hx
          refine ⟨fun v ↦ ⟨x v, hx v⟩, ?_⟩
          rfl
        · rintro ⟨y, rfl⟩
          intro v
          exact (y v).2
      rw [hRange]
      simpa [Set.range] using (isCompact_univ.image hf)
    have hKS_open : IsOpen {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} := by
      have h :
          IsOpen (⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v}) := by
        exact isOpen_biInter_finset fun v hv =>
          (GL2.localTameLevel.isOpen v).preimage (RestrictedProduct.continuous_eval v)
      have hset :
          {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} =
            ⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v} := by
        ext x
        simp
      rw [hset]
      exact h
    have hKS_closed : IsClosed {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} := by
      have h :
          IsClosed (⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v}) := by
        exact isClosed_biInter fun v hv =>
          (GL2.localTameLevel.isCompact v).isClosed.preimage
            (RestrictedProduct.continuous_eval v)
      have hset :
          {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} =
            ⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v} := by
        ext x
        simp
      rw [hset]
      exact h
    have hK_open :
        IsOpen
          ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} ∩
            {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v}) := by
      exact hK0_open.inter hKS_open
    have hK_compact :
        IsCompact
          ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} ∩
            {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v}) := by
      exact hK0_compact.inter_right hKS_closed
    have hEq :
        (GL2.TameLevel S).carrier =
          (GL2.restrictedProduct (F := F)) ⁻¹'
            ({x : RP | (∀ v, x v ∈ (M2.localFullLevel v).units) ∧
              ∀ v ∈ S, x v ∈ GL2.localTameLevel v}) := by
      ext x
      constructor <;> intro hx <;>
        simpa [GL2.TameLevel, GL2.localFullLevel_eq_units, and_left_comm, and_assoc] using hx
    have hpre :
        IsOpen
          ((GL2.restrictedProduct (F := F)).toHomeomorph ⁻¹'
            ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} ∩
              {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v})) :=
      (GL2.restrictedProduct (F := F)).toHomeomorph.isOpen_preimage.2 hK_open
    simpa [hEq] using hpre

theorem GL2.TameLevel.isCompact : IsCompact (GL2.TameLevel S).carrier :=
  by
    classical
    let RP :=
      Πʳ (v : HeightOneSpectrum (𝓞 F)),
        [GL (Fin 2) (v.adicCompletion F), ↑(M2.localFullLevel v).units]_[Filter.cofinite]
    have hK0_compact : IsCompact {x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} := by
      have hf :
          Continuous
            (RestrictedProduct.structureMap
              (fun v : HeightOneSpectrum (𝓞 F) => GL (Fin 2) (v.adicCompletion F))
              (fun v => ((M2.localFullLevel v).units : Set (GL (Fin 2) (v.adicCompletion F))))
              Filter.cofinite) :=
        (RestrictedProduct.isOpenEmbedding_structureMap
          (fun v =>
            Submonoid.isOpen_units
              (U := (M2.localFullLevel v).toSubmonoid)
              (M2.localFullLevel.isOpen v))).continuous
      letI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace ((M2.localFullLevel v).units) :=
        fun v =>
          isCompact_iff_compactSpace.mp <|
            Submonoid.units_isCompact
              (S := (M2.localFullLevel v).toSubmonoid)
              (M2.localFullLevel.isCompact v)
      letI : Nonempty ((i : HeightOneSpectrum (𝓞 F)) → (M2.localFullLevel i).units) :=
        ⟨fun v => 1⟩
      have hRange :
          ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} : Set RP) =
            Set.range
              (RestrictedProduct.structureMap
                (fun v : HeightOneSpectrum (𝓞 F) => GL (Fin 2) (v.adicCompletion F))
                (fun v => ((M2.localFullLevel v).units : Set (GL (Fin 2) (v.adicCompletion F))))
                Filter.cofinite) := by
        ext x
        constructor
        · intro hx
          refine ⟨fun v ↦ ⟨x v, hx v⟩, ?_⟩
          rfl
        · rintro ⟨y, rfl⟩
          intro v
          exact (y v).2
      rw [hRange]
      simpa [Set.range] using (isCompact_univ.image hf)
    have hKS_closed : IsClosed {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} := by
      have h :
          IsClosed (⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v}) := by
        exact isClosed_biInter fun v hv =>
          (GL2.localTameLevel.isCompact v).isClosed.preimage
            (RestrictedProduct.continuous_eval v)
      have hset :
          {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v} =
            ⋂ v ∈ S, {x : RP | x v ∈ GL2.localTameLevel v} := by
        ext x
        simp
      rw [hset]
      exact h
    have hK_compact :
        IsCompact
          ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} ∩
            {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v}) := by
      exact hK0_compact.inter_right hKS_closed
    have hEq :
        (GL2.TameLevel S).carrier =
          (GL2.restrictedProduct (F := F)) ⁻¹'
            ({x : RP | (∀ v, x v ∈ (M2.localFullLevel v).units) ∧
              ∀ v ∈ S, x v ∈ GL2.localTameLevel v}) := by
      ext x
      constructor <;> intro hx <;>
        simpa [GL2.TameLevel, GL2.localFullLevel_eq_units, and_left_comm, and_assoc] using hx
    have hpre :
        IsCompact
          ((GL2.restrictedProduct (F := F)).toHomeomorph ⁻¹'
            ({x : RP | ∀ v, x v ∈ (M2.localFullLevel v).units} ∩
              {x : RP | ∀ v ∈ S, x v ∈ GL2.localTameLevel v})) :=
      (GL2.restrictedProduct (F := F)).toHomeomorph.isCompact_preimage.2 hK_compact
    simpa [hEq] using hpre

open scoped TensorProduct.RightActions in
/-- The subgroup of `(D ⊗ 𝔸_F^∞)ˣ` corresponding to the subgroup `U₁(S)` of `GL₂(𝔸_F^∞)`
(that is, matrices congruent to `(a *; 0 a) mod v` for all `v ∈ S`) via the rigidification `r`. -/
noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D) :
    Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_toFun (r : Rigidification F D) :
    Continuous r :=
  letI : ∀ (i : HeightOneSpectrum (𝓞 F)),
      Algebra (FiniteAdeleRing (𝓞 F) F) ((i.adicCompletion F)) :=
    fun i ↦ (RestrictedProduct.evalRingHom _ i).toAlgebra
  IsModuleTopology.continuous_of_linearMap r.toLinearMap

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_invFun (r : Rigidification F D) :
    Continuous r.symm := by
  haveI : ContinuousAdd (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))
  exact IsModuleTopology.continuous_of_linearMap r.symm.toLinearMap

end HeightOneSpectrum

end IsDedekindDomain
