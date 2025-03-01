import Mathlib
import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import FLT.Mathlib.RingTheory.Valuation.Basic
import FLT.Mathlib.RingTheory.Valuation.ValuationSubring
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Instances.Matrix

variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

open DedekindDomain

open scoped NumberField TensorProduct

namespace IsQuaternionAlgebra.NumberField
/--
A rigidification of a quaternion algebra D over a number field F
is a fixed choice of isomorphism D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞). In other
words, it is a choice of splitting of `D ⊗[F] Fᵥ` (i.e. an isomorphism to `M₂(Fᵥ)`)
for all finite places `v` together with a guarantee that the isomorphism works
on the integral level at all but finitely many places. Such a rigidification exists
if and only if F is unramified at all finite places.
-/
abbrev Rigidification :=
    ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D ≃ₐ[FiniteAdeleRing (𝓞 F) F]
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

noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

theorem GL2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localFullLevel v).carrier :=
  sorry

theorem GL2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localFullLevel v).carrier :=
  sorry

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

lemma GL2.v_det_val_mem_localFullLevel_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} (hx : x ∈ localFullLevel v) :
    Valued.v x.val.det = 1 := by
  obtain ⟨y, hy⟩ := mem_localFullLevel hx
  have hd : IsUnit y.det.val := by simp
  rw [Valued.isUnit_valuationSubring_iff] at hd
  simpa [← hy, Matrix.det_fin_two] using hd

lemma GL2.v_le_one_of_mem_localFullLevel (v : HeightOneSpectrum (𝓞 F)) {x}
    (hx : x ∈ localFullLevel v) (i j) : Valued.v (x i j) ≤ 1 := by
  simp [-iff_false, localFullLevel, RingHom.mapMatrix, Units.map, Matrix.map,
    ValuationSubring.subtype, Subring.subtype, Matrix.GeneralLinearGroup.ext_iff] at hx
  obtain ⟨x', hx'⟩ := hx
  simp only [← hx', ← HeightOneSpectrum.mem_adicCompletionIntegers, SetLike.coe_mem]

open Valued

noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {x ∈ localFullLevel v |
    Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
  mul_mem' {a b} ha hb := by
    simp_all only [Set.mem_setOf_eq, Units.val_mul]
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.isValue, Fin.sum_univ_two]
      convert_to Valued.v ((a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) + (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) < 1
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
      · convert_to Valued.v (a.val 0 0 * (b.val 0 0 - b.val 1 1) + (a.val 0 0 - a.val 1 1) * b.val 1 1) < 1
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
      Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, ← mul_sub, map_mul, map_inv₀, mul_neg, Valuation.map_neg]
    rw [Valuation.map_sub_swap, v_det_val_mem_localFullLevel_eq_one ha.1]
    simp [ha.2]

theorem GL2.localTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localTameLevel v).carrier :=
  sorry

theorem GL2.localTameLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localTameLevel v).carrier :=
  sorry

end IsDedekindDomain

-- should be in mathlib
def DedekindDomain.ProdAdicCompletions.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    ProdAdicCompletions (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun k := k v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

-- should be in mathlib
def DedekindDomain.FiniteAdeleRing.toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v :=
  (ProdAdicCompletions.toAdicCompletion v).comp
  ((FiniteAdeleRing.subalgebra (𝓞 F) F).val)

namespace DedekindDomain.FiniteAdeleRing

noncomputable def GL2.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →*
    GL (Fin 2) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (FiniteAdeleRing.toAdicCompletion v)).toMonoidHom

end DedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

def GL2.TameLevel (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
    carrier := {x | (∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v) ∧
      (∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v)}
    mul_mem' {a b} ha hb := by simp_all [mul_mem]
    one_mem' := by simp_all [one_mem]
    inv_mem' {x} hx := by simp_all

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem GL2.TameLevel.isOpen : IsOpen (GL2.TameLevel S).carrier :=
  sorry

theorem GL2.TameLevel.isCompact : IsCompact (GL2.TameLevel S).carrier :=
  sorry

noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D) :
    Subgroup ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)

instance : TopologicalSpace ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D) :=
  moduleTopology (FiniteAdeleRing (𝓞 F) F) _

instance : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D) :=
  ⟨rfl⟩

instance : IsTopologicalRing ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D) :=
  IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)

omit [IsQuaternionAlgebra F D] in
theorem Rigidification.continuous_toFun (r : Rigidification F D) :
    Continuous r :=
  IsModuleTopology.continuous_of_linearMap r.toLinearMap

omit [IsQuaternionAlgebra F D] in
theorem Rigidification.continuous_invFun (r : Rigidification F D) :
    Continuous r.symm := by
  haveI : ContinuousAdd (FiniteAdeleRing (𝓞 F) F ⊗[F] D) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)
  exact IsModuleTopology.continuous_of_linearMap r.symm.toLinearMap
