import Mathlib
import FLT.Mathlib.Algebra.IsQuaternionAlgebra
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

lemma GL2.v_le_one_of_mem_localFullLevel (v : HeightOneSpectrum (𝓞 F)) {x}
    (hx : x ∈ localFullLevel v) (i j) : Valued.v (x i j) ≤ 1 := by
  simp [-iff_false, localFullLevel, RingHom.mapMatrix, Units.map, Matrix.map,
    ValuationSubring.subtype, Subring.subtype, Matrix.GeneralLinearGroup.ext_iff] at hx
  obtain ⟨x', hx'⟩ := hx
  simp only [← hx', ← mem_adicCompletionIntegers, SetLike.coe_mem]

open Valued

lemma norm_add_le_max (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    Valued.v (x + y) ≤ max (Valued.v x) (Valued.v y) := by
  sorry

lemma norm_sub_le_max (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    Valued.v (x - y) ≤ max (Valued.v x) (Valued.v y) := by
  rw [sub_eq_add_neg, ← Valuation.map_neg _ y]
  exact norm_add_le_max v x (-y)

lemma GL2.v_det_eq_one (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F))
    (hx : x ∈ localFullLevel v) :
    Valued.v (Matrix.det (x : (Matrix (Fin 2) (Fin 2) (adicCompletion F v)))) = 1 := by
  obtain ⟨x', hx⟩ := Matrix.isUnits_det_units x
  rw [← hx]
  rw [← Valuation.mem_unitGroup_iff]
  simp
  sorry

lemma GL2.aux (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F))
    (hx : x ∈ localFullLevel v) (hx' : Valued.v (x.val 1 0) < 1) :
    Valued.v (x.val 0 0) = 1 ∧ Valued.v (x.val 1 1) = 1 := by
  have h0 := GL2.v_det_eq_one v x hx
  rw [Matrix.det_fin_two] at h0
  have h1 := norm_sub_le_max v (x.val 0 0 * x.val 1 1) (x.val 0 1 * x.val 1 0)
  rw [h0] at h1
  rw [@le_max_iff] at h1
  cases h1 with
  | inl h1 =>
    rw [@Valuation.map_mul] at h1
    refine ⟨eq_one_of_one_le_mul_left ?_ ?_ h1, eq_one_of_one_le_mul_right ?_ ?_ h1⟩ <;>
      apply v_le_one_of_mem_localFullLevel _ hx
  | inr h1 =>
    rw [@Valuation.map_mul, mul_comm] at h1
    have := eq_one_of_one_le_mul_left hx'.le (v_le_one_of_mem_localFullLevel _ hx _ _) h1
    rw [this] at hx'
    exact hx'.false.elim

noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
      carrier := {x ∈ localFullLevel v |
        Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
      mul_mem' {a b} ha hb := by
        simp_all only [Set.mem_setOf_eq, Units.val_mul]
        refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_, ?_⟩
        · rw [@Matrix.mul_apply, Matrix.mul_apply]
          simp
          suffices Valued.v (a.val 0 1 * b.val 1 0) < 1 ∧
                   Valued.v (a.val 1 0 * b.val 0 1) < 1 ∧
                   Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) < 1 by
            calc
                Valued.v (a.val 0 0 * b.val 0 0 + a.val 0 1 * b.val 1 0 - (a.val 1 0 * b.val 0 1 + a.val 1 1 * b.val 1 1))
              _ = Valued.v ((a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) + (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) := by ring_nf
              _ ≤ max (Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1)) (Valued.v (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) := by apply norm_add_le_max
              _ ≤ max (Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1)) (max (Valued.v (a.val 0 1 * b.val 1 0)) (Valued.v (a.val 1 0 * b.val 0 1))) := by
                  apply max_le_max_left
                  apply norm_sub_le_max
              _ < 1 := max_lt this.2.2 (max_lt this.1 this.2.1)
          refine ⟨?_, ?_, ?_⟩
          · rw [map_mul, mul_comm]
            apply mul_lt_one_of_lt_of_le hb.2.2
            apply v_le_one_of_mem_localFullLevel _ ha.1
          · rw [map_mul]
            apply mul_lt_one_of_lt_of_le ha.2.2
            apply v_le_one_of_mem_localFullLevel _ hb.1
          · convert_to Valued.v (a.val 0 0 * (b.val 0 0 - b.val 1 1) + (a.val 0 0 - a.val 1 1) * b.val 1 1) < 1
            · ring_nf
            apply (norm_add_le_max _ _ _).trans_lt (max_lt ?_ ?_)
            · rw [map_mul, mul_comm]
              apply mul_lt_one_of_lt_of_le hb.2.1
              apply v_le_one_of_mem_localFullLevel _ ha.1
            · rw [map_mul]
              apply mul_lt_one_of_lt_of_le ha.2.1
              apply v_le_one_of_mem_localFullLevel _ hb.1
        · simp [Matrix.mul_apply]
          apply (norm_add_le_max _ _ _).trans_lt (max_lt ?_ ?_)
          · rw [map_mul]
            apply mul_lt_one_of_lt_of_le ha.2.2
            apply v_le_one_of_mem_localFullLevel _ hb.1
          · rw [map_mul, mul_comm]
            apply mul_lt_one_of_lt_of_le hb.2.2
            apply v_le_one_of_mem_localFullLevel _ ha.1
      one_mem' := by simp [one_mem]
      inv_mem' {a} ha := by
        simp_all only [Set.mem_setOf_eq, inv_mem_iff, Matrix.coe_units_inv, true_and]
        simp_all only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
          Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.head_fin_const, ← mul_sub, map_mul, map_inv₀, mul_neg, Valuation.map_neg]
        rw [@Valuation.map_sub_swap]
        rw [v_det_eq_one _ _ ha.1]
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
