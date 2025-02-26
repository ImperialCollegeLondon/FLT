import Mathlib
import FLT.Mathlib.Algebra.IsQuaternionAlgebra

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
def Rigidification :=
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

namespace IsDedekindDomain.HeightOneSpectrum

noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

open Valued

noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
      carrier := {x ∈ localFullLevel v |
        Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
      mul_mem' := sorry
      one_mem' := by simp [one_mem]
      inv_mem' := sorry

end IsDedekindDomain.HeightOneSpectrum

-- should be in mathlib once sorry-free
def DedekindDomain.ProdAdicCompletions.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    ProdAdicCompletions (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun k := k v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

namespace DedekindDomain.FiniteAdeleRing

def toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v :=
  (ProdAdicCompletions.toAdicCompletion v).comp
  ((FiniteAdeleRing.subalgebra (𝓞 F) F).val)

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

noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)
