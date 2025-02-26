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
for all finite places `v`. Such a rigidification exists if and only if
F is unramified at all finite places.
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

-- surely we have this
def Matrix.mapRingHom {A B : Type*} [Semiring A] [Semiring B] (i : Type*) [Fintype i]
    [DecidableEq i] (f : A →+* B) : Matrix i i A →+* Matrix i i B where
  toFun M := Matrix.map M f
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

variable {F}

namespace IsDedekindDomain.HeightOneSpectrum

noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (Matrix.mapRingHom (Fin 2) (v.adicCompletionIntegers F).subtype).toMonoidHom)

open Valued

noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
      carrier := {x ∈ localFullLevel v |
        Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
      mul_mem' := sorry
      one_mem' := by simp [one_mem]
      inv_mem' := sorry

end IsDedekindDomain.HeightOneSpectrum

namespace DedekindDomain

def ProdAdicCompletions.toAdicCompletionAlgHom (v : HeightOneSpectrum (𝓞 F)) :
    ProdAdicCompletions (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun k := k v
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

namespace FiniteAdeleRing

def toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v :=
  (ProdAdicCompletions.toAdicCompletionAlgHom v).comp
  ((FiniteAdeleRing.subalgebra (𝓞 F) F).val)

private noncomputable def localFactor
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) :=
  Units.map (Matrix.mapRingHom (Fin 2) (toAdicCompletion v)).toMonoidHom g

end DedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

def GL2.TameLevel (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
    carrier := {x | ∀ v, localFactor x v ∈ GL2.localFullLevel v}
    mul_mem' := sorry
    one_mem' := sorry
    inv_mem' := sorry

noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)
