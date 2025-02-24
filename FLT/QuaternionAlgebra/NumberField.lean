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
def Matrix.mapRingHom {A B : Type*} [Semiring A] [Semiring B]
    (i : Type*) [Fintype i] [DecidableEq i] (f : A →+* B) :
    Matrix i i A →+* Matrix i i B := sorry

variable {F}

noncomputable def localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (Matrix.mapRingHom (Fin 2) (v.adicCompletionIntegers F).subtype).toMonoidHom)

open Valued

noncomputable def localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
      carrier := {x ∈ localFullLevel v | Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
      mul_mem' := sorry
      one_mem' := by
        simp [one_mem]
      inv_mem' := sorry

def TameLevel_aux (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)ˣ := sorry
def TameLevel (r : Rigidification F D) (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup ((FiniteAdeleRing (𝓞 F) F) ⊗[F] D)ˣ := sorry
