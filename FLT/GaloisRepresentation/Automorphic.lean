/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kevin Buzzard
-/
import Mathlib
import FLT

/-!
# Automorphic Galois representations

For our proof of Fermat's Last Theorem, the following definition is the most convenient.

We say that a 2-dimensional $p$-adic or a mod $p$ Galois representation of the absolute
Galois of a totally real field number field $F$ is *automorphic* if there exists a totally
definite quaternion algebra $D/F$ unramified at all finite places, a squarefree ideal $n$
of the integers of $F$, and an automorphic form of level $U_1(n)$ (matrices congruent
to $(a *;0 a)$ mod $n$) and weight 2 for $D$
such that the Galois representation is associated to the form by the construction of
Carayol, Taylor et al.

## Notes

Several things here are non-standard. We demand that the quaternion algebra is unramified
everywhere because this is the only case that we need. We stick to weight 2 because this is
the only case that we need. The level is also non-standard: the automorphic forms it
catches are principal series`π(χ₁, χ₂)` with `χᵢ` tame and `χ₁χ₂` unramified, and
also Steinberg representations.

-/

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsLocalRing A]

open scoped TensorProduct

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

abbrev primes_dividing_n' (F : Type*) (n : ℕ) [Field F] [NumberField F] :
  Set (HeightOneSpectrum (𝓞 F)) :=
  {v : HeightOneSpectrum (𝓞 F)| ↑n ∈ v.1}

instance fin (F : Type*) (n : ℕ) [NeZero n] [Field F] [NumberField F] :
    Set.Finite (primes_dividing_n' F n) := by
  simp only [primes_dividing_n']
  have eq : {v : HeightOneSpectrum (𝓞 F)| ↑n ∈ v.1} =
    {v : HeightOneSpectrum (𝓞 F) | v.1 ∣ Ideal.span {↑n}} := by simp
  rw [eq]
  exact Ideal.finite_factors (by simpa using NeZero.ne n)

noncomputable abbrev primes_dividing_n (F : Type*) (n : ℕ) [NeZero n] [Field F] [NumberField F] :
  Finset (HeightOneSpectrum (𝓞 F)) := Set.Finite.toFinset <| fin F n

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

lemma not_mem (F : Type*) (n p : ℕ) [NeZero n] [NeZero p] [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (hv : ↑(n * p) ∉ v.1) :
    v ∉ primes_dividing_n F n := by
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  rw [Nat.mul_comm, Nat.cast_mul, ← smul_eq_mul, Nat.cast_smul_eq_nsmul] at hv
  intro h
  have : p • (Nat.cast n) ∈ v.1 := Submodule.smul_of_tower_mem v.asIdeal p h
  tauto

def GaloisRep.IsModular (F D : Type*) (p : ℕ) [NeZero p] [Field F] [NumberField F]
    [IsTotallyReal F] (ρ : GaloisRep F A (Fin 2 → A)) [Ring D] [Algebra F D]
    [IsQuaternionAlgebra F D] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
    (π : HeckeAlgebra F D r (primes_dividing_n F N) A →ₐ[A] A),
  ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : ↑(N * p) ∉ v.1),
    ρ.IsUnramifiedAt v ∧ (ρ.toLocal v (Frob v)).det = v.1.absNorm
    ∧ LinearMap.trace A (Fin 2 → A) (ρ.toLocal v (Frob v)) =
      π (HeckeAlgebra.T D r A v (not_mem F N p v hv))
