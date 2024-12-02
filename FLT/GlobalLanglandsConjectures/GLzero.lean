/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.FieldTheory.Cardinality
import FLT.GlobalLanglandsConjectures.GLnDefs
/-

# Proof of a case of the global Langlands conjectures.

Class Field Theory was one of the highlights of 19th century mathematics, linking
analysis to arithmetic of extensions of number fields with abelian Galois groups.
In the 1960s the main results had been re-interpreted as the GL(1) case of the global
Langlands conjectures. The general global Langlands conjectures are for GL(n) for any natural
number n, and work over any number field or global function field. Much is known in the function
field case (Lafforgue got a Fields Medal for his work on the topic), but the general number
field case remains largely open even today. For example we have very few results if the
base number field is not totally real or CM. For simplicity, let us stick to GL(n)/Q.

In 1993 Wiles announced his proof of the modularity of semistable elliptic curves over the
rationals. The result gave us a way of constructing automorphic forms from Galois representations;
refinements of the work by Taylor and others over the next decade led to a profound understanding
of the "holomorphic" or "odd" part of global Langlands functoriality for GL(2) over the rationals.
Wiles' work used class field theory (in the form of global Tate duality) crucially in a
central proof that a deformation ring R was isomorphic to a Hecke algebra T.

The fact that Wiles needed the theory for GL(1) to make progress in the GL(2) case,
is surely evidence that at the end of the day the proof for GL(n) is going to be by induction on n.
We will thus attempt to prove the global Langlands conjectures for GL(0).

## Structure of the proof

We will deduce the global Langlands conjectures for GL(0) from a far stronger theorem,
called the *classification theorem for automorphic representations for GL(0) over Q*.
This theorem gives a *canonical isomorphism* between the space of automorphic representations
and the complex numbers. Except in Lean we're not allowed to say "canonical" so instead
our "theorem" is a *definition* of a bijection.

## TODO

State them first.

-/

namespace AutomorphicForm

def GLn.Weight.IsTrivial {n : ℕ} (ρ : Weight n) : Prop := sorry -- (ρ = trivial 1d rep)

open GLn

namespace GL0

variable (ρ : Weight 0)

def ofComplex (c : ℂ) : AutomorphicFormForGLnOverQ 0 ρ := {
    toFun := fun _ => c,
    is_smooth := {
      continuous := by continuity
      loc_cst := by
        rw [IsLocallyConstant]
        aesop
      smooth := by simp [contMDiff_const]
    }
    is_periodic := by simp
    is_slowly_increasing := by
      intros x
      exact {
      bounded_by := by
        simp
        apply Exists.intro (Complex.abs c)
        apply Exists.intro 0
        simp
    }
    is_finite_cod := by
      intros x
      rw [FiniteDimensional]
      rw [annihilator]
      simp
      exact {
        out := by sorry
      }
    has_finite_level := by
      let U : Subgroup (GL (Fin 0) (DedekindDomain.FiniteAdeleRing ℤ ℚ)) := {
        carrier := {1},
        one_mem' := by simp,
        mul_mem' := by simp
        inv_mem' := by simp
      }
      apply Exists.intro U
      exact {
          is_open := by simp
          is_compact := by aesop
          finite_level := by simp
      }
  }

-- the weakest form of the classification theorem
noncomputable def classification: AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ := {
  toFun := fun f ↦ f 1
  invFun := fun c ↦ ofComplex ρ c
  left_inv := by
    rw [Function.LeftInverse]
    simp [ofComplex]
    intro x
    have h: x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    simp_rw [← h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]
}

end GL0

namespace GLn

-- Let's write down an inverse
-- For general n, it will only work for ρ the trivial representation, but we didn't
-- define the trivial representation yet.
-- Some of the other fields will work for all n.
def ofComplex (z : ℂ) {n : ℕ} (ρ : Weight n) (hρ : ρ.IsTrivial) :
    AutomorphicFormForGLnOverQ n ρ where
      toFun _ := z
      is_smooth := sorry
      is_periodic := sorry
      is_slowly_increasing := sorry
      is_finite_cod := sorry -- needs a better name
      has_finite_level := sorry -- needs a better name

-- no idea why it's not computable
noncomputable def classification (ρ : Weight 0) : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ where
  toFun f := f 1
  invFun z := ofComplex z ρ sorry
  left_inv := sorry
  right_inv := sorry

-- Can this be beefed up to an isomorphism of complex
-- vector spaces?
