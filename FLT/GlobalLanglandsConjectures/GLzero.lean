/-
Copyright (c) 2024 Kevin Buzzaed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
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

open GLn

namespace GL0

#check classification
-- the weakest form of the classification theorem
theorem classification : ∀ (ρ : weight 0),
    Function.Bijective (fun f ↦ f 1 : AutomorphicFormForGLnOverQ 0 ρ → ℂ) := sorry

-- Let's write down an inverse

def ofComplex (z : ℂ) {n : ℕ} (ρ : Weight n) : AutomorphicFormForGLnOverQ 0 ρ
