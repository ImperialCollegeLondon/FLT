/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kenny Lau
-/
import Mathlib.Init
/-!

# A tactic for theorems known in the 1980s

`knownin1980s` is like `sorry` -- it can be used to prove
an arbitrary theorem. KMB will allow it in the FLT repo,
but only when it is used to prove a result which he is
basically convinced that he would be able to prove on paper
using only results which were well-known pre-1990.

KMB's vision of the evolution of the FLT project is as follows.
In this initial stage of evolution, we allow liberal usage
of the tactic to justify *any* proof which was known to humanity
pre-1990, ranging from standard results about elliptic curves
or modular forms to deep theorems such as the work of Mazur
on elliptic curves, Taylor and others on attaching Galois representations
to Hilbert modular forms, Langlands on cyclic base change
and so on. The first goal of the project should be to get a proof
of FLT which is sorry-free but which uses `knownin1980s` liberally.

After this initial phase, the work will turn to hugely reducing
the use of `knownin1980s` to a small (perhaps around ten) deep
statements in mathematics, each of which will have a clear reference
to a pre-1990 statement in the literature.

KMB is optimistic that this can be achieved by September 2029, when
the funding for the proposal runs out. At that point we shall review
the status of autoformalization tools and see whether the process
can be finished by such tools, or whether more manual work will
be required.

-/

/-- `knownin1980s` is a term which provides a proof of an
arbitrary proposition. In this current phase of the FLT project,
`knownin1980s` will be allowed as a proof of any theorem
which would have been easy for an expert to deduce from
the pre-1990 literature. This stretches from standard easy
statements about things like elliptic curves to much deeper results
which are relatively short derivations from deep results published
pre-1990 such as Taylor's theorem attaching Galois representations
to Hilbert modular forms, Langlands' work on cyclic base change
and so on.
-/
axiom knownin1980s {P : Prop} : P

/-- `knownin1980s` is a term which provides a proof of an
arbitrary proposition. In this current phase of the FLT project,
`knownin1980s` will be allowed as a proof of any theorem
which would have been easy for an expert to deduce from
the pre-1990 literature. This stretches from standard easy
statements about things like elliptic curves to much deeper results
which are relatively short derivations from deep results published
pre-1990 such as Taylor's theorem attaching Galois representations
to Hilbert modular forms, Langlands' work on cyclic base change
and so on.
-/
macro "knownin1980s" : tactic => `(tactic| exact knownin1980s)
