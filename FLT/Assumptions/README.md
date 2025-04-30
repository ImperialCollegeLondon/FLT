# Assumptions

The initial goal of this project (hopefully to be attained by 2029,
the period of the EPSRC funding) is to reduce Fermat's Last Theorem
to various mathematical results which were known in the 1980s.
This directory `FLT/Assumptions` contains formal statements of these
assumptions. More assumptions will be added as the project progresses;
some of the assumptions we need cannot even be stated until we formalize
more definitions.

Anybody (humans, AI) is welcome to work on formalizing the proofs of these
assumptions; this task is not high priority for me at this point. For now,
my focus is on proving FLT assuming these assumptions. To avoid duplication,
anyone proposing to work on an assumption should consider indicating this
on the github issue associated to the assumption.

Each file in this directory contains one `axiom`. The `axiom` corresponds
to a theorem which was in the published mathematical literature
by 31st December 1989. The file contains a precise reference to the
literature where the theorem is proved.

## Formalized assumptions

We give a brief summary of each file in this directory.

* `Odlyzko.lean` : an "Odlyzko bound" for root discriminants. Issue #458.

## Formalizable assumptions

The statements of the bassumptions below are probably formalizable,
but nobody did them yet.

* `Mazur.lean` : Mazur's bounds for the torsion of an elliptic curve over the rationals.

* Existence of a solvable extension of a number field with prescribed behaviour
at a finite set of places (the proof uses class field theory).

* Moret-Bailly's theorem (existence of global points on curves with prescribed
local properties).

## Forthcoming assumptions

The assumptions below cannot yet be stated because of missing definitions.

* The existence of a p-adic Galois representation attached to a weight 2 automorphic
form over a totally definite quaternion algebra.

This is work in progress; we need Hecke algebras. The second two assumptions need a
definition of modularity, and thus also rely on Hecke algebras.

* Automorphic induction from GL_1 to GL_2 (e.g. "CM elliptic curves are modular")

* Cyclic base change for GL_2 + classification of image.

The next assumption can't be stated yet because we don't have Galois cohomology.

* Poitou-Tate (aka the "Greenberg-Wiles long exact sequence")
