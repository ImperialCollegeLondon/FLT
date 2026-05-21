import Verso
import VersoManual
import VersoBlueprint
import FLT.Basic.Reductions

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Mazur–Frey theorem" =>

This chapter links the Verso blueprint to a real FLT declaration: the
Mazur–Frey theorem, whose Lean statement is `Mazur_Frey` in
`FLT/Basic/Reductions.lean`.

:::group "mazur_frey_core"
The reduction of Fermat's Last Theorem to a profound theorem of Mazur.
:::

:::author "flt_author" (name := "FLT Project")
:::

:::definition "frey_package" (parent := "mazur_frey_core") (lean := "FreyPackage")
A *Frey package* is a tuple $`P = (a, b, c, p)` consisting of nonzero integers
$`a`, $`b`, $`c` and a prime $`p \geq 5` satisfying $`a^p + b^p = c^p`,
together with the coprimality and congruence conditions that make the
associated elliptic curve well-behaved.
:::

:::definition "frey_curve" (parent := "mazur_frey_core") (lean := "FreyPackage.freyCurve")
The *Frey curve* associated to a Frey package {uses "frey_package"}[] is the
elliptic curve over $`\mathbb{Q}` cut out by the Weierstrass equation with
$`a_2 = (b^p - 1 - a^p)/4` and $`a_4 = -a^p b^p / 16`.
:::

:::theorem "mazur_frey" (parent := "mazur_frey_core") (owner := "flt_author") (lean := "Mazur_Frey")
If $`P = (a, b, c, p)` is a Frey package {uses "frey_package"}[], then the
$`p`-torsion in the associated Frey curve {uses "frey_curve"}[] is irreducible
as a Galois representation.
:::

:::proof "mazur_frey"
Obvious: this Blueprint node is linked directly to the existing FLT declaration
`Mazur_Frey` in `FLT/Basic/Reductions.lean`.
:::
