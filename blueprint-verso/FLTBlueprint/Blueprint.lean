import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FLTBlueprint.Chapters.Level01Statement
import FLTBlueprint.Chapters.Level02ReductionToPrimeCase
import FLTBlueprint.Chapters.Level03FreyPackages

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem: a formal blueprint." =>

*Fermat's Last Theorem* is the innocuous-looking claim that if $`a,b,c,n` are positive
whole numbers with $`n \geq 3` then $`a^n+b^n\not= c^n`. It was open for over 350
years, before being resolved in the early 1990s by Wiles, with the argument
completed by Taylor--Wiles. All known proof, when written out in full, are several thousand
pages long.

*Lean* is an interactive theorem prover. It is a computer program which
knows the axioms of mathematics and the rules of logic. The ultimate purpose of this
project is to teach some of the key ideas (and perhaps, one day, all of the key
ideas) behind the proof of Fermat's Last Theorem to Lean.
The initial goal of the project is to *reduce* the proof of Fermat's Last Theorem to
various (sometimes rather complex) mathematical claims, all of which were known in the 1980s.

The project is currently being led by Kevin Buzzard. It is funded by grant
[EP/Y022904/1](https://gtr.ukri.org/projects?ref=EP%2FY022904%2F1), awarded by the UK’s
Engineering and Physical Sciences Research Council. The project is hosted at
[Imperial College London](https://www.imperial.ac.uk/). Kevin would like to extend many many thanks to both of
these institutions for their ongoing support of this nonstandard research.

{include 0 FLTBlueprint.Chapters.Level01Statement}
{include 0 FLTBlueprint.Chapters.Level02ReductionToPrimeCase}
{include 0 FLTBlueprint.Chapters.Level03FreyPackages}

{blueprint_graph}
{blueprint_summary}
