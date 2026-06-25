import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FLTBlueprint.Chapters.Definitions
import FLTBlueprint.Chapters.Ch3Assumptions
import FLTBlueprint.Chapters.Ch3Cohomology

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem (Verso Blueprint)" =>

This is an early Verso blueprint for the
[Fermat's Last Theorem project](https://github.com/leanprover-community/FLT).
The chapters below build towards Gee's Proposition 3.24 (the presentation of a global
Galois deformation ring over the local lifting ring); further chapters will be added as the
blueprint grows.

{include 0 FLTBlueprint.Chapters.Definitions}

{include 0 FLTBlueprint.Chapters.Ch3Assumptions}

{include 0 FLTBlueprint.Chapters.Ch3Cohomology}

{blueprint_graph}
{blueprint_summary}
