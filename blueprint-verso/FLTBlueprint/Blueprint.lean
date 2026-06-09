import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FLTBlueprint.Chapters.Level00Statement
import FLTBlueprint.Chapters.Level01ReductionToPrimeCase

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem (Verso Blueprint)" =>

This is an early Verso blueprint for the
[Fermat's Last Theorem project](https://github.com/leanprover-community/FLT).
The chapters below link Blueprint nodes to real declarations in the FLT Lean
codebase and in mathlib; further chapters will be added as the blueprint grows.

{include 0 FLTBlueprint.Chapters.Level00Statement}
{include 0 FLTBlueprint.Chapters.Level01ReductionToPrimeCase}

{blueprint_graph}
{blueprint_summary}
