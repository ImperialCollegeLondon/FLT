import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import FLTBlueprint.Chapters.Basics

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fermat's Last Theorem (Verso Blueprint)" =>

This is an early Verso blueprint for the
[Fermat's Last Theorem project](https://github.com/leanprover-community/FLT).
The single chapter below links a Blueprint node to a real declaration in the
FLT Lean codebase; further chapters will be added as the blueprint grows.

{include 0 FLTBlueprint.Chapters.Basics}

{blueprint_graph}
{blueprint_summary}
