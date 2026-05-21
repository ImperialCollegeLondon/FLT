import VersoManual
import VersoBlueprint.PreviewManifest
import FLTBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc FLTBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
