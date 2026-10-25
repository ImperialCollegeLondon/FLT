import VersoManual
import VersoBlueprint.PreviewManifest
import FLTBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/--
The FLT blueprint's house style; see `static/flt-blueprint.css` for what it does
and why. It is injected through `extraHead` rather than `extraCss` because
`extraHead` is emitted last in the `<head>`, after both `book.css` and the CSS
that VersoBlueprint contributes inline, so these rules win without needing
`!important`.
-/
def fltStyleSheet : Output.Html :=
  .tag "style" #[("type", "text/css")] (.text false (include_str "static/flt-blueprint.css"))

/--
Verso emits a bare `<html>` with no `lang`, and browsers will not hyphenate
text in a document of unknown language. Without hyphenation the justified
setting in `flt-blueprint.css` opens rivers of whitespace, which is exactly
what LaTeX's paragraph breaker exists to avoid. The attribute lives outside
`<head>`, so it cannot be set by injecting markup; this sets it instead.
-/
def fltLangScript : Output.Html :=
  .tag "script" #[] (.text false "document.documentElement.lang = \"en\";")

def fltConfig : RenderConfig where
  extraHead := #[fltLangScript, fltStyleSheet]

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc FLTBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := fltConfig)
