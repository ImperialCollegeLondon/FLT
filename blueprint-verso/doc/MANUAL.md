# Blueprint Manual

This document is the current reference for Blueprint authoring and rendering.

If you are starting a first project, read
[project_template/README.md](../project_template/README.md) and
[GETTING_STARTED.md](./GETTING_STARTED.md) before this manual.

## Contents

- [Mental Model](#mental-model)
- [Labels and Node Identity](#labels-and-node-identity)
- [Minimal Project Shape](#minimal-project-shape)
- [The Blueprint Top-Level File](#the-blueprint-top-level-file)
- [A First Chapter](#a-first-chapter)
- [Core Block Forms](#core-block-forms)
- [Connecting Blocks to Lean](#connecting-blocks-to-lean)
- [Attached Rust Code](#attached-rust-code)
- [Math and TeX](#math-and-tex)
- [Groups, Authors, and Metadata](#groups-authors-and-metadata)
- [Rendering Surface](#rendering-surface)
- [Metadata Export and Preview Manifest](#metadata-export-and-preview-manifest)
- [The Generator Entry Point](#the-generator-entry-point)
- [Blueprint Options](#blueprint-options)
- [Experimental Widget](#experimental-widget)
- [Current Limits](#current-limits)

## Mental Model

A Blueprint project usually owns three things:

- chapter modules containing the mathematical content
- a Blueprint top-level file that assembles the document
- a generator entry point that renders the site

The Blueprint top-level file is often called `Contents.lean` in existing
projects, but the filename is not special. What matters is that one module
assembles the chapters and chooses the rendered overview pages.

## Labels and Node Identity

Blueprint nodes are identified by labels chosen by the author.

Examples:

- statement labels such as `addition_spec` and `addition_right_identity`
- group labels such as `addition_core`
- author ids such as `jason`

These identifiers are used by:

- `{uses "addition_spec"}[]` dependency references
- `{bpref "addition_spec"}[]` link-only references
- labeled inline Lean code blocks
- labeled inline Rust code blocks
- `tex` code blocks carrying raw TeX source
- `@[blueprint "label"]` on compiled Lean declarations
- summary and graph nodes
- preview lookup and exported metadata

Choose labels early and treat them as stable project identifiers.

Use `uses` when the current node depends on the target and should add an edge to
the graph and dependency summaries. Use `bpref` when prose should link to a
Blueprint node without registering that relationship as a dependency.

If a role such as `{uses "addition_spec"}[]`, `{bpref "addition_spec"}[]`, or a
citation has an empty payload, Blueprint can generate the visible text
automatically, for example `Theorem N`.

## Minimal Project Shape

The starter template in [project_template/](../project_template/) uses this
layout:

```text
ProjectTemplate/
  Blueprint.lean
  Chapters/
    Addition.lean
    Multiplication.lean
    Collatz.lean
ProjectTemplate.lean
ProjectTemplateMain.lean
lakefile.lean
```

The role of each file is:

- `ProjectTemplate/Chapters/Addition.lean`: a chapter with Blueprint blocks
- `ProjectTemplate/Chapters/Multiplication.lean`: another chapter with the same
  pattern
- `ProjectTemplate/Chapters/Collatz.lean`: a separate chapter for an
  intentionally unfinished open problem
- `ProjectTemplate/Blueprint.lean`: the Blueprint top-level file
- `ProjectTemplateMain.lean`: the renderer entry point
- `lakefile.lean`: the package definition and optional generator executable

## The Blueprint Top-Level File

The Blueprint top-level file assembles the rendered document.

Example:

```lean
import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ProjectTemplate.Chapters.Addition
import ProjectTemplate.Chapters.Collatz
import ProjectTemplate.Chapters.Multiplication

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Starter Blueprint" =>

This small Blueprint tracks a few basic arithmetic facts on natural numbers,
then ends with a separate Collatz chapter that is intentionally unfinished.

{include 0 ProjectTemplate.Chapters.Addition}
{include 0 ProjectTemplate.Chapters.Multiplication}
{include 0 ProjectTemplate.Chapters.Collatz}

{blueprint_graph}
{blueprint_summary}
```

This file decides:

- which chapter modules are included
- whether the dependency graph is rendered
- whether the summary page is rendered
- whether other global pages such as the bibliography are rendered

## A First Chapter

The following chapter example uses descriptive labels and a real mathematical
story about addition.

````lean
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Addition" =>

:::group "addition_core"
Core statements about addition on natural numbers.
:::

:::author "project_author" (name := "Project Author")
:::

:::definition "addition_spec" (parent := "addition_core")
We write $`a + b` for the result of adding $`b` to $`a`.
This Blueprint starts with the most basic sanity checks around that operation.
:::

:::theorem "addition_right_identity" (parent := "addition_core") (owner := "project_author") (tags := "starter, arithmetic") (effort := "small") (priority := "high")
For every natural number $`n`, adding zero on the right leaves it unchanged:
$`n + 0 = n`.
This is the first sanity check for {uses "addition_spec"}[].
:::

:::proof "addition_right_identity"
Induct on $`n`. The base case is immediate and the inductive step unfolds one
successor on each side.
:::

```lean "addition_right_identity"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```

:::theorem "addition_assoc" (parent := "addition_core") (lean := "Nat.add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative:
$`(a + b) + c = a + (b + c)`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "addition_assoc"
Lean already provides this theorem as `Nat.add_assoc`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::
````

This example shows the core pattern:

- define an informal mathematical object
- attach later statements to it with `uses`
- point to related entries without adding dependencies with `bpref`
- keep informal proofs close to the statement
- connect to Lean either locally or through an existing declaration

## Core Block Forms

Blueprint chapters commonly use:

- `:::definition "label_1"`
- `:::lemma_ "label_2"`
- `:::theorem "label_3"`
- `:::corollary "label_4"`
- `:::proof "label_3"`

`:::proof "label_3"` attaches to the earlier statement with the same label.

## Connecting Blocks to Lean

Statement-like blocks can connect to Lean in three main ways.

### Inline Lean code

Attach a labeled Lean code block to the same Blueprint label:

````md
:::theorem "addition_right_identity"
For every natural number $`n`, $`n + 0 = n`.
:::

```lean "addition_right_identity"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```
````

This is the clearest way to connect a Blueprint entry to local formalization
work in the same project.

### Compiled code tagged with `@[blueprint "addition_assoc_compiled"]`

Use the `@[blueprint "label"]` attribute when a compiled definition-like declaration or theorem
should appear as a Lean-owned Blueprint node:

```lean
/-- Associativity of addition, exposed as a Lean-owned blueprint node. -/
@[blueprint "addition_assoc_compiled"]
theorem addition_assoc_compiled (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simpa [Nat.add_assoc]
```

This mode is useful when the formal declaration already exists as ordinary Lean
code and you want to register it as a Blueprint node.

If the declaration has a docstring, Blueprint tries to reuse it as the informal
statement body for that Lean-owned node. Plain docstrings are parsed through the
manual Markdown path when possible, and richer internal docstring structures are
converted into Manual blocks directly. If no docstring is available, the node is
still registered, but there is no imported informal statement body.

### Existing Lean declarations

Use `(lean := "Nat.add_assoc")` when Lean already owns the declaration and you
want an informal Blueprint node to point at it:

```md
:::theorem "addition_assoc" (lean := "Nat.add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative.
:::
```

This links the Blueprint entry to an existing Lean declaration without copying
the declaration body into the chapter.

Notes:

- `(lean := "Nat.add_assoc")` points at Lean-owned declaration names
- `(lean := "Nat.add, Nat.succ")` supports comma-separated declaration lists
- `@[blueprint "addition_assoc_compiled"]` registers a Lean-owned Blueprint node
- Blueprint labels are Blueprint-owned metadata
- Blueprint label conventions do not rewrite external Lean names

## Attached Rust Code

Blueprint also supports labeled inline Rust code blocks as attached source:

````md
:::definition "ffi_helper"
Helper routine mirrored in Rust.
:::

```rust "ffi_helper"
pub fn ffi_helper(x: i32) -> i32 {
    x + 1
}
```
````

Current behavior:

- the `rust` block label is parsed the same way as a labeled `lean` block
- the block attaches to the Blueprint node with the same label
- the rendered page shows an associated Rust code panel for that node
- Rust rendering currently uses a small built-in syntax highlighter
- Rust attachments do not currently participate in Blueprint progress or proof
  status computation
- Rust diagnostics, hover information, and external Rust refs are not currently
  part of the supported surface

## Math and TeX

Blueprint supports ordinary Verso math syntax inside the informal text.

Examples:

```md
Inline math: $`n + 0 = n`

Display math:
$$`\sum_{i=0}^{n} i = \frac{n(n+1)}{2}`
```

Projects can also define reusable TeX macros:

```lean
tex_prelude r#"\newcommand{\NatAdd}{\mathbin{+}}"#
```

After that, Blueprint math can use the macro in rendered pages:

```md
We write $`a \NatAdd b` for addition on natural numbers.
```

Blueprint nodes can also store raw general-TeX source through `tex`
code blocks:

````md
:::theorem "addition_right_identity"
For every natural number $`n`, $`n + 0 = n`.
:::

```tex "addition_right_identity"
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```
````

To keep a raw TeX witness without attaching it to a Blueprint node, omit the
label:

````md
```tex
\begin{theorem}
Unlabeled TeX witness kept in the source file while porting.
\end{theorem}
```
````

To start a port from TeX before writing the Verso statement, use a labeled
standalone witness block:

````md
```tex "raw_addition_right_identity"
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```
````

If a label needs more than one TeX witness, give each block a separate slot:

````md
```tex "raw_addition_right_identity" (slot := statement)
\begin{theorem}\label{thm:addition-right-identity}
For every natural number $n$, adding zero on the right leaves it unchanged.
\end{theorem}
```

```tex "raw_addition_right_identity" (slot := "proof")
\begin{proof}
Raw proof witness kept near the imported source.
\end{proof}
```
````

Current behavior:

- unlabeled `tex` blocks are accepted as hidden source witnesses and do not
  create Blueprint nodes
- labeled `tex` block labels are parsed like labeled `lean` blocks
- a labeled block stores the raw TeX source on the associated Blueprint node
  under slot `"default"` unless `(slot := ...)` is provided
- the same label may have several TeX witnesses as long as they use different
  slots
- repeating the same `(label, slot)` pair is an error
- the block is not displayed in the rendered output
- the current primary use is to help port an existing TeX source alongside the
  Blueprint entry
- other uses may be possible later; for now it is just a structured raw-TeX
  attachment

Blueprint also supports best-effort KaTeX linting during elaboration. KaTeX is
the renderer used by the generated HTML, so this helps catch math problems
before the final site render.

## Groups, Authors, and Metadata

Use `:::group` to define reusable group metadata:

```md
:::group "group_1"
Core statements for the first chapter.
:::
```

Use `:::author` to define author metadata:

```md
:::author "author_1" (name := "Jason Example")
:::
```

Statement-like directives can carry:

- `(parent := "group_1")`
- `(owner := "author_1")`
- `(tags := "starter, arithmetic")`
- `(effort := "small" | "medium" | "large")`
- `(priority := "high" | "medium" | "low")`
- `(pr_url := "https://github.com/org/repo/pull/123")`

These fields are primarily used by rendered overview pages and project triage
views.

## Rendering Surface

### Rendered statement blocks

Rendered statement headers show a Lean status badge and related metadata.
When local or external Lean material is available, the rendered page links or
previews the associated content.

When labeled inline Rust code is attached to a node, the rendered page also
shows an associated Rust code panel below the statement body.

### Dependency graph

`blueprint_graph` renders a dependency-oriented view of the current Blueprint
document.

Use it as either:

```lean
{blueprint_graph}
```

or with explicit graph layout options:

```lean
{blueprint_graph (direction := LR)}
{blueprint_graph (direction := LR) (pack := true)}
```

Supported directions are `LR`, `RL`, `TB`, and `BT`. When `(direction := ...)`
is omitted, the command falls back to the
`verso.blueprint.graph.defaultDirection` option.
The `(pack := true | false)` option controls Graphviz component packing for
disconnected graph components. It defaults to
`verso.blueprint.graph.defaultPack`, which is `false`.

The rendered graph page is interactive:

- a `View` selector switches between the full graph and any derived grouped
  views
- a `Legend` button opens the current graph legend in a popover
- a `Graph options` button exposes runtime graph options such as direction and
  component packing
- when grouped metadata produces multiple children for the same parent, the
  selector includes a synthetic group overview plus one subgraph view per group

The command-side options and the runtime graph controls are compatible:

- `(direction := ...)` chooses the initial graph direction when the page first
  loads
- the rendered `Graph options` control lets readers switch among the supported
  directions and toggle component packing without regenerating the site

Group metadata may be used to organize the presentation, but grouping does not
change dependency edges.

The graph uses two orthogonal status tracks:

- statement border:
  `Blocked`, `Ready to formalize`, `Formalized`, `In Mathlib`
- proof fill:
  `Not ready`, `Ready to formalize`, `Lean code incomplete`,
  `Locally formalized`, `Locally formalized + dependencies complete`

This split is intentional. For theorem-like nodes, the statement can already be
formalized while the proof still remains unstarted, in progress, or complete.

Read the proof fill states as:

- `Not ready`: the proof still depends on unfinished prerequisites
- `Ready to formalize`: prerequisites are done, but there is no associated Lean
  proof code yet
- `Lean code incomplete`: associated Lean code exists, but still has gaps such
  as `sorry`
- `Locally formalized`: the node's own Lean code is complete, but some
  dependency upstream is still not complete
- `Locally formalized + dependencies complete`: both the node and its full
  dependency closure are complete

Warning markers are reserved for structural or resolution issues such as:

- unresolved Blueprint references
- missing external Lean declarations
- Lean-owned entries that have code but no informal statement body

### Progress summary

`blueprint_summary` renders a summary page for the current Blueprint document.

The default view is an overview: it highlights overall progress, current
blockers, and the next ready work items first, while keeping deeper audit and
structural sections collapsed until needed.

That page uses dependency data, metadata, and Lean status to present:

- automatic progress counts
- blockers and incomplete declarations
- next ready work and project triage information
- grouped rollups by parent, owner, and tags

Maintainer-oriented diagnostics such as external declaration render failures are
available through an explicit summary debug option so they do not appear in the
default end-user view.

### Bibliography page

`blueprint_bibliography` renders the bibliography entries
registered in the document.

Projects that do not use citations can omit this page entirely.

### Math-enabled previews

Blueprint pages support shared previews in generated HTML, including math
rendering through KaTeX.

## Metadata Export and Preview Manifest

Blueprint builds emit a shared preview manifest at:

`html-multi/-verso-data/blueprint-preview-manifest.json`

Most authors do not need this file for routine writing. It is mainly useful
for:

- runtime preview support in generated sites
- tooling and integration work
- metadata export for other tools
- inspection and debugging

After building the relevant Lean targets, useful inspection flags on a
Blueprint generator are:

```bash
lake env lean --run <GeneratorMain>.lean --dump-schema
lake env lean --run <GeneratorMain>.lean --dump-manifest
lake env lean --run <GeneratorMain>.lean --help
```

- `--dump-schema` prints the JSON Schema for the manifest
- `--dump-manifest` prints the generated manifest JSON instead of writing the
  site and then reading the file
- `--help` includes these manifest-related flags alongside the usual rendering
  options

## The Generator Entry Point

Blueprint projects normally expose a small generator `main` function.

In the commands below, `<GeneratorMain>.lean` stands for the Lean file that
defines the generator `main`, such as `ProjectTemplateMain.lean`.

Minimal example:

```lean
import VersoManual
import VersoBlueprint.PreviewManifest
import ProjectTemplate.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithSharedPreviewManifest
    (%doc ProjectTemplate.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
```

This Blueprint-provided main wrapper owns the Blueprint-specific generation
layer around Verso's renderer. It injects the frontend assets required by
Blueprint-specific rendered surfaces, applies Blueprint's shared preview and
public-xref emission policy, and keeps downstream projects from needing to
remember those dependencies manually.

Recommended CI usage builds the Lean library or formalization targets needed by
the document, then runs the generator file directly:

```bash
lake build <library-or-formalization-target>
lake env lean --run <GeneratorMain>.lean --output _out/site
```

That path still checks the Blueprint document and writes the same HTML output,
but it does not force Lake to compile the generator executable and its
transitive native artifacts. In Mathlib-heavy projects this is often faster for
cold CI jobs, even though the interpreted generator step itself can be a little
slower than a compiled executable.

Projects may also declare a `lean_exe` for repeated local runs:

```lean
lean_exe «blueprint-gen» where
  root := `ProjectTemplateMain
```

Then the compiled-executable path remains available:

```bash
lake exe blueprint-gen --output _out/site
```

## Blueprint Options

Set Blueprint options with ordinary Lean `set_option` commands in the module
that elaborates the Blueprint chapter or document:

```lean
set_option verso.blueprint.numbering global
set_option verso.blueprint.foldProofBlocks true
set_option verso.blueprint.foldCodeBlocks false
```

Current options:

- `verso.blueprint.numbering`
  - default: `sub`
  - `sub`: chapter-prefixed numbering such as `Theorem 5.5`
  - `global`: document-order numbering such as `Theorem 27`
  - `local`: legacy local numbering without a chapter prefix
- `verso.blueprint.foldProofs`
  - default: `true`
  - folds proof bodies in rendered Lean code panels after `by`
- `verso.blueprint.foldProofBlocks`
  - default: `false`
  - renders proof blocks as collapsed disclosure blocks
- `verso.blueprint.foldCodeBlocks`
  - default: `false`
  - renders Lean, Rust, and external code panels as collapsed disclosure blocks
- `verso.blueprint.trimTeXLabelPrefix`
  - default: `false`
  - trims TeX-style label prefixes when deriving Lean names
- `verso.blueprint.math.lint`
  - default: `true`
  - runs best-effort KaTeX validation during elaboration
- `verso.blueprint.externalCode.strictResolve`
  - default: `false`
  - upgrades unresolved or ambiguous external Lean names from warnings to errors
- `verso.blueprint.externalCode.sourceLinkTemplate`
  - default: `""` (automatic GitHub links when the source file belongs to a
    Git checkout with a GitHub `origin` remote)
  - builds source links for external declarations using `{path}`, `{relpath}`,
    `{module}`, `{line}`, `{column}`, `{endLine}`, and `{endColumn}`
- `verso.blueprint.summary.debugDiagnostics`
  - default: `false`
  - adds maintainer diagnostics such as external declaration render failures to
    `blueprint_summary`
- `verso.blueprint.graph.defaultDirection`
  - default: `TB`
  - sets the fallback graph direction for `blueprint_graph` when
    `(direction := ...)` is omitted
- `verso.blueprint.graph.defaultPack`
  - default: `false`
  - sets the fallback Graphviz component packing behavior for
    `blueprint_graph` when `(pack := ...)` is omitted
- `verso.blueprint.debug.commands`
  - default: `false`
  - emits debug info logs while elaborating Blueprint graph, summary, and
    bibliography commands
- `verso.blueprint.profile`
  - default: `false`
  - enables timing logs for Blueprint directive and code-block elaboration

## Experimental Widget

The widget surface is experimental.

To enable it, import `VersoBlueprint.Widget` explicitly in the project that
wants to use it.

## Current Limits

- parent/group metadata is structural only; it does not change proof status or
  dependency edges
- group labels are metadata, not first-class reference targets
- unresolved Blueprint references currently degrade locally at the call site;
  they are not accumulated into a global diagnostics report
- Rust support currently covers only labeled inline Rust blocks with basic
  built-in syntax coloring
- Rust attachments currently do not provide diagnostics, hover data, or
  external Rust symbol references
- some rendering details and summary ranking policies are still expected to
  evolve
