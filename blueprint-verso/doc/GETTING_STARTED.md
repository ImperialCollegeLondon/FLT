# Getting Started

This guide is the shortest path from "I want a Blueprint project" to "I can
render a first site".

If you are new to Verso, the easiest approach is to copy the starter template
and keep the initial structure intact while you replace the example content.

## What You Are Building

A Blueprint project usually has three moving parts:

1. one or more chapter modules with the mathematical content
2. one Blueprint top-level file that assembles the document
3. one generator entry point that renders the site

Many older examples call the top-level file `Contents.lean`. In this doc set we
refer to it as the Blueprint top-level file because the role matters more than
the filename.

## Choose labels first

Blueprint blocks are identified by labels chosen by the author.

Examples:

- `addition_spec`
- `addition_right_identity`
- `multiplication_assoc`

Those labels are the key to the whole system. They are used to:

- identify nodes in the summary and graph views
- connect dependency references with `{uses "addition_spec"}[]`
- point at a node without adding a dependency edge with `{bpref "addition_spec"}[]`
- attach inline Lean code with a labeled `lean` code block
- attach raw TeX source for porting with a `tex` code block
- tag compiled declarations with `@[blueprint "label"]`

If you pick stable labels early, the rest of the project structure becomes much
easier to maintain.

Unlike Lean code references, `{uses "addition_spec"}[]` can refer to a label
before its final use sites are elaborated. Blueprint resolves those forward
references when building the document.

Use `uses` when the current Blueprint node mathematically depends on the target
node. Use `bpref` for prose references that should render as Blueprint links but
should not affect the graph or dependency summaries.

If the payload of `{uses "addition_spec"}[]` or `{bpref "addition_spec"}[]` is
empty, Blueprint can generate the visible text automatically, for example
`Theorem N`.

## Start from the template

Use [project_template/](../project_template/) as the starting point.

Its key files are:

- `ProjectTemplate/Chapters/Addition.lean`: the first chapter
- `ProjectTemplate/Chapters/Multiplication.lean`: the second chapter
- `ProjectTemplate/Chapters/Collatz.lean`: a third chapter with a deliberately
  unfinished open problem
- `ProjectTemplate/Blueprint.lean`: the Blueprint top-level file
- `ProjectTemplateMain.lean`: the generator entry point
- `lakefile.lean`: package configuration, including the optional generator
  executable

The template is intentionally small. It is meant to teach the shape of a
Blueprint project before you scale it up.

## The three Verso forms to recognize first

If you are new to Verso, there are only three forms you need to understand at
the start:

- `#doc (Manual) "Title" =>` starts a document module
- `{include 0 Some.Module}` includes a chapter into the top-level file
- `:::definition "label_1"` starts a Blueprint block

You can get a long way just by following those three patterns in the template.

## Read the first chapters

The starter chapters in
[project_template/ProjectTemplate/Chapters/Addition.lean](../project_template/ProjectTemplate/Chapters/Addition.lean)
and
[project_template/ProjectTemplate/Chapters/Multiplication.lean](../project_template/ProjectTemplate/Chapters/Multiplication.lean),
plus
[project_template/ProjectTemplate/Chapters/Collatz.lean](../project_template/ProjectTemplate/Chapters/Collatz.lean)
show the most important authoring patterns:

- definition, theorem, and proof blocks
- labels that identify nodes
- a `uses` link to another Blueprint entry
- a `bpref` link when prose should reference a node without adding a dependency
- a local Lean code block
- a statement linked to an existing Lean declaration
- optional metadata such as `parent`, `owner`, `tags`, `effort`, and `priority`

The examples are about basic arithmetic on natural numbers, followed by a small
Collatz chapter. They read like a real mathematical story, but they are still
small enough to copy and adapt.

## Read the Blueprint top-level file

The top-level file in
[project_template/ProjectTemplate/Blueprint.lean](../project_template/ProjectTemplate/Blueprint.lean)
does two jobs:

1. it includes the chapter modules into the document
2. it chooses which rendered overview pages to include

The starter template includes:

- the chapter pages with `{include 0 ProjectTemplate.Chapters.Addition}` and
  the other chapter includes
- a dependency graph with `{blueprint_graph}`
- a progress summary with `{blueprint_summary}`

That is the core HTML surface most projects want first. The dependency graph can
also take `(direction := LR | RL | TB | BT)` and `(pack := true | false)`, and
grouped projects expose the current graph views through the rendered page's
`View`, `Legend`, and `Graph options` controls.

## Read the generator entry point

The entry point in
[project_template/ProjectTemplateMain.lean](../project_template/ProjectTemplateMain.lean)
is the `main` function you run to generate the site.

The included CI script first builds the project's Lean library artifacts, then
runs the generator file through Lean:

```bash
lake update
./scripts/ci-pages.sh
```

Run `lake update` once after copying the template. After that, run
`./scripts/ci-pages.sh` whenever you want the same local build-and-render check
that the included GitHub Pages workflow uses. Internally that script uses:

```bash
lake build ProjectTemplate
lake env lean --run ProjectTemplateMain.lean --output _out/site
```

This path avoids building the generator executable and its transitive native
artifacts, which is usually the better tradeoff for CI and Mathlib-heavy
projects. If you repeatedly run the same generator locally and want a compiled
executable, the `blueprint-gen` executable declared in `lakefile.lean` still
supports:

```bash
lake exe blueprint-gen --output _out/site
```

## What to change first

After copying the template:

1. rename `ProjectTemplate` to your project name
2. change the document title in the Blueprint top-level file
3. replace the addition, multiplication, and Collatz chapters with your own
   first chapters
4. keep the generator entry point and top-level file structure until your
   project is stable

## What to read next

After the first site renders:

1. read [doc/MANUAL.md](./MANUAL.md) for the full authoring surface
2. return to [project_template/README.md](../project_template/README.md) when
   you want to compare your project against the starter layout
