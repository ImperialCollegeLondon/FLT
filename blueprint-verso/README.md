# FLT Verso Blueprint

This directory is a self-contained [Verso Blueprint](https://github.com/leanprover/verso-blueprint)
package for the FLT project. It is a nested Lake package: it has its own
`lakefile.lean`, `lean-toolchain`, and `.lake/` and does **not** modify FLT's
top-level `lakefile.toml`.

## Layout

```text
blueprint-verso/
  lakefile.lean              package definition + `blueprint-gen` executable
  lean-toolchain
  FLTBlueprint.lean          library root
  FLTBlueprint/
    Blueprint.lean           top-level file: assembles chapters + graph + summary
    Chapters/
      Basics.lean            chapter linking to the FLT declaration `Mazur_Frey`
  FLTBlueprintMain.lean      generator entry point
  scripts/
    ci-pages.sh              local build-and-render check
```

## Building

```bash
cd blueprint-verso
lake update            # once, to resolve dependencies (also fetches the Mathlib cache)
lake exe cache get     # ensure Mathlib's prebuilt artifacts are present
lake build FLTBlueprint
lake exe blueprint-gen --output _out/site
```

`lake exe blueprint-gen --output _out/site` compiles the blueprint into HTML
under `_out/site/html-multi/`. The CI-equivalent path that avoids building the
generator executable is `./scripts/ci-pages.sh`, which runs
`lake env lean --run FLTBlueprintMain.lean --output _out/site`.

## Authoring chapters

The full authoring reference is vendored under [`doc/`](./doc/):
[`doc/MANUAL.md`](./doc/MANUAL.md) is the complete directive and rendering
reference, and [`doc/GETTING_STARTED.md`](./doc/GETTING_STARTED.md) is the
walkthrough. `FLTBlueprint/Chapters/Basics.lean` is a worked example.

A chapter module is a Verso document. The core directives:

- `:::group "label"` … `:::` — reusable group metadata
- `:::author "id" (name := "…")` … `:::` — author metadata
- `:::definition "label" (parent := "…")` … `:::`
- `:::theorem "label" (parent := …) (owner := …) (tags := …) (effort := …) (priority := …)` … `:::`
- `:::lemma_ "label"` and `:::corollary "label"` — note the underscore on `lemma_`
- `:::proof "label"` … `:::` — attaches to the statement with the same label
- `{uses "label"}[]` — dependency reference (adds a graph edge)
- `{bpref "label"}[]` — link-only reference (no edge)
- inline math `` $`…` ``, display math `` $$`…` ``

To add a chapter:

1. Create `FLTBlueprint/Chapters/<Name>.lean` starting with the standard Verso
   imports and a `#doc (Manual) "<Title>" =>` header.
2. Add `import FLTBlueprint.Chapters.<Name>` and
   `{include 0 FLTBlueprint.Chapters.<Name>}` to `FLTBlueprint/Blueprint.lean`.

For mathematics not yet in Lean, omit `(lean := …)` and the labeled `lean` code
blocks; the nodes still render and appear in the graph and summary.

## Linking to FLT declarations

The package depends on FLT itself via `require FLT from ".."`, so chapter
modules can `import` FLT modules directly and Blueprint nodes can link to real
FLT declarations with `(lean := "...")` — for example
`:::theorem "mazur_frey" (lean := "Mazur_Frey")`, which links to `Mazur_Frey`
in `FLT/Basic/Reductions.lean`.

### Dependency resolution

Verso and Mathlib pin different versions of ProofWidgets and plausible. Lake
resolves a later `require` over an earlier one, so `lakefile.lean`:

- lists `require FLT` *after* `VersoBlueprint`, and
- pins `proofwidgets` and `plausible` explicitly, last, to the exact versions
  FLT's Mathlib uses.

Without this, `lake exe cache get` computes the wrong hashes and Mathlib is
rebuilt from scratch instead of restored from cache.
