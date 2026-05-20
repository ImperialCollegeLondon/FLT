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
      Basics.lean            placeholder chapter (dummy material)
  FLTBlueprintMain.lean      generator entry point
  scripts/
    ci-pages.sh              local build-and-render check
```

## Building

```bash
cd blueprint-verso
lake update            # once, to resolve dependencies
lake build FLTBlueprint
lake exe blueprint-gen --output _out/site
```

`lake exe blueprint-gen --output _out/site` compiles the blueprint into HTML
under `_out/site/html-multi/`. The CI-equivalent path that avoids building the
generator executable is `./scripts/ci-pages.sh`, which runs
`lake env lean --run FLTBlueprintMain.lean --output _out/site`.

## Linking to FLT declarations (phase 2)

To reference real FLT declarations from Blueprint nodes, add

```lean
require FLT from ".."
```

to `lakefile.lean` *before* the `VersoBlueprint` require (so FLT's mathlib
dependency pins win during resolution). Blueprint nodes then link to FLT code
with `(lean := "FLT.SomeDeclaration")`.
