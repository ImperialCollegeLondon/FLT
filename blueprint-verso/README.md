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
