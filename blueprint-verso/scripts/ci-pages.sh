#!/usr/bin/env bash

set -euo pipefail

lake build FLTBlueprint
# The `./` is load-bearing.  FLTBlueprintMain.lean pulls in its stylesheet with
# `include_str`, which resolves relative to the directory of the source file it
# appears in; given a bare `FLTBlueprintMain.lean` Lean cannot compute a parent
# directory and fails with "cannot compute parent directory".
lake env lean --run ./FLTBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
