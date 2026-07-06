#!/usr/bin/env python3
"""
List the FLT files required by a given FLT "boss" file.

Starting from a root FLT module (by default the file containing the boss
theorems, ``FLT.NumberField.AdeleRing``), walk the import graph following
only ``FLT.*`` edges and collect every FLT module transitively reached.

The traversal naturally terminates at "leaf" FLT files -- ones whose imports
are all Mathlib (no further ``FLT.*`` imports) -- so the returned list is
exactly the set of FLT files required to reach a state where every remaining
import is a Mathlib import.

Import parsing is delegated to ``scripts/dag_traversal.py``, which shells out
to ``lean --deps-json`` and therefore understands the ``module`` /
``public import`` syntax correctly.

Usage:
    tools/flt_import_closure.py                       # default boss file
    tools/flt_import_closure.py FLT.NumberField.AdeleRing
    tools/flt_import_closure.py --json
    tools/flt_import_closure.py --leaves-only
"""

import argparse
import sys
from collections import deque
from pathlib import Path

# Make scripts/ importable regardless of the current working directory.
_PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_PROJECT_ROOT / "scripts"))

from dag_traversal import DAG  # noqa: E402

DEFAULT_ROOT = "FLT.NumberField.AdeleRing"


def flt_closure(dag: DAG, root: str) -> dict[str, list[str]]:
    """Return every FLT module transitively imported by *root* (inclusive).

    Only edges into ``FLT.*`` modules are followed; Mathlib (and any other
    non-FLT) imports are ignored.  The result maps each reached FLT module to
    the sorted list of FLT modules it directly imports (empty list => a leaf
    whose remaining imports are all Mathlib).
    """
    if root not in dag.modules:
        raise KeyError(
            f"{root!r} is not an FLT module in the DAG "
            f"(expected e.g. FLT.NumberField.AdeleRing)"
        )

    reached: dict[str, list[str]] = {}
    queue: deque[str] = deque([root])
    while queue:
        name = queue.popleft()
        if name in reached:
            continue
        flt_imports = sorted(
            imp
            for imp in dag.modules[name].imports
            if imp.startswith("FLT.") and imp in dag.modules
        )
        reached[name] = flt_imports
        for imp in flt_imports:
            if imp not in reached:
                queue.append(imp)
    return reached


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("root", nargs="?", default=DEFAULT_ROOT,
                        help=f"Root FLT module (default: {DEFAULT_ROOT})")
    parser.add_argument("--json", action="store_true",
                        help="Emit JSON instead of a human-readable report")
    parser.add_argument("--leaves-only", action="store_true",
                        help="Only list leaf FLT files (imports are all Mathlib)")
    args = parser.parse_args()

    dag = DAG.from_directories(_PROJECT_ROOT, ["FLT"])
    reached = flt_closure(dag, args.root)

    leaves = sorted(name for name, imps in reached.items() if not imps)
    non_leaves = sorted(name for name, imps in reached.items() if imps)

    if args.json:
        import json
        print(json.dumps({
            "root": args.root,
            "count": len(reached),
            "leaf_count": len(leaves),
            "modules": sorted(reached),
            "leaves": leaves,
            "imports": {k: reached[k] for k in sorted(reached)},
        }, indent=2))
        return 0

    if args.leaves_only:
        print(f"# {len(leaves)} leaf FLT files (all remaining imports are Mathlib)")
        for name in leaves:
            print(name)
        return 0

    print(f"Root: {args.root}")
    print(f"Total FLT files required: {len(reached)} "
          f"({len(leaves)} leaves, {len(non_leaves)} intermediate)\n")
    print("All required FLT files (alphabetical):")
    for name in sorted(reached):
        marker = "  (leaf)" if not reached[name] else ""
        print(f"  {name}{marker}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
