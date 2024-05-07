#!/usr/bin/env bash
# Usage: mk_all.sh
#
# Examples:
#   ./scripts/mk_all.sh
#   ./scripts/mk_all.sh data/real
#   ./scripts/mk_all.sh ../archive
#
# Makes an FLT_files.lean file importing all files inside FLT/ .

cd "$( dirname "${BASH_SOURCE[0]}" )"/../FLT
if [[ $# = 1 ]]; then
  dir="${1%/}"  # remove trailing slash if present
else
  dir="."
fi

# remove an initial `./`
# replace an initial `../test/` with just `.` (similarly for `roadmap`/`archive`/...)
# replace all `/` with `».«`
# replace the `.lean` suffix with `»`
# prepend `import «`
# Does the above really describe what's going on below??
find "$dir" -name \*.lean -not -name FLT_files.lean \
  | sed 's,^\./,,;s,^\.\./[^/]*,,;s,/,.,g;s,\.lean$,,;s,^,import FLT.,' \
  | sort >"$dir"/../FLT_files.lean
