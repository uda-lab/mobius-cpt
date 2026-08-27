#!/usr/bin/env bash
# Fail on undeclared trust-extending declarations in Lean sources:
#     axiom   constant   opaque   unsafe
#
# These widen the trusted base or hide content behind an irreducible term. They
# are permitted only when the declaration line carries a marker citing the Issue
# in which the owner authorised them:
#     axiom foo : ...  -- ALLOW_AXIOM: #34 external theorem, see Issue
# Even then, scripts/check-axioms.sh rejects any pinned theorem whose closure
# contains a project axiom; the marker only silences this textual guard.
#
# Matching is anchored to declaration-leading keywords (optionally preceded by
# attributes/modifiers) in the comment-stripped code of each line, so words inside
# comments, docstrings, identifiers, or strings do not trip the check.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Enumerate Lean sources fail-closed: `find` writes to a temp file and its exit
# status is checked BEFORE the list is consumed (a bare process substitution
# would swallow traversal errors and let a partial scan report OK). `.git`/`.lake`
# are pruned by basename at any depth (worktrees vendor their own `.lake`,
# issue #84); agent worktrees are scanned by their own CI.
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

# Comment-aware single awk scan over all sources, fed via NUL-safe xargs batching
# (ARG_MAX-safe). Block comments (`/- … -/`, nested) and line comments are stripped
# first — a docstring line that happens to begin with "axiom …" is prose, not a
# declaration. The declaration regex is then anchored to the CODE portion of the
# line: keyword optionally preceded by attributes/modifiers, and the full line lacks
# an ALLOW_AXIOM marker citing an Issue. No here-strings and no per-file grep: a
# failing awk/xargs in any batch makes the plain command substitution non-zero,
# which `set -e` turns into an abort, so the guard fails closed.
violations="$(xargs -0 awk '
  FNR == 1 { depth = 0 }
  {
    line = $0; code = ""; inLine = 0
    n = length(line); i = 1
    while (i <= n) {
      two = substr(line, i, 2)
      if (depth > 0) {
        if (two == "-/") { depth--; i += 2; continue }
        if (two == "/-") { depth++; i += 2; continue }
        i++; continue
      }
      if (inLine) { i++; continue }
      if (two == "--") { inLine = 1; i += 2; continue }
      if (two == "/-") { depth++; i += 2; continue }
      code = code substr(line, i, 1); i++
    }
    if (code ~ /^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|scoped|local)[[:space:]]+)*(axiom|constant|opaque|unsafe)[[:space:]]/ && line !~ /ALLOW_AXIOM: .*#[0-9]+/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  }
' < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations"
  echo "ERROR: undeclared axiom/constant/opaque/unsafe found above." >&2
  echo "Add '-- ALLOW_AXIOM: #<issue> <reason>' on the same line; this needs an owner-authorised Issue, and scripts/check-axioms.sh still rejects it if it reaches a pinned theorem." >&2
  exit 1
fi
echo "OK: no undeclared axiom/constant/opaque/unsafe in Lean sources."
