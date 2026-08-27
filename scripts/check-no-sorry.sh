#!/usr/bin/env bash
# Fail if an unmarked `sorry` (or `admit`, which is `sorry` under another name)
# appears in *code* in Lean sources.
#
# A `sorry` is permitted only when its OWN line carries a marker citing the Issue
# that explicitly authorises the work to land incomplete:
#     theorem foo : P := by sorry  -- ALLOW_SORRY: #<n> <reason>
#
# Per-line markers with an Issue number are deliberate: every incomplete proof is
# justified in place and traceable, so `sorry` cannot accumulate silently. Note that
# a marked `sorry` still fails scripts/check-axioms.sh if it reaches a pinned theorem.
#
# Only a `sorry` token in actual code counts. The word may appear freely in
# documentation prose — line comments (`-- …`) and block comments (`/- … -/`,
# `/-! … -/`, nested) are stripped before matching, so "sorry-free" and
# "marked sorry" in a docstring do not trip the check. The ALLOW_SORRY marker,
# which lives in the trailing line comment, is still honored on real code lines.
#
# FAIL-CLOSED by design: the comment-aware scan is a single `awk` over all files
# with NO error suppression. `set -euo pipefail` makes any scanner or portability
# failure abort the script with a nonzero status, so a broken check can never
# report success.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# Enumerate Lean sources fail-closed: `find` writes to a temp file and its exit
# status is checked BEFORE the list is consumed. (A bare process substitution
# `< <(find …)` would swallow traversal errors — bash does not propagate them —
# letting a partial scan report OK.) `.git`/`.lake` are pruned by basename at
# any depth, because linked worktrees and nested package directories carry their
# own `.lake`; agent worktrees under .claude/worktrees/ are out of scope (they
# are scanned by their own CI).
list="$(mktemp)"
trap 'rm -f "$list"' EXIT
find . \( -name '.git' -o -name '.lake' -o -path './.claude/worktrees' \) -prune \
     -o -type f -name '*.lean' -print0 > "$list"

if [ ! -s "$list" ]; then
  echo "OK: no Lean sources to scan."
  exit 0
fi

# Comment-aware scanner. Maintains block-comment nesting across lines (reset per
# file), strips line comments, and prints `file:line:content` for any code line
# whose CODE portion holds a whole-word `sorry` but whose full line lacks an
# ALLOW_SORRY marker. Any awk failure propagates (no `|| true`, no `2>/dev/null`;
# a failing awk in any xargs batch makes the substitution non-zero under
# `pipefail`), so the guard fails closed. Files are fed via NUL-safe xargs
# batching so the scan stays under ARG_MAX regardless of tree size.
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
    if (code ~ /(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)/ && line !~ /ALLOW_SORRY: .*#[0-9]+/)
      printf "%s:%d:%s\n", FILENAME, FNR, line
  }
' < "$list")"

if [ -n "$violations" ]; then
  printf '%s\n' "$violations" >&2
  echo "ERROR: unmarked 'sorry'/'admit' found above." >&2
  echo "Add '-- ALLOW_SORRY: #<issue> <reason>' on the same line (only for work an Issue explicitly authorises to land incomplete), or finish the proof." >&2
  exit 1
fi
echo "OK: no unmarked 'sorry'/'admit' in Lean sources."
