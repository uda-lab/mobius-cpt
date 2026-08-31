#!/usr/bin/env bash
# Canonical local/CI integrity gate, in this order:
#   textual guards (sorry/admit, custom axioms, transient artefacts) → lake build →
#   live axiom audit → axiom-coverage guard (every public theorem is pinned in
#   scripts/print_axioms.lean).
# The whole run is serialised container-wide on /tmp/lean-build.lock: concurrent mathlib
# builds in a shared container OOM each other. The lock is an fd-based flock(2) held by
# this process (flock(1) on Linux; the same syscall via perl on macOS, which lacks flock(1)),
# so a killed build releases it — nothing stale to reclaim.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

LOCK=/tmp/lean-build.lock
if [ -z "${MOBIUS_CPT_LOCKED:-}" ]; then
  export MOBIUS_CPT_LOCKED=1
  if command -v flock >/dev/null 2>&1; then
    exec flock "$LOCK" bash "$0" "$@"
  elif command -v perl >/dev/null 2>&1; then
    exec perl -e '
      use Fcntl qw(:flock F_SETFD);
      my $lock = shift @ARGV;
      open(my $fh, ">>", $lock) or die "lock open $lock: $!\n";
      flock($fh, LOCK_EX)         or die "flock: $!\n";
      fcntl($fh, F_SETFD, 0)      or die "fcntl: $!\n";   # child inherits the locked fd
      exec @ARGV or die "exec: $!\n";
    ' "$LOCK" bash "$0" "$@"
  else
    echo "WARNING: neither flock nor perl found; running unserialised." >&2
  fi
fi

step() { echo "==> $*"; }

step "no unmarked sorry/admit";        bash scripts/check-no-sorry.sh
step "no custom axiom/opaque/unsafe";  bash scripts/check-no-custom-axiom.sh
step "no transient artefacts tracked"; bash scripts/check-transient-artifacts.sh

# From here only lake runs. Inside a linked git worktree the caller's GIT_DIR & co. would make
# lake's git subprocesses inside .lake/packages/* resolve THIS repository instead of their own;
# clear them now (not earlier: the transient guard above needs the caller's git object access).
# shellcheck disable=SC2046
unset $(git rev-parse --local-env-vars)

step "lake build";                     lake build
step "live axiom audit";               bash scripts/check-axioms.sh
step "axiom coverage";                 bash scripts/check-axiom-coverage.sh
echo "CHECK OK"
