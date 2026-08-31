# Agent Guidelines

<!-- Do not restructure or delete sections. Update individual values in-place when they change. -->

## Core Principles

- Keep this file under 20-30 lines of visible guidance.
- Keep only repo-specific, non-obvious instructions here.

## Project Overview

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Lean 4 + mathlib formalisation of the Möbius-covariant PCT theorem for Wightman CFTs on S¹ (Tener, CMP 407 (2026) 128; Carpi–Raymond–Tanimoto–Tener, Sel. Math. 31 (2025) 66). The staged scope lives in the owner's charter Issue; `docs/math/pct-theorem.md` is the working mathematical SoT and the primary papers win on any conflict.
- GitHub Issues and PRs are the only queue, planning and evidence surface: no status, roadmap, handoff, ledger or activity-log files in the tree (`scripts/check-transient-artifacts.sh` enforces the name patterns).

## Commands

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
~~~sh
scripts/bootstrap.sh   # idempotent: mathlib oleans + git hooks path; never cold-build mathlib, never run `lake update`
scripts/check.sh       # full gate: guards, lake build, live #print axioms; serialised on /tmp/lean-build.lock
~~~

## Code Conventions

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- Accepted code has no `sorry`/`admit`; `-- ALLOW_SORRY: #<issue> …` is a same-line escape only for work an Issue explicitly authorises to land incomplete, and it never reaches a pinned theorem's closure.
- No `axiom`/`constant`/`opaque`/`unsafe` declarations; an owner-authorised `-- ALLOW_AXIOM: #<issue> …` passes the textual guard but `scripts/check-axioms.sh` still rejects it (allowlist: propext, Classical.choice, Quot.sound; changing it is `needs-decision`).
- Never weaken, specialise or trivialise a statement to close a proof; statement-changing PRs need a source-to-Lean semantic review by an agent distinct from the implementer.
- Every public theorem a PR claims as a result is appended to `scripts/print_axioms.lean` (append-only) so the live audit covers it (enforced by `scripts/check-axiom-coverage.sh`).
- Proof experiments, build logs and scratch files stay untracked; `.gitignore` plus the transient-artefact guard are the contract.

## Architecture

<!-- Managed section: update with apply input, or omit/pass [] to remove. -->
- `MobiusCPT/` module tree with root aggregator `MobiusCPT.lean`; mathlib pinned by tag in `lakefile.toml` and by commit in `lake-manifest.json` (bumping is an infrastructure Issue).
- Flow: Issue → `issue-<n>-<slug>` branch → PR (`Closes #n`, no unchecked boxes) → independent review → CI job `check` → squash merge; no direct pushes to `main`.
- `agent:ready` is the execution-authorisation label: applied only by the owner or an authorised AI maintainer after auditing scope and acceptance (and source vs literal claim for source-sensitive Issues); agent-created Issues are backlog until then.
- `blocked`, `needs-decision`, `do-not-merge` are hard stops; anything changing mathematical scope, the physical model, the main theorem, repository architecture, credentials or budget is `needs-decision`.
- Durable decisions go to `docs/adr/` (`NNNN-<slug>.md`), mathematical definitions and statements to `docs/math/`; everything else lives in Issues and PRs.

## Maintenance Notes

<!-- This section is permanent. Do not delete. -->
- Delete stale or inferable guidance.
- Update commands and architecture when workflows change.
- Keep durable rules here; move detail to dedicated docs.
