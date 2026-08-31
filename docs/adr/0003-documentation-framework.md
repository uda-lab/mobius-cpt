# 0003 — Documentation framework: reference docs only, not the research note

## Context

Issue #49 asked whether the project should adopt an existing
formalisation-documentation framework — `leanblueprint`, `verso-blueprint`,
or plain generated Lean API docs (`doc-gen4`) — rather than assuming any of
them is the right publication format. The comparison against each option
lives in `docs/documentation-options.md`; this ADR records the resulting
decision.

The project already has two distinct documentation goals: a
mathematician-facing research note for readers with no Lean knowledge
(Issue #48, ordinary Japanese mathematical prose), and Lean/library
reference documentation for readers working with the source. Adoption is not
an acceptance criterion for #49, and this decision must not block #48.

## Decision

**Use only for reference docs.**

- Adopt `doc-gen4` for Lean/library reference documentation. It renders the
  existing 969 doc-comment blocks across the codebase with no content
  restructuring, adds no new language toolchain (Lean/elan only), and its
  `v4.33.1` tag matches this repository's pinned toolchain exactly. Minimum
  scope: a nested `docbuild/` Lake project and one CI job building
  `lake build MobiusCPT:docs`, run on `main` pushes rather than on the
  `check` gate's critical path.
- Do not adopt `leanblueprint` or `verso-blueprint` for the mathematician-
  facing research note. Both are built around per-statement labelled nodes
  for dependency/status tracking, not the continuous mathematical prose
  Issue #48 requires; retrofitting either onto the existing declaration tree
  means rewriting the narrative into that node structure rather than reusing
  it. `leanblueprint` adds a second, unrelated toolchain (Python, plasTeX,
  Graphviz, a LaTeX engine); `verso-blueprint` avoids that but is young
  (created 2026-02-22, three reference deployments) and its parent project
  self-describes as changing at a rapid pace — both are unattractive risk
  profiles for a project with no dedicated maintenance bandwidth beyond the
  active driver.

## Consequences

- Issue #48's conventional LaTeX/PDF note remains the sole vehicle for the
  mathematician-facing narrative; nothing here changes its scope or blocks
  it.
- A `doc-gen4` reference-docs integration is a bounded, independent
  follow-up (tracked separately, not part of this Issue's closure); it
  touches no existing Lean file.
- Revisit `verso-blueprint` if a standalone dependency-graph/status web page
  becomes independently valuable and the tool has matured past its current
  three-deployment adopter base; revisit `leanblueprint` only if its
  Python/plasTeX toolchain becomes acceptable overhead for that same goal.
  Neither is adopted now.
