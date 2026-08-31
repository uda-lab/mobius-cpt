# Documentation framework options

Comparison of documentation-tooling options for this repository, prepared for
Issue #49. Facts about external tools were checked against their live
repositories on 2026-08-31; every load-bearing claim below cites the source
and that date. Repository facts (toolchain pin, declaration count, doc-string
density) were measured on `main` at commit `a50feb4`.

## Reader model and the two products

The repository has two documentation goals with different readers, which
this comparison keeps separate as Issue #49 requires:

1. **Mathematician-facing research note** — narrative proof exposition,
   difficult points, gaps, status, written for a reader with no Lean
   knowledge. Issue #48 already owns this product as a conventional Japanese
   LaTeX/PDF note; that scope does not depend on the outcome here.
2. **Lean/library reference documentation** — declaration and module lookup,
   source links, dependency and status navigation for a reader who *is*
   working with the Lean source.

A framework decision for (2) does not need to touch (1), and this write-up
recommends against conflating them.

## Baseline: conventional LaTeX/PDF note

Ordinary LaTeX with hand-written cross-references. No dependency-graph
generation, no automatic formalisation-status extraction, no link checking
against Lean declarations — everything is maintained by hand. Zero new CI
dependency and zero coupling to the Lean toolchain: a change to
`lean-toolchain` or a mathlib bump never breaks the note's build. This is the
correct vehicle for product (1) precisely because its content is prose about
mathematics, not a per-declaration status table, and it is what Issue #48
already specifies.

## Option: `leanblueprint` (PatrickMassot/leanblueprint)

Source: [github.com/PatrickMassot/leanblueprint](https://github.com/PatrickMassot/leanblueprint), checked 2026-08-31.

- **What it is.** A plasTeX plugin: write the narrative in LaTeX, tag
  statements with `\lean{Declaration.name}` and `\leanok`, and it renders
  both a PDF and a web page with a dependency graph and per-node
  formalisation status (proved / stated / sorry), and a `checkdecls` command
  that fails CI if a tagged declaration no longer exists.
- **Dependencies.** Python, `pip install leanblueprint`, plasTeX, Graphviz
  and its development headers, and a LaTeX engine (xelatex/lualatex) for the
  PDF. None of this overlaps with the repository's existing Lean-only
  toolchain — it is a second, unrelated build stack to install, pin and keep
  working in CI.
- **Lean-version coupling.** The tool itself has no toolchain-specific
  branches; it consumes a `blueprint/lean_decls` list matched against
  whatever the project's own `lake build` produces, so it is largely
  insulated from Lean/mathlib version bumps. No explicit Lean 4 version
  requirement is documented on the repository.
  (Source as above, checked 2026-08-31.)
- **Maintenance status.** 370 stars, last push 2025-12-23 (per
  `pushed_at` on the GitHub API, checked 2026-08-31) — about eight months
  stale relative to today. No sign of abandonment (issues are still
  triaged), but the cadence is markedly slower than `verso-blueprint`'s
  (below). In production use by more than 40 projects, including Fermat's
  Last Theorem and the Prime Number Theorem formalisations — the track
  record for a large, long-running formalisation is real.
- **Fit for this repository.** Strong on exactly the two things Issue #49
  asks about — dependency graphs and status exposure — and it is the
  battle-tested choice for a large existing codebase. The cost is a second
  toolchain (Python/plasTeX/Graphviz/LaTeX) the project does not otherwise
  need, and every declaration the note wants to reference must be retrofitted
  with a hand-written blueprint node and `\lean{}` tag; nothing here is
  generated from the existing `/--  --/` doc-comments.

## Option: `leanprover/verso-blueprint`

Source: [github.com/leanprover/verso-blueprint](https://github.com/leanprover/verso-blueprint), checked 2026-08-31.

- **What it is.** A Lean-native successor in the same design space as
  `leanblueprint`: write chapters as Verso documents with `:::definition`,
  `:::theorem`, `:::proof` directives carrying `(lean := "Decl.name")`
  metadata; `lake exe vbp build` renders an HTML site (`_out/site/html-multi`)
  with dependency graphs, progress summaries and generated-data queries
  (`lake exe vbp query work-queue`), and an optional `--pdf` flag drives
  `lualatex` for a PDF. Its own README states it is built as "a
  next-generation system" following the design of "Patrick Massot's Lean
  blueprints" — an explicit acknowledgement, not a claim of drop-in
  compatibility.
- **Dependencies.** Lean/Lake plus Node.js/TypeScript (the repository ships
  `package.json`/`tsconfig.json` alongside `lakefile.lean`) for its
  interactive web components. No Python/plasTeX/Graphviz stack.
- **Lean-version coupling.** `branch-policy.json` in the repository (checked
  2026-08-31) pins the maintained `v4.33.0` release branch to
  **toolchain `v4.33.1`** — an exact match for this repository's
  `lean-toolchain`. The `v4.34.0` default branch runs ahead of that. Being a
  Lean/Lake package itself, it must track Lean releases the way any Lake
  dependency does, which is a real, recurring coupling this project does not
  have with a plain LaTeX note.
- **Maintenance status.** Created 2026-02-22, last push 2026-08-30 (the day
  before this evaluation), 27 stars. Actively developed by the `leanprover`
  org itself, but young: three reference deployments are listed
  (`verso-noperthedron`, `verso-flt`, `verso-carleson`), none at the scale or
  age of `leanblueprint`'s adopter list. The parent `verso` project's own
  README (checked 2026-08-31) describes itself as "undergoing change at a
  rapid pace" and recommends discussing non-trivial use with maintainers
  first — a caution for a project that runs on a single disposable driver at
  a time with no dedicated maintenance bandwidth for a moving upstream API.
- **Fit for this repository.** The toolchain match is a genuine point in its
  favour, and it avoids adding a Python stack. But its youth and small
  adopter base mean betting the primary research artefact on it now carries
  API-churn risk that a mature tool does not. Like `leanblueprint`, it needs
  the narrative content restructured into labelled nodes; nothing here is
  generated from existing doc-comments either.

## Option: `leanprover/doc-gen4`

Source: [github.com/leanprover/doc-gen4](https://github.com/leanprover/doc-gen4), checked 2026-08-31.

- **What it is.** The API-reference generator behind
  `leanprover-community.github.io/mathlib4_docs`: point it at a Lake target
  and it emits a searchable HTML site of every declaration, module, and
  cross-reference, built from the project's own `/--  --/` doc-comments and
  signatures — no separate narrative-authoring step. Standard integration is
  a small nested `docbuild/` Lake project depending on the target library
  plus `doc-gen4`, built with `lake build <Target>:docs`.
- **Dependencies.** A Lean/elan toolchain (already present) and a C compiler
  on Linux/macOS. No new language stack.
- **Lean-version coupling.** Tagged per Lean release; the tag list (checked
  2026-08-31) includes **`v4.33.1`** exactly, matching this repository's pin
  in `lean-toolchain` and the mathlib `rev` in `lakefile.toml`. Bumping the
  toolchain later means bumping this one pin, the same motion already
  required for mathlib.
- **Maintenance status.** 169 stars, last push 2026-08-21 (10 days before
  this evaluation). Actively maintained by the `leanprover` org and is the
  tool mathlib4 itself depends on for its public docs — the most
  battle-tested option of the three for exactly the reference-lookup use
  case.
- **Fit for this repository.** This is the only option that needs *no*
  content restructuring: the repository already carries 969 doc-comment
  blocks across 75 of its 76 `.lean` files (measured on `main`,
  commit `a50feb4`), so a `docbuild` target renders immediately useful
  output on day one. It answers "what does `Declaration.name` mean and what
  does it depend on" for a reader in the Lean source — not "why is this
  proof structured this way," which remains the research note's job.

## Comparison against the Issue's criteria

| Criterion | LaTeX/PDF note | `leanblueprint` | `verso-blueprint` | `doc-gen4` |
|---|---|---|---|---|
| Readable narrative for non-Lean readers | Yes — its whole purpose | Possible but node-structured, not free prose | Possible but node-structured, not free prose | No — API reference, not narrative |
| Informal↔declaration linking | Manual | Built in (`\lean{}`) | Built in (`lean :=`) | N/A (declarations only) |
| Dependency/proof-flow graph | Manual/none | Built in | Built in | Module/declaration dependency only |
| Status/incomplete-node exposure | Manual | Built in (`\leanok`, sorry detection) | Built in (sorry detection) | N/A |
| Documents *why*/gaps, not just dependencies | Yes (prose) | Only via node prose | Only via node prose | No |
| PDF quality | High (hand-tuned) | High (mature LaTeX pipeline) | Usable, less proven | N/A (web only) |
| Web quality | N/A unless built | Mature | Mature but young ecosystem | Mature (mathlib4 uses it) |
| Retrofit cost onto ~800-decl/76-file base | None (independent) | High — every referenced node rewritten by hand | High — same | Low — renders existing doc-comments |
| New CI/toolchain surface | None | Python+plasTeX+Graphviz+LaTeX | Node.js/TypeScript alongside Lean | None (Lean-only) |
| Sync with declarations | Manual | Automatic + `checkdecls` CI check | Automatic | Automatic (generated from source) |
| Public-artefact suitability | Yes, proven | Yes, proven at scale | Not yet proven at this scale | Yes, proven (mathlib4) |

## Recommendation

**Verdict: use only for reference docs.**

- **Adopt `doc-gen4`** for Lean/library reference documentation (product 2).
  It needs no narrative restructuring, adds no new language toolchain, pins
  exactly to the existing `v4.33.1` toolchain, and is the same tool mathlib4
  publishes its own docs with. This is the low-risk, low-cost option that
  clears every "reference lookup" criterion in the Issue.
- **Do not adopt `leanblueprint` or `verso-blueprint`** as the vehicle for
  product 1, the mathematician-facing narrative. Issue #48 already specifies
  that product as ordinary Japanese mathematical prose for a Lean-naive
  reader; a Blueprint's per-statement labelled-node model is built for
  dependency/status tracking, not for the kind of continuous mathematical
  argument #48 requires, and retrofitting either tool onto the existing
  ~800-declaration tree means rewriting the narrative into that node
  structure rather than reusing it. Adopting one now would also put the
  project's primary public artefact on a second, non-Lean build stack
  (`leanblueprint`) or a young, fast-moving one (`verso-blueprint`) for a
  gain — proof-flow visualisation — that a single hand-drawn figure in the
  existing note already covers per Issue #48's own content list.
- Between the two, if a standalone dependency-graph/status web page becomes
  independently worth having later, `verso-blueprint` is the better-placed
  candidate on toolchain grounds (exact `v4.33.1` match, no Python
  dependency) but the weaker one on maturity (created 2026-02-22, 27 stars,
  three reference deployments, upstream `verso` self-describing "rapid pace"
  change); `leanblueprint` is the reverse (proven at scale, but an added
  Python/plasTeX/Graphviz stack and a slower push cadence). Neither
  clears the bar to adopt now.

### Minimum useful scope if revisited (`doc-gen4`)

1. A nested `docbuild/` Lake project (per the tool's standard pattern)
   depending on `MobiusCPT` and pinning `doc-gen4` at tag `v4.33.1`.
2. One CI job that runs `lake build MobiusCPT:docs` and publishes the
   output — scheduled on `main` pushes or a manual trigger, not on every PR,
   so it never sits on the `check` gate's critical path.
3. No changes to any existing Lean file: doc-comments already present
   (969 blocks measured above) are the only input needed.

This is a self-contained follow-up, not a dependency of #48 or of any
in-flight mathematical Issue.
