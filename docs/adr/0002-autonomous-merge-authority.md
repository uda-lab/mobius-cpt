# 0002 — Autonomous merge authority and the completion mandate

## Context

The flow is Issue → branch → PR → independent review → CI job `check` → squash merge, with no
direct pushes to `main`, and the loop runs without a human in the decision path. The owner's
standing mandate is fully autonomous AI-driven task completion, including the merge once the
gates are satisfied. The formalisation programme carries a one-week completion target from
2026-08-31, and idle time on ready work is the primary failure mode to engineer against.

## Decision

Both the Issue driver and the orchestrator hold permanent, pre-authorised authority to
squash-merge a PR whose gates are verified: CI `check` green on the head, the review round
classified non-substantive under the routing rules, and no `do-not-merge`, `blocked` or
`needs-decision` label. Normally the driver merges its own PR; the orchestrator merges when the
driver cannot. Session tooling must not block `gh pr merge`. This codifies the repository's
operating discipline since its start.

## Consequences

- Branch protection, the guards and CI remain the actual gates; merge authority adds no gate and
  removes none.
- A merge past a substantive finding, a red gate, or a hard-stop label remains prohibited.
- A merge-ready PR is merged promptly; leaving it idle is the failure.
