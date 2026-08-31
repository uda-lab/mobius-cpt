# 0004 — Contract.lean as a statement surface after #12

## Context

Once #12 discharges `thm_3_10_i/ii/iii`, `MobiusCPT/Contract.lean` holds no obligation and no
theorem: one opaque `def_wanted W : WightmanBundle` (never inhabited), its transparent
projections, and ~150 lines of "Issue #N has landed" chronology accumulated over ten PRs. The
results live in `MobiusCPT.WightmanBundle.thm_3_10_i/ii/iii`, which quantify over a real `W`.
An activity log inside the Lean tree is what `AGENTS.md` forbids.

## Decision

Keep the file as the **statement surface**: delete the landing chronology, reduce the module
header to (i) what the file is (the Issue #2 statement contract, now fully discharged), (ii) the
soundness note for `def_wanted`/`❰…❱`, and (iii) a pointer at the three `WightmanBundle.thm_3_10_*`
theorems and the modules holding the lemma chain. Keep `W` and the projections unchanged so the
file still reads as "the target, in the source's vocabulary". No retirement: a reader must be
able to see the target without navigating the module tree.

## Consequences

- `MobiusCPT/Contract.lean`'s header names `MobiusCPT.WightmanBundle.thm_3_10_i/ii/iii` in
  `MobiusCPT.Wightman.Thm310` and the lemma chain feeding them, instead of a per-Issue landing
  log; every declaration in the file stays byte-identical to before this decision.
- No theorem statement changes anywhere; `scripts/print_axioms.lean` is unaffected, since it
  pins nothing from `Contract.lean`.
- A later child Issue that adds a genuinely new placeholder to the file extends the pointer
  section rather than reintroducing chronology.
