/-
Live coverage guard for the axiom-pinning contract in `scripts/print_axioms.lean`
(Issue #56). Walks the fully elaborated environment produced by `lake build` and fails
unless every public `theorem` declared inside a `MobiusCPT…` module has a
`#print axioms` line in `scripts/print_axioms.lean` (the input consumed at run time by
`scripts/check-axioms.sh`, the live trust-footprint audit).

Run via `lake env lean scripts/check_axiom_coverage.lean` from the repository root
(`scripts/check-axiom-coverage.sh` wraps this; `scripts/check.sh` runs it immediately
after the live axiom audit, under the same `/tmp/lean-build.lock` as the rest of the
gate — this walk costs roughly the same memory as that audit run).

No Lean statement in `MobiusCPT/` is read or altered here; only `ConstantInfo`
metadata already produced by `lake build` is inspected.

"Public theorem" excludes every one of the following kinds — each a legitimate,
non-claimed `.thmInfo` declaration Lean/Mathlib elaboration produces, not a
mathematical result a PR is claiming as a result:

  * anything Lean's own kernel/elaborator considers an automatically generated
    declaration or a private one — `Lean.isAutoDeclOrPrivate_Internal`, the
    canonical Lean-core provenance check (not a name-suffix heuristic; it
    consults the `Environment`'s actual reserved-name-predicate registry, so
    it correctly covers `.injEq`, `.mk.inj`, `.mk.sizeOf_spec`, `.noConfusion`,
    `.noConfusionType`, `recOn`/`casesOn`/`brecOn`-style auxiliary recursors,
    the auto-generated `simp`-congruence suffix `.congr_simp`, `match_`/
    `proof_`/`eq_`-style equation-compiler auxiliaries, and `private`
    declarations, all without risking a name a human happens to also choose).
    This project went through two review rounds discovering that hand-rolled
    name-suffix heuristics for this category are exactly the wrong tool: a
    blanket `.ext`/`.ext_iff`/`.sizeOf_spec` suffix match hid the hand-proved,
    `@[ext]`-tagged `MobiusCPT.TestFn.ext`/`MobiusCPT.SU11.ext`, and a blanket
    `mk` component match would have hidden any hand-written theorem nested
    under a namespace component literally called `mk` — `isAutoDeclOrPrivate_Internal`
    does not match on the string `"ext"`/`"mk"` anywhere; it checks whether the
    *parent* name is a registered constructor before treating an `.inj`/
    `.injEq`/`.sizeOf_spec`/`.noConfusion` suffix as generated, so a
    coincidentally-named hand-written theorem is never caught by mistake.
  * `structure`/`class` field projections — a `Prop`-valued field of a
    `structure`/`class ... where` block elaborates as a `theorem`-kind
    projection function (e.g. `WightmanData.U_mul`, `MobiusAction.beta_mul`,
    `IsRapidlyDecaying.contDiff`); these are mechanical accessors, not
    independently claimed results, and Lean does not classify them as
    "auto-generated" in the sense above (the field itself is user-written) so
    this needs its own check                                  — `Environment.isProjectionFn`

That is the whole list. In particular this guard does NOT exclude `instance`
declarations: a codex broker review on this PR found that blanket-excluding
every `Prop`-valued `instance` was itself a false-negative risk of the same
shape as the `.ext`/`mk` ones above — `MobiusCPT.testFnBaireSpace`,
`MobiusCPT.testFnBarrelledSpace` and `MobiusCPT.signSubgroupNormal` are
hand-proved `instance`s already pinned as genuine claimed results (a project
`instance : SomePropClass ... := proof` line is always something a human
wrote here — typeclass *resolution* uses existing instances at a call site,
it never creates a new named declaration in this project's own modules — so
there is no "mechanical, auto-derived instance" category to exclude in the
first place). `Lean.Meta.isInstance` is deliberately unused now.

Iterate this list, not the caller, if a false positive or false negative shows up:
every excluded kind above must stay listed here.
-/
import MobiusCPT

open Lean

/-- `n` was declared in a module named `MobiusCPT`, or a submodule of it
(`MobiusCPT.Wightman.Basic`, the root aggregator `MobiusCPT`, etc). -/
private def isMobiusModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match env.header.moduleNames[idx.toNat]? with
    | some modName => (`MobiusCPT).isPrefixOf modName
    | none => false
  | none => false

/-- `n`/`info` is a public theorem this repository must pin in
`scripts/print_axioms.lean`. -/
private def isPublicMobiusTheorem (env : Environment) (n : Name) (info : ConstantInfo) :
    CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if (← isAutoDeclOrPrivate_Internal n) then return false
    if env.isProjectionFn n then return false
    if !isMobiusModule env n then return false
    return true
  | _ => return false

/-- The declaration names pinned by `#print axioms <name>` lines in `path`, under the exact
same extraction rule `scripts/check-axioms.sh` uses (`awk '/^#print axioms /{print $3}'`):
the line must start with the literal, unindented text `#print axioms ` — not merely contain it
after trimming. A line inside a block comment, or indented, is never a real `#print axioms`
command as far as Lean or that audit are concerned, so this walk must not treat it as pinned
either; doing so would let the coverage guard pass while the live audit never actually checks
the name. -/
private def readPinnedNames (path : System.FilePath) : IO (Std.HashSet String) := do
  let contents ← IO.FS.readFile path
  let prefix' := "#print axioms "
  let names := (contents.splitOn "\n").filterMap fun line =>
    if line.startsWith prefix' then
      match (line.drop prefix'.length).toString.splitOn " " |>.filter (· ≠ "") with
      | name :: _ => some name
      | [] => none
    else
      none
  return Std.HashSet.ofList names

#eval show CoreM Unit from do
  let env ← getEnv
  let pinned ← readPinnedNames "scripts/print_axioms.lean"
  let mut total : Nat := 0
  let mut missing : Array String := #[]
  for (n, info) in env.constants.toList do
    if (← isPublicMobiusTheorem env n info) then
      total := total + 1
      let name := n.toString
      unless pinned.contains name do
        missing := missing.push name
  if missing.isEmpty then
    IO.println s!"COVERAGE OK — {total} public theorems, all pinned"
  else
    for name in missing.qsort (· < ·) do
      IO.println s!"MISSING: {name}"
    -- `throwError`, not `IO.Process.exit`: the latter terminates the process
    -- immediately and was observed (in review) to discard the `MISSING:` lines
    -- printed just above when stdout is not a terminal (as under `lake env lean`
    -- here). `throwError` reports through Lean's own elaboration-error channel,
    -- which both prints reliably and gives `lean`/`lake env lean` a nonzero exit
    -- code, the same mechanism `scripts/check-axioms.sh` already relies on when
    -- `lake env lean scripts/print_axioms.lean` fails.
    throwError s!"{missing.size} public theorem(s) declared in a MobiusCPT module are not pinned in scripts/print_axioms.lean (see MISSING: lines above)"
