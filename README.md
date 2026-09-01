# mobius-cpt

Lean 4 + mathlib formalisation of the **PCT theorem for Möbius-covariant Wightman conformal field
theories on the circle**, in the non-unitary setting of Tener (Comm. Math. Phys. 407 (2026) 128) and
Carpi–Raymond–Tanimoto–Tener (Sel. Math. 31 (2025) 66). Bibliography: `docs/math/references.md`.

## The theorem

For a Möbius-covariant Wightman CFT `(D, 𝓕, U, Ω)`, Möbius-covariant fields `φ_j ∈ 𝓕` of conformal
dimension `d_j`, and test functions `f_j ∈ C^∞(S¹)` supported in the upper half circle `I_+`,

    Ṽ_{iπ} φ_1(f_1) ⋯ φ_k(f_k) Ω = (−1)^{d_1+⋯+d_k} φ_k(f_k ∘ z⁻¹) ⋯ φ_1(f_1 ∘ z⁻¹) Ω ,

where `Ṽ_τ` is the analytic continuation of the boost flow `t ↦ U(v_t)` to the strip `0 ≤ Im τ ≤ π`;
the mirror statement holds for `I_−` and `−iπ`. Definitions, conventions and the exact statement are
in `docs/math/pct-theorem.md`, the working mathematical source of truth; the primary papers win on
any conflict.

The programme's scope, milestones, non-goals and authority model are fixed by the owner's charter,
the pinned Issue of this repository.

## Layout

| Path | Role |
|---|---|
| `MobiusCPT/` | Lean library (module tree) |
| `MobiusCPT.lean` | library root; imports every module |
| `scripts/` | bootstrap, canonical gate, integrity guards, git hooks |
| `scripts/print_axioms.lean` | append-only list of pinned public theorems for the live axiom audit |
| `docs/math/` | mathematical definitions, statements, conventions, references |
| `docs/adr/` | architecture decision records (only for durable decisions) |

## Build

```sh
scripts/bootstrap.sh   # once per clone: mathlib oleans via `lake exe cache get`, git hooks path
scripts/check.sh       # guards → lake build → live #print axioms audit
```

The toolchain is `lean-toolchain`; mathlib is pinned by tag in `lakefile.toml` and by commit in
`lake-manifest.json`. CI runs the textual guards on every pull request and the same `scripts/check.sh`
gate (build and live audit) whenever Lean sources, build configuration, scripts or workflows change.

## Trust footprint

Accepted theorems are `sorry`-free and their axiom closure is contained in
`{propext, Classical.choice, Quot.sound}`; `scripts/check-axioms.sh` verifies this live for every
declaration listed in `scripts/print_axioms.lean`, and no project axioms are admitted.

## Workflow

Agent guidance is in `AGENTS.md`. GitHub Issues and pull requests are the only work queue and
evidence record: Issue → branch → PR → independent review → CI → squash merge.

## Citation

The v0.1.0 release is archived on Zenodo: https://zenodo.org/records/22222446 (DOI
`10.5281/zenodo.22222446`). See `CITATION.cff` for the full citation metadata.

## License

Apache-2.0, see `LICENSE`.
