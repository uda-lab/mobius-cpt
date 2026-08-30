# 0001 — Fix the Möbius group and the conformal action in `WightmanBundle`

## Context

The contract's single data hole, `W : WightmanBundle`, bundled an arbitrary group `G` with a
`MobiusAction G TestFn` instance. The source ([T26], Definitions 2.4–2.5) defines a
Möbius-covariant Wightman CFT as a representation of Möb = PSU(1,1) with the conformal action
`β_d`; no abstract group appears. Two contract statements already presuppose the concrete
action: `lemma_3_7` equates `Ṽ_τ` on smeared products with smearing by the concrete `betaBoost`,
and `vtilde_real` needs continuity of `t ↦ β_d(v_t) f` ([CRTT25], Lemma 2.10(i)), a property of
the concrete action that no interface field supplies. Over an abstract `G` both are unprovable.

## Decision

`WightmanBundle` fixes the group to `Mob` and the action to `mobiusActionMobTestFn`; the `G`
and `mobiusAction` fields are removed and `data : WightmanData Mob TestFn 𝓓 𝓕`. The generic
development (`WightmanData G TF 𝓓 𝓕`, `MobiusAction`) stays parametrised over `G` for results
that do not depend on the concrete action. Every contract statement keeps its text: they see
`❰W❱` only through projections.

## Consequences

- `vtilde_real` is provable from the concrete continuity theorem, and `lemma_3_7` is provable
  as stated; the main theorem is stated for exactly the source's class of theories.
- No continuity axiom is added to `MobiusAction`: [CRTT25] Lemma 2.10(i) is proved, not
  assumed, as the source does.
- Rejected: continuity fields on `MobiusAction` (axiomatises a derived fact and leaves the
  `lemma_3_7` presupposition unrepaired); adding a `BoostOrbitContinuous` hypothesis to the
  contract statements (statement weakening); leaving `vtilde_real` as a hole.
