import MobiusCPT.TestFunctions.WightmanInstance
import MobiusCPT.Wightman.Axioms
import MobiusCPT.Mobius.Beta

/-!
# Bundled concrete-test-function Wightman data

This module packages the variable carriers of Wightman data over the concrete
test-function space `C^∞(S¹)`.  It exists as plumbing for the single bundle hole in
`MobiusCPT.Contract`: a `def_wanted` hole cannot have a type that mentions another
hole, so the carriers must be closed over together.  This bundling is forced by
the contract mechanism and is not a mathematical choice.

[docs/adr/0001-fix-mobius-group-in-bundle.md]; [T26], Definitions 2.4–2.5: a Möbius-covariant
Wightman CFT is a representation of `Möb = PSU(1,1)` with the conformal action `β_d`, not a
representation of an abstract group. `WightmanBundle` therefore fixes the group to `Mob` and the
action to `mobiusActionMobTestFn`, rather than bundling an arbitrary `G` with a
`MobiusAction G TestFn` instance: an abstract `G` gives `MobiusCPT.Contract`'s `vtilde_real` and
`lemma_3_7` no hypothesis to prove from (`MobiusAction` carries no continuity, and (W1) is
continuity in the vector for a fixed group element, never in the group parameter), and
`lemma_3_7` already presupposes the concrete action by equating `Ṽ_τ` with smearing by the
concrete `betaBoost`. The generic development (`WightmanData G TF 𝓓 𝓕`, `MobiusAction`) stays
parametrised over `G` for results that do not depend on the concrete action; only this bundle,
used solely as `MobiusCPT.Contract`'s single data hole, is fixed.
-/

namespace MobiusCPT

/-- [T26], Definitions 2.4–2.5; Wightman data over the concrete test-function space, for the
concrete Möbius group `Mob` acting by the concrete conformal action `mobiusActionMobTestFn`,
with the domain and field-index carriers bundled. -/
structure WightmanBundle where
  𝓓 : Type
  [domAddCommGroup : AddCommGroup 𝓓]
  [domModule : Module ℂ 𝓓]
  𝓕 : Type
  data : WightmanData Mob TestFn 𝓓 𝓕

attribute [instance] WightmanBundle.domAddCommGroup WightmanBundle.domModule

end MobiusCPT
