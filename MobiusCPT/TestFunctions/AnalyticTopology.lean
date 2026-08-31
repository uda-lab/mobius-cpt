import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.CNorm

/-!
# MobiusCPT.TestFunctions.AnalyticTopology

[T26], Definition 3.2: "we regard `𝓧` as a subset of `C^∞(S¹)` with the relative topology"
(after identifying `F` with `F|_{S¹}`). This file equips `AnalyticTestFn` with the topology
induced through the restriction map `xRestrictS1`, i.e. the relative `C^∞(S¹)` topology in the
literal, pulled-back sense.

The source's `𝓧` is a set of functions on `𝕆 = {|z| ≥ 1}`; the Lean structure `AnalyticTestFn`
totalises `toFun` to all of `ℂ`, with unconstrained values strictly inside the open unit disc
(an encoding choice made at #7/#36, not revisited here — none of `AnalyticTestFn`'s five proof
fields reference that region). Consequently `xRestrictS1` is **not** injective on the raw type,
and this file does not claim `Topology.IsEmbedding xRestrictS1` or that the induced topology is
`T0` on `AnalyticTestFn`. What *is* true, and is the faithful encoding of the source's "identify
`F` with `F|_{S¹}`", is that the restriction map is injective precisely on `𝕆`-data:
`xRestrictS1_eq_iff` below. A quotient or partial-function redesign of `AnalyticTestFn` that
would recover literal injectivity is out of scope for this file (Issue #53 ruling, 2026-09-01):
it would change every landed statement about `AnalyticTestFn` for a property nothing downstream
uses; a future consumer that needs genuine injectivity should build a quotient type on top of
`AnalyticTestFn` using `xRestrictS1_eq_iff`, leaving this structure unchanged.
-/

namespace MobiusCPT

open scoped Topology

noncomputable section

/-- [T26], Definition 3.2; the relative `C^∞(S¹)` topology on `𝓧`, pulled back along the
restriction `F ↦ F|_{S¹}`. -/
instance analyticTestFnTopologicalSpace : TopologicalSpace AnalyticTestFn :=
  TopologicalSpace.induced xRestrictS1 inferInstance

/-- The restriction `F ↦ F|_{S¹}` is inducing for the relative topology, by definition of the
latter. -/
theorem isInducing_xRestrictS1 : Topology.IsInducing (xRestrictS1) :=
  ⟨rfl⟩

/-- The restriction `F ↦ F|_{S¹}` is continuous for the relative topology. -/
theorem continuous_xRestrictS1 : Continuous (xRestrictS1) :=
  isInducing_xRestrictS1.continuous

/-- [T26], Definition 3.2; the faithful encoding of "identify `F` with `F|_{S¹}`": the
restriction map identifies exactly the elements of `𝓧` that agree as functions on `𝕆 = Oexterior`,
the domain the source's `𝓧` actually lives on. This is the injectivity Definition 3.2's
identification asserts; it is not `Function.Injective xRestrictS1` on the raw, totalised
structure (see the module docstring). -/
theorem xRestrictS1_eq_iff (F G : AnalyticTestFn) :
    xRestrictS1 F = xRestrictS1 G ↔ Set.EqOn F.toFun G.toFun Oexterior := by
  constructor
  · exact eqOn_Oexterior_of_xRestrictS1_eq
  · intro h
    apply TestFn.ext
    intro z
    rw [xRestrictS1_apply, xRestrictS1_apply]
    exact h (circle_subset_Oexterior z)

end

end MobiusCPT
