import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.CNorm

/-!
# MobiusCPT.TestFunctions.AnalyticTopology

[T26], Definition 3.2: "we regard `𝓧` as a subset of `C^∞(S¹)` with the relative topology"
(after identifying `F` with `F|_{S¹}`). This file equips `AnalyticTestFn` with the topology
induced through the restriction map `xRestrictS1`, i.e. the relative `C^∞(S¹)` topology in the
literal, pulled-back sense.

The source's "subset" / "identifying `F` with `F|_{S¹}`" language describes the quotient of
`AnalyticTestFn` by agreement on `Oexterior`; the raw Lean structure carries an unconstrained
`toFun` value strictly inside the open unit disc (none of `AnalyticTestFn`'s proof fields
reference that region), so `xRestrictS1` is not literally injective on the raw type and no
`IsEmbedding xRestrictS1` statement is claimed here. `eqOn_Oexterior_of_xRestrictS1_eq`
(`TestFunctions/Analytic.lean`) already gives the injectivity that *is* true: agreement of the
`S¹`-restrictions forces agreement of the `Oexterior`-restrictions, which is the sense in which
the source's identification holds.
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

end

end MobiusCPT
