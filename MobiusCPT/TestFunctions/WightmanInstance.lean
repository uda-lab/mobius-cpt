import MobiusCPT.TestFunctions.Inv
import MobiusCPT.Wightman.TestFn

/-!
# MobiusCPT.TestFunctions.WightmanInstance

The concrete test-function space of Issue #3 satisfies the abstract `TestFunctions`
interface that Issue #4 states the Wightman axioms against.

This is the join between the two foundation Issues: `MobiusCPT.TestFn` is
`C^∞(S¹)` in the `Circle`/`ContMDiffMap` picture, and `MobiusCPT.TestFunctions`
is the interface [T26] §2.2 and §3 actually use.  Providing the instance shows
the interface is inhabited by the intended model rather than vacuously assumed.
-/

namespace MobiusCPT

/-- [T26], §2.2 and §3; `C^∞(S¹)` is a model of the abstract test-function interface. -/
noncomputable instance : TestFunctions TestFn where
  cnorm := MobiusCPT.cnorm
  starInv := MobiusCPT.inv
  SuppUpper := MobiusCPT.SuppUpper
  SuppLower := MobiusCPT.SuppLower
  DisjointSupp := MobiusCPT.DisjointSupport
  tendsto_iff_cnorm := MobiusCPT.tendsto_iff_cnorm
  starInv_add := MobiusCPT.inv_add
  starInv_involutive := MobiusCPT.inv_involutive
  starInv_supp := MobiusCPT.inv_supp
  cnorm_starInv := MobiusCPT.cnorm_inv

end MobiusCPT
