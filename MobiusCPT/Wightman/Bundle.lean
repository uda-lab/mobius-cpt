import MobiusCPT.TestFunctions.WightmanInstance
import MobiusCPT.Wightman.Axioms

/-!
# Bundled concrete-test-function Wightman data

This module packages the variable carriers of Wightman data over the concrete
test-function space `C^∞(S¹)`.  It exists as plumbing for the single bundle hole in
`MobiusCPT.Contract`: a `def_wanted` hole cannot have a type that mentions another
hole, so the carriers must be closed over together.  This bundling is forced by
the contract mechanism and is not a mathematical choice.
-/

namespace MobiusCPT

/-- [T26], Definitions 2.4–2.5; Wightman data over the concrete test-function space,
with its otherwise variable group, domain, and field-index carriers bundled. -/
structure WightmanBundle where
  G : Type
  [group : Group G]
  𝓓 : Type
  [domAddCommGroup : AddCommGroup 𝓓]
  [domModule : Module ℂ 𝓓]
  𝓕 : Type
  [mobiusAction : MobiusAction G TestFn]
  data : WightmanData G TestFn 𝓓 𝓕

attribute [instance] WightmanBundle.group WightmanBundle.domAddCommGroup
  WightmanBundle.domModule WightmanBundle.mobiusAction

end MobiusCPT
