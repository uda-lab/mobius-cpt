import Mathlib.Data.Real.Basic

/-!
# MobiusCPT.Basic

Scaffold module. `placeholder_add_zero` exists only so that the live axiom audit
(`scripts/print_axioms.lean` → `scripts/check-axioms.sh`) is exercised end to end
from the first commit. Replace it through a charter-authorised Issue.
-/

namespace MobiusCPT

/-- Placeholder pinned in `scripts/print_axioms.lean`. Stating it over `ℝ` makes its
axiom closure the kernel trio (`propext`, `Classical.choice`, `Quot.sound`), so the
audit's allowlist path is tested rather than only the "no axioms" path. -/
theorem placeholder_add_zero (x : ℝ) : x + 0 = x := add_zero x

end MobiusCPT
