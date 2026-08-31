import Batteries.Util.ProofWanted
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Basic
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.Inv
import MobiusCPT.TestFunctions.Support
import MobiusCPT.Wightman.Bundle
import MobiusCPT.Wightman.VtildeLinear
import MobiusCPT.Wightman.VtildeLaws
import MobiusCPT.Mobius.ComplexBetaLaws

/-!
# MobiusCPT.Contract

This file is the Issue #2 statement contract for [T26], Theorem 3.10, now fully discharged:
every statement it once held as a placeholder is a proved theorem elsewhere in the tree, and
`W` — the single Wightman-data hole — together with its transparent projections is all that
remains here. It stands as the statement surface: the capstone target and the semantic
decisions Issue #2 settled, read off directly in the source's vocabulary rather than navigated
through the module tree.

Its opaque placeholders are sound because they inhabit `ProofWanted T` or `DefWanted T`, never
`T`, so no statement here is usable as a proof and no axiom is introduced. A transparent
`def_wanted` is a genuine `@[reducible] def` returning `DerivedWanted T`, never `T`; its body
can be inlined through `❰…❱`, but it cannot itself inhabit `T`. Thus the only unfilled piece
remaining is the opaque `DefWanted` hole `W`, with no `axiom` or `sorry`.

[T26], Theorem 3.10 is proved as `MobiusCPT.WightmanBundle.thm_3_10_i`, `.thm_3_10_ii` and
`.thm_3_10_iii` in `MobiusCPT.Wightman.Thm310`, assembled from the lemma chain: Lemma 3.7 in
`MobiusCPT.Wightman.Lemma37Continuation` and `MobiusCPT.Wightman.Lemma37`, Lemma 3.8 in
`MobiusCPT.Wightman.Lemma38`, Lemma 3.9 in `MobiusCPT.Wightman.Lemma39` (with its interior and
boundary cases in `MobiusCPT.Wightman.Lemma39Interior`, `.Lemma39Boundary` and
`.Lemma39DiffContOnCl`), the mirror step in `MobiusCPT.Wightman.VtildeMirror`, the real-axis
reduction of `Ṽ_τ` in `MobiusCPT.Wightman.VtildeReal`, the rotation-by-`π` identities in
`MobiusCPT.Mobius.RotationPi`, and the strip maximum-principle infrastructure in
`MobiusCPT.Analysis.StripMaxPrinciple`. `WightmanBundle` fixes the abstract group to `Mob` and
the action to the concrete conformal action ([docs/adr/0001-fix-mobius-group-in-bundle.md]),
which the boost-continuity and Lemma 3.6 holomorphy inputs to this chain depend on.
-/

namespace MobiusCPT

/-- [T26], Definitions 2.4–2.5; the Wightman CFT this contract is about. Its
carriers are bundled so this is the only Wightman-data hole. -/
def_wanted W : WightmanBundle

/-- [T26], §2; the domain `𝓓`, now projected from the real interface landed by Issue #4. -/
def_wanted Dom : Type := (❰W❱).𝓓

/-- [T26], §2; the `𝓕`-strong topology on `𝓓`, projected from the real interface
landed by Issue #4 and deliberately not installed as a global instance. -/
def_wanted domTopologicalSpace : TopologicalSpace ❰Dom❱ := (❰W❱).data.strongTop

/-- [T26], §2; the field index type `𝓕`, now projected from the real interface landed by
Issue #4. -/
def_wanted Field : Type := (❰W❱).𝓕

/-- [T26], §2 and (W1); the conformal dimension `dim : 𝓕 → ℤ_{≥0}` represented in
Lean by naturals, now projected from the real interface landed by Issue #4. -/
def_wanted dim : ❰Field❱ → ℕ := fun φ => (❰W❱).data.dim φ

/-- [T26], §2; the smeared field operator `φ(f)`, now projected from the real interface
landed by Issue #4. -/
def_wanted smear : ❰Field❱ → TestFn → ❰Dom❱ → ❰Dom❱ :=
  fun φ f Φ => (❰W❱).data.smear φ f Φ

/-- [T26], §2; the vacuum vector `Ω`, now projected from the real interface landed by
Issue #4. -/
def_wanted vac : ❰Dom❱ := (❰W❱).data.vac

/-- [T26], §2; the compatible-function space `D*_𝓕`, now projected from the real
interface landed by Issue #4. -/
def_wanted Compat : Type := (❰W❱).data.toWightmanStruct.Compat

/-- [T26], §2; evaluation of a compatible functional on `𝓓`, now projected from the real
interface landed by Issue #4. -/
def_wanted compatApply : ❰Compat❱ → ❰Dom❱ → ℂ :=
  fun lam Φ => (❰W❱).data.toWightmanStruct.compatApply lam Φ

/-- [T26], §2 and Definition 3.1; `V_t = U(v_t)`, now projected from the real interface
landed by Issue #4. -/
def_wanted boost : ℝ → ❰Dom❱ → ❰Dom❱ := fun t Φ => (❰W❱).data.boost t Φ

/-- [T26], Definitions 2.4–2.5; regular action of `𝓕`, now projected from the real
interface landed by Issue #4. -/
def_wanted ActsRegularly : Prop := (❰W❱).data.toWightmanStruct.ActsRegularly

/-- [T26], Definition 2.5 (W1); Möbius covariance, now projected from the real interface
landed by Issue #4. -/
def_wanted W1 : Prop := (❰W❱).data.W1

/-- [T26], Definition 2.5 (W2); locality, now projected from the real interface landed by
Issue #25. -/
def_wanted W2 : Prop := (❰W❱).data.toWightmanStruct.W2

/-- [T26], Definition 2.5 (W3); the spectrum condition, now projected from the real interface
landed by Issue #4. -/
def_wanted W3 : Prop := (❰W❱).data.W3

/-- [T26], Definition 2.5 (W4); the vacuum axiom, now projected from the real interface
landed by Issue #4. -/
def_wanted W4 : Prop := (❰W❱).data.W4

/-- [T26], Definition 2.5; the Möbius-covariant Wightman CFT conjunction, now projected from
the real interface landed by Issue #25. -/
def_wanted IsWightmanCFT : Prop := (❰W❱).data.IsWightmanCFT

/-- [T26], Definition 3.1; the domain `D(Ṽ_τ)` of the partially defined boost, now projected
from the real definition landed by Issue #6. -/
def_wanted VtildeDom : ℂ → ❰Dom❱ → Prop :=
  fun τ Φ => (❰W❱).data.VtildeDom τ Φ

/-- [T26], Definition 3.1; a total Lean representative of `Ṽ_τ`, agreeing with it on
`VtildeDom τ`, now projected from the real definition landed by Issue #6.  Its value is read off
the uniqueness statement, so it is never an unconstrained choice. -/
def_wanted VtildeMap : ℂ → ❰Dom❱ → ❰Dom❱ :=
  fun τ Φ => (❰W❱).data.vtildeMap τ Φ

/-- [T26], §2; the left-to-right product `φ₁(f₁)⋯φ_k(f_k)Ω`, now projected from
the real interface landed by Issue #4. -/
def_wanted smearedProduct : List (❰Field❱ × TestFn) → ❰Dom❱ :=
  fun l => (❰W❱).data.toWightmanStruct.smearedProduct l

/-- [T26], §2; membership in the localized subspace `P(I_+)Ω`, now projected from the
real interface landed by Issue #4. -/
def_wanted MemPUpperOmega : ❰Dom❱ → Prop :=
  fun Φ => (❰W❱).data.toWightmanStruct.MemPUpperOmega Φ

/-- [T26], §2; membership in the localized subspace `P(I_-)Ω`, now projected from the
real interface landed by Issue #4. -/
def_wanted MemPLowerOmega : ❰Dom❱ → Prop :=
  fun Φ => (❰W❱).data.toWightmanStruct.MemPLowerOmega Φ

end MobiusCPT
