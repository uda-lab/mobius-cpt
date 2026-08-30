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

This file is the Issue #2 statement contract for [T26], Theorem 3.10.  Its opaque
placeholders are sound because they inhabit `ProofWanted T` or `DefWanted T`, never
`T`, so no statement here is usable as a proof and no axiom is introduced.  A
transparent `def_wanted` is a genuine `@[reducible] def` returning `DerivedWanted T`,
never `T`; its body can be inlined through `❰…❱`, but it cannot itself inhabit `T`.
Thus the only unfilled pieces remain opaque `DefWanted` or `ProofWanted` placeholders,
with no `axiom` or `sorry`.
This file pins the capstone target of [T26] Thm. 3.10 together with the semantic
decisions Issue #2 settled; it is deliberately not the full interface — the general
`β_d` action on `C^∞(S¹)`, the Def. 3.5 cocycle, the `C^N` covariance estimate,
and Lemma 3.9 are owned by the corresponding child Issues.

As each child Issue lands, its placeholders are deleted here and the remaining
statements are re-expressed against the real definitions.  Issue #3 has landed:
`TestFn`, `cnorm`, `inv`, `SuppUpper` and `SuppLower` below are the genuine
definitions from `MobiusCPT.TestFunctions.*`, not holes, and the statements that
Issue #3 owned (`tendsto_iff_cnorm`, `inv_add`, `inv_involutive`, `inv_supp`,
`cnorm_inv`) are proved theorems in those modules.

Issue #7 has landed as well: `AnalyticTestFn` ([T26], Definition 3.2), `xRestrictS1`,
`xRestrictUpper` and `xRestrictLower` below are the genuine definitions from
`MobiusCPT.TestFunctions.Analytic`, not holes, and the statements Issue #7 owned
(`xRestrictUpper_supp`, `xRestrictLower_supp`, `xRestrict_split`) are proved theorems there.
Lemma 3.4 is proved as
`lemma_3_4_density_upper` in `MobiusCPT.TestFunctions.AnalyticDensity`, so its statement is gone
from here too.

Issue #4 has also landed.  `W` is now the single bundle hole for the Wightman data,
and `Dom`, `Field`, `dim`, `smear`, `vac`, `Compat`, `compatApply`, `boost`,
`ActsRegularly`, `W1`, `W3`, `W4`, `smearedProduct`, `MemPUpperOmega`, and
`MemPLowerOmega` are transparent projections of it.  `domTopologicalSpace` is one
too, projecting the `𝓕`-strong topology; it is a `def_wanted` rather than an
`instance_wanted` because `instance_wanted` is always an opaque hole, and it is
deliberately not a global instance.  The instance holes `domAddCommGroup` and
`domModule` are gone: the bundle carries them. `W2` and `IsWightmanCFT` are
transparent projections of `W`, so besides the bundle hole `W` itself the only
remaining #4-adjacent hole was `w3_vacuum_annihilation`, discharged below by Issue #9. The
capstone obligations taking `❰IsWightmanCFT❱` as a hypothesis are genuinely
conditional on [T26], Definition 2.5.

Issue #8 has landed.  `betaBoost` below is the genuine definition
`MobiusCPT.betaBoost` from `MobiusCPT.Mobius.ComplexBetaDef` ([T26], Definition 3.5,
eq. (3.4), with the `d = 0` removable singularity built in), not a hole, so it is referred to
directly rather than through `❰…❱`; the statement of `lemma_3_7` is unchanged, since a
transparent `def_wanted` inlines to exactly this definition.  The statement Issue #5 owned,
`beta_boost_at_ipi`, is a proved theorem `MobiusCPT.betaBoost_I_mul_pi` in
`MobiusCPT.Mobius.ComplexBetaLaws` with identical statement text, so it is gone from here.

Issue #6 has landed.  `strip` below is the genuine definition from
`MobiusCPT.Analysis.Strip`, not a hole, and `VtildeDom` and `VtildeMap` are transparent
projections of the real `WightmanData.VtildeDom` and `WightmanData.vtildeMap` from
`MobiusCPT.Wightman.Vtilde`.  The statements Issue #6 owned (`strip_eq`, `vtilde_spec`,
`vtilde_translation`, `vtilde_vacuum`) are proved theorems in `MobiusCPT.Analysis.Strip`,
`MobiusCPT.Wightman.Vtilde` and `MobiusCPT.Wightman.VtildeLaws`, so their statements are gone
from here.

Issue #38 has landed.  For real `τ` the strip degenerates to the real axis, so [T26] Def.
3.1's `ContinuousOn` clause is exactly continuity of `t ↦ λ(V_t Φ)`, which [CRTT25], Lemma
2.10(i) gives as a *consequence* of the source's axioms rather than a hypothesis of this
repository's `IsWightmanCFT` — (W1) gives continuity in the vector, not in the group parameter.
`MobiusCPT.Wightman.VtildeReal` names that input as `WightmanData.BoostOrbitContinuous` and
proves the real-parameter statement from it, reducing it to continuity of `t ↦ β_d(v_t) f` on
test functions; `MobiusCPT.Mobius.BoostContinuity` proves that continuity for the concrete
conformal action.  Discharging `vtilde_real` from these needed `WightmanBundle` to fix the
group and the action ([docs/adr/0001-fix-mobius-group-in-bundle.md]) rather than bundling an
arbitrary group, since an abstract group's `MobiusAction` instance carries no continuity for
`boostOrbitContinuous_of_beta_continuous` to consume.  The statement Issue #38 owned,
`vtilde_real`, is a proved theorem `MobiusCPT.WightmanBundle.vtilde_real` in
`MobiusCPT.Wightman.VtildeReal` with identical statement text, so it is gone from here.

Issue #9 is landing in blocks. Its first block discharges `lemma_3_7`, [T26] Lemma 3.7(i): a
proved theorem `MobiusCPT.WightmanBundle.lemma_3_7` in `MobiusCPT.Wightman.Lemma37Continuation`
with identical statement text, so it is gone from here. The proof exhibits the `G_λ` family of
[T26], Definition 3.1 built from `betaBoost` as an `IsBoostContinuation` witness, assembled from
Issue #8/#38's already-landed Lemma 3.6 continuity/holomorphy
(`continuousOn_compatApply_smearedProduct_betaBoost`,
`differentiableOn_compatApply_smearedProduct_betaBoost`) and covariance
(`WightmanData.boost_smearedProduct`) infrastructure together with the real-parameter and
boost-translation identities for the concrete complex boost
(`betaBoost_ofReal_mob`, `beta_boostMat_betaBoost`).

Issue #9's second block discharges `w3_vacuum_annihilation`, the (W3) vacuum-annihilation
bridge: a proved theorem `MobiusCPT.WightmanBundle.w3_vacuum_annihilation` in
`MobiusCPT.TestFunctions.FourierCauchy` with identical statement text, so it is gone from
here. The proof identifies the boundary values of `inv (xRestrictS1 F)` with `F.invExt`
(#7's disc-holomorphic inversion), shows its Fourier coefficients vanish for every `n ≤ 0` by
Cauchy's theorem (`n < 0`) and the Cauchy integral formula at the origin (`n = 0`, using
`F.invExt 0 = 0`), and feeds that into the already-landed (#26)
`smear_vac_eq_zero_of_fourierCoef_eq_zero'`.

Issue #9's third block discharges `lemma_3_7_at_ipi`, [T26] Lemma 3.7(ii): a proved theorem
`MobiusCPT.WightmanBundle.lemma_3_7_at_ipi` in `MobiusCPT.Wightman.Lemma37` with identical
statement text, so it is gone from here — completing Issue #9. The proof combines Lemma 3.7(i)
at `τ = iπ` with the conformal-factor sign `betaBoost_I_mul_pi` (`(-1)^{d+1}` per field) and a
combinatorial sign-reversal identity (`MobiusCPT.Wightman.SignReversal`,
`smearedProduct_invLower_eq_smearedProduct_invUpper_reverse`): moving each field's
`inv (xRestrictUpper F)` piece from adjacent-to-vacuum to the front of the product picks up one
`(-1)` from the vacuum-annihilation identity per field (`w3_vacuum_annihilation` applied to
`inv (xRestrictUpper F) + inv (xRestrictLower F) = inv (xRestrictS1 F)`), with the reordering
itself using (W2) through the endpoint-cutoff limit (`MobiusCPT.Wightman.LocalityLimit`,
`MobiusCPT.TestFunctions.EndpointCutoff`) and carrying no sign of its own — the total
`(-1)^{Σ(d_j+1)} · (-1)^k` collapsing to the contract's `(-1)^{Σ d_j}` since `Σ(d_j+1) = Σd_j +
k` and `(-1)^{2k} = 1`.

Issue #10 has landed: `lemma_3_8` is now the proved theorem
`MobiusCPT.WightmanBundle.lemma_3_8` in `MobiusCPT.Wightman.Lemma38`, with byte-identical
statement text, so it is gone from here.

Issue #40 has landed: `lemma_3_9` below is [T26] Lemma 3.9, a statement-only placeholder
discharged later by Issue #11 with byte-identical statement text.
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

/-- [T26], Lemma 3.9; for fixed fields and compatible functional, the strip-uniform difference
estimate for analytic-core vectors has constants independent of the analytic data `F_j, G_j` and
of `τ`. The vectors lie in `D(Ṽ_τ)` for every `τ` in the closed strip by Lemma 3.7(i)
(`WightmanBundle.lemma_3_7`), so `VtildeMap` is `Ṽ_τ` on them and no domain clause is restated.
The product and the `foldr max 0` follow `lemma_3_8` exactly: the entries are nonnegative by
construction, and for `k = 0` the bound reads `0 ≤ 0`, where the source's maximum over an empty
index set is undefined. A positive integer `N` and a positive real `M` are required, owned by
Issue #11. -/
theorem_wanted lemma_3_9 :
    ❰IsWightmanCFT❱ →
      ∀ (φs : List ❰Field❱) (lam : ❰Compat❱),
        ∃ (N : ℕ) (M : ℝ),
          0 < N ∧ 0 < M ∧
            ∀ (Fs Gs : List AnalyticTestFn),
              Fs.length = φs.length → Gs.length = φs.length →
                ∀ τ ∈ strip (Complex.I * Real.pi),
                  ‖❰compatApply❱ lam
                      (❰VtildeMap❱ τ (❰smearedProduct❱ (φs.zip (Fs.map xRestrictUpper))) -
                        ❰VtildeMap❱ τ (❰smearedProduct❱ (φs.zip (Gs.map xRestrictUpper))))‖ ≤
                    M * Real.exp (τ.re ^ 2) *
                        (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                          (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
                      ((List.foldr max 0
                        (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                          (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ)

/-- [T26], Theorem 3.10(i); upper and lower localized vectors lie in the corresponding domains
of the partially defined imaginary boosts, owned by Issue #12. -/
theorem_wanted thm_3_10_i :
    ❰IsWightmanCFT❱ →
      (∀ Φ : ❰Dom❱,
        ❰MemPUpperOmega❱ Φ → ❰VtildeDom❱ (Complex.I * Real.pi) Φ) ∧
        (∀ Φ : ❰Dom❱,
          ❰MemPLowerOmega❱ Φ → ❰VtildeDom❱ (-(Complex.I * Real.pi)) Φ)

/-- [T26], Theorem 3.10(i)+(ii); for upper-supported products, the imaginary boost
is defined and reverses the product with the conformal-dimension sign, owned by Issue #12. -/
theorem_wanted thm_3_10_ii :
    ❰IsWightmanCFT❱ →
      ∀ (l : List (❰Field❱ × TestFn)),
        (∀ p ∈ l, SuppUpper p.2) →
          ❰VtildeDom❱ (Complex.I * Real.pi) (❰smearedProduct❱ l) ∧
            ❰VtildeMap❱ (Complex.I * Real.pi) (❰smearedProduct❱ l) =
              (-1 : ℂ) ^ ((l.map (fun p => ❰dim❱ p.1)).sum) •
                ❰smearedProduct❱
                  (l.reverse.map (fun p => (p.1, inv p.2)))

/-- [T26], Theorem 3.10(i)+(iii); for lower-supported products, the negative
imaginary boost is defined and gives the mirrored reversed-product identity, owned by Issue #12. -/
theorem_wanted thm_3_10_iii :
    ❰IsWightmanCFT❱ →
      ∀ (l : List (❰Field❱ × TestFn)),
        (∀ p ∈ l, SuppLower p.2) →
          ❰VtildeDom❱ (-(Complex.I * Real.pi)) (❰smearedProduct❱ l) ∧
            ❰VtildeMap❱ (-(Complex.I * Real.pi)) (❰smearedProduct❱ l) =
              (-1 : ℂ) ^ ((l.map (fun p => ❰dim❱ p.1)).sum) •
                ❰smearedProduct❱
                  (l.reverse.map (fun p => (p.1, inv p.2)))

end MobiusCPT
