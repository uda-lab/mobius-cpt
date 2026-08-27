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
import MobiusCPT.TestFunctions.Inv
import MobiusCPT.TestFunctions.Support
import MobiusCPT.Wightman.Bundle

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
Lemma 3.9, and the full locality axiom (W2) are owned by the corresponding child Issues.

As each child Issue lands, its placeholders are deleted here and the remaining
statements are re-expressed against the real definitions.  Issue #3 has landed:
`TestFn`, `cnorm`, `inv`, `SuppUpper` and `SuppLower` below are the genuine
definitions from `MobiusCPT.TestFunctions.*`, not holes, and the statements that
Issue #3 owned (`tendsto_iff_cnorm`, `inv_add`, `inv_involutive`, `inv_supp`,
`cnorm_inv`) are proved theorems in those modules.

Issue #4 has also landed.  `W` is now the single bundle hole for the Wightman data,
and `Dom`, `Field`, `dim`, `smear`, `vac`, `Compat`, `compatApply`, `boost`,
`ActsRegularly`, `W1`, `W3`, `W4`, `smearedProduct`, `MemPUpperOmega`, and
`MemPLowerOmega` are transparent projections of it.  The #4-adjacent holes that
remain are `W2` and `IsWightmanCFT`, owned by Issue #25, and
`w3_vacuum_annihilation`, owned by Issue #26.
-/

namespace MobiusCPT

/-- [T26], Definition 3.2; the analytic test-function class `𝓧`, owned by Issue #7. -/
def_wanted AnalyticTestFn : Type

/-- [T26], Definition 3.2; restriction `F ↦ F|_{S¹}`, owned by Issue #7. -/
def_wanted xRestrictS1 : ❰AnalyticTestFn❱ → TestFn

/-- [T26], Definition 3.2; restriction to `I_+` with zero extension, owned by Issue #7. -/
def_wanted xRestrictUpper : ❰AnalyticTestFn❱ → TestFn

/-- [T26], Definition 3.2; restriction to `I_-` with zero extension, owned by Issue #7. -/
def_wanted xRestrictLower : ❰AnalyticTestFn❱ → TestFn

/-- [T26], Definition 3.5, equation (3.4); the closed-strip removable-singularity
extension `β_d(v_τ)F|_{I_+}`, owned by Issues #5 and #8. -/
def_wanted betaBoost : ℕ → ℂ → ❰AnalyticTestFn❱ → TestFn

/-- [T26], Definition 3.2; restriction to `I_+` has upper support, owned by Issue #7. -/
theorem_wanted xRestrictUpper_supp :
    ∀ F : ❰AnalyticTestFn❱, SuppUpper (❰xRestrictUpper❱ F)

/-- [T26], Definition 3.2; restriction to `I_-` has lower support, owned by Issue #7. -/
theorem_wanted xRestrictLower_supp :
    ∀ F : ❰AnalyticTestFn❱, SuppLower (❰xRestrictLower❱ F)

/-- [T26], Definition 3.2; the circle restriction splits into the two zero-extended semicircle
restrictions, owned by Issue #7. -/
theorem_wanted xRestrict_split :
    ∀ F : ❰AnalyticTestFn❱,
      ❰xRestrictS1❱ F = ❰xRestrictUpper❱ F + ❰xRestrictLower❱ F

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

/-- [T26], Definition 2.5 (W2); locality, still owed by Issue #25. -/
def_wanted W2 : Prop

/-- [T26], Definition 2.5 (W3); the spectrum condition, now projected from the real interface
landed by Issue #4. -/
def_wanted W3 : Prop := (❰W❱).data.W3

/-- [T26], Definition 2.5 (W4); the vacuum axiom, now projected from the real interface
landed by Issue #4. -/
def_wanted W4 : Prop := (❰W❱).data.W4

/-- [T26], Definition 2.5; the Möbius-covariant Wightman CFT conjunction, still owed by
Issue #25. -/
def_wanted IsWightmanCFT : Prop

/-- [T26], Definition 2.5; unpacking the named Wightman CFT conjunction, still owed by
Issue #25. -/
theorem_wanted isWightmanCFT_iff :
    ❰IsWightmanCFT❱ ↔
      (❰ActsRegularly❱ ∧ ❰W1❱ ∧ ❰W2❱ ∧ ❰W3❱ ∧ ❰W4❱)

/-- [T26], Definition 3.1; the domain `D(Ṽ_τ)` of the partially defined boost,
owned by Issue #6. -/
def_wanted VtildeDom : ℂ → ❰Dom❱ → Prop

/-- [T26], Definition 3.1; a total Lean representative of `Ṽ_τ`, agreeing with it on
`VtildeDom τ`, owned by Issue #6. -/
def_wanted VtildeMap : ℂ → ❰Dom❱ → ❰Dom❱

/-- [T26], Definition 3.1; the closed strip bounded by `ℝ` and `ℝ + τ`, owned by Issue #6. -/
def_wanted strip : ℂ → Set ℂ

/-- [T26] Def. 3.1, owned by Issue #6; the geometric closed strip bounded by `ℝ` and `ℝ + τ`.
For real `τ` this degenerates to `ℝ`, which is what makes `vtilde_real` consistent. -/
theorem_wanted strip_eq :
    ∀ τ : ℂ, ❰strip❱ τ = { z : ℂ | min 0 τ.im ≤ z.im ∧ z.im ≤ max 0 τ.im }

/-- [T26], Definition 3.1; the compatible-functional characterization of the partially defined
`Ṽ_τ`, including continuity on the closed strip, holomorphy in its interior, and both boundary
values, owned by Issue #6. Regularity is the precise separation-of-points hypothesis needed for
this equivalence; `IsWightmanCFT` would be stronger than necessary. -/
theorem_wanted vtilde_spec :
    ❰ActsRegularly❱ →
      ∀ (τ : ℂ) (Φ Ψ : ❰Dom❱),
      (❰VtildeDom❱ τ Φ ∧ ❰VtildeMap❱ τ Φ = Ψ) ↔
        ∃ G : ❰Compat❱ → ℂ → ℂ,
          ∀ lam : ❰Compat❱,
            ContinuousOn (G lam) (❰strip❱ τ) ∧
              DifferentiableOn ℂ (G lam) (interior (❰strip❱ τ)) ∧
              (∀ t : ℝ,
                G lam (t : ℂ) = ❰compatApply❱ lam (❰boost❱ t Φ)) ∧
              (∀ t : ℝ,
                G lam (τ + (t : ℂ)) = ❰compatApply❱ lam (❰boost❱ t Ψ))

/-- [T26], Definition 3.1; real parameters give the ordinary boost on all of `𝓓`; the leading
Wightman hypothesis supplies the regularity/continuity axiom for `t ↦ λ(V_t Φ)` needed here,
owned by Issue #6. -/
theorem_wanted vtilde_real :
    ❰IsWightmanCFT❱ →
      ∀ (t : ℝ) (Φ : ❰Dom❱),
        ❰VtildeDom❱ (t : ℂ) Φ ∧ ❰VtildeMap❱ (t : ℂ) Φ = ❰boost❱ t Φ

/-- [T26], Definition 3.1 and footnote 7; real translation of the partially defined boost,
including equality of the domains of both compositions and equality of values on their common
domain, owned by Issue #6. Regularity is the precise separation-of-points hypothesis needed to
pin the values of `VtildeMap`; `IsWightmanCFT` would be stronger than necessary. -/
theorem_wanted vtilde_translation :
    ❰ActsRegularly❱ →
      ∀ (τ : ℂ) (t : ℝ) (Φ : ❰Dom❱),
      (❰VtildeDom❱ (τ + (t : ℂ)) Φ ↔ ❰VtildeDom❱ τ (❰boost❱ t Φ)) ∧
        (❰VtildeDom❱ (τ + (t : ℂ)) Φ ↔ ❰VtildeDom❱ τ Φ) ∧
          (❰VtildeDom❱ (τ + (t : ℂ)) Φ →
            ❰VtildeDom❱ τ Φ →
              ❰VtildeMap❱ (τ + (t : ℂ)) Φ =
                ❰boost❱ t (❰VtildeMap❱ τ Φ)) ∧
          (❰VtildeDom❱ τ (❰boost❱ t Φ) →
            ❰VtildeMap❱ (τ + (t : ℂ)) Φ = ❰VtildeMap❱ τ (❰boost❱ t Φ))

/-- [T26], Definition 3.1; the vacuum is in every continued-boost domain and is fixed there,
leading Wightman hypothesis is needed for the (W4) vacuum axiom, owned by Issue #6. -/
theorem_wanted vtilde_vacuum :
    ❰IsWightmanCFT❱ →
      ∀ τ : ℂ, ❰VtildeDom❱ τ ❰vac❱ ∧ ❰VtildeMap❱ τ ❰vac❱ = ❰vac❱

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

/-- [T26], Lemma 3.4; upper-supported test functions lie in the closure of
analytic restrictions, owned by Issue #7. -/
theorem_wanted lemma_3_4_density :
    { f : TestFn | SuppUpper f } ⊆
      closure { g : TestFn | ∃ F : ❰AnalyticTestFn❱, ❰xRestrictUpper❱ F = g }

/-- [T26], the (W3) bridge used in the proof of Lemma 3.7, still owed by Issue #26. -/
theorem_wanted w3_vacuum_annihilation :
    ❰IsWightmanCFT❱ →
      ∀ (φ : ❰Field❱) (F : ❰AnalyticTestFn❱),
        ❰smear❱ φ (inv (❰xRestrictS1❱ F)) ❰vac❱ = 0

/-- [T26], Definition 3.5, equation (3.4); at `τ = iπ` the source scalar
`(-1)^(d-1)` is represented as `(-1)^(d+1)` for `d : ℕ`, since these exponents
have the same parity in `ℂ`; owned by Issue #5.
The restriction is the lower one because inversion exchanges the semicircles: the source uses
`(F ∘ z⁻¹)|_{I_+} = F|_{I_-} ∘ z⁻¹`. -/
theorem_wanted beta_boost_at_ipi :
    ∀ (d : ℕ) (F : ❰AnalyticTestFn❱),
      ❰betaBoost❱ d (Complex.I * Real.pi) F =
        (-1 : ℂ) ^ (d + 1) • inv (❰xRestrictLower❱ F)

/-- [T26], Lemma 3.7(i); the analytic-core continued-boost formula on upper-supported
analytic restrictions, owned by Issue #9. -/
theorem_wanted lemma_3_7 :
    ❰IsWightmanCFT❱ →
      ∀ (l : List (❰Field❱ × ❰AnalyticTestFn❱)) (τ : ℂ), τ ∈ ❰strip❱ (Complex.I * Real.pi) →
        ❰VtildeDom❱ τ (❰smearedProduct❱ (l.map (fun p => (p.1, ❰xRestrictUpper❱ p.2)))) ∧
          ❰VtildeMap❱ τ (❰smearedProduct❱ (l.map (fun p => (p.1, ❰xRestrictUpper❱ p.2)))) =
            ❰smearedProduct❱ (l.map (fun p => (p.1, ❰betaBoost❱ (❰dim❱ p.1) τ p.2)))

/-- [T26], Lemma 3.7(ii); at `τ = Complex.I * Real.pi`, the analytic-core vector maps to the
reversed product with the conformal-dimension sign, owned by Issue #9. Here
`inv (xRestrictUpper p.2)` means `F|_{I_+} ∘ z⁻¹`, supported in `I_-`; this is deliberately
the opposite restriction from `beta_boost_at_ipi`, where the source needs
`(F ∘ z⁻¹)|_{I_+} = F|_{I_-} ∘ z⁻¹` and therefore uses `xRestrictLower`. -/
theorem_wanted lemma_3_7_at_ipi :
    ❰IsWightmanCFT❱ →
      ∀ (l : List (❰Field❱ × ❰AnalyticTestFn❱)),
        ❰VtildeMap❱ (Complex.I * Real.pi)
            (❰smearedProduct❱ (l.map (fun p => (p.1, ❰xRestrictUpper❱ p.2)))) =
          (-1 : ℂ) ^ ((l.map (fun p => ❰dim❱ p.1)).sum) •
            ❰smearedProduct❱
              (l.reverse.map (fun p => (p.1, inv (❰xRestrictUpper❱ p.2))))

/-- [T26], Lemma 3.8; for fixed fields and compatible functional, the exponential
continuity estimate has constants independent of test-function lists and `t`. The `foldr max 0`
is the source's maximum because its entries are nonnegative by construction; for `k = 0` it gives
`0 ≤ 0`, where the source's maximum over an empty index set is undefined. A positive integer `N`
is required, owned by Issue #10. -/
theorem_wanted lemma_3_8 :
    ❰IsWightmanCFT❱ →
      ∀ (φs : List ❰Field❱) (lam : ❰Compat❱),
        ∃ (N : ℕ) (C : ℝ → ℝ) (k₁ k₂ : ℝ),
          0 < N ∧ 0 < k₁ ∧ 0 < k₂ ∧
            (∀ t : ℝ, 0 < C t) ∧
            (∀ t : ℝ, C t ≤ k₁ * Real.exp (k₂ * |t|)) ∧
            ∀ (t : ℝ) (fs gs : List TestFn),
              fs.length = φs.length → gs.length = φs.length →
                ‖❰compatApply❱ lam
                    (❰boost❱ t (❰smearedProduct❱ (φs.zip fs)) -
                      ❰boost❱ t (❰smearedProduct❱ (φs.zip gs)))‖ ≤
                  C t *
                      ((((fs.zip gs).map
                        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
                    ((List.foldr max 0
                      ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ)

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
