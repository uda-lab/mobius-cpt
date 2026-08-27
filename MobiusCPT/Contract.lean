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

/-!
# MobiusCPT.Contract

This file is the Issue #2 statement contract for [T26], Theorem 3.10.  Its
placeholders are sound because they inhabit `ProofWanted T` or `DefWanted T`,
never `T`, so no statement here is usable as a proof and no axiom is introduced.
This file pins the capstone target of [T26] Thm. 3.10 together with the semantic
decisions Issue #2 settled; it is deliberately not the full interface — the general
`β_d` action on `C^∞(S¹)`, the Def. 3.5 cocycle, the `C^N` covariance estimate,
Lemma 3.9, and the content of (W1)–(W3) are owned by the corresponding child Issues.

As each child Issue lands, its placeholders are deleted here and the remaining
statements are re-expressed against the real definitions.  Issue #3 has landed:
`TestFn`, `cnorm`, `inv`, `SuppUpper` and `SuppLower` below are the genuine
definitions from `MobiusCPT.TestFunctions.*`, not holes, and the statements that
Issue #3 owned (`tendsto_iff_cnorm`, `inv_add`, `inv_involutive`, `inv_supp`,
`cnorm_inv`) are proved theorems in those modules.
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

/-- [T26], §2; the domain `𝓓`, owned by Issue #4. -/
def_wanted Dom : Type

/-- [T26], §2; the additive structure on `𝓓`, owned by Issue #4. -/
instance_wanted domAddCommGroup : AddCommGroup ❰Dom❱

/-- [T26], §2; the complex module structure on `𝓓`, owned by Issue #4. -/
instance_wanted domModule : Module ℂ ❰Dom❱

/-- [T26], §2; the topology on `𝓓`, owned by Issue #4. -/
instance_wanted domTopologicalSpace : TopologicalSpace ❰Dom❱

/-- [T26], §2; the field index type `𝓕`, owned by Issue #4. -/
def_wanted Field : Type

/-- [T26], §2 and (W1); the conformal dimension `dim : 𝓕 → ℤ_{≥0}`
represented in Lean by naturals, owned by Issue #4. -/
def_wanted dim : ❰Field❱ → ℕ

/-- [T26], §2; the smeared field operator `φ(f)`, owned by Issue #4. -/
def_wanted smear : ❰Field❱ → TestFn → ❰Dom❱ → ❰Dom❱

/-- [T26], §2; linearity of the smeared field in the domain vector, owned by Issue #4. -/
theorem_wanted smear_linear :
    ∀ (φ : ❰Field❱) (f : TestFn) (Φ Ψ : ❰Dom❱),
      (❰smear❱ φ f (Φ + Ψ) = ❰smear❱ φ f Φ + ❰smear❱ φ f Ψ) ∧
        (∀ c : ℂ, ❰smear❱ φ f (c • Φ) = c • ❰smear❱ φ f Φ)

/-- [T26], §2; linearity of the operator-valued distribution in the test function, owned by
Issue #4. -/
theorem_wanted smear_addLinear :
    ∀ (φ : ❰Field❱) (f g : TestFn) (Φ : ❰Dom❱),
      (❰smear❱ φ (f + g) Φ = ❰smear❱ φ f Φ + ❰smear❱ φ g Φ) ∧
        (∀ c : ℂ, ❰smear❱ φ (c • f) Φ = c • ❰smear❱ φ f Φ)

/-- [T26], §2; the vacuum vector `Ω`, owned by Issue #4. -/
def_wanted vac : ❰Dom❱

/-- [T26], §2; the compatible-function space `D*_𝓕`, owned by Issue #4. -/
def_wanted Compat : Type

/-- [T26], §2; evaluation of a compatible functional on `𝓓`, owned by Issue #4. -/
def_wanted compatApply : ❰Compat❱ → ❰Dom❱ → ℂ

/-- [T26], §2; linearity of compatible-function evaluation, owned by Issue #4. -/
theorem_wanted compatApply_linear :
    ∀ (lam : ❰Compat❱) (Φ Ψ : ❰Dom❱),
      (❰compatApply❱ lam (Φ + Ψ) = ❰compatApply❱ lam Φ + ❰compatApply❱ lam Ψ) ∧
        (∀ c : ℂ, ❰compatApply❱ lam (c • Φ) = c • ❰compatApply❱ lam Φ)

/-- [T26], §2 and Definition 3.1; `V_t = U(v_t)`, owned by Issues #4 and #5. -/
def_wanted boost : ℝ → ❰Dom❱ → ❰Dom❱

/-- [T26], §2 and Definition 3.1; linearity of the real boost action, owned by Issues #4 and #5. -/
theorem_wanted boost_linear :
    ∀ (t : ℝ) (Φ Ψ : ❰Dom❱),
      (❰boost❱ t (Φ + Ψ) = ❰boost❱ t Φ + ❰boost❱ t Ψ) ∧
        (∀ c : ℂ, ❰boost❱ t (c • Φ) = c • ❰boost❱ t Φ)

/-- [T26], Definition 3.1; the boost at zero is the identity, owned by Issues #4 and #5. -/
theorem_wanted boost_zero : ∀ Φ : ❰Dom❱, ❰boost❱ 0 Φ = Φ

/-- [T26], §3; the boosts form a one-parameter group, owned by Issues #4 and #5. -/
theorem_wanted boost_add :
    ∀ (s t : ℝ) (Φ : ❰Dom❱),
      ❰boost❱ s (❰boost❱ t Φ) = ❰boost❱ (s + t) Φ

/-- [T26], Definitions 2.4–2.5; `𝓕` acts regularly, owned by Issue #4. -/
def_wanted ActsRegularly : Prop

/-- [T26] Def. 2.4 — `𝓕` acts regularly iff `𝓓*_𝓕` separates points. Owner #4. -/
theorem_wanted actsRegularly_iff :
    ❰ActsRegularly❱ ↔
      ∀ Φ Ψ : ❰Dom❱, (∀ lam : ❰Compat❱, ❰compatApply❱ lam Φ = ❰compatApply❱ lam Ψ) → Φ = Ψ

/-- [T26], Definition 2.5 (W1); Möbius covariance, owned by Issue #4. -/
def_wanted W1 : Prop

/-- [T26], Definition 2.5 (W2); locality, owned by Issue #4. -/
def_wanted W2 : Prop

/-- [T26], Definition 2.5 (W3); the spectrum condition, owned by Issue #4. -/
def_wanted W3 : Prop

/-- [T26], Definition 2.5 (W4); the vacuum axiom, owned by Issue #4. -/
def_wanted W4 : Prop

/-- [T26] Def. 2.5 (W4), the half of the vacuum axiom that §3 uses. Owner #4.
(W1)–(W3) and the spanning half of (W4) deliberately stay opaque here and are
owned by #4. -/
theorem_wanted w4_vacuum_invariant :
    ❰W4❱ → ∀ t : ℝ, ❰boost❱ t ❰vac❱ = ❰vac❱

/-- [T26], Definition 2.5; the Möbius-covariant Wightman CFT conjunction, owned by Issue #4. -/
def_wanted IsWightmanCFT : Prop

/-- [T26], Definition 2.5; unpacking the named Wightman CFT conjunction, owned by Issue #4. -/
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

/-- [T26], §2; the left-to-right product `φ₁(f₁)⋯φ_k(f_k)Ω`, owned by Issue #4. -/
def_wanted smearedProduct : List (❰Field❱ × TestFn) → ❰Dom❱

/-- [T26], §2; membership in the localized subspace `P(I_+)Ω`, owned by Issue #4. -/
def_wanted MemPUpperOmega : ❰Dom❱ → Prop

/-- [T26], §2; membership in the localized subspace `P(I_-)Ω`, owned by Issue #4. -/
def_wanted MemPLowerOmega : ❰Dom❱ → Prop

/-- [T26], §2; the empty product is `Ω`, fixing the left-to-right convention;
owned by Issue #4. -/
theorem_wanted smearedProduct_nil : ❰smearedProduct❱ [] = ❰vac❱

/-- [T26], §2; cons acts on the product to its right, fixing the left-to-right
convention; owned by Issue #4. -/
theorem_wanted smearedProduct_cons :
    ∀ (p : ❰Field❱ × TestFn) (l : List (❰Field❱ × TestFn)),
      ❰smearedProduct❱ (p :: l) = ❰smear❱ p.1 p.2 (❰smearedProduct❱ l)

/-- [T26], §2; upper localized vectors are exactly finite complex-linear combinations of
upper-supported smeared products, owned by Issue #4. -/
theorem_wanted memPUpperOmega_iff :
    ∀ (Φ : ❰Dom❱),
      ❰MemPUpperOmega❱ Φ ↔
        ∃ (n : ℕ) (c : Fin n → ℂ)
          (ls : Fin n → List (❰Field❱ × TestFn)),
          (∀ i, ∀ p ∈ ls i, SuppUpper p.2) ∧
            Φ = ∑ i, c i • ❰smearedProduct❱ (ls i)

/-- [T26], §2; lower localized vectors are exactly finite complex-linear combinations of
lower-supported smeared products, owned by Issue #4. -/
theorem_wanted memPLowerOmega_iff :
    ∀ (Φ : ❰Dom❱),
      ❰MemPLowerOmega❱ Φ ↔
        ∃ (n : ℕ) (c : Fin n → ℂ)
          (ls : Fin n → List (❰Field❱ × TestFn)),
          (∀ i, ∀ p ∈ ls i, SuppLower p.2) ∧
            Φ = ∑ i, c i • ❰smearedProduct❱ (ls i)

/-- [T26], §2; the upper localized subspace is closed under addition, owned by Issue #4. -/
theorem_wanted memPUpperOmega_add :
    ∀ (Φ Ψ : ❰Dom❱),
      ❰MemPUpperOmega❱ Φ → ❰MemPUpperOmega❱ Ψ →
        ❰MemPUpperOmega❱ (Φ + Ψ)

/-- [T26], §2; the upper localized subspace is closed under complex scalars, owned by Issue #4. -/
theorem_wanted memPUpperOmega_smul :
    ∀ (c : ℂ) (Φ : ❰Dom❱),
      ❰MemPUpperOmega❱ Φ → ❰MemPUpperOmega❱ (c • Φ)

/-- [T26], §2; the lower localized subspace is closed under addition, owned by Issue #4. -/
theorem_wanted memPLowerOmega_add :
    ∀ (Φ Ψ : ❰Dom❱),
      ❰MemPLowerOmega❱ Φ → ❰MemPLowerOmega❱ Ψ →
        ❰MemPLowerOmega❱ (Φ + Ψ)

/-- [T26], §2; the lower localized subspace is closed under complex scalars, owned by Issue #4. -/
theorem_wanted memPLowerOmega_smul :
    ∀ (c : ℂ) (Φ : ❰Dom❱),
      ❰MemPLowerOmega❱ Φ → ❰MemPLowerOmega❱ (c • Φ)

/-- [T26], Lemma 3.4; upper-supported test functions lie in the closure of
analytic restrictions, owned by Issue #7. -/
theorem_wanted lemma_3_4_density :
    { f : TestFn | SuppUpper f } ⊆
      closure { g : TestFn | ∃ F : ❰AnalyticTestFn❱, ❰xRestrictUpper❱ F = g }

/-- [T26], the (W3) bridge used in the proof of Lemma 3.7; owned by Issues #4 and #9. -/
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
