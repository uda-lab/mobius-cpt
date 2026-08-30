import MobiusCPT.Wightman.BoostCurve
import MobiusCPT.Wightman.Bundle
import MobiusCPT.Wightman.Vtilde
import MobiusCPT.Wightman.VtildeLinear
import MobiusCPT.Mobius.Covariance
import MobiusCPT.Mobius.ComplexBetaLaws

/-!
# [T26], Lemma 3.7(i): the analytic-core continued-boost formula

This module discharges `MobiusCPT.Contract`'s `theorem_wanted lemma_3_7`. The proof follows
[T26]'s own route via Lemma 3.6: exhibit the family `G_λ(τ') = λ(φ₁(β(v_{τ'})F₁)⋯φ_k(β(v_{τ'})F_k)Ω)`
as an `IsBoostContinuation` witness between the upper-restricted product and the
`betaBoost`-smeared product. Its continuity and holomorphy clauses are exactly [T26], Lemma 3.6,
already proved for a general `WightmanStruct` by `MobiusCPT.Wightman.BoostCurve` (Issue #8); its
two real-boundary clauses reduce algebraically to `betaBoost_ofReal_mob` (the real-parameter
value of the complex boost) and `beta_boostMat_betaBoost` (the real/complex boost translation
cocycle), both already proved in `MobiusCPT.Mobius.ComplexBetaLaws`, together with the covariance
rewrite `WightmanData.boost_smearedProduct` from `MobiusCPT.Mobius.Covariance` (Issue #38's `W1`
covariance input). No new analysis is needed here: the module is assembly, not proof search.
-/

namespace MobiusCPT

open Set

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- A parameter in the closed strip up to `iπ` sees its own strip contained in the big one; this
is the domain-monotonicity `IsBoostContinuation τ` needs from [T26], Lemma 3.6's statement, which
is proved only on the fixed strip `strip (Complex.I * Real.pi)`. -/
theorem strip_subset_strip_I_mul_pi {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    strip τ ⊆ strip (Complex.I * Real.pi) := by
  have himτ : (Complex.I * (Real.pi : ℂ)).im = Real.pi := by simp
  rw [mem_strip, himτ, min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hτ
  intro z hz
  rw [mem_strip] at hz
  have hτnonneg : (0 : ℝ) ≤ τ.im := hτ.1
  rw [min_eq_left hτnonneg, max_eq_right hτnonneg] at hz
  rw [mem_strip, himτ, min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le]
  exact ⟨hz.1, hz.2.trans hτ.2⟩

/-- The family `G_λ` of [T26], Definition 3.1, built from the complex boost, in the exact shape
`IsBoostContinuation` asks for its bound family. -/
noncomputable def betaBoostGf (W : WightmanStruct TestFn 𝓓 𝓕)
    (l : List (𝓕 × AnalyticTestFn)) : W.Compat → ℂ → ℂ :=
  fun lam τ' => W.compatApply lam
    (W.smearedProduct (l.map (fun p => (p.1, betaBoost (W.dim p.1) τ' p.2))))

namespace WightmanData

/-- `MobiusAction.beta`/`MobiusAction.boostElt` at the concrete instance `mobiusActionMobTestFn`
are literally `Mob.beta`/`Mob.boost`, by the instance's own field assignment. -/
private theorem beta_boostElt_eq_mob (d : ℕ) (t : ℝ) (f : TestFn) :
    MobiusAction.beta (G := Mob) (TF := TestFn) d
        (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) f =
      Mob.beta d (Mob.boost t) f := rfl

/-- `G_λ` built from `betaBoost` is an `IsBoostContinuation` witness between the
upper-restricted smeared product and the `betaBoost`-smeared product, for every `τ` in the
closed strip up to `iπ`. -/
theorem isBoostContinuation_betaBoost {W : WightmanData Mob TestFn 𝓓 𝓕} (hW4 : W.W4)
    (hcov : ∀ φ : 𝓕, W.IsCovariant φ (W.dim φ))
    (l : List (𝓕 × AnalyticTestFn)) {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    W.IsBoostContinuation τ
      (W.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2))))
      (W.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2))))
      (betaBoostGf W.toWightmanStruct l) := by
  have hsub : strip τ ⊆ strip (Complex.I * Real.pi) := strip_subset_strip_I_mul_pi hτ
  intro lam
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuousOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam l).mono hsub
  · exact (differentiableOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam l).mono
      (interior_mono hsub)
  · intro t
    simp only [betaBoostGf]
    have hcovUpper : ∀ p ∈ l.map (fun p => (p.1, xRestrictUpper p.2)),
        W.IsCovariant p.1 (W.dim p.1) := by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      exact hcov q.1
    have hlist :
        (l.map (fun p => (p.1, xRestrictUpper p.2))).map
            (fun p => (p.1, MobiusAction.beta (G := Mob) (TF := TestFn) (W.dim p.1)
              (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) p.2)) =
          l.map (fun p => (p.1, betaBoost (W.dim p.1) (t : ℂ) p.2)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, beta_boostElt_eq_mob]
      congr 1
      exact (betaBoost_ofReal_mob (W.dim p.1) t p.2).symm
    rw [WightmanData.boost_smearedProduct hW4 t _ hcovUpper, hlist]
  · intro t
    simp only [betaBoostGf]
    have hcovBeta : ∀ p ∈ l.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2)),
        W.IsCovariant p.1 (W.dim p.1) := by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, _, rfl⟩ := hp
      exact hcov q.1
    have hlist :
        (l.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2))).map
            (fun p => (p.1, MobiusAction.beta (G := Mob) (TF := TestFn) (W.dim p.1)
              (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) p.2)) =
          l.map (fun p => (p.1, betaBoost (W.dim p.1) (τ + (t : ℂ)) p.2)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p _
      simp only [Function.comp_apply, beta_boostElt_eq_mob]
      congr 1
      exact beta_boostMat_betaBoost (W.dim p.1) t hτ p.2
    rw [WightmanData.boost_smearedProduct hW4 t _ hcovBeta, hlist]

/-- [T26], Lemma 3.7(i); the analytic-core continued-boost formula on upper-supported analytic
restrictions. -/
theorem lemma_3_7 {W : WightmanData Mob TestFn 𝓓 𝓕} (hW : W.IsWightmanCFT)
    (l : List (𝓕 × AnalyticTestFn)) (τ : ℂ) (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    W.VtildeDom τ
        (W.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2)))) ∧
      W.vtildeMap τ
          (W.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2)))) =
        W.toWightmanStruct.smearedProduct
          (l.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2))) :=
  W.vtildeDom_and_vtildeMap_eq hW.actsRegularly
    (isBoostContinuation_betaBoost hW.w4 (fun φ => hW.w1.2 φ) l hτ)

end WightmanData

namespace WightmanBundle

/-- [T26], Lemma 3.7(i). Issue #9 discharges `MobiusCPT.Contract`'s `theorem_wanted lemma_3_7`,
byte-identical statement text, for the concrete Möbius group and conformal action
`WightmanBundle` fixes (`docs/adr/0001-fix-mobius-group-in-bundle.md`). -/
theorem lemma_3_7 (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (l : List (W.𝓕 × AnalyticTestFn)) (τ : ℂ) (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    W.data.VtildeDom τ
        (W.data.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2)))) ∧
      W.data.vtildeMap τ
          (W.data.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2)))) =
        W.data.toWightmanStruct.smearedProduct
          (l.map (fun p => (p.1, betaBoost (W.data.dim p.1) τ p.2))) :=
  WightmanData.lemma_3_7 h l τ hτ

end WightmanBundle

end MobiusCPT
