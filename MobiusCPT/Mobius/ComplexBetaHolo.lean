import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MobiusCPT.Mobius.ComplexBetaDerivFn

namespace MobiusCPT

open Filter Set
open scoped ContDiff Interval Topology

noncomputable section

/-- [T26], Lemma 3.6; the difference quotients of every angle derivative of the complex boost
converge to its parameter derivative uniformly over the closed upper semicircle. -/
theorem eventually_forall_norm_slice_diff_quotient_sub_lt (d : ℕ) (F : AnalyticTestFn) (j : ℕ)
    {τ : ℂ} (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
      (τ + h ∈ strip (Complex.I * Real.pi)) ∧
        ∀ θ ∈ Set.Icc 0 Real.pi,
          ‖(betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h -
            betaBoostSliceDot d F j (τ, θ)‖ < ε := by
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp isOpen_interior τ hτ
  have hdot : ∀ᶠ σ in 𝓝[strip (Complex.I * Real.pi)] τ,
      ∀ θ ∈ Set.Icc 0 Real.pi,
        ‖betaBoostSliceDot d F j (σ, θ) - betaBoostSliceDot d F j (τ, θ)‖ < ε / 2 :=
    eventually_forall_norm_sub_lt isCompact_Icc
      (continuousOn_betaBoostSliceDot d F j) (interior_subset hτ) (by linarith)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hdot
  have hρ : 0 < min R δ := lt_min hR hδ
  have hsmall : ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
      ‖h‖ < min R δ := by
    have hball : ∀ᶠ h : ℂ in nhds (0 : ℂ), ‖h‖ < min R δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρ] with h hh
      simpa only [Metric.mem_ball, dist_zero_right] using hh
    exact hball.filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hne
  have hne' : h ≠ 0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hne
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      τ + s • h ∈ interior (strip (Complex.I * Real.pi)) := by
    intro s hs
    have hnorm : ‖s • h‖ ≤ ‖h‖ := by
      calc
        ‖s • h‖ = ‖s‖ * ‖h‖ := norm_smul _ _
        _ = |s| * ‖h‖ := by rw [Real.norm_eq_abs]
        _ = s * ‖h‖ := by rw [abs_of_nonneg hs.1]
        _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖h‖ := one_mul _
    have hltR : ‖s • h‖ < R :=
      hnorm.trans_lt (hh.trans_le (min_le_left R δ))
    apply hRsub
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hltR
  have hstrip : τ + h ∈ strip (Complex.I * Real.pi) := by
    have hone := hseg 1 ⟨zero_le_one, le_rfl⟩
    simpa using interior_subset hone
  refine ⟨hstrip, ?_⟩
  intro θ hθ
  have hmap : Continuous (fun s : ℝ => (τ + s • h, θ)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const
  have hcont : ContinuousOn
      (fun s : ℝ => betaBoostSliceDot d F j (τ + s • h, θ)) (Set.Icc (0 : ℝ) 1) := by
    apply (continuousOn_betaBoostSliceDot d F j).comp hmap.continuousOn
    intro s hs
    exact ⟨interior_subset (hseg s hs), hθ⟩
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
        (betaBoostSliceDot d F j (τ + s • h, θ)) (τ + s • h) := by
    intro s hs
    exact hasDerivAt_betaBoostSlice d F j (hseg s hs) hθ
  have hFTC :
      h • (∫ s : ℝ in (0 : ℝ)..1,
        betaBoostSliceDot d F j (τ + s • h, θ)) =
        betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ) := by
    exact intervalIntegral.integral_unitInterval_deriv_eq_sub
      (f := fun σ : ℂ => betaBoostSlice d F j (σ, θ))
      (f' := fun σ : ℂ => betaBoostSliceDot d F j (σ, θ)) hcont hderiv
  have hquot :
      (betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h =
        ∫ s : ℝ in (0 : ℝ)..1, betaBoostSliceDot d F j (τ + s • h, θ) := by
    calc
      (betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h =
          (h • (∫ s : ℝ in (0 : ℝ)..1,
            betaBoostSliceDot d F j (τ + s • h, θ))) / h := by rw [hFTC]
      _ = ∫ s : ℝ in (0 : ℝ)..1, betaBoostSliceDot d F j (τ + s • h, θ) := by
        simp only [smul_eq_mul]
        field_simp [hne']
  have hconst : IntervalIntegrable
      (fun _s : ℝ => betaBoostSliceDot d F j (τ, θ))
      MeasureTheory.volume (0 : ℝ) 1 :=
    continuousOn_const.intervalIntegrable
  have hcontU : ContinuousOn (fun s : ℝ =>
      betaBoostSliceDot d F j (τ + s • h, θ)) (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hcont
  have hidentity :
      (betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h -
          betaBoostSliceDot d F j (τ, θ) =
        ∫ s : ℝ in (0 : ℝ)..1,
          (betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ)) := by
    rw [hquot, intervalIntegral.integral_sub hcontU.intervalIntegrable hconst,
      intervalIntegral.integral_const]
    simp
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ)‖ < ε / 2 := by
    intro s hs
    have hnorm : ‖s • h‖ ≤ ‖h‖ := by
      calc
        ‖s • h‖ = ‖s‖ * ‖h‖ := norm_smul _ _
        _ = |s| * ‖h‖ := by rw [Real.norm_eq_abs]
        _ = s * ‖h‖ := by rw [abs_of_nonneg hs.1]
        _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖h‖ := one_mul _
    have hltδ : ‖s • h‖ < δ :=
      hnorm.trans_lt (hh.trans_le (min_le_right R δ))
    have hballδ : τ + s • h ∈ Metric.ball τ δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa only [add_sub_cancel_left] using hltδ
    have hdot_at : ∀ θ ∈ Set.Icc 0 Real.pi,
        ‖betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ)‖ < ε / 2 :=
      hδsub ⟨hballδ, interior_subset (hseg s hs)⟩
    exact hdot_at θ hθ
  have hintegral :
      ‖∫ s : ℝ in (0 : ℝ)..1,
        (betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ))‖ ≤ ε / 2 := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s : ℝ =>
        betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ))
      (a := (0 : ℝ)) (b := 1) (C := ε / 2)
      (fun s hs => (hpoint s (by
        rw [← Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
        exact uIoc_subset_uIcc hs)).le)
    simpa using hbound
  calc
    ‖(betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h -
        betaBoostSliceDot d F j (τ, θ)‖ =
      ‖∫ s : ℝ in (0 : ℝ)..1,
        (betaBoostSliceDot d F j (τ + s • h, θ) - betaBoostSliceDot d F j (τ, θ))‖ := by
          rw [hidentity]
    _ ≤ ε / 2 := hintegral
    _ < ε := by linarith

/-- [T26], Lemma 3.6; the same estimate on the whole circle, by periodicity and support. -/
theorem eventually_forall_norm_angleDeriv_diff_quotient_sub_lt (d : ℕ) (F : AnalyticTestFn)
    (j : ℕ) {τ : ℂ} (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
      ∀ θ : ℝ,
        ‖angleDeriv j ((h⁻¹ : ℂ) • (betaBoost d (τ + h) F - betaBoost d τ F)) θ -
          angleDeriv j (betaBoostDeriv d τ F) θ‖ < ε := by
  have hslice : ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
      (τ + h ∈ strip (Complex.I * Real.pi)) ∧
        ∀ θ ∈ Set.Icc 0 Real.pi,
          ‖(betaBoostSlice d F j (τ + h, θ) - betaBoostSlice d F j (τ, θ)) / h -
            betaBoostSliceDot d F j (τ, θ)‖ < ε :=
    eventually_forall_norm_slice_diff_quotient_sub_lt d F j hτ hε
  filter_upwards [hslice] with h hh
  obtain ⟨hτh, hhbound⟩ := hh
  intro θ
  obtain ⟨n, hmem⟩ := exists_sub_int_mul_mem_Ico θ
  set θ' : ℝ := θ - n * (2 * Real.pi) with hθ'
  let q : TestFn := (h⁻¹ : ℂ) • (betaBoost d (τ + h) F - betaBoost d τ F)
  have hredq : angleDeriv j q θ' = angleDeriv j q θ :=
    (periodic_angleDeriv j q).sub_int_mul_eq n
  have hredderiv :
      angleDeriv j (betaBoostDeriv d τ F) θ' = angleDeriv j (betaBoostDeriv d τ F) θ :=
    (periodic_angleDeriv j (betaBoostDeriv d τ F)).sub_int_mul_eq n
  change ‖angleDeriv j q θ - angleDeriv j (betaBoostDeriv d τ F) θ‖ < ε
  rw [← hredq, ← hredderiv]
  by_cases hle : θ' ≤ Real.pi
  · have hθmem : θ' ∈ Set.Icc 0 Real.pi := ⟨hmem.1, hle⟩
    have hbound := hhbound θ' hθmem
    simp only [q, angleDeriv_smul, Pi.smul_apply, Pi.sub_apply, angleDeriv_sub]
    rw [
      angleDeriv_betaBoost_of_mem d F j hτh hθmem,
      angleDeriv_betaBoost_of_mem d F j (interior_subset hτ) hθmem,
      angleDeriv_betaBoostDeriv_of_mem d F j (interior_subset hτ) hθmem]
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hbound
  · have hIoo : θ' ∈ Set.Ioo Real.pi (2 * Real.pi) :=
      ⟨lt_of_not_ge hle, hmem.2⟩
    simp only [q, angleDeriv_smul, Pi.smul_apply, Pi.sub_apply, angleDeriv_sub]
    rw [
      angleDeriv_betaBoost_of_notMem d F j hτh hIoo,
      angleDeriv_betaBoost_of_notMem d F j (interior_subset hτ) hIoo,
      angleDeriv_betaBoostDeriv_of_notMem d F j (interior_subset hτ) hIoo]
    simpa using hε

/-- [T26], Lemma 3.6; the complex boost is differentiable in the strip parameter as a curve of test
functions, in the locally convex sense: its difference quotients converge in the Fréchet topology
of `C^∞(S¹)`.  No norm on `C^∞(S¹)` is used or implied. -/
theorem hasTestFnDerivAt_betaBoost (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) :
    HasTestFnDerivAt (fun σ : ℂ => betaBoost d σ F) (betaBoostDeriv d τ F) τ := by
  unfold HasTestFnDerivAt
  apply tendsto_testFn_of_forall_eventually
  intro N ε hε
  have hslice : ∀ j : ℕ,
      ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
        ∀ θ : ℝ,
          ‖angleDeriv j ((h⁻¹ : ℂ) •
              (betaBoost d (τ + h) F - betaBoost d τ F)) θ -
            angleDeriv j (betaBoostDeriv d τ F) θ‖ < ε := by
    intro j
    exact eventually_forall_norm_angleDeriv_diff_quotient_sub_lt d F j hτ hε
  have hfin :
      ∀ᶠ h : ℂ in nhdsWithin (0 : ℂ) (({0} : Set ℂ)ᶜ),
        ∀ j ∈ Finset.range (N + 1), ∀ θ : ℝ,
          ‖angleDeriv j ((h⁻¹ : ℂ) •
              (betaBoost d (τ + h) F - betaBoost d τ F)) θ -
            angleDeriv j (betaBoostDeriv d τ F) θ‖ < ε :=
    (Filter.eventually_all_finset _).mpr fun j _ => hslice j
  filter_upwards [hfin] with h hh
  intro j hj θ
  exact hh j (Finset.mem_range.mpr (by omega)) θ

/-- [T26], Lemma 3.6; the scalarised form of the holomorphy clause: composing the boost curve with
any continuous linear functional gives a function holomorphic on the interior of the strip.  This
is the form [T26], Definition 3.1 uses, and it is a consequence of the locally convex derivative
above rather than an extra assumption. -/
theorem differentiableOn_clm_comp_betaBoost (d : ℕ) (F : AnalyticTestFn)
    (μ : TestFn →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun τ : ℂ => μ (betaBoost d τ F))
      (interior (strip (Complex.I * Real.pi))) := by
  intro τ hτ
  have htest := hasTestFnDerivAt_betaBoost d F hτ
  have htest_slope := (hasTestFnDerivAt_iff_tendsto_slope.mp htest)
  have hμ := (μ.continuous.tendsto (betaBoostDeriv d τ F)).comp htest_slope
  have hscalar :
      Filter.Tendsto
        (slope (fun t : ℂ => μ (betaBoost d t F)) τ)
        (nhdsWithin τ ({τ} : Set ℂ)ᶜ)
        (𝓝 (μ (betaBoostDeriv d τ F))) := by
    simpa only [Function.comp_def, slope_fun_def_field, div_eq_inv_mul, map_smul,
      map_sub, smul_eq_mul] using hμ
  exact (hasDerivAt_iff_tendsto_slope.mpr hscalar).differentiableAt.differentiableWithinAt

end

end MobiusCPT
