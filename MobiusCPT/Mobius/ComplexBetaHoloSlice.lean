import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MobiusCPT.Mobius.ComplexBetaCont

/-!
# Holomorphy of the complex boost and its angle derivatives

The pointwise complex boost is holomorphic in the interior of the complex-parameter strip.  The
same holds for every angle derivative: successive derivatives are obtained as locally uniform
limits of holomorphic angle difference quotients.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Interval Topology

noncomputable section

private theorem mem_interior_strip_I_mul_pi {τ : ℂ} :
    τ ∈ interior (strip (Complex.I * Real.pi)) ↔ 0 < τ.im ∧ τ.im < Real.pi := by
  rw [interior_strip, im_I_mul_pi, min_eq_left Real.pi_pos.le,
    max_eq_right Real.pi_pos.le]
  exact Iff.rfl

/-- [T26], Definition 3.5; strictly inside the strip and strictly inside the upper semicircle, the
ratio fed to the divided inverted function lies in the open unit disc, where that function is
holomorphic. -/
theorem norm_cden_div_cnum_lt_one {τ : ℂ} (h₀ : 0 < τ.im) (h₁ : τ.im < Real.pi)
    {z : Circle} (hz : 0 < (z : ℂ).im) :
    ‖cden (-τ) z / cnum (-τ) z‖ < 1 := by
  have hsin : 0 < Real.sin τ.im := Real.sin_pos_of_pos_of_lt_pi h₀ h₁
  have hdiff :
      0 < Complex.normSq (cnum (-τ) z) - Complex.normSq (cden (-τ) z) := by
    rw [normSq_cnum_neg_sub_normSq_cden_neg]
    exact mul_pos (mul_pos (by norm_num) hsin) hz
  have hsq : ‖cden (-τ) z‖ ^ 2 < ‖cnum (-τ) z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith
  have hnorm : ‖cden (-τ) z‖ < ‖cnum (-τ) z‖ :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hP : cnum (-τ) z ≠ 0 :=
    cnum_neg_ne_zero_of_upper h₀.le h₁.le hz.le
  rw [Complex.norm_div]
  exact (div_lt_one (norm_pos_iff.mpr hP)).2 hnorm

/-- [T26], Lemma 3.6; for a fixed point of the closed upper semicircle the complex boost is
holomorphic in the strip parameter on the interior of the strip.  At the two endpoints the value
is identically zero and the statement is trivial; in between, the ratio lies in the open unit disc
where the divided inverted function is holomorphic. -/
theorem differentiableOn_betaBoostVal (d : ℕ) (F : AnalyticTestFn) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    DifferentiableOn ℂ (fun τ : ℂ => betaBoostVal d τ F (Circle.exp θ))
      (interior (strip (Complex.I * Real.pi))) := by
  by_cases hzero : θ = 0
  · subst θ
    apply (differentiableOn_const (𝕜 := ℂ) (s := interior (strip (Complex.I * Real.pi)))
      (0 : ℂ)).congr
    intro τ hτ
    exact betaBoostVal_circleExp_zero d F (interior_subset hτ)
  by_cases hpi : θ = Real.pi
  · subst θ
    apply (differentiableOn_const (𝕜 := ℂ) (s := interior (strip (Complex.I * Real.pi)))
      (0 : ℂ)).congr
    intro τ hτ
    exact betaBoostVal_circleExp_pi d F (interior_subset hτ)
  have hθopen : θ ∈ Set.Ioo 0 Real.pi :=
    ⟨lt_of_le_of_ne hθ.1 (fun h => hzero h.symm), lt_of_le_of_ne hθ.2 hpi⟩
  have hz : 0 < ((Circle.exp θ : Circle) : ℂ).im := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi hθopen.1 hθopen.2
  set z : Circle := Circle.exp θ with hzdef
  have hhalf : Differentiable ℂ (fun τ : ℂ => τ / 2) :=
    differentiable_id.div_const 2
  have hP : Differentiable ℂ (fun τ : ℂ => cnum (-τ) z) := by
    have h3 : Differentiable ℂ
        (fun τ : ℂ => Complex.cosh (τ / 2) * (z : ℂ) + Complex.sinh (τ / 2)) :=
      fun τ => (((Differentiable.ccosh hhalf).mul_const (z : ℂ)) τ).add
        ((Differentiable.csinh hhalf) τ)
    simpa only [cnum_neg] using h3
  have hQ : Differentiable ℂ (fun τ : ℂ => cden (-τ) z) := by
    have h3 : Differentiable ℂ
        (fun τ : ℂ => Complex.sinh (τ / 2) * (z : ℂ) + Complex.cosh (τ / 2)) :=
      fun τ => (((Differentiable.csinh hhalf).mul_const (z : ℂ)) τ).add
        ((Differentiable.ccosh hhalf) τ)
    simpa only [cden_neg] using h3
  have hP_ne : ∀ τ ∈ interior (strip (Complex.I * Real.pi)), cnum (-τ) z ≠ 0 := by
    intro τ hτ
    have hτ' := mem_interior_strip_I_mul_pi.mp hτ
    exact cnum_neg_ne_zero_of_upper hτ'.1.le hτ'.2.le hz.le
  have hPP_inv : DifferentiableOn ℂ
      (fun τ : ℂ => (cnum (-τ) z * cnum (-τ) z)⁻¹)
      (interior (strip (Complex.I * Real.pi))) :=
    (hP.mul hP).differentiableOn.inv fun τ hτ =>
      mul_ne_zero (hP_ne τ hτ) (hP_ne τ hτ)
  have hquot : DifferentiableOn ℂ
      (fun τ : ℂ => cden (-τ) z / cnum (-τ) z)
      (interior (strip (Complex.I * Real.pi))) :=
    hQ.differentiableOn.div hP.differentiableOn hP_ne
  have hquot_maps : Set.MapsTo
      (fun τ : ℂ => cden (-τ) z / cnum (-τ) z)
      (interior (strip (Complex.I * Real.pi))) (Metric.ball (0 : ℂ) 1) := by
    intro τ hτ
    rw [Metric.mem_ball, dist_zero_right]
    have hτ' := mem_interior_strip_I_mul_pi.mp hτ
    exact norm_cden_div_cnum_lt_one hτ'.1 hτ'.2 hz
  have hinvQuot : DifferentiableOn ℂ
      (fun τ : ℂ => F.invQuot (cden (-τ) z / cnum (-τ) z))
      (interior (strip (Complex.I * Real.pi))) := by
    exact F.differentiableOn_invQuot.comp hquot hquot_maps
  have hconst : DifferentiableOn ℂ
      (fun _τ : ℂ => (z : ℂ) * ((z : ℂ) ^ d)⁻¹)
      (interior (strip (Complex.I * Real.pi))) :=
    differentiableOn_const _
  have hsmooth : DifferentiableOn ℂ
      (fun τ : ℂ =>
        cnum (-τ) z ^ d * (cnum (-τ) z * cnum (-τ) z)⁻¹ * cden (-τ) z ^ d *
          ((z : ℂ) * ((z : ℂ) ^ d)⁻¹) *
          F.invQuot (cden (-τ) z / cnum (-τ) z))
      (interior (strip (Complex.I * Real.pi))) :=
    ((((hP.differentiableOn.pow d).mul hPP_inv).mul
      (hQ.differentiableOn.pow d)).mul hconst).mul hinvQuot
  apply hsmooth.congr
  intro τ hτ
  exact betaBoostVal_eq_mul_inv d F (hP_ne τ hτ)

private theorem hasDerivAt_betaBoostSlice_angle (d : ℕ) (F : AnalyticTestFn) (j : ℕ)
    {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    HasDerivAt (fun t : ℝ => betaBoostSlice d F j (τ, t))
      (betaBoostSlice d F (j + 1) (τ, θ)) θ := by
  have hdiff : DifferentiableOn ℝ
      (sliceDeriv stripUpper j (betaBoostJoint d F)) stripUpper :=
    (contDiffOn_sliceDeriv uniqueDiffOn_stripUpper
      (contDiffOn_betaBoostJoint d F) j).differentiableOn (by simp)
  have hslice := hasDerivWithinAt_slice (K := Set.Icc 0 Real.pi) hτ
    (hdiff (τ, θ) ⟨hτ, hθ.1.le, hθ.2.le⟩)
  simpa only [betaBoostSlice, stripUpper, sliceDeriv_succ] using
    hslice.hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)

/-- [T26], Lemma 3.6; every angle derivative of the complex boost is holomorphic in the strip
parameter on the interior of the strip.  The step from one order to the next is Weierstrass'
theorem: the difference quotients in the angle are holomorphic in the parameter and converge
locally uniformly, because the next angle derivative is jointly continuous, hence uniformly
continuous on compacta. -/
theorem differentiableOn_betaBoostSlice (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    DifferentiableOn ℂ (fun τ : ℂ => betaBoostSlice d F j (τ, θ))
      (interior (strip (Complex.I * Real.pi))) := by
  induction j generalizing θ with
  | zero =>
      simpa only [betaBoostSlice, sliceDeriv_zero, betaBoostJoint] using
        differentiableOn_betaBoostVal d F hθ
  | succ j ih =>
      by_cases hzero : θ = 0
      · subst θ
        apply (differentiableOn_const (𝕜 := ℂ)
          (s := interior (strip (Complex.I * Real.pi))) (0 : ℂ)).congr
        intro τ hτ
        rw [betaBoostSlice_eq d F (j + 1) (interior_subset hτ)
          ⟨le_rfl, Real.pi_pos.le⟩]
        exact iteratedDerivWithin_betaBoostVal_circleExp_zero d F
          (interior_subset hτ) (j + 1)
      by_cases hpi : θ = Real.pi
      · subst θ
        apply (differentiableOn_const (𝕜 := ℂ)
          (s := interior (strip (Complex.I * Real.pi))) (0 : ℂ)).congr
        intro τ hτ
        rw [betaBoostSlice_eq d F (j + 1) (interior_subset hτ)
          ⟨Real.pi_pos.le, le_rfl⟩]
        exact iteratedDerivWithin_betaBoostVal_circleExp_pi d F
          (interior_subset hτ) (j + 1)
      have hθopen : θ ∈ Set.Ioo 0 Real.pi :=
        ⟨lt_of_le_of_ne hθ.1 (fun h => hzero h.symm), lt_of_le_of_ne hθ.2 hpi⟩
      let δ : ℝ := min θ (Real.pi - θ) / 2
      have hmin : 0 < min θ (Real.pi - θ) :=
        lt_min hθopen.1 (sub_pos.mpr hθopen.2)
      have hδ : 0 < δ := div_pos hmin (by norm_num)
      have hδθ : δ < θ := by
        calc
          δ < min θ (Real.pi - θ) := div_lt_self hmin (by norm_num)
          _ ≤ θ := min_le_left _ _
      have hδpi : δ < Real.pi - θ := by
        calc
          δ < min θ (Real.pi - θ) := div_lt_self hmin (by norm_num)
          _ ≤ Real.pi - θ := min_le_right _ _
      have hinterval : Set.Icc (θ - δ) (θ + δ) ⊆ Set.Ioo 0 Real.pi :=
        Icc_subset_Ioo (by linarith) (by linarith)
      let U : Set ℂ := interior (strip (Complex.I * Real.pi))
      let DQ : ℝ → ℂ → ℂ := fun k τ =>
        (betaBoostSlice d F j (τ, θ + k) - betaBoostSlice d F j (τ, θ)) / k
      let next : ℂ → ℂ := fun τ => betaBoostSlice d F (j + 1) (τ, θ)
      have hhol : ∀ᶠ k in nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ), DifferentiableOn ℂ (DQ k) U := by
        have hevent : ∀ᶠ k : ℝ in nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ), |k| < δ := by
          have hball : ∀ᶠ k : ℝ in nhds (0 : ℝ), |k| < δ := by
            filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with k hk
            simpa [Real.dist_eq] using hk
          exact hball.filter_mono nhdsWithin_le_nhds
        filter_upwards [hevent] with k habs
        have hkIcc : θ + k ∈ Set.Icc (θ - δ) (θ + δ) := by
          obtain ⟨hkneg, hkpos⟩ := abs_lt.mp habs
          constructor <;> linarith
        have hkθ : θ + k ∈ Set.Icc 0 Real.pi :=
          Set.Ioo_subset_Icc_self (hinterval hkIcc)
        simpa only [DQ, Pi.sub_apply] using
          ((ih hkθ).sub (ih hθ)).div_const (k : ℂ)
      have hloc : TendstoLocallyUniformlyOn DQ next
          (nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ)) U := by
        rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior]
        intro K hKU hK
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hcompact : IsCompact (K ×ˢ Set.Icc (θ - δ) (θ + δ)) :=
          hK.prod isCompact_Icc
        have hsubset : K ×ˢ Set.Icc (θ - δ) (θ + δ) ⊆ stripUpper := by
          rintro ⟨τ, s⟩ ⟨hτ, hs⟩
          exact ⟨interior_subset (hKU hτ), Set.Ioo_subset_Icc_self (hinterval hs)⟩
        have hcont : ContinuousOn (betaBoostSlice d F (j + 1))
            (K ×ˢ Set.Icc (θ - δ) (θ + δ)) :=
          (continuousOn_betaBoostSlice d F (j + 1)).mono hsubset
        have huc : UniformContinuousOn (betaBoostSlice d F (j + 1))
            (K ×ˢ Set.Icc (θ - δ) (θ + δ)) :=
          hcompact.uniformContinuousOn_of_continuous hcont
        obtain ⟨ρ, hρ, hclose⟩ :=
          (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by linarith)
        have hradius : 0 < min δ ρ := lt_min hδ hρ
        have hevent : ∀ᶠ k : ℝ in nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ), |k| < min δ ρ := by
          have hball : ∀ᶠ k : ℝ in nhds (0 : ℝ), |k| < min δ ρ := by
            filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hradius] with k hk
            simpa [Real.dist_eq] using hk
          exact hball.filter_mono nhdsWithin_le_nhds
        filter_upwards [hevent, self_mem_nhdsWithin] with k habs hk0
        have hkne : k ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hk0
        have habsδ : |k| < δ := habs.trans_le (min_le_left _ _)
        have habsρ : |k| < ρ := habs.trans_le (min_le_right _ _)
        have hkIcc : θ + k ∈ Set.Icc (θ - δ) (θ + δ) := by
          obtain ⟨hkneg, hkpos⟩ := abs_lt.mp habsδ
          constructor <;> linarith
        have huIcc : [[θ, θ + k]] ⊆ Set.Icc (θ - δ) (θ + δ) :=
          uIcc_subset_Icc ⟨by linarith [hδ.le], by linarith [hδ.le]⟩ hkIcc
        intro τ hτ
        have hτstrip : τ ∈ strip (Complex.I * Real.pi) :=
          interior_subset (hKU hτ)
        have hsliceCont : ContinuousOn
            (fun s : ℝ => betaBoostSlice d F (j + 1) (τ, s)) [[θ, θ + k]] :=
          hcont.comp (Continuous.prodMk_right τ).continuousOn fun s hs =>
            ⟨hτ, huIcc hs⟩
        have hderiv : ∀ s ∈ [[θ, θ + k]],
            HasDerivAt (fun t : ℝ => betaBoostSlice d F j (τ, t))
              (betaBoostSlice d F (j + 1) (τ, s)) s := by
          intro s hs
          exact hasDerivAt_betaBoostSlice_angle d F j hτstrip
            (hinterval (huIcc hs))
        have hFTC :
            (∫ s : ℝ in θ..θ + k, betaBoostSlice d F (j + 1) (τ, s)) =
              betaBoostSlice d F j (τ, θ + k) - betaBoostSlice d F j (τ, θ) :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
            hsliceCont.intervalIntegrable
        have hconstInt : IntervalIntegrable
            (fun _s : ℝ => betaBoostSlice d F (j + 1) (τ, θ))
            MeasureTheory.volume θ (θ + k) :=
          continuousOn_const.intervalIntegrable
        have herror :
            DQ k τ - next τ =
              (∫ s : ℝ in θ..θ + k,
                (betaBoostSlice d F (j + 1) (τ, s) -
                  betaBoostSlice d F (j + 1) (τ, θ))) / k := by
          rw [intervalIntegral.integral_sub hsliceCont.intervalIntegrable hconstInt,
            hFTC, intervalIntegral.integral_const]
          simp only [DQ, next, add_sub_cancel_left, Complex.real_smul]
          field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hkne]
        have hpoint : ∀ s ∈ [[θ, θ + k]],
            ‖betaBoostSlice d F (j + 1) (τ, s) -
              betaBoostSlice d F (j + 1) (τ, θ)‖ < ε / 2 := by
          intro s hs
          have hsIcc : s ∈ Set.Icc (θ - δ) (θ + δ) := huIcc hs
          have hdist : dist (τ, s) (τ, θ) < ρ := by
            rw [dist_prod_same_left, Real.dist_eq]
            exact (abs_sub_left_of_mem_uIcc hs).trans_lt (by simpa using habsρ)
          simpa only [dist_eq_norm] using
            hclose (τ, s) ⟨hτ, hsIcc⟩ (τ, θ)
              ⟨hτ, ⟨by linarith [hδ.le], by linarith [hδ.le]⟩⟩ hdist
        have hintegral :
            ‖∫ s : ℝ in θ..θ + k,
              (betaBoostSlice d F (j + 1) (τ, s) -
                betaBoostSlice d F (j + 1) (τ, θ))‖ ≤ ε / 2 * |k| := by
          have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s hs => (hpoint s (uIoc_subset_uIcc hs)).le)
          simpa only [add_sub_cancel_left] using hbound
        have hquotient :
            ‖(∫ s : ℝ in θ..θ + k,
                (betaBoostSlice d F (j + 1) (τ, s) -
                  betaBoostSlice d F (j + 1) (τ, θ))) / k‖ < ε := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
          have hkpos : 0 < |k| := abs_pos.mpr hkne
          calc
            ‖∫ s : ℝ in θ..θ + k,
                (betaBoostSlice d F (j + 1) (τ, s) -
                  betaBoostSlice d F (j + 1) (τ, θ))‖ / |k| ≤
                (ε / 2 * |k|) / |k| :=
              (div_le_div_iff_of_pos_right hkpos).2 hintegral
            _ = ε / 2 := by field_simp [ne_of_gt hkpos]
            _ < ε := by linarith
        rw [dist_comm, dist_eq_norm, herror]
        exact hquotient
      exact hloc.differentiableOn hhol isOpen_interior

end

end MobiusCPT
