import MobiusCPT.Mobius.ComplexBetaHoloSlice
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Lemma 3.6; the derivative in the strip parameter of the `j`-th angle derivative of the
complex boost, read off the joint Fréchet derivative in the parameter direction.  Taking it in
this form is what makes it jointly continuous: joint smoothness of the slice derivatives gives
continuity of the joint Fréchet derivative, and evaluation at a fixed direction is continuous
linear. -/
def betaBoostSliceDot (d : ℕ) (F : AnalyticTestFn) (j : ℕ) : ℂ × ℝ → ℂ := fun p =>
  fderivWithin ℝ (betaBoostSlice d F j) stripUpper p (1, 0)

/-- [T26], Lemma 3.6; the parameter derivative of every angle derivative is jointly continuous on
the closed strip over the closed upper semicircle. -/
theorem continuousOn_betaBoostSliceDot (d : ℕ) (F : AnalyticTestFn) (j : ℕ) :
    ContinuousOn (betaBoostSliceDot d F j) stripUpper := by
  have hcont : ContinuousOn (fderivWithin ℝ (betaBoostSlice d F j) stripUpper) stripUpper := by
    simpa only [betaBoostSlice] using
      (contDiffOn_sliceDeriv uniqueDiffOn_stripUpper (contDiffOn_betaBoostJoint d F) j).continuousOn_fderivWithin
        uniqueDiffOn_stripUpper (by simp)
  have hev : Continuous
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℂ), (0 : ℝ))) :=
    ContinuousLinearMap.continuous _
  have hcomp := hev.comp_continuousOn hcont
  refine hcomp.congr fun p hp => ?_
  rfl

/-- [T26], Lemma 3.6; at an interior parameter the joint directional derivative is the complex
derivative of the parameter slice.  The slice is complex differentiable by
`differentiableOn_betaBoostSlice`, so its real Fréchet derivative is complex linear and evaluating
it at `1` returns the complex derivative. -/
theorem hasDerivAt_betaBoostSlice (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    HasDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
      (betaBoostSliceDot d F j (τ, θ)) τ := by
  have hdiffAt : DifferentiableAt ℂ
      (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) τ := by
    apply (differentiableOn_betaBoostSlice d F j hθ).differentiableAt
    exact isOpen_interior.mem_nhds hτ
  let g' : ℂ := deriv (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) τ
  have hg' : HasDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) g' τ := by
    simpa only [g'] using hdiffAt.hasDerivAt
  have hgC : HasFDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) g') τ := by
    simpa only [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hg'.hasFDerivAt
  have hgR : HasFDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) g').restrictScalars ℝ) τ :=
    hgC.restrictScalars ℝ
  have hgfderiv :
      fderiv ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) τ (1 : ℂ) = g' := by
    rw [hgR.fderiv]
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
  have hjoint : DifferentiableOn ℝ (betaBoostSlice d F j) stripUpper := by
    simpa only [betaBoostSlice] using
      (contDiffOn_sliceDeriv uniqueDiffOn_stripUpper (contDiffOn_betaBoostJoint d F) j).differentiableOn
        (by simp)
  have hpoint : (τ, θ) ∈ stripUpper := by
    exact ⟨interior_subset hτ, hθ⟩
  have hjointAt : DifferentiableWithinAt ℝ (betaBoostSlice d F j)
      stripUpper (τ, θ) := hjoint (τ, θ) hpoint
  have hinsert : HasFDerivAt (fun σ : ℂ => (σ, θ))
      (ContinuousLinearMap.inl ℝ ℂ ℝ) τ :=
    hasFDerivAt_prodMk_left τ θ
  have hmaps : MapsTo (fun σ : ℂ => (σ, θ))
      (strip (Complex.I * Real.pi)) stripUpper := by
    intro σ hσ
    exact ⟨hσ, hθ⟩
  have hjointWithin :
      HasFDerivWithinAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
        ((fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, θ)).comp
          (ContinuousLinearMap.inl ℝ ℂ ℝ))
        (strip (Complex.I * Real.pi)) τ := by
    exact hjointAt.hasFDerivWithinAt.comp τ hinsert.hasFDerivWithinAt hmaps
  have hstrip : strip (Complex.I * Real.pi) ∈ 𝓝 τ := by
    exact mem_of_superset (isOpen_interior.mem_nhds hτ) interior_subset
  have hjointAt' :
      HasFDerivAt (fun σ : ℂ => betaBoostSlice d F j (σ, θ))
        ((fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, θ)).comp
          (ContinuousLinearMap.inl ℝ ℂ ℝ)) τ :=
    hjointWithin.hasFDerivAt hstrip
  have hderiv_eq : g' =
      fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, θ) ((1 : ℂ), (0 : ℝ)) := by
    calc
      g' = fderiv ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) τ (1 : ℂ) :=
        hgfderiv.symm
      _ = ((fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, θ)).comp
          (ContinuousLinearMap.inl ℝ ℂ ℝ)) (1 : ℂ) := by
        rw [hjointAt'.fderiv]
      _ = fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, θ) ((1 : ℂ), (0 : ℝ)) := by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  apply hg'.congr_deriv
  simpa only [betaBoostSliceDot] using hderiv_eq

/-- [T26], Lemma 3.6; at an interior parameter the ordinary complex derivative of the parameter
slice is the joint directional derivative `betaBoostSliceDot`. -/
theorem deriv_betaBoostSlice (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    deriv (fun σ : ℂ => betaBoostSlice d F j (σ, θ)) τ = betaBoostSliceDot d F j (τ, θ) := by
  exact (hasDerivAt_betaBoostSlice d F j hτ hθ).deriv

/-- [T26], Definition 3.5; at the endpoints of `I_+` every angle derivative of the boost is
identically zero in the parameter, hence so is its parameter derivative. -/
theorem betaBoostSliceDot_eq_zero_of_endpoint (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ interior (strip (Complex.I * Real.pi))) {θ : ℝ}
    (hθ : θ = 0 ∨ θ = Real.pi) :
    betaBoostSliceDot d F j (τ, θ) = 0 := by
  have hstrip : strip (Complex.I * Real.pi) ∈ 𝓝 τ := by
    exact mem_of_superset (isOpen_interior.mem_nhds hτ) interior_subset
  rcases hθ with rfl | rfl
  · have hzero : ∀ σ ∈ strip (Complex.I * Real.pi),
        betaBoostSlice d F j (σ, 0) = 0 := by
      intro σ hσ
      rw [betaBoostSlice_eq d F j hσ ⟨le_rfl, Real.pi_pos.le⟩]
      exact iteratedDerivWithin_betaBoostVal_circleExp_zero d F hσ j
    have hev : (fun σ : ℂ => betaBoostSlice d F j (σ, 0)) =ᶠ[𝓝 τ]
        (0 : ℂ → ℂ) := by
      filter_upwards [hstrip] with σ hσ
      simpa using hzero σ hσ
    calc
      betaBoostSliceDot d F j (τ, 0) =
          deriv (fun σ : ℂ => betaBoostSlice d F j (σ, 0)) τ :=
        (deriv_betaBoostSlice d F j hτ ⟨le_rfl, Real.pi_pos.le⟩).symm
      _ = deriv (0 : ℂ → ℂ) τ := hev.deriv_eq
      _ = 0 := by simpa using (deriv_const τ (0 : ℂ))
  · have hzero : ∀ σ ∈ strip (Complex.I * Real.pi),
        betaBoostSlice d F j (σ, Real.pi) = 0 := by
      intro σ hσ
      rw [betaBoostSlice_eq d F j hσ ⟨Real.pi_pos.le, le_rfl⟩]
      exact iteratedDerivWithin_betaBoostVal_circleExp_pi d F hσ j
    have hev : (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi)) =ᶠ[𝓝 τ]
        (0 : ℂ → ℂ) := by
      filter_upwards [hstrip] with σ hσ
      simpa using hzero σ hσ
    calc
      betaBoostSliceDot d F j (τ, Real.pi) =
          deriv (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi)) τ :=
        (deriv_betaBoostSlice d F j hτ ⟨Real.pi_pos.le, le_rfl⟩).symm
      _ = deriv (0 : ℂ → ℂ) τ := hev.deriv_eq
      _ = 0 := by simpa using (deriv_const τ (0 : ℂ))

end

end MobiusCPT
