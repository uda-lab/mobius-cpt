import MobiusCPT.Mobius.ComplexBetaFlat
import MobiusCPT.Mobius.ComplexBetaSmooth
import MobiusCPT.TestFunctions.Support

/-!
# The complex boost as a test function

[T26], Definition 3.5 and equation (3.4).  This file promotes the pointwise complex boost on the
closed upper semicircle to an upper-supported smooth test function on the whole circle.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Definition 3.5; the prefactor of the complex boost in the circle angle, containing all
of the boost's rational dependence on the angle. -/
def betaBoostPre (d : ℕ) (τ : ℂ) : ℝ → ℂ := fun θ =>
  cnum (-τ) (Circle.exp θ) ^ d *
      (cnum (-τ) (Circle.exp θ) * cnum (-τ) (Circle.exp θ))⁻¹ *
      cden (-τ) (Circle.exp θ) ^ d *
      (((Circle.exp θ : Circle) : ℂ) * (((Circle.exp θ : Circle) : ℂ) ^ d)⁻¹)

/-- [T26], Definition 3.5; the ratio `v_{-τ}`-denominator over numerator, which the complex boost
feeds to the divided inverted function.  On the closed strip over the closed upper semicircle it
takes values in the closed unit disc, and at the endpoints `θ = 0, π` its values are `1` and `-1`,
the two points at which `F` is flat. -/
def betaBoostRatio (τ : ℂ) : ℝ → ℂ := fun θ =>
  cden (-τ) (Circle.exp θ) / cnum (-τ) (Circle.exp θ)

/-- On the closed strip and closed upper semicircle, the numerator in the boost ratio is
nonzero. -/
theorem cnum_neg_circleExp_ne_zero {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi))
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) : cnum (-τ) (Circle.exp θ) ≠ 0 := by
  have hstrip := mem_strip_I_mul_pi.mp hτ
  exact cnum_neg_ne_zero_of_upper hstrip.1 hstrip.2 (im_circleExp_nonneg hθ)

/-- [T26], Definition 3.5; in the angle coordinate the pointwise complex boost is the product of
its smooth rational prefactor and the divided inverted function evaluated at the boost ratio. -/
theorem betaBoostVal_circleExp_eq (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    betaBoostVal d τ F (Circle.exp θ) =
      betaBoostPre d τ θ * F.invQuot (betaBoostRatio τ θ) := by
  simpa only [betaBoostPre, betaBoostRatio] using
    betaBoostVal_eq_mul_inv d F (cnum_neg_circleExp_ne_zero hτ hθ)

/-- The rational prefactor of a fixed-strip-parameter complex boost is smooth on the closed angle
interval. -/
theorem contDiffOn_betaBoostPre (d : ℕ) {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    ContDiffOn ℝ ∞ (betaBoostPre d τ) (Set.Icc 0 Real.pi) := by
  have hcircle : ContDiff ℝ ∞ (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) :=
    contDiff_circle_map
  have hcosh : ContDiff ℝ ∞ (fun _ : ℝ => Complex.cosh (τ / 2)) := contDiff_const
  have hsinh : ContDiff ℝ ∞ (fun _ : ℝ => Complex.sinh (τ / 2)) := contDiff_const
  have hP : ContDiff ℝ ∞ (fun θ : ℝ => cnum (-τ) (Circle.exp θ)) := by
    simpa only [cnum_neg] using (hcosh.mul hcircle).add hsinh
  have hQ : ContDiff ℝ ∞ (fun θ : ℝ => cden (-τ) (Circle.exp θ)) := by
    simpa only [cden_neg] using (hsinh.mul hcircle).add hcosh
  have hPP_inv : ContDiffOn ℝ ∞
      (fun θ : ℝ =>
        (cnum (-τ) (Circle.exp θ) * cnum (-τ) (Circle.exp θ))⁻¹)
      (Set.Icc 0 Real.pi) := by
    exact (hP.mul hP).contDiffOn.inv fun θ hθ =>
      mul_ne_zero (cnum_neg_circleExp_ne_zero hτ hθ)
        (cnum_neg_circleExp_ne_zero hτ hθ)
  have hzpow_inv : ContDiffOn ℝ ∞
      (fun θ : ℝ => (((Circle.exp θ : Circle) : ℂ) ^ d)⁻¹)
      (Set.Icc 0 Real.pi) := by
    exact (hcircle.pow d).contDiffOn.inv fun θ _ =>
      pow_ne_zero d (Circle.coe_ne_zero (Circle.exp θ))
  exact ((((hP.contDiffOn.pow d).mul hPP_inv).mul (hQ.contDiffOn.pow d)).mul
    (hcircle.contDiffOn.mul hzpow_inv))

/-- The ratio fed to the divided inverted function is smooth on the closed angle interval for a
fixed parameter in the closed strip. -/
theorem contDiffOn_betaBoostRatio {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    ContDiffOn ℝ ∞ (betaBoostRatio τ) (Set.Icc 0 Real.pi) := by
  have hcircle : ContDiff ℝ ∞ (fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) :=
    contDiff_circle_map
  have hcosh : ContDiff ℝ ∞ (fun _ : ℝ => Complex.cosh (τ / 2)) := contDiff_const
  have hsinh : ContDiff ℝ ∞ (fun _ : ℝ => Complex.sinh (τ / 2)) := contDiff_const
  have hP : ContDiff ℝ ∞ (fun θ : ℝ => cnum (-τ) (Circle.exp θ)) := by
    simpa only [cnum_neg] using (hcosh.mul hcircle).add hsinh
  have hQ : ContDiff ℝ ∞ (fun θ : ℝ => cden (-τ) (Circle.exp θ)) := by
    simpa only [cden_neg] using (hsinh.mul hcircle).add hcosh
  have hPinv : ContDiffOn ℝ ∞
      (fun θ : ℝ => (cnum (-τ) (Circle.exp θ))⁻¹) (Set.Icc 0 Real.pi) :=
    hP.contDiffOn.inv fun θ hθ => cnum_neg_circleExp_ne_zero hτ hθ
  have hmul : ContDiffOn ℝ ∞
      (fun θ : ℝ => cden (-τ) (Circle.exp θ) * (cnum (-τ) (Circle.exp θ))⁻¹)
      (Set.Icc 0 Real.pi) := hQ.contDiffOn.mul hPinv
  refine hmul.congr fun θ _ => ?_
  rw [betaBoostRatio, div_eq_mul_inv]

/-- The boost ratio maps the closed upper-semicircle angle interval into the closed unit disc. -/
theorem mapsTo_betaBoostRatio {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    Set.MapsTo (betaBoostRatio τ) (Set.Icc 0 Real.pi) (Metric.closedBall (0 : ℂ) 1) := by
  intro θ hθ
  have hstrip := mem_strip_I_mul_pi.mp hτ
  exact cden_div_cnum_mem_closedBall hstrip.1 hstrip.2 (im_circleExp_nonneg hθ)

/-- [T26], §3; the complex boost fixes the endpoint `z = 1` of `I_+`. -/
theorem betaBoostRatio_zero (τ : ℂ) : betaBoostRatio τ 0 = 1 := by
  apply cden_div_cnum_of_coe_eq_one
  simp

/-- [T26], §3; the complex boost fixes the endpoint `z = -1` of `I_+`. -/
theorem betaBoostRatio_pi (τ : ℂ) : betaBoostRatio τ Real.pi = -1 := by
  apply cden_div_cnum_of_coe_eq_neg_one
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

private theorem uniqueDiffOn_closedBall_zero_one :
    UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) := by
  apply uniqueDiffOn_of_convex (convex_closedBall (0 : ℂ) 1)
  refine ⟨0, ?_⟩
  exact (interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball)
    (Metric.mem_ball_self one_pos)

/-- [T26], Definition 3.5; the complex boost vanishes to infinite order at the endpoints of `I_+`.
The boost fixes `±1` and `F` is flat there ([T26], Definition 3.2), so the flatness passes through
the divided inverted function and survives multiplication by the smooth prefactor.  This is the
statement that keeps `β_d(v_τ)F|_{I_+}` inside `C_0^∞(I_+)`. -/
theorem iteratedDerivWithin_betaBoostVal_circleExp_zero (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) (j : ℕ) :
    iteratedDerivWithin j (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
      (Set.Icc 0 Real.pi) 0 = 0 := by
  have hs : UniqueDiffOn ℝ (Set.Icc 0 Real.pi) := uniqueDiffOn_Icc Real.pi_pos
  have hx : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hcomp : ContDiffOn ℝ ∞ (F.invQuot ∘ betaBoostRatio τ) (Set.Icc 0 Real.pi) :=
    F.contDiffOn_invQuot.comp (contDiffOn_betaBoostRatio hτ) (mapsTo_betaBoostRatio hτ)
  have hcompflat : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i (F.invQuot ∘ betaBoostRatio τ)
        (Set.Icc 0 Real.pi) 0 = 0 := by
    intro i
    apply iteratedFDerivWithin_comp_eq_zero_of_flat
      (g := F.invQuot) (t := Metric.closedBall (0 : ℂ) 1)
      (f := betaBoostRatio τ) (s := Set.Icc 0 Real.pi) (x := (0 : ℝ))
      F.contDiffOn_invQuot (contDiffOn_betaBoostRatio hτ)
      uniqueDiffOn_closedBall_zero_one hs (mapsTo_betaBoostRatio hτ) hx
    intro n
    rw [betaBoostRatio_zero]
    exact F.iteratedFDerivWithin_invQuot_one n
  have hmulflat : iteratedFDerivWithin ℝ j
      (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
      (Set.Icc 0 Real.pi) 0 = 0 :=
    iteratedFDerivWithin_mul_eq_zero_of_flat (contDiffOn_betaBoostPre d hτ) hcomp hs hx
      hcompflat j
  have heq : Set.EqOn
      (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
      (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
      (Set.Icc 0 Real.pi) := by
    intro θ hθ
    simpa only [Function.comp_apply] using betaBoostVal_circleExp_eq d F hτ hθ
  apply iteratedDerivWithin_eq_zero_of_iteratedFDerivWithin_eq_zero
  calc
    iteratedFDerivWithin ℝ j (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
        (Set.Icc 0 Real.pi) 0 =
        iteratedFDerivWithin ℝ j
          (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
          (Set.Icc 0 Real.pi) 0 := iteratedFDerivWithin_congr heq hx j
    _ = 0 := hmulflat

/-- [T26], Definition 3.5; every within derivative of the angle formula vanishes at the right
endpoint of the closed upper semicircle. -/
theorem iteratedDerivWithin_betaBoostVal_circleExp_pi (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) (j : ℕ) :
    iteratedDerivWithin j (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
      (Set.Icc 0 Real.pi) Real.pi = 0 := by
  have hs : UniqueDiffOn ℝ (Set.Icc 0 Real.pi) := uniqueDiffOn_Icc Real.pi_pos
  have hx : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
  have hcomp : ContDiffOn ℝ ∞ (F.invQuot ∘ betaBoostRatio τ) (Set.Icc 0 Real.pi) :=
    F.contDiffOn_invQuot.comp (contDiffOn_betaBoostRatio hτ) (mapsTo_betaBoostRatio hτ)
  have hcompflat : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i (F.invQuot ∘ betaBoostRatio τ)
        (Set.Icc 0 Real.pi) Real.pi = 0 := by
    intro i
    apply iteratedFDerivWithin_comp_eq_zero_of_flat
      (g := F.invQuot) (t := Metric.closedBall (0 : ℂ) 1)
      (f := betaBoostRatio τ) (s := Set.Icc 0 Real.pi) (x := Real.pi)
      F.contDiffOn_invQuot (contDiffOn_betaBoostRatio hτ)
      uniqueDiffOn_closedBall_zero_one hs (mapsTo_betaBoostRatio hτ) hx
    intro n
    rw [betaBoostRatio_pi]
    exact F.iteratedFDerivWithin_invQuot_neg_one n
  have hmulflat : iteratedFDerivWithin ℝ j
      (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
      (Set.Icc 0 Real.pi) Real.pi = 0 :=
    iteratedFDerivWithin_mul_eq_zero_of_flat (contDiffOn_betaBoostPre d hτ) hcomp hs hx
      hcompflat j
  have heq : Set.EqOn
      (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
      (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
      (Set.Icc 0 Real.pi) := by
    intro θ hθ
    simpa only [Function.comp_apply] using betaBoostVal_circleExp_eq d F hτ hθ
  apply iteratedDerivWithin_eq_zero_of_iteratedFDerivWithin_eq_zero
  calc
    iteratedFDerivWithin ℝ j (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
        (Set.Icc 0 Real.pi) Real.pi =
        iteratedFDerivWithin ℝ j
          (fun θ : ℝ => betaBoostPre d τ θ * (F.invQuot ∘ betaBoostRatio τ) θ)
          (Set.Icc 0 Real.pi) Real.pi := iteratedFDerivWithin_congr heq hx j
    _ = 0 := hmulflat

/-- [T26], Definition 3.5; the angle formula vanishes at the endpoint `θ = 0`. -/
theorem betaBoostVal_circleExp_zero (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) : betaBoostVal d τ F (Circle.exp 0) = 0 := by
  rw [betaBoostVal_circleExp_eq d F hτ ⟨le_rfl, Real.pi_pos.le⟩,
    betaBoostRatio_zero, F.invQuot_one, mul_zero]

/-- [T26], Definition 3.5; the angle formula vanishes at the endpoint `θ = π`. -/
theorem betaBoostVal_circleExp_pi (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    betaBoostVal d τ F (Circle.exp Real.pi) = 0 := by
  rw [betaBoostVal_circleExp_eq d F hτ ⟨Real.pi_pos.le, le_rfl⟩,
    betaBoostRatio_pi, F.invQuot_neg_one, mul_zero]

/-- [T26], Definition 3.5; the complex boost read on the whole circle: the value on the closed
upper semicircle, zero on the rest.  It is smooth because the value is smooth on the closed
semicircle and flat at both endpoints. -/
def betaBoostCut (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) : ℝ → ℂ :=
  zeroExtendIcc 0 Real.pi (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))

/-- The zero extension of the endpoint-flat complex boost angle formula is smooth on the real
line. -/
theorem contDiff_betaBoostCut (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) : ContDiff ℝ ∞ (betaBoostCut d τ F) := by
  exact contDiff_zeroExtend_of_flat_contDiffOn Real.pi_pos
    (contDiffOn_betaBoostAngle d F hτ)
    (iteratedDerivWithin_betaBoostVal_circleExp_zero d F hτ)
    (iteratedDerivWithin_betaBoostVal_circleExp_pi d F hτ)

/-- The zero-extended complex boost angle formula is upper-flat. -/
theorem isUpperFlat_betaBoostCut (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) : IsUpperFlat (betaBoostCut d τ F) := by
  refine ⟨contDiff_betaBoostCut d F hτ, ?_⟩
  intro θ hθ
  by_cases hIcc : θ ∈ Set.Icc 0 Real.pi
  · by_cases hzero : θ = 0
    · subst θ
      rw [betaBoostCut, zeroExtend_eq_of_mem _ ⟨le_rfl, Real.pi_pos.le⟩]
      exact betaBoostVal_circleExp_zero d F hτ
    · have hpos : 0 < θ := lt_of_le_of_ne hIcc.1 (Ne.symm hzero)
      have hpi : θ = Real.pi := by
        apply le_antisymm hIcc.2
        apply le_of_not_gt
        intro hlt
        exact hθ ⟨hpos, hlt⟩
      subst θ
      rw [betaBoostCut, zeroExtend_eq_of_mem _ ⟨Real.pi_pos.le, le_rfl⟩]
      exact betaBoostVal_circleExp_pi d F hτ
  · exact zeroExtend_eq_zero_of_notMem _ hIcc

/-- [T26], Definition 3.5, equation (3.4); the complexified conformal action
`β_d(v_τ)F|_{I_+}` as an element of `C_0^∞(I_+) ⊆ C^∞(S¹)`, for `τ` in the closed strip
`0 ≤ Im τ ≤ π`.  Off the strip the source says nothing and the value is `0`, which no statement
below appeals to. -/
noncomputable def betaBoost (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) : TestFn :=
  open Classical in
  if hτ : τ ∈ strip (Complex.I * Real.pi) then
    Classical.choose (exists_suppUpper_toAngle_eq_periodize (isUpperFlat_betaBoostCut d F hτ))
  else 0

/-- On the closed strip, the angle representative of the complex boost is the periodisation of
its zero-extended upper-semicircle formula. -/
theorem toAngle_betaBoost (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    toAngle (betaBoost d τ F) = periodize (2 * Real.pi) (betaBoostCut d τ F) := by
  rw [betaBoost, dif_pos hτ]
  exact (Classical.choose_spec
    (exists_suppUpper_toAngle_eq_periodize (isUpperFlat_betaBoostCut d F hτ))).1

/-- [T26], Definition 3.5; the complex boost is supported in the upper semicircle, so it lies in
`C_0^∞(I_+)`. -/
theorem suppUpper_betaBoost (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) :
    SuppUpper (betaBoost d τ F) := by
  by_cases hτ : τ ∈ strip (Complex.I * Real.pi)
  · rw [betaBoost, dif_pos hτ]
    exact (Classical.choose_spec
      (exists_suppUpper_toAngle_eq_periodize (isUpperFlat_betaBoostCut d F hτ))).2
  · rw [betaBoost, dif_neg hτ]
    exact suppUpper_zero

/-- [T26], Definition 3.5; on the closed upper semicircle the complex boost takes the value of the
pointwise formula. -/
theorem betaBoost_apply_circleExp (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    betaBoost d τ F (Circle.exp θ) = betaBoostVal d τ F (Circle.exp θ) := by
  change toAngle (betaBoost d τ F) θ = betaBoostVal d τ F (Circle.exp θ)
  rw [toAngle_betaBoost d F hτ]
  have hθco : θ ∈ Set.Ico 0 (2 * Real.pi) := by
    exact ⟨hθ.1, hθ.2.trans_lt (by linarith [Real.pi_pos])⟩
  rw [periodize_eq_self Real.two_pi_pos hθco]
  exact zeroExtend_eq_of_mem _ hθ

end

end MobiusCPT
