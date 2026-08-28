import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import MobiusCPT.Analysis.ParamSlice
import MobiusCPT.Analysis.Strip
import MobiusCPT.Mobius.ComplexBeta

/-!
# Joint smoothness of the complex boost

The pole-free formula for the complex boost is jointly smooth in the closed strip parameter and
the angle on the closed upper semicircle.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Definition 3.5; the complex boost as a function of the strip parameter and the circle
angle jointly. Joint smoothness in `(τ, θ)` is what makes the boost continuous, and holomorphic
inside the strip, as a curve of test functions. -/
def betaBoostJoint (d : ℕ) (F : AnalyticTestFn) : ℂ × ℝ → ℂ :=
  fun p => betaBoostVal d p.1 F (Circle.exp p.2)

/-- [T26], Definition 3.5; the closed strip together with the closed upper semicircle, the region
on which the complex boost is defined. -/
def stripUpper : Set (ℂ × ℝ) := strip (Complex.I * Real.pi) ×ˢ Set.Icc 0 Real.pi

/-- The imaginary part of `I * π` is `π`. -/
theorem im_I_mul_pi : (Complex.I * (Real.pi : ℂ)).im = Real.pi := by
  simpa only [Complex.I_mul_im, Complex.ofReal_re]

/-- [T26], Definition 3.5; membership in the closed strip `0 ≤ Im τ ≤ π`, unfolded. -/
theorem mem_strip_I_mul_pi {τ : ℂ} :
    τ ∈ strip (Complex.I * Real.pi) ↔ 0 ≤ τ.im ∧ τ.im ≤ Real.pi := by
  rw [mem_strip, im_I_mul_pi, min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le]

/-- The closed upper semicircle in the angle coordinate. -/
theorem im_circleExp_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    0 ≤ ((Circle.exp θ : Circle) : ℂ).im := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2

/-- [T26], Definition 3.1; the closed strip is convex with nonempty interior, so it determines
derivatives at each of its points. -/
theorem uniqueDiffOn_strip_I_mul_pi : UniqueDiffOn ℝ (strip (Complex.I * Real.pi)) := by
  have hstrip : strip (Complex.I * Real.pi) =
      Complex.imLm ⁻¹' Set.Icc (0 : ℝ) Real.pi := by
    ext z
    simpa only [Set.mem_preimage, Set.mem_Icc, Complex.imLm_coe] using
      (mem_strip_I_mul_pi (τ := z))
  have hconvex : Convex ℝ (strip (Complex.I * Real.pi)) := by
    rw [hstrip]
    exact (convex_Icc (0 : ℝ) Real.pi).linear_preimage Complex.imLm
  apply uniqueDiffOn_of_convex hconvex
  refine ⟨Complex.I * (Real.pi / 2 : ℝ), ?_⟩
  rw [interior_strip, im_I_mul_pi]
  simp only [Set.mem_setOf_eq, min_eq_left Real.pi_pos.le,
    max_eq_right Real.pi_pos.le, Complex.I_mul_im, Complex.ofReal_re]
  exact ⟨Real.pi_div_two_pos, half_lt_self Real.pi_pos⟩

/-- The region of the complex boost determines derivatives at each of its points. -/
theorem uniqueDiffOn_stripUpper : UniqueDiffOn ℝ stripUpper := by
  simpa only [stripUpper] using
    uniqueDiffOn_strip_I_mul_pi.prod (uniqueDiffOn_Icc Real.pi_pos)

/-- [T26], Definition 3.5; the complex boost is jointly smooth in the strip parameter and the
circle angle. All the negative powers occurring in its definition are powers of quantities that
do not vanish on this region, and the divided inverted function is read only inside the closed
unit disc, where it is smooth. -/
theorem contDiffOn_betaBoostJoint (d : ℕ) (F : AnalyticTestFn) :
    ContDiffOn ℝ ∞ (betaBoostJoint d F) stripUpper := by
  have hcircle : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => ((Circle.exp p.2 : Circle) : ℂ)) :=
    contDiff_circle_map.comp contDiff_snd
  have hhalf : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.1 / 2) :=
    contDiff_fst.div_const 2
  have hcosh : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Complex.cosh (p.1 / 2)) :=
    (Complex.contDiff_cosh.restrict_scalars ℝ).comp hhalf
  have hsinh : ContDiff ℝ ∞ (fun p : ℂ × ℝ => Complex.sinh (p.1 / 2)) :=
    (Complex.contDiff_sinh.restrict_scalars ℝ).comp hhalf
  have hP : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => cnum (-p.1) (Circle.exp p.2)) := by
    simpa only [cnum_neg] using (hcosh.mul hcircle).add hsinh
  have hQ : ContDiff ℝ ∞
      (fun p : ℂ × ℝ => cden (-p.1) (Circle.exp p.2)) := by
    simpa only [cden_neg] using (hsinh.mul hcircle).add hcosh
  have hP_ne : ∀ p ∈ stripUpper, cnum (-p.1) (Circle.exp p.2) ≠ 0 := by
    intro p hp
    change p.1 ∈ strip (Complex.I * Real.pi) ∧ p.2 ∈ Set.Icc 0 Real.pi at hp
    have hτ := mem_strip_I_mul_pi.mp hp.1
    exact cnum_neg_ne_zero_of_upper hτ.1 hτ.2 (im_circleExp_nonneg hp.2)
  have hPP_inv : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        (cnum (-p.1) (Circle.exp p.2) * cnum (-p.1) (Circle.exp p.2))⁻¹)
      stripUpper := by
    exact (hP.mul hP).contDiffOn.inv fun p hp => mul_ne_zero (hP_ne p hp) (hP_ne p hp)
  have hzpow_inv : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => (((Circle.exp p.2 : Circle) : ℂ) ^ d)⁻¹) stripUpper := by
    exact (hcircle.pow d).contDiffOn.inv fun p _ =>
      pow_ne_zero d (Circle.coe_ne_zero (Circle.exp p.2))
  have hquot : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        cden (-p.1) (Circle.exp p.2) / cnum (-p.1) (Circle.exp p.2)) stripUpper := by
    have hPinv : ContDiffOn ℝ ∞
        (fun p : ℂ × ℝ => (cnum (-p.1) (Circle.exp p.2))⁻¹) stripUpper :=
      hP.contDiffOn.inv hP_ne
    have hmul := hQ.contDiffOn.mul hPinv
    simpa only [div_eq_mul_inv] using hmul
  have hquot_maps : Set.MapsTo
      (fun p : ℂ × ℝ =>
        cden (-p.1) (Circle.exp p.2) / cnum (-p.1) (Circle.exp p.2))
      stripUpper (Metric.closedBall (0 : ℂ) 1) := by
    intro p hp
    change p.1 ∈ strip (Complex.I * Real.pi) ∧ p.2 ∈ Set.Icc 0 Real.pi at hp
    have hτ := mem_strip_I_mul_pi.mp hp.1
    exact cden_div_cnum_mem_closedBall hτ.1 hτ.2 (im_circleExp_nonneg hp.2)
  have hinvQuot : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ => F.invQuot
        (cden (-p.1) (Circle.exp p.2) / cnum (-p.1) (Circle.exp p.2))) stripUpper := by
    exact F.contDiffOn_invQuot.comp hquot hquot_maps
  have hsmooth : ContDiffOn ℝ ∞
      (fun p : ℂ × ℝ =>
        cnum (-p.1) (Circle.exp p.2) ^ d *
          (cnum (-p.1) (Circle.exp p.2) * cnum (-p.1) (Circle.exp p.2))⁻¹ *
          cden (-p.1) (Circle.exp p.2) ^ d *
          (((Circle.exp p.2 : Circle) : ℂ) *
            (((Circle.exp p.2 : Circle) : ℂ) ^ d)⁻¹) *
          F.invQuot
            (cden (-p.1) (Circle.exp p.2) / cnum (-p.1) (Circle.exp p.2)))
        stripUpper := by
    exact ((((hP.contDiffOn.pow d).mul hPP_inv).mul (hQ.contDiffOn.pow d)).mul
      (hcircle.contDiffOn.mul hzpow_inv)).mul hinvQuot
  apply hsmooth.congr
  intro p hp
  simpa only [betaBoostJoint] using betaBoostVal_eq_mul_inv d F (hP_ne p hp)

/-- [T26], Definition 3.5; for a fixed strip parameter the complex boost is smooth in the circle
angle on the closed upper semicircle. -/
theorem contDiffOn_betaBoostAngle (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => betaBoostVal d τ F (Circle.exp θ))
      (Set.Icc 0 Real.pi) := by
  have hinsert : ContDiff ℝ ∞ (fun θ : ℝ => (τ, θ)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : Set.MapsTo (fun θ : ℝ => (τ, θ)) (Set.Icc 0 Real.pi) stripUpper := by
    intro θ hθ
    exact ⟨hτ, hθ⟩
  have hcomp : ContDiffOn ℝ ∞ (betaBoostJoint d F ∘ fun θ : ℝ => (τ, θ))
      (Set.Icc 0 Real.pi) :=
    (contDiffOn_betaBoostJoint d F).comp hinsert.contDiffOn hmaps
  exact hcomp.congr fun θ _ => rfl

end

end MobiusCPT
