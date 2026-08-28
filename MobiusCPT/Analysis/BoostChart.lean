import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import MobiusCPT.Mobius.ComplexBoost

/-!
# The analytic boost chart

This file gives the Cayley-coordinate chart used for the analytic continuation in [T26], §3.
The logarithm is taken on the branch whose cut is the real segment `[-1, 1]`.
-/

namespace MobiusCPT

noncomputable section

open Set
open scoped ContDiff

/-- [T26], §3; the Cayley coordinate `ζ(z) = (1 + z)/(1 - z)`, which carries the unit circle to
the imaginary axis and the closed exterior to the closed left half-plane. -/
def cayley (z : ℂ) : ℂ := (1 + z) / (1 - z)

/-- [T26], §3; in the Cayley coordinate the boost is the dilation by `e^τ`. -/
theorem cayley_vApply_neg (τ z : ℂ) (hz : z ≠ 1) (hden : cden (-τ) z ≠ 0) :
    cayley (vApply (-τ) z) = Complex.exp τ * cayley z := by
  have hden' : Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2) ≠ 0 := by
    simpa [cden_neg] using hden
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hsum : Complex.cosh (τ / 2) + Complex.sinh (τ / 2) = Complex.exp (τ / 2) :=
    Complex.cosh_add_sinh _
  have hdiff : Complex.cosh (τ / 2) - Complex.sinh (τ / 2) = Complex.exp (-(τ / 2)) :=
    Complex.cosh_sub_sinh _
  have hdiff_ne : Complex.cosh (τ / 2) - Complex.sinh (τ / 2) ≠ 0 := by
    rw [hdiff]; exact Complex.exp_ne_zero _
  have hexp : Complex.exp τ =
      (Complex.cosh (τ / 2) + Complex.sinh (τ / 2)) /
        (Complex.cosh (τ / 2) - Complex.sinh (τ / 2)) := by
    rw [hsum, hdiff, ← Complex.exp_sub]
    congr 1
    ring
  -- `(A/D)/(B/D) = A/B`, the only division identity the computation needs.
  have hquot : ∀ A B D : ℂ, D ≠ 0 → B ≠ 0 → A / D / (B / D) = A / B := by
    intro A B D hD hB
    field_simp
  have hnum1 : 1 + (Complex.cosh (τ / 2) * z + Complex.sinh (τ / 2)) /
        (Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2)) =
      (Complex.cosh (τ / 2) + Complex.sinh (τ / 2)) * (1 + z) /
        (Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2)) := by
    rw [eq_div_iff hden', add_mul, one_mul, div_mul_cancel₀ _ hden']
    ring
  have hden1 : 1 - (Complex.cosh (τ / 2) * z + Complex.sinh (τ / 2)) /
        (Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2)) =
      (Complex.cosh (τ / 2) - Complex.sinh (τ / 2)) * (1 - z) /
        (Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2)) := by
    rw [eq_div_iff hden', sub_mul, one_mul, div_mul_cancel₀ _ hden']
    ring
  have hBne : (Complex.cosh (τ / 2) - Complex.sinh (τ / 2)) * (1 - z) ≠ 0 :=
    mul_ne_zero hdiff_ne h1z
  rw [cayley, vApply, cnum_neg, cden_neg, hnum1, hden1,
    hquot _ _ _ hden' hBne, hexp, cayley, div_mul_div_comm]

/-- The real and imaginary parts of the Cayley coordinate, with the denominator written as a
real norm square. -/
theorem cayley_re_formula (z : ℂ) :
    (cayley z).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
  simp [cayley, Complex.div_re, Complex.normSq_apply, Complex.sq_norm]
  ring

/-- The imaginary part of the Cayley coordinate, with the denominator written as a real norm
square. -/
theorem cayley_im_formula (z : ℂ) :
    (cayley z).im = 2 * z.im / ‖1 - z‖ ^ 2 := by
  simp [cayley, Complex.div_im, Complex.normSq_apply, Complex.sq_norm]
  ring

/-- [T26], §3; the branch cut of the boost coordinate is the real segment `[-1, 1]`. -/
def cutSegment : Set ℂ := {z : ℂ | z.im = 0 ∧ -1 ≤ z.re ∧ z.re ≤ 1}

/-- An exterior point on the cut can only be one of the two endpoints. -/
theorem notMem_cutSegment_of_one_le_norm {z : ℂ} (h : 1 ≤ ‖z‖) (h1 : z ≠ 1)
    (h2 : z ≠ -1) : z ∉ cutSegment := by
  intro hz
  rcases hz with ⟨hzim, hzlo, hzhi⟩
  have hnormsq : ‖z‖ ^ 2 = z.re ^ 2 := by
    have h := Complex.sq_norm_sub_sq_im z
    rw [hzim] at h
    simpa using h
  have hzre_sq_le : z.re ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - z.re) * (1 + z.re) :=
      mul_nonneg (sub_nonneg.mpr hzhi) (by linarith)
    nlinarith [hprod]
  have hzre_sq_one : z.re ^ 2 = 1 := by
    have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have hnormsq_one : 1 ≤ ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - 1)]
    nlinarith [hnormsq, hnormsq_one, hzre_sq_le]
  have hzre : z.re = 1 ∨ z.re = -1 := sq_eq_one_iff.mp hzre_sq_one
  rcases hzre with hzre | hzre
  · apply h1
    apply Complex.ext
    · simpa using hzre
    · simpa using hzim
  · apply h2
    apply Complex.ext
    · simpa using hzre
    · simpa using hzim

/-- The negative Cayley coordinate avoids the closed negative real axis exactly off the cut. -/
theorem neg_cayley_mem_slitPlane {z : ℂ} (hz : z ∉ cutSegment) :
    -cayley z ∈ Complex.slitPlane := by
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hz
    rw [hz1]
    norm_num [cutSegment]
  have hden : 0 < ‖1 - z‖ ^ 2 := by
    have hne : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz1.symm
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (-cayley z).im ≠ 0
  · exact Or.inr him
  by_cases hpos : 0 < (-cayley z).re
  · exact Or.inl hpos
  have hzim : z.im = 0 := by
    have hcim' : (-cayley z).im = 0 := Classical.not_not.mp him
    have hcim : (cayley z).im = 0 := by simpa using hcim'
    rw [cayley_im_formula] at hcim
    have hnum : 2 * z.im = 0 :=
      (div_eq_zero_iff.mp hcim).resolve_right (ne_of_gt hden)
    linarith
  have hcre : 0 ≤ (cayley z).re := by
    have hneg_re : (-cayley z).re ≤ 0 := le_of_not_gt hpos
    simpa using hneg_re
  rw [cayley_re_formula] at hcre
  have hnormsq : ‖z‖ ^ 2 ≤ 1 := by
    have hmul := (le_div_iff₀ hden).mp hcre
    linarith
  have hzre_sq : z.re ^ 2 ≤ 1 := by
    have h := Complex.sq_norm_sub_sq_im z
    rw [hzim] at h
    nlinarith
  have hzre : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.re + 1)]
  exact (hz ⟨hzim, hzre.1, hzre.2⟩).elim

/-- [T26], §3; the logarithmic boost coordinate is analytic away from its branch cut. -/
def boostCoord (z : ℂ) : ℂ := Complex.log (-cayley z) + Complex.I * (Real.pi / 2)

/-- The boost coordinate is holomorphic at every point off the branch cut. -/
theorem analyticAt_boostCoord {z : ℂ} (hz : z ∉ cutSegment) :
    AnalyticAt ℂ boostCoord z := by
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hz
    rw [hz1]
    norm_num [cutSegment]
  have hnum : AnalyticAt ℂ (fun w : ℂ => 1 + w) z := analyticAt_const.add analyticAt_id
  have hden : AnalyticAt ℂ (fun w : ℂ => 1 - w) z := analyticAt_const.sub analyticAt_id
  have hcay : AnalyticAt ℂ cayley z :=
    hnum.fun_div hden (sub_ne_zero.mpr hz1.symm)
  have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (-cayley w)) z :=
    (hcay.neg).clog (neg_cayley_mem_slitPlane hz)
  exact hlog.add analyticAt_const

/-- Exponentiating the boost coordinate recovers the rotated Cayley coordinate. -/
theorem exp_boostCoord {z : ℂ} (hz : z ∉ cutSegment) :
    Complex.exp (boostCoord z) = -Complex.I * cayley z := by
  have hslit := neg_cayley_mem_slitPlane hz
  calc
    Complex.exp (boostCoord z) =
        Complex.exp (Complex.log (-cayley z)) *
          Complex.exp (Complex.I * (Real.pi / 2)) := by
            rw [boostCoord, Complex.exp_add]
    _ = (-cayley z) * Complex.I := by
      rw [Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
      rw [show Complex.I * (Real.pi / 2) = (Real.pi / 2 : ℂ) * Complex.I by
        push_cast
        ring, Complex.exp_pi_div_two_mul_I]
    _ = -Complex.I * cayley z := by ring

/-- The real part of the boost coordinate is the logarithm of the Cayley radial ratio. -/
theorem re_boostCoord {z : ℂ} (hz : z ∉ cutSegment) :
    (boostCoord z).re = Real.log (‖1 + z‖ / ‖1 - z‖) := by
  simp [boostCoord, cayley, Complex.log_re, Complex.norm_div]

/-- Exponential decay at the `z = -1` end becomes the reciprocal radial ratio. -/
theorem exp_neg_re_boostCoord {z : ℂ} (hz : z ∉ cutSegment) (h1 : z ≠ -1) :
    Real.exp (-(boostCoord z).re) = ‖1 - z‖ / ‖1 + z‖ := by
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hz
    rw [hz1]
    norm_num [cutSegment]
  have hminus : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  have hplus_ne : (1 : ℂ) ≠ -z := by
    intro h
    apply h1
    simpa using (congrArg Neg.neg h).symm
  have hplus : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    simpa [sub_eq_add_neg] using (sub_ne_zero.mpr hplus_ne)
  rw [re_boostCoord hz, Real.exp_neg, Real.exp_log (div_pos hplus hminus), inv_div]

/-- Exponentiating the real part of the boost coordinate gives the radial ratio. -/
theorem exp_re_boostCoord {z : ℂ} (hz : z ∉ cutSegment) :
    Real.exp ((boostCoord z).re) = ‖1 + z‖ / ‖1 - z‖ := by
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hz
    rw [hz1]
    norm_num [cutSegment]
  have hminus : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  have hplus : 0 < ‖1 + z‖ := by
    have hne : (1 : ℂ) + z ≠ 0 := by
      intro h
      have h' : z = -1 := by
        have hreal : 1 + z.re = 0 := by
          simpa using congrArg Complex.re h
        have himag : z.im = 0 := by
          simpa using congrArg Complex.im h
        apply Complex.ext
        · simp only [Complex.neg_re, Complex.one_re]
          linarith
        · simpa using himag
      apply hz
      rw [h']
      norm_num [cutSegment]
    exact norm_pos_iff.mpr hne
  rw [re_boostCoord hz, Real.exp_log (div_pos hplus hminus)]

/-- A crude global bound for the imaginary part of the boost coordinate. -/
theorem abs_im_boostCoord_le (z : ℂ) : |(boostCoord z).im| ≤ 3 * Real.pi / 2 := by
  have hlo := Complex.neg_pi_lt_log_im (-cayley z)
  have hhi := Complex.log_im_le_pi (-cayley z)
  have him : (boostCoord z).im = (Complex.log (-cayley z)).im + Real.pi / 2 := by
    simp [boostCoord, Complex.add_im, Complex.mul_im]
  rw [him, abs_le]
  constructor <;> linarith [Real.pi_pos]

/-- [T26], §3; the boost coordinate of a point of the open upper semicircle. -/
noncomputable def angleToBoost (θ : ℝ) : ℝ :=
  Real.log (Real.cos (θ / 2) / Real.sin (θ / 2))

/-- [T26], §3; the inverse parametrisation of `I_+` by the boost coordinate. -/
noncomputable def boostToAngle (x : ℝ) : ℝ := 2 * Real.arctan (Real.exp (-x))

/-- The half-angle sine is positive on the upper semicircle. -/
theorem sin_half_angle_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < Real.sin (θ / 2) := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith [Real.pi_pos]

/-- The half-angle cosine is positive on the upper semicircle. -/
theorem cos_half_angle_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < Real.cos (θ / 2) := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

/-- The negative half-angle cosine is positive on the lower semicircle. -/
theorem neg_cos_half_angle_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi)) :
    0 < -Real.cos (θ / 2) := by
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hhalf : Real.pi / 2 < θ / 2 := by linarith
  have hhalf' : θ / 2 < Real.pi + Real.pi / 2 := by linarith
  exact neg_pos.mpr (Real.cos_neg_of_pi_div_two_lt_of_lt hhalf hhalf')

/-- The inverse boost parametrisation takes every real number into the open upper semicircle. -/
theorem boostToAngle_mem_Ioo (x : ℝ) : boostToAngle x ∈ Set.Ioo 0 Real.pi := by
  unfold boostToAngle
  constructor
  · nlinarith [Real.arctan_pos.mpr (Real.exp_pos (-x))]
  · nlinarith [Real.arctan_lt_pi_div_two (Real.exp (-x)), Real.pi_pos]

/-- A mirrored form of the inverse parametrisation, useful at the opposite end of the strip. -/
theorem boostToAngle_eq_pi_sub (x : ℝ) :
    boostToAngle x = Real.pi - 2 * Real.arctan (Real.exp x) := by
  rw [boostToAngle, Real.exp_neg, Real.arctan_inv_of_pos (Real.exp_pos x)]
  ring

/-- The inverse boost parametrisation is smooth to all orders. -/
theorem contDiff_boostToAngle : ContDiff ℝ ∞ boostToAngle := by
  have h : ContDiff ℝ ∞ fun y : ℝ => Real.arctan (Real.exp (-y)) :=
    Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_neg)
  exact contDiff_const.mul h

/-- The derivative of the inverse boost parametrisation is `-1 / cosh x`. -/
theorem hasDerivAt_boostToAngle (x : ℝ) :
    HasDerivAt boostToAngle (-(Real.cosh x)⁻¹) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_neg' x).exp
  have hatan : HasDerivAt (fun y : ℝ => Real.arctan (Real.exp (-y)))
      (1 / (1 + Real.exp (-x) ^ 2) * -Real.exp (-x)) x := hexp.arctan
  have hval : 2 * (1 / (1 + Real.exp (-x) ^ 2) * -Real.exp (-x)) = -(Real.cosh x)⁻¹ := by
    have hx : Real.exp (-x) ≠ 0 := (Real.exp_pos _).ne'
    have hsum : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
    have hmul : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    have key : (1 : ℝ) + Real.exp (-x) ^ 2 = Real.exp (-x) * (Real.exp x + Real.exp (-x)) := by
      rw [mul_add, hmul]
      ring
    rw [Real.cosh_eq, key]
    field_simp
  have hscaled := hatan.const_mul (2 : ℝ)
  rw [hval] at hscaled
  exact hscaled

/-- The sine of the inverse-parametrised angle is positive. -/
theorem sin_boostToAngle_pos (x : ℝ) : 0 < Real.sin (boostToAngle x) := by
  exact Real.sin_pos_of_mem_Ioo (boostToAngle_mem_Ioo x)

/-- The half-angle sine at the inverse-parametrised upper semicircle is positive. -/
theorem sin_half_boostToAngle_pos (x : ℝ) :
    0 < Real.sin (boostToAngle x / 2) := by
  exact sin_half_angle_pos (boostToAngle_mem_Ioo x)

/-- The upper-circle angle coordinate recovers the original real boost coordinate. -/
theorem angleToBoost_boostToAngle (x : ℝ) : angleToBoost (boostToAngle x) = x := by
  have hr : 0 < Real.exp (-x) := Real.exp_pos _
  have hsqrt : 0 < Real.sqrt (1 + Real.exp (-x) ^ 2) := by positivity
  have hratio :
      (1 / Real.sqrt (1 + Real.exp (-x) ^ 2)) /
          (Real.exp (-x) / Real.sqrt (1 + Real.exp (-x) ^ 2)) =
        (Real.exp (-x))⁻¹ := by
    field_simp [hr.ne', hsqrt.ne']
  have hxinverse : (Real.exp (-x))⁻¹ = Real.exp x := by
    rw [Real.exp_neg]
    simp
  rw [angleToBoost, boostToAngle]
  have hhalf : (2 * Real.arctan (Real.exp (-x))) / 2 =
      Real.arctan (Real.exp (-x)) := by ring
  rw [hhalf, Real.cos_arctan, Real.sin_arctan, hratio, hxinverse, Real.log_exp]

/-- The inverse parametrisation recovers every angle in the open upper semicircle. -/
theorem boostToAngle_angleToBoost {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    boostToAngle (angleToBoost θ) = θ := by
  have hs : 0 < Real.sin (θ / 2) := sin_half_angle_pos hθ
  have hc : 0 < Real.cos (θ / 2) := cos_half_angle_pos hθ
  have hr : 0 < Real.cos (θ / 2) / Real.sin (θ / 2) := div_pos hc hs
  have hexp : Real.exp (-(Real.log (Real.cos (θ / 2) / Real.sin (θ / 2)))) =
      Real.sin (θ / 2) / Real.cos (θ / 2) := by
    rw [Real.exp_neg, Real.exp_log hr, inv_div]
  have hhalf : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  rw [boostToAngle, angleToBoost, hexp, ← Real.tan_eq_sin_div_cos,
    Real.arctan_tan hhalf.1 hhalf.2]
  ring

/-- The two elementary half-angle factors for the circle exponential. -/
private theorem circle_exp_add_factor (θ : ℝ) :
    1 + Complex.exp (θ * Complex.I) =
      (2 * (Real.cos (θ / 2) : ℂ)) * Complex.exp ((θ / 2) * Complex.I) := by
  have hcast : ((Real.cos (θ / 2) : ℝ) : ℂ) = Complex.cos ((θ : ℂ) / 2) := by
    rw [show ((θ : ℂ) / 2) = ((θ / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos]
  have e1 : -((θ : ℂ) / 2) * Complex.I + (θ : ℂ) / 2 * Complex.I = 0 := by ring
  have e2 : (θ : ℂ) / 2 * Complex.I + (θ : ℂ) / 2 * Complex.I = (θ : ℂ) * Complex.I := by ring
  calc
    1 + Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) / 2) * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) +
          Complex.exp ((θ : ℂ) / 2 * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add, e1, e2, Complex.exp_zero]
    _ = (Complex.exp ((θ : ℂ) / 2 * Complex.I) + Complex.exp (-((θ : ℂ) / 2) * Complex.I)) *
          Complex.exp ((θ : ℂ) / 2 * Complex.I) := by ring
    _ = 2 * Complex.cos ((θ : ℂ) / 2) * Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [Complex.two_cos]
    _ = 2 * ((Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [hcast]

/-- The corresponding half-angle factor for the circle difference. -/
private theorem circle_exp_sub_factor (θ : ℝ) :
    1 - Complex.exp (θ * Complex.I) =
      (-2 * (Real.sin (θ / 2) : ℂ) * Complex.I) *
        Complex.exp ((θ / 2) * Complex.I) := by
  have hcast : ((Real.sin (θ / 2) : ℝ) : ℂ) = Complex.sin ((θ : ℂ) / 2) := by
    rw [show ((θ : ℂ) / 2) = ((θ / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
  have e1 : -((θ : ℂ) / 2) * Complex.I + (θ : ℂ) / 2 * Complex.I = 0 := by ring
  have e2 : (θ : ℂ) / 2 * Complex.I + (θ : ℂ) / 2 * Complex.I = (θ : ℂ) * Complex.I := by ring
  have hsin : 2 * Complex.sin ((θ : ℂ) / 2) =
      (Complex.exp (-((θ : ℂ) / 2) * Complex.I) - Complex.exp ((θ : ℂ) / 2 * Complex.I)) *
        Complex.I := Complex.two_sin _
  calc
    1 - Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) / 2) * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) -
          Complex.exp ((θ : ℂ) / 2 * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add, e1, e2, Complex.exp_zero]
    _ = -((2 * Complex.sin ((θ : ℂ) / 2)) * Complex.I) *
          Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [hsin]
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc
        Complex.exp (-((θ : ℂ) / 2) * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) -
            Complex.exp ((θ : ℂ) / 2 * Complex.I) * Complex.exp ((θ : ℂ) / 2 * Complex.I) =
            -((Complex.exp (-((θ : ℂ) / 2) * Complex.I) -
                Complex.exp ((θ : ℂ) / 2 * Complex.I)) * (Complex.I * Complex.I)) *
              Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
          rw [hI]
          ring
        _ = -((Complex.exp (-((θ : ℂ) / 2) * Complex.I) -
                Complex.exp ((θ : ℂ) / 2 * Complex.I)) * Complex.I * Complex.I) *
              Complex.exp ((θ : ℂ) / 2 * Complex.I) := by ring
    _ = -2 * ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I *
          Complex.exp ((θ : ℂ) / 2 * Complex.I) := by
      rw [hcast]
      ring

/-- The Cayley coordinate of a circle point, expressed through its half-angle cotangent. -/
private theorem cayley_circleExp_of_sin_half_ne_zero {θ : ℝ}
    (hs : Real.sin (θ / 2) ≠ 0) :
    cayley (Complex.exp (θ * Complex.I)) =
      Complex.I * (Real.cos (θ / 2) / Real.sin (θ / 2) : ℝ) := by
  rw [cayley, circle_exp_add_factor, circle_exp_sub_factor]
  have hsC : ((Real.sin (θ / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The logarithm of the negative imaginary unit on the chosen branch. -/
private theorem log_neg_I : Complex.log (-Complex.I) =
    -(Real.pi / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_I]

/-- The logarithm of the positive imaginary unit on the chosen branch. -/
private theorem log_I : Complex.log Complex.I =
    (Real.pi / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_I]

/-- The boost coordinate agrees with the real angle coordinate on the open upper semicircle. -/
theorem boostCoord_circleExp {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    boostCoord (Complex.exp (θ * Complex.I)) = (angleToBoost θ : ℂ) := by
  have hs := sin_half_angle_pos hθ
  have hc := cos_half_angle_pos hθ
  have hr : 0 < Real.cos (θ / 2) / Real.sin (θ / 2) := div_pos hc hs
  have hlog : Complex.log (-cayley (Complex.exp (θ * Complex.I))) =
      (Real.log (Real.cos (θ / 2) / Real.sin (θ / 2)) : ℂ) +
        Complex.log (-Complex.I) := by
    calc
      Complex.log (-cayley (Complex.exp (θ * Complex.I))) =
          Complex.log ((Real.cos (θ / 2) / Real.sin (θ / 2) : ℝ) *
            (-Complex.I)) := by
              congr 1
              rw [cayley_circleExp_of_sin_half_ne_zero hs.ne']
              push_cast
              ring
      _ = (Real.log (Real.cos (θ / 2) / Real.sin (θ / 2)) : ℂ) +
          Complex.log (-Complex.I) := Complex.log_ofReal_mul hr (by simp)
  unfold boostCoord angleToBoost
  rw [hlog, log_neg_I]
  push_cast
  ring

/-- The boost coordinate on the lower semicircle is the upper strip edge.  Its real logarithm is
`log((-cos(θ/2))/sin(θ/2))`; this is the corrected ratio forced by `re_boostCoord`. -/
theorem boostCoord_circleExp_lower {θ : ℝ} (hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi)) :
    boostCoord (Complex.exp (θ * Complex.I)) =
      (Real.log ((-Real.cos (θ / 2)) / Real.sin (θ / 2)) : ℂ) +
        Complex.I * Real.pi := by
  have hs : 0 < Real.sin (θ / 2) := by
    obtain ⟨hθ1, hθ2⟩ := hθ
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have hc : 0 < -Real.cos (θ / 2) := neg_cos_half_angle_pos hθ
  have hr : 0 < (-Real.cos (θ / 2)) / Real.sin (θ / 2) := div_pos hc hs
  have hlog : Complex.log (-cayley (Complex.exp (θ * Complex.I))) =
      (Real.log ((-Real.cos (θ / 2)) / Real.sin (θ / 2)) : ℂ) +
        Complex.log Complex.I := by
    calc
      Complex.log (-cayley (Complex.exp (θ * Complex.I))) =
          Complex.log (((-Real.cos (θ / 2)) / Real.sin (θ / 2) : ℝ) *
            Complex.I) := by
              congr 1
              rw [cayley_circleExp_of_sin_half_ne_zero hs.ne']
              push_cast
              ring
      _ = (Real.log ((-Real.cos (θ / 2)) / Real.sin (θ / 2)) : ℂ) +
          Complex.log Complex.I := Complex.log_ofReal_mul hr (by simp)
  unfold boostCoord
  rw [hlog, log_I]
  push_cast
  ring

end
end MobiusCPT
