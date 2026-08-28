import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Order.Field

open Complex Filter MeasureTheory Set
open scoped ContDiff Topology

namespace MobiusCPT

noncomputable section

/-! The real-line analytic input for the Gaussian approximation in [T26], Lemma 3.4. -/

section Kernel

/-- [T26], proof of Lemma 3.4; the Gaussian kernel of width `s`, as an entire function of a
complex argument. -/
noncomputable def gaussKernel (s : ℝ) (w : ℂ) : ℂ :=
  ((Real.sqrt (4 * Real.pi * s) : ℝ) : ℂ)⁻¹ * Complex.exp (-w ^ 2 / (4 * s))

/-- [T26], proof of Lemma 3.4; on the real axis `gaussKernel` is the normalized real Gaussian. -/
theorem gaussKernel_ofReal (s t : ℝ) :
    gaussKernel s (t : ℂ) =
      (((Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (-t ^ 2 / (4 * s)) : ℝ) : ℂ) := by
  simp [gaussKernel, Complex.ofReal_inv, Complex.ofReal_exp, Complex.ofReal_pow,
    Complex.ofReal_div]

/-- [T26], proof of Lemma 3.4; the norm of the complex Gaussian is explicit in its real and
imaginary coordinates. -/
theorem norm_gaussKernel {s : ℝ} (hs : 0 < s) (w : ℂ) :
    ‖gaussKernel s w‖ =
      (Real.sqrt (4 * Real.pi * s))⁻¹ *
        Real.exp ((w.im ^ 2 - w.re ^ 2) / (4 * s)) := by
  have hsqrt : 0 < Real.sqrt (4 * Real.pi * s) := by positivity
  have h4s : (4 : ℂ) * (s : ℂ) = ((4 * s : ℝ) : ℂ) := by push_cast; ring
  have hre : (-w ^ 2 / (4 * (s : ℂ))).re = (w.im ^ 2 - w.re ^ 2) / (4 * s) := by
    rw [h4s, Complex.div_ofReal_re]
    congr 1
    simp only [Complex.neg_re, pow_two, Complex.mul_re]
    ring
  rw [gaussKernel, norm_mul, norm_inv, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hsqrt, hre]

/-- [T26], proof of Lemma 3.4; the real Gaussian kernel written with a quadratic exponent. -/
theorem gaussKernel_ofReal' (s : ℝ) (t : ℝ) :
    gaussKernel s (t : ℂ) =
      (((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-(1 / (4 * s)) * t ^ 2) : ℝ) : ℂ) := by
  rw [gaussKernel_ofReal s t]
  have hexp : -t ^ 2 / (4 * s) = -(1 / (4 * s)) * t ^ 2 := by
    by_cases hs : s = 0
    · simp [hs]
    · field_simp
  rw [hexp]
  push_cast
  ring

/-- [T26], proof of Lemma 3.4; the real restriction of the Gaussian kernel is integrable. -/
theorem integrable_gaussKernel {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => gaussKernel s (t : ℂ)) := by
  have hb : (0 : ℝ) < 1 / (4 * s) := by positivity
  have h : Integrable (fun t : ℝ => Real.exp (-(1 / (4 * s)) * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hfun : (fun t : ℝ => gaussKernel s (t : ℂ)) =
      fun t : ℝ => (((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-(1 / (4 * s)) * t ^ 2) : ℝ) : ℂ) := by
    funext t
    exact gaussKernel_ofReal' s t
  rw [hfun]
  exact (h.ofReal).const_mul _

/-- [T26], proof of Lemma 3.4; the real Gaussian kernel has total mass one. -/
theorem integral_gaussKernel {s : ℝ} (hs : 0 < s) :
    ∫ t : ℝ, gaussKernel s (t : ℂ) = 1 := by
  have hpos : (0 : ℝ) < Real.sqrt (4 * Real.pi * s) := by positivity
  have hfun : (fun t : ℝ => gaussKernel s (t : ℂ)) =
      fun t : ℝ => (((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ) *
        ((Real.exp (-(1 / (4 * s)) * t ^ 2) : ℝ) : ℂ) := by
    funext t
    exact gaussKernel_ofReal' s t
  have hcast : ∫ t : ℝ, ((Real.exp (-(1 / (4 * s)) * t ^ 2) : ℝ) : ℂ) =
      ((∫ t : ℝ, Real.exp (-(1 / (4 * s)) * t ^ 2) : ℝ) : ℂ) := integral_ofReal
  rw [hfun, integral_const_mul, hcast, integral_gaussian]
  have hval : Real.sqrt (Real.pi / (1 / (4 * s))) = Real.sqrt (4 * Real.pi * s) := by
    congr 1
    field_simp
  rw [hval, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]

/-- [T26], proof of Lemma 3.4; the derivative of the entire Gaussian kernel. -/
theorem hasDerivAt_gaussKernel {s : ℝ} (hs : s ≠ 0) (w : ℂ) :
    HasDerivAt (gaussKernel s) (-(w / (2 * s)) * gaussKernel s w) w := by
  have hs_complex : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hsq : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hpoly' : HasDerivAt (fun z : ℂ => -z ^ 2 / (4 * (s : ℂ)))
      (-(2 * w) / (4 * (s : ℂ))) w := hsq.neg.div_const (4 * (s : ℂ))
  have hval : -(2 * w) / (4 * (s : ℂ)) = -(w / (2 * (s : ℂ))) := by
    field_simp
    ring
  rw [hval] at hpoly'
  have hexp := hpoly'.cexp
  have hmul := hexp.const_mul ((((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ))
  have hgauss : (fun z : ℂ => (((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ) *
      Complex.exp (-z ^ 2 / (4 * (s : ℂ)))) = gaussKernel s := by
    funext z
    rw [gaussKernel]
    push_cast
    ring
  rw [hgauss] at hmul
  have hval2 : (((Real.sqrt (4 * Real.pi * s))⁻¹ : ℝ) : ℂ) *
      (Complex.exp (-w ^ 2 / (4 * (s : ℂ))) * -(w / (2 * (s : ℂ)))) =
      -(w / (2 * (s : ℂ))) * gaussKernel s w := by
    rw [gaussKernel]
    push_cast
    ring
  rw [hval2] at hmul
  exact hmul

/-- [T26], proof of Lemma 3.4; the Gaussian kernel is complex differentiable everywhere when
its width is nonzero. -/
theorem differentiable_gaussKernel {s : ℝ} (hs : s ≠ 0) :
    Differentiable ℂ (gaussKernel s) := fun w =>
  (hasDerivAt_gaussKernel hs w).differentiableAt

/-- [T26], proof of Lemma 3.4; scaling a Gaussian reduces its width to one. -/
theorem gaussKernel_scale {s : ℝ} (hs : 0 < s) (v : ℝ) :
    gaussKernel s ((Real.sqrt s * v : ℝ) : ℂ) =
      (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * gaussKernel 1 (v : ℂ) := by
  have hspos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hnorm : Real.sqrt (4 * Real.pi * s) = Real.sqrt (4 * Real.pi * 1) * Real.sqrt s := by
    rw [mul_one, Real.sqrt_mul (by positivity)]
  have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hexp : (-(((Real.sqrt s * v : ℝ) : ℂ)) ^ 2 / (4 * (s : ℂ))) =
      -(v : ℂ) ^ 2 / (4 * ((1 : ℝ) : ℂ)) := by
    have h1 : (((Real.sqrt s * v : ℝ)) : ℂ) ^ 2 = (s : ℂ) * (v : ℂ) ^ 2 := by
      push_cast
      rw [mul_pow, ← Complex.ofReal_pow, hsq]
    rw [h1]
    push_cast
    field_simp
  rw [gaussKernel, gaussKernel, hexp, hnorm]
  have hrootne : ((Real.sqrt (4 * Real.pi * 1) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hsqrtne : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  push_cast
  field_simp

end Kernel

section Decay

/-- [T26], proof of Lemma 3.4; smooth functions on the line whose derivatives decay faster than
every exponential. -/
structure IsRapidlyDecaying (a : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ a
  decay : ∀ k N : ℕ, ∃ C : ℝ, ∀ x : ℝ,
    ‖iteratedDeriv k a x‖ ≤ C * Real.exp (-(N : ℝ) * |x|)

/-- The iterated derivatives of a rapidly decaying function are rapidly decaying. -/
theorem IsRapidlyDecaying.iteratedDeriv {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (k : ℕ) :
    IsRapidlyDecaying (iteratedDeriv k a) := by
  have hshift : ∀ j : ℕ,
      _root_.iteratedDeriv j (_root_.iteratedDeriv k a) =
        _root_.iteratedDeriv (j + k) a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [_root_.iteratedDeriv_succ, ih, ← _root_.iteratedDeriv_succ]
        congr 1
        omega
  refine ⟨?_, ?_⟩
  · refine contDiff_of_differentiable_iteratedDeriv (fun j hj => ?_)
    rw [hshift]
    have hc : ContDiff ℝ ∞ (_root_.iteratedDeriv (j + k) a) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv _ ha.contDiff
    exact (contDiff_infty_iff_deriv.mp hc).1
  · intro j N
    obtain ⟨C, hC⟩ := ha.decay (j + k) N
    refine ⟨C, fun x => ?_⟩
    rw [hshift]
    exact hC x

/-- A rapidly decaying function is bounded. -/
theorem IsRapidlyDecaying.exists_bound {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha.decay 0 0
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : ‖a x‖ ≤ C := by simpa using hC x
  exact hx.trans (le_max_left _ _)

/-- The exponential `exp (-|x|)` is integrable on the real line, by comparison with the
Cauchy density. -/
theorem integrable_exp_neg_abs :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hquad : ∀ x : ℝ, 1 + x ^ 2 ≤ 4 * Real.exp |x| := by
    intro x
    have h1 : |x| / 2 + 1 ≤ Real.exp (|x| / 2) := Real.add_one_le_exp _
    have h0 : (0 : ℝ) ≤ |x| / 2 + 1 := by positivity
    have hsplit : Real.exp |x| = Real.exp (|x| / 2) * Real.exp (|x| / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsq : (|x| / 2 + 1) * (|x| / 2 + 1) ≤ Real.exp (|x| / 2) * Real.exp (|x| / 2) :=
      mul_le_mul h1 h1 h0 (Real.exp_pos _).le
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    have hnn : 0 ≤ |x| := abs_nonneg x
    rw [hsplit]
    nlinarith [hsq, habs, hnn]
  have hdom : Integrable (fun x : ℝ => 4 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 4
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [] with x
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hexp : (0 : ℝ) < Real.exp |x| := Real.exp_pos _
  have hexpneg : (0 : ℝ) < Real.exp (-|x|) := Real.exp_pos _
  have he : Real.exp (-|x|) * Real.exp |x| = 1 := by
    rw [← Real.exp_add]
    simp
  have h1 : Real.exp (-|x|) * (1 + x ^ 2) ≤ 4 := by
    nlinarith [hquad x, hexpneg, he]
  have hkey : Real.exp (-|x|) ≤ 4 * (1 + x ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ hpos]
    linarith [h1]
  simpa [Real.norm_eq_abs, abs_of_pos hexpneg] using hkey

/-- A rapidly decaying function is Bochner integrable. -/
theorem IsRapidlyDecaying.integrable {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) :
    Integrable a := by
  obtain ⟨C, hC⟩ := ha.decay 0 1
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul |C|) ?_ ?_
  · exact ha.contDiff.continuous.aestronglyMeasurable
  · filter_upwards [] with x
    calc
      ‖a x‖ ≤ C * Real.exp (-(1 : ℝ) * |x|) := by simpa using hC x
      _ ≤ |C| * Real.exp (-|x|) := by
        rw [show -(1 : ℝ) * |x| = -|x| by ring]
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_nonneg _)

/-- Iterated derivatives compose by addition of their orders. -/
theorem iteratedDeriv_iteratedDeriv (a : ℝ → ℂ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k a) = iteratedDeriv (j + k) a := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ]
      congr 1
      omega

end Decay

section RealConvolution

/-- [T26], proof of Lemma 3.4; Gaussian convolution on the boost coordinate. -/
noncomputable def gaussConvReal (s : ℝ) (a : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, gaussKernel s (u : ℂ) * a (x - u)

/-- The real convolution integrand is integrable for a positive Gaussian width. -/
theorem integrable_gaussConvReal_integrand {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (x : ℝ) :
    Integrable (fun u : ℝ => gaussKernel s (u : ℂ) * a (x - u)) := by
  obtain ⟨C, hC, hbound⟩ := ha.exists_bound
  refine Integrable.mono' ((integrable_gaussKernel hs).norm.const_mul C) ?_ ?_
  · exact (integrable_gaussKernel hs).aestronglyMeasurable.mul
      (ha.contDiff.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [] with u
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound (x - u)) (norm_nonneg _)).trans_eq (by ring)

/-- Subtracting the input from its convolution can be put under one integral. -/
theorem gaussConvReal_sub {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (x : ℝ) :
    gaussConvReal s a x - a x =
      ∫ u : ℝ, gaussKernel s (u : ℂ) * (a (x - u) - a x) := by
  have h₁ := integrable_gaussConvReal_integrand hs ha x
  have h₂ := (integrable_gaussKernel hs).mul_const (a x)
  have hmass : (∫ u : ℝ, gaussKernel s (u : ℂ) * a x) = a x := by
    rw [integral_mul_const, integral_gaussKernel hs]
    simp
  calc
    gaussConvReal s a x - a x =
        (∫ u : ℝ, gaussKernel s (u : ℂ) * a (x - u)) -
          (∫ u : ℝ, gaussKernel s (u : ℂ) * a x) := by
      rw [gaussConvReal, hmass]
    _ = ∫ u : ℝ, (gaussKernel s (u : ℂ) * a (x - u)) -
          (gaussKernel s (u : ℂ) * a x) := (integral_sub h₁ h₂).symm
    _ = ∫ u : ℝ, gaussKernel s (u : ℂ) * (a (x - u) - a x) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by ring)

/-- Differentiating the real convolution differentiates the rapidly decaying factor. -/
theorem iteratedDeriv_gaussConvReal {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (k : ℕ) :
    iteratedDeriv k (gaussConvReal s a) = gaussConvReal s (iteratedDeriv k a) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      let F : ℝ → ℝ → ℂ := fun y u => gaussKernel s (u : ℂ) * iteratedDeriv k a (y - u)
      let F' : ℝ → ℝ → ℂ :=
        fun y u => gaussKernel s (u : ℂ) * iteratedDeriv (k + 1) a (y - u)
      obtain ⟨C, hC, hbound⟩ := (ha.iteratedDeriv (k + 1)).exists_bound
      have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (𝕜 := ℝ) (α := ℝ) (μ := volume) (F := F) (x₀ := x) (s := Metric.ball x 1)
        (bound := fun u : ℝ => C * ‖gaussKernel s (u : ℂ)‖) (F' := F')
        (Metric.ball_mem_nhds x zero_lt_one)
        (Eventually.of_forall fun y =>
          (integrable_gaussConvReal_integrand hs (ha.iteratedDeriv k) y).aestronglyMeasurable)
        (integrable_gaussConvReal_integrand hs (ha.iteratedDeriv k) x)
        (integrable_gaussConvReal_integrand hs (ha.iteratedDeriv (k + 1)) x).aestronglyMeasurable
        (by
          filter_upwards [] with u y hy
          change ‖gaussKernel s (u : ℂ) *
              iteratedDeriv (k + 1) a (y - u)‖ ≤ C * ‖gaussKernel s (u : ℂ)‖
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (hbound (y - u)) (norm_nonneg _)).trans_eq
            (by ring))
        ((integrable_gaussKernel hs).norm.const_mul C)
        (by
          filter_upwards [] with u y hy
          have hderiv : HasDerivAt (iteratedDeriv k a)
              (iteratedDeriv (k + 1) a (y - u)) (y - u) := by
            have hc : ContDiff ℝ ∞ (iteratedDeriv k a) := by
              rw [iteratedDeriv_eq_iterate]
              exact ContDiff.iterate_deriv _ ha.contDiff
            simpa [_root_.iteratedDeriv_succ] using
              ((contDiff_infty_iff_deriv.mp hc).1 (y - u)).hasDerivAt
          have hsub : HasDerivAt (fun z : ℝ => z - u) 1 y := by
            simpa using (hasDerivAt_id y).sub_const u
          simpa [F, F'] using
            ((hderiv.scomp y hsub).const_mul
              (gaussKernel s (u : ℂ))))
      change deriv (fun y : ℝ => ∫ u : ℝ,
          gaussKernel s (u : ℂ) * iteratedDeriv k a (y - u)) x =
        ∫ u : ℝ, gaussKernel s (u : ℂ) * iteratedDeriv (k + 1) a (x - u)
      simpa [F, F'] using hparam.2.deriv

/-- The first Gaussian moment is finite. -/
theorem integrable_norm_gaussKernel_mul_abs {s : ℝ} (hs : 0 < s) :
    Integrable (fun v : ℝ => ‖gaussKernel s (v : ℂ)‖ * |v|) := by
  have hb : 0 < (1 / (4 * s) : ℝ) := by positivity
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / (4 * s)) hb).norm
  have hA : 0 ≤ (Real.sqrt (4 * Real.pi * s))⁻¹ := by positivity
  have hkernel_meas : AEStronglyMeasurable
      (fun v : ℝ => ‖gaussKernel s (v : ℂ)‖) := by
    have hcont := (differentiable_gaussKernel hs.ne').continuous.comp continuous_ofReal
    exact hcont.norm.aestronglyMeasurable
  refine Integrable.mono' (h.const_mul (Real.sqrt (4 * Real.pi * s))⁻¹)
    (hkernel_meas.mul (by fun_prop)) ?_
  · filter_upwards [] with v
    rw [norm_gaussKernel hs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_pow, neg_zero, zero_sub,
      div_neg, neg_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    rw [abs_of_nonneg (by positivity), abs_abs]
    ring_nf
    exact le_rfl

/-- The first Gaussian moment scales like the square root of the width. -/
theorem integral_norm_gaussKernel_mul_abs_scale {s : ℝ} (hs : 0 < s) :
    (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) =
      Real.sqrt s * ∫ v : ℝ, ‖gaussKernel 1 (v : ℂ)‖ * |v| := by
  have hchange := Measure.integral_comp_mul_left
    (fun u : ℝ => ‖gaussKernel s (u : ℂ)‖ * |u|) (Real.sqrt s)
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hpoint : ∀ v : ℝ,
      ‖gaussKernel s ((Real.sqrt s * v : ℝ) : ℂ)‖ * |Real.sqrt s * v| =
        ‖gaussKernel 1 (v : ℂ)‖ * |v| := by
    intro v
    rw [gaussKernel_scale hs, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_pos hsqrt, abs_mul]
    simp only [abs_of_pos hsqrt]
    field_simp [ne_of_gt hsqrt] <;> ring
  have hleft :
      (∫ v : ℝ, ‖gaussKernel s ((Real.sqrt s * v : ℝ) : ℂ)‖ *
        |Real.sqrt s * v|) = ∫ v : ℝ, ‖gaussKernel 1 (v : ℂ)‖ * |v| := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint
  rw [hleft] at hchange
  simp only [smul_eq_mul, abs_of_pos hsqrt, abs_inv, abs_of_nonneg hsqrt.le] at hchange
  calc
    (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) =
        Real.sqrt s * ∫ v : ℝ, ‖gaussKernel 1 (v : ℂ)‖ * |v| := by
          rw [hchange]
          field_simp [ne_of_gt hsqrt] <;> ring

/-- A Gaussian absorbs every fixed exponential weight. -/
theorem integrable_gaussKernel_mul_exp (N : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun v : ℝ =>
      ‖gaussKernel s (v : ℂ)‖ * Real.exp ((N : ℝ) * |v|)) := by
  have hgauss := integrable_exp_neg_mul_sq (b := (1 / (8 * s) : ℝ)) (by positivity)
  have hA : 0 ≤ (Real.sqrt (4 * Real.pi * s))⁻¹ *
      Real.exp (2 * (N : ℝ) ^ 2 * s) := by
    positivity
  have hkernel_meas : AEStronglyMeasurable
      (fun v : ℝ => ‖gaussKernel s (v : ℂ)‖) := by
    have hcont := (differentiable_gaussKernel hs.ne').continuous.comp continuous_ofReal
    exact hcont.norm.aestronglyMeasurable
  refine (hgauss.const_mul
      ((Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (2 * (N : ℝ) ^ 2 * s))).mono'
    (hkernel_meas.mul (by fun_prop)) ?_
  · filter_upwards [] with v
    rw [norm_gaussKernel hs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (4 * Real.pi * s))⁻¹),
      abs_of_pos (Real.exp_pos _)]
    have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hzero, zero_sub]
    calc
      (Real.sqrt (4 * Real.pi * s))⁻¹ *
          Real.exp (-v ^ 2 / (4 * s)) * Real.exp ((N : ℝ) * |v|) =
          (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (-v ^ 2 / (4 * s) + (N : ℝ) * |v|) := by
              rw [mul_assoc, ← Real.exp_add]
      _ ≤ (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (2 * (N : ℝ) ^ 2 * s - v ^ 2 / (8 * s)) := by
              apply mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr ?_)
                (by positivity)
              have hamgm : (N : ℝ) * |v| ≤
                  2 * (N : ℝ) ^ 2 * s + v ^ 2 / (8 * s) := by
                refine le_of_mul_le_mul_of_pos_left (a := (8 * s : ℝ)) ?_
                  (by positivity)
                field_simp [ne_of_gt hs]
                nlinarith [sq_nonneg (4 * (N : ℝ) * s - |v|), sq_abs v]
              calc
                -v ^ 2 / (4 * s) + (N : ℝ) * |v| =
                    ((N : ℝ) * |v| - v ^ 2 / (8 * s)) - v ^ 2 / (8 * s) := by
                      field_simp [ne_of_gt hs]
                      ring
                _ ≤ 2 * (N : ℝ) ^ 2 * s - v ^ 2 / (8 * s) := by
                  linarith [hamgm]
      _ = (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (2 * (N : ℝ) ^ 2 * s) *
            Real.exp (-v ^ 2 / (8 * s)) := by
              have hexp : 2 * (N : ℝ) ^ 2 * s - v ^ 2 / (8 * s) =
                  2 * (N : ℝ) ^ 2 * s + (-v ^ 2 / (8 * s)) := by ring
              rw [hexp, Real.exp_add]
              ring
      _ = (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (2 * (N : ℝ) ^ 2 * s) *
            Real.exp (-(1 / (8 * s)) * v ^ 2) := by
        have hexp : -v ^ 2 / (8 * s) = -(1 / (8 * s)) * v ^ 2 := by
          field_simp [ne_of_gt hs] <;> ring
        rw [hexp]

/-- Integrable tails vanish as the radius tends to infinity. -/
theorem tendsto_integral_abs_tail {f : ℝ → ℝ} (hf : Integrable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    Tendsto (fun R : ℝ => ∫ x in {x | R < |x|}, f x) atTop (𝓝 0) := by
  have hmeas : ∀ R : ℝ, MeasurableSet {x : ℝ | R < |x|} := by
    intro R
    exact measurableSet_Ioi.preimage continuous_abs.measurable
  have h : Tendsto
      (fun R : ℝ => ∫ x, Set.indicator {x : ℝ | R < |x|} f x) atTop
      (𝓝 (∫ _x : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (ι := ℝ) (l := atTop)
      (μ := volume)
      (F := fun R x => Set.indicator {x : ℝ | R < |x|} f x)
      (f := fun _ : ℝ => (0 : ℝ)) f ?_ ?_ hf ?_
    · exact Filter.Eventually.of_forall fun R => hf.aestronglyMeasurable.indicator (hmeas R)
    · refine Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ {x : ℝ | R < |x|}
      · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact hf_nonneg x
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop |x|] with R hR
      have hx : x ∉ {x : ℝ | R < |x|} := by
        simp only [Set.mem_setOf_eq, not_lt]
        exact hR
      rw [Set.indicator_of_notMem hx]
  simpa only [integral_indicator (hmeas _), integral_zero] using h

/-- The exponentially weighted Gaussian mass outside a fixed neighbourhood tends to zero with
the width of the Gaussian. -/
theorem tendsto_gaussKernel_weighted_far (N : ℕ) :
    Tendsto
      (fun s : ℝ =>
        ∫ u in {u : ℝ | 1 < |u|},
          ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1))
      (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℝ := fun v =>
    ‖gaussKernel 1 (v : ℂ)‖ * (Real.exp ((N : ℝ) * |v|) + 1)
  have hf : Integrable f := by
    have h₁ := integrable_gaussKernel_mul_exp N 1 one_pos
    have h₂ := (integrable_gaussKernel (s := 1) one_pos).norm
    have heq : f =
        (fun v : ℝ => ‖gaussKernel 1 (v : ℂ)‖ * Real.exp ((N : ℝ) * |v|)) +
          (fun v : ℝ => ‖gaussKernel 1 (v : ℂ)‖) := by
      funext v
      dsimp [f]
      ring
    rw [heq]
    exact h₁.add h₂
  have hf_nonneg : ∀ v, 0 ≤ f v := by
    intro v
    exact mul_nonneg (norm_nonneg _) (by positivity)
  have htail := tendsto_integral_abs_tail hf hf_nonneg
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s : ℝ => Real.sqrt s)
    · simpa only [Function.comp_def, id_eq, Real.sqrt_zero] using
        (tendsto_id.mono_right
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).sqrt
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.2 hs
  have hrad : Tendsto (fun s : ℝ => (Real.sqrt s)⁻¹) (𝓝[>] 0) atTop :=
    hsqrt.inv_tendsto_nhdsGT_zero
  have htail' : Tendsto
      (fun s : ℝ => ∫ v in {v : ℝ | (Real.sqrt s)⁻¹ < |v|}, f v)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using htail.comp hrad
  have hpointwise : ∀ {s : ℝ}, 0 < s → s ≤ 1 →
      (∫ u in {u : ℝ | 1 < |u|},
        ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) =
      ∫ v in {v : ℝ | (Real.sqrt s)⁻¹ < |v|},
        ‖gaussKernel 1 (v : ℂ)‖ *
          (Real.exp ((N : ℝ) * (Real.sqrt s) * |v|) + 1) := by
    intro s hs hsl
    let c : ℝ := Real.sqrt s
    let E : Set ℝ := {u : ℝ | 1 < |u|}
    let Ec : Set ℝ := {v : ℝ | c⁻¹ < |v|}
    let G : ℝ → ℝ := fun u =>
      ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)
    let H : ℝ → ℝ := fun v =>
      ‖gaussKernel 1 (v : ℂ)‖ * (Real.exp ((N : ℝ) * c * |v|) + 1)
    have hc : 0 < c := Real.sqrt_pos.2 hs
    have hc_le : c ≤ 1 := by
      dsimp [c]
      apply (Real.sqrt_le_left (show (0 : ℝ) ≤ 1 by positivity)).2
      simpa using hsl
    have hG : Integrable G := by
      have h₁ := integrable_gaussKernel_mul_exp N s hs
      have h₂ := (integrable_gaussKernel hs).norm
      have heq : G =
          (fun u : ℝ => ‖gaussKernel s (u : ℂ)‖ * Real.exp ((N : ℝ) * |u|)) +
            (fun u : ℝ => ‖gaussKernel s (u : ℂ)‖) := by
        funext u
        dsimp [G]
        ring
      rw [heq]
      exact h₁.add h₂
    have hE_meas : MeasurableSet E := by
      dsimp [E]
      exact measurableSet_Ioi.preimage continuous_abs.measurable
    have hEc_meas : MeasurableSet Ec := by
      dsimp [Ec]
      exact measurableSet_Ioi.preimage continuous_abs.measurable
    have hchange := Measure.integral_comp_mul_left
      (fun u : ℝ => Set.indicator E G u) c
    simp only [smul_eq_mul, abs_of_pos hc, abs_inv, abs_of_nonneg hc.le] at hchange
    have hset : ∀ v : ℝ, Set.indicator E G (c * v) =
        c⁻¹ * Set.indicator Ec H v := by
      intro v
      by_cases hv : c⁻¹ < |v|
      · have hcv : 1 < |c * v| := by
          rw [abs_mul, abs_of_pos hc]
          have hv' : 1 / c < |v| := by simpa [one_div] using hv
          rw [div_lt_iff₀ hc] at hv'
          simpa [mul_comm] using hv'
        have hvEc : v ∈ Ec := hv
        have hcvE : c * v ∈ E := hcv
        simp only [Set.indicator_of_mem hvEc, Set.indicator_of_mem hcvE]
        dsimp [G, H]
        rw [show ‖gaussKernel s ((c * v : ℝ) : ℂ)‖ =
            c⁻¹ * ‖gaussKernel 1 (v : ℂ)‖ by
              simpa [c, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos hc] using congrArg norm (gaussKernel_scale hs v)]
        rw [abs_mul, abs_of_pos hc]
        ring_nf
      · have hcv : ¬1 < |c * v| := by
          intro h
          have hv' : ¬1 / c < |v| := by simpa [one_div] using hv
          apply hv'
          rw [abs_mul, abs_of_pos hc] at h
          rw [div_lt_iff₀ hc]
          simpa [mul_comm] using h
        have hvEc : v ∉ Ec := hv
        have hcvE : c * v ∉ E := hcv
        simp only [Set.indicator_of_notMem hvEc, Set.indicator_of_notMem hcvE, mul_zero]
    have hleft : (∫ v : ℝ, Set.indicator E G (c * v)) =
        c⁻¹ * ∫ v : ℝ, Set.indicator Ec H v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall hset
    have hmass : (∫ u : ℝ, Set.indicator E G u) =
        ∫ u in E, G u := integral_indicator hE_meas
    have hmassc : (∫ v : ℝ, Set.indicator Ec H v) =
        ∫ v in Ec, H v := integral_indicator hEc_meas
    have hsolve : (∫ u in E, G u) = ∫ v in Ec, H v := by
      calc
        (∫ u in E, G u) = c * (c⁻¹ * (∫ u in E, G u)) := by
          field_simp [ne_of_gt hc] <;> ring
        _ = c * (∫ v : ℝ, Set.indicator E G (c * v)) := by
          rw [hchange, hmass]
        _ = c * (c⁻¹ * (∫ v in Ec, H v)) := by rw [hleft, hmassc]
        _ = ∫ v in Ec, H v := by field_simp [ne_of_gt hc] <;> ring
    simpa [E, Ec, G, H, c] using hsolve
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 := by
    exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
  have hupper : Tendsto
      (fun s : ℝ => ∫ v in {v : ℝ | (Real.sqrt s)⁻¹ < |v|}, f v)
      (𝓝[>] 0) (𝓝 0) := htail'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [] with s
    exact integral_nonneg (fun u => mul_nonneg (norm_nonneg _) (by positivity))
  · filter_upwards [hle, self_mem_nhdsWithin] with s hsle hspos
    rw [hpointwise (s := s) hspos hsle]
    have hsqrt_le : Real.sqrt s ≤ 1 := by
      apply (Real.sqrt_le_left (show (0 : ℝ) ≤ 1 by positivity)).2
      simpa using hsle
    have hHs : Integrable (fun v : ℝ =>
        ‖gaussKernel 1 (v : ℂ)‖ *
          (Real.exp ((N : ℝ) * Real.sqrt s * |v|) + 1)) := by
      have hkernel_meas : AEStronglyMeasurable
          (fun v : ℝ => ‖gaussKernel 1 (v : ℂ)‖) :=
        ((differentiable_gaussKernel (s := 1) one_ne_zero).continuous.comp
          continuous_ofReal).norm.aestronglyMeasurable
      refine Integrable.mono' hf (hkernel_meas.mul (by fun_prop)) ?_
      · filter_upwards [] with v
        dsimp [f]
        have hnonneg : 0 ≤ ‖gaussKernel 1 (v : ℂ)‖ *
            (Real.exp ((N : ℝ) * Real.sqrt s * |v|) + 1) :=
          mul_nonneg (norm_nonneg _) (add_nonneg (Real.exp_nonneg _) zero_le_one)
        rw [abs_of_nonneg hnonneg]
        have hN : (N : ℝ) * Real.sqrt s ≤ (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg N)
        have hexp : (N : ℝ) * Real.sqrt s * |v| ≤ (N : ℝ) * |v| := by
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right hN (abs_nonneg v)
        exact mul_le_mul_of_nonneg_left
          (add_le_add (Real.exp_le_exp.mpr hexp) (le_refl _)) (norm_nonneg _)
    have hE : MeasurableSet {v : ℝ | (Real.sqrt s)⁻¹ < |v|} := by
      exact measurableSet_Ioi.preimage continuous_abs.measurable
    have hmono :
        ∫ v in {v : ℝ | (Real.sqrt s)⁻¹ < |v|},
            ‖gaussKernel 1 (v : ℂ)‖ *
              (Real.exp ((N : ℝ) * Real.sqrt s * |v|) + 1) ≤
          ∫ v in {v : ℝ | (Real.sqrt s)⁻¹ < |v|}, f v := by
      apply integral_mono (hHs.integrableOn) (hf.integrableOn)
      intro v
      dsimp [f]
      have hN : (N : ℝ) * Real.sqrt s ≤ (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hsqrt_le (Nat.cast_nonneg N)
      have hexp : (N : ℝ) * Real.sqrt s * |v| ≤ (N : ℝ) * |v| := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hN (abs_nonneg v)
      exact mul_le_mul_of_nonneg_left
        (add_le_add (Real.exp_le_exp.mpr hexp) (le_refl _)) (norm_nonneg _)
    simpa [f] using hmono

/-- A rapidly decaying function has a uniform first-order estimate on every unit interval. -/
theorem exists_norm_isRapidlyDecaying_sub_le {a : ℝ → ℂ} (ha : IsRapidlyDecaying a)
    (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x u : ℝ, |u| ≤ 1 →
      ‖a (x - u) - a x‖ ≤ K * Real.exp (-(N : ℝ) * |x|) * |u| := by
  obtain ⟨C, hC⟩ := ha.decay 1 (N + 1)
  let C₀ : ℝ := max C 0
  let K : ℝ := C₀ * Real.exp ((N + 1 : ℕ) : ℝ)
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hdecay : ∀ y : ℝ,
      ‖iteratedDeriv 1 a y‖ ≤ C₀ * Real.exp (-((N + 1 : ℕ) : ℝ) * |y|) := by
    intro y
    exact (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_pos _).le)
  refine ⟨K, mul_nonneg hC₀ (Real.exp_pos _).le, ?_⟩
  intro x u hu
  have hxmem : x ∈ Icc (x - 1) (x + 1) := by constructor <;> linarith
  have humem : x - u ∈ Icc (x - 1) (x + 1) := by
    constructor
    · have hu' := (abs_le.1 hu).2
      linarith
    · have hu' := (abs_le.1 hu).1
      linarith
  have hderiv : ∀ y ∈ Icc (x - 1) (x + 1),
      ‖deriv a y‖ ≤ K * Real.exp (-(N : ℝ) * |x|) := by
    intro y hy
    have hxy : |x - y| ≤ 1 := by
      apply abs_le.2
      constructor <;> linarith [hy.1, hy.2]
    have hxy' : |x| - 1 ≤ |y| := by
      have htriangle : |x| ≤ |x - y| + |y| := by
        calc
          |x| = |(x - y) + y| := by congr 1 <;> ring
          _ ≤ |x - y| + |y| := abs_add_le _ _
      linarith
    have hexp : Real.exp (-((N + 1 : ℕ) : ℝ) * |y|) ≤
        Real.exp ((N + 1 : ℕ) - ((N + 1 : ℕ) : ℝ) * |x|) := by
      apply Real.exp_le_exp.mpr
      have hc : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
      have hstep : -((N + 1 : ℕ) : ℝ) * |y| ≤
          -((N + 1 : ℕ) : ℝ) * (|x| - 1) := by nlinarith [hxy', hc]
      calc
        -((N + 1 : ℕ) : ℝ) * |y| ≤
            -((N + 1 : ℕ) : ℝ) * (|x| - 1) := hstep
        _ = (N + 1 : ℕ) - ((N + 1 : ℕ) : ℝ) * |x| := by
          push_cast
          ring
    rw [← iteratedDeriv_one]
    calc
      ‖iteratedDeriv 1 a y‖ ≤ C₀ * Real.exp (-((N + 1 : ℕ) : ℝ) * |y|) := hdecay y
      _ ≤ C₀ * Real.exp ((N + 1 : ℕ) - ((N + 1 : ℕ) : ℝ) * |x|) := by
        exact mul_le_mul_of_nonneg_left hexp hC₀
      _ ≤ K * Real.exp (-(N : ℝ) * |x|) := by
        dsimp [K]
        rw [mul_assoc, ← Real.exp_add]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            push_cast
            nlinarith [abs_nonneg x])) hC₀
  have hmv : ‖a (x - u) - a x‖ ≤
      (K * Real.exp (-(N : ℝ) * |x|)) * ‖(x - u) - x‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le
    · intro z hz
      exact (ha.contDiff.differentiable (by simp)) z
    · exact hderiv
    · exact convex_Icc (𝕜 := ℝ) _ _
    · exact hxmem
    · exact humem
  simpa [Real.norm_eq_abs] using hmv

/-- The difference of two values of a rapidly decaying function has the weighted far-field bound
used in the Gaussian approximation. -/
theorem exists_norm_isRapidlyDecaying_far_le {a : ℝ → ℂ} (ha : IsRapidlyDecaying a)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x u : ℝ,
      ‖a (x - u) - a x‖ ≤
        C * Real.exp (-(N : ℝ) * |x|) * (Real.exp ((N : ℝ) * |u|) + 1) := by
  obtain ⟨C, hC⟩ := ha.decay 0 N
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hdecay : ∀ y : ℝ, ‖a y‖ ≤ C₀ * Real.exp (-(N : ℝ) * |y|) := by
    intro y
    have hCy : ‖a y‖ ≤ C * Real.exp (-(N : ℝ) * |y|) := by
      simpa using hC y
    exact hCy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_pos _).le)
  refine ⟨C₀, hC₀, ?_⟩
  intro x u
  have htriangle : |x| ≤ |x - u| + |u| := by
    calc
      |x| = |(x - u) + u| := by congr 1 <;> ring
      _ ≤ |x - u| + |u| := abs_add_le _ _
  have hexp : Real.exp (-(N : ℝ) * |x - u|) ≤
      Real.exp (-(N : ℝ) * |x|) * Real.exp ((N : ℝ) * |u|) := by
    rw [← Real.exp_add]
    gcongr
    have hdiff : |x| - |u| ≤ |x - u| := by
      linarith [htriangle]
    have hc : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hmul : -(N : ℝ) * |x - u| ≤ -(N : ℝ) * (|x| - |u|) := by nlinarith [hdiff, hc]
    calc
      -(N : ℝ) * |x - u| ≤ -(N : ℝ) * (|x| - |u|) := hmul
      _ = -(N : ℝ) * |x| + (N : ℝ) * |u| := by ring
  calc
    ‖a (x - u) - a x‖ ≤ ‖a (x - u)‖ + ‖a x‖ := norm_sub_le _ _
    _ ≤ C₀ * Real.exp (-(N : ℝ) * |x - u|) +
          C₀ * Real.exp (-(N : ℝ) * |x|) := add_le_add (hdecay _) (hdecay _)
    _ ≤ C₀ * (Real.exp (-(N : ℝ) * |x|) * Real.exp ((N : ℝ) * |u|)) +
          C₀ * Real.exp (-(N : ℝ) * |x|) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hexp hC₀)
          (le_refl _)
    _ = C₀ * Real.exp (-(N : ℝ) * |x|) *
          (Real.exp ((N : ℝ) * |u|) + 1) := by ring

/- The two tails below are kept separate so that the approximation proof exposes the two uses of
   dominated convergence: the local first moment and the exponentially weighted far tail. -/

/-- [T26], proof of Lemma 3.4; Gaussian convolution converges to its argument in every
exponentially weighted sup-norm. -/
theorem exists_norm_gaussConvReal_sub_le {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → ∀ x : ℝ,
      ‖gaussConvReal s a x - a x‖ ≤ ε * Real.exp (-(N : ℝ) * |x|) := by
  obtain ⟨K, hK, hnear⟩ := exists_norm_isRapidlyDecaying_sub_le ha N
  obtain ⟨C, hC, hfar⟩ := exists_norm_isRapidlyDecaying_far_le ha N
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, Real.sqrt_zero] using
      (tendsto_id.mono_right
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).sqrt
  have hnear_tendsto : Tendsto
      (fun s : ℝ => K * (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|))
      (𝓝[>] 0) (𝓝 0) := by
    have heq :
        (fun s : ℝ => K * (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|)) =ᶠ[𝓝[>] 0]
        (fun s : ℝ => K * (Real.sqrt s * ∫ u : ℝ,
          ‖gaussKernel 1 (u : ℂ)‖ * |u|)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [integral_norm_gaussKernel_mul_abs_scale hs]
    apply Tendsto.congr' heq.symm
    simpa [Function.comp_def, mul_zero, zero_mul] using
      tendsto_const_nhds.mul (hsqrt.mul tendsto_const_nhds)
  have hfar_tendsto : Tendsto
      (fun s : ℝ => C * (∫ u in {u : ℝ | 1 < |u|},
        ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def, mul_zero, zero_mul] using
      tendsto_const_nhds.mul (tendsto_gaussKernel_weighted_far N)
  have hgood : {s : ℝ |
      K * (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) < ε / 2 ∧
      C * (∫ u in {u : ℝ | 1 < |u|},
        ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) < ε / 2} ∈
      𝓝[>] 0 := by
    have h₁ := hnear_tendsto.eventually (Iio_mem_nhds (half_pos hε))
    have h₂ := hfar_tendsto.eventually (Iio_mem_nhds (half_pos hε))
    filter_upwards [h₁, h₂] with s hs₁ hs₂
    exact ⟨hs₁, hs₂⟩
  rcases Metric.mem_nhdsWithin_iff.mp hgood with ⟨δ, hδ, hδsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ x
  have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs]
    exact hsδ
  have hsmall := hδsub ⟨hsball, hs⟩
  let E : Set ℝ := {u : ℝ | |u| ≤ 1}
  let f : ℝ → ℂ := fun u => gaussKernel s (u : ℂ) * (a (x - u) - a x)
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_Iic.preimage continuous_abs.measurable
  have hfi : Integrable f := by
    have h₁ := integrable_gaussConvReal_integrand hs ha x
    have h₂ := (integrable_gaussKernel hs).mul_const (a x)
    have h₃ := h₁.sub h₂
    convert h₃ using 1
    ext u
    dsimp [f]
    ring
  have hnear_integral : ‖∫ u in E, f u‖ ≤
      K * Real.exp (-(N : ℝ) * |x|) *
        (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) := by
    calc
      ‖∫ u in E, f u‖ ≤ ∫ u in E, ‖f u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in E, (K * Real.exp (-(N : ℝ) * |x|)) *
          (‖gaussKernel s (u : ℂ)‖ * |u|) := by
        refine setIntegral_mono_on hfi.norm.integrableOn
          ((integrable_norm_gaussKernel_mul_abs hs).const_mul _).integrableOn hE ?_
        intro u hu
        rw [norm_mul]
        have hu' := hnear x u hu
        exact (mul_le_mul_of_nonneg_left hu'
          (norm_nonneg (gaussKernel s (u : ℂ)))).trans_eq (by ring)
      _ = (K * Real.exp (-(N : ℝ) * |x|)) *
          (∫ u in E, ‖gaussKernel s (u : ℂ)‖ * |u|) := by
        rw [integral_const_mul]
      _ ≤ (K * Real.exp (-(N : ℝ) * |x|)) *
          (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral (s := E) (integrable_norm_gaussKernel_mul_abs hs)
            (ae_of_all _ fun u => mul_nonneg (norm_nonneg _) (abs_nonneg _)))
          (mul_nonneg hK (Real.exp_nonneg _))
  have hfar_integral : ‖∫ u in Eᶜ, f u‖ ≤
      C * Real.exp (-(N : ℝ) * |x|) *
        (∫ u in {u : ℝ | 1 < |u|},
          ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) := by
    have hEc : Eᶜ = {u : ℝ | 1 < |u|} := by
      ext u
      simp [E, not_le]
    rw [hEc]
    have hweight : Integrable (fun u : ℝ =>
        ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) := by
      have heq : (fun u : ℝ =>
          ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) =
          (fun u : ℝ => ‖gaussKernel s (u : ℂ)‖ * Real.exp ((N : ℝ) * |u|)) +
            (fun u : ℝ => ‖gaussKernel s (u : ℂ)‖) := by
        funext u
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact (integrable_gaussKernel_mul_exp N s hs).add
        (integrable_gaussKernel hs).norm
    calc
      ‖∫ u in {u : ℝ | 1 < |u|}, f u‖ ≤ ∫ u in {u : ℝ | 1 < |u|}, ‖f u‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in {u : ℝ | 1 < |u|}, (C * Real.exp (-(N : ℝ) * |x|)) *
          (‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) := by
        refine setIntegral_mono_on hfi.norm.integrableOn (hweight.const_mul _).integrableOn
          (measurableSet_Ioi.preimage continuous_abs.measurable) ?_
        intro u hu
        rw [norm_mul]
        have hu' := hfar x u
        exact (mul_le_mul_of_nonneg_left hu'
          (norm_nonneg (gaussKernel s (u : ℂ)))).trans_eq (by ring)
      _ = (C * Real.exp (-(N : ℝ) * |x|)) *
          (∫ u in {u : ℝ | 1 < |u|},
            ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) := by
        rw [integral_const_mul]
  have hsplit := integral_add_compl hE hfi
  rw [gaussConvReal_sub hs ha x]
  calc
    ‖∫ u, f u‖ = ‖(∫ u in E, f u) + (∫ u in Eᶜ, f u)‖ := by rw [hsplit]
    _ ≤ ‖∫ u in E, f u‖ + ‖∫ u in Eᶜ, f u‖ := norm_add_le _ _
    _ ≤ K * Real.exp (-(N : ℝ) * |x|) *
          (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) +
        C * Real.exp (-(N : ℝ) * |x|) *
          (∫ u in {u : ℝ | 1 < |u|},
            ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) :=
      add_le_add hnear_integral hfar_integral
    _ ≤ ε * Real.exp (-(N : ℝ) * |x|) := by
      have he := Real.exp_nonneg (-(N : ℝ) * |x|)
      have hs₁ := hsmall.1
      have hs₂ := hsmall.2
      have hcoef : K * (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) +
          C * (∫ u in {u : ℝ | 1 < |u|},
            ‖gaussKernel s (u : ℂ)‖ * (Real.exp ((N : ℝ) * |u|) + 1)) < ε := by
        linarith
      calc
        K * Real.exp (-(N : ℝ) * |x|) *
              (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) +
            C * Real.exp (-(N : ℝ) * |x|) *
              (∫ u in {u : ℝ | 1 < |u|},
                ‖gaussKernel s (u : ℂ)‖ *
                  (Real.exp ((N : ℝ) * |u|) + 1)) =
            (K * (∫ u : ℝ, ‖gaussKernel s (u : ℂ)‖ * |u|) +
              C * (∫ u in {u : ℝ | 1 < |u|},
                ‖gaussKernel s (u : ℂ)‖ *
                  (Real.exp ((N : ℝ) * |u|) + 1))) *
              Real.exp (-(N : ℝ) * |x|) := by ring
        _ ≤ ε * Real.exp (-(N : ℝ) * |x|) :=
          mul_le_mul_of_nonneg_right hcoef.le he

end RealConvolution

section ComplexConvolution

/-- [T26], proof of Lemma 3.4; Gaussian convolution with a complex parameter. -/
noncomputable def gaussConv (s : ℝ) (a : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ t : ℝ, gaussKernel s (w - (t : ℂ)) * a t

/-- The Gaussian kernel remains integrable after translation by a complex parameter. -/
theorem integrable_gaussKernel_sub {s : ℝ} (hs : 0 < s) (w : ℂ) :
    Integrable (fun t : ℝ => gaussKernel s (w - (t : ℂ))) := by
  let b : ℝ := 1 / (4 * s)
  let A : ℝ := (Real.sqrt (4 * Real.pi * s))⁻¹ * Real.exp (w.im ^ 2 / (4 * s))
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hbase : Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hshift : Integrable (fun t : ℝ => Real.exp (-b * (w.re - t) ^ 2)) := by
    convert hbase.comp_sub_right w.re using 1
    ext t
    congr 1
    ring
  have hnorm : Integrable (fun t : ℝ => ‖gaussKernel s (w - (t : ℂ))‖) := by
    have hA : Integrable (fun t : ℝ => A * Real.exp (-b * (w.re - t) ^ 2)) :=
      hshift.const_mul A
    convert hA using 1
    ext t
    rw [norm_gaussKernel hs]
    simp only [sub_re, Complex.ofReal_re, sub_im, Complex.ofReal_im, zero_sub, sub_zero,
      zero_pow]
    dsimp [A, b]
    have hexp : (w.im ^ 2 - (w.re - t) ^ 2) / (4 * s) =
        w.im ^ 2 / (4 * s) + -(1 / (4 * s)) * (w.re - t) ^ 2 := by
      field_simp [ne_of_gt hs] <;> ring
    rw [hexp, Real.exp_add]
    ring
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => gaussKernel s (w - (t : ℂ))) :=
    ((differentiable_gaussKernel hs.ne').continuous.comp
      (continuous_const.sub continuous_ofReal)).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  exact hnorm

/-- The complex-parameter convolution integrand is integrable for a positive Gaussian width. -/
theorem integrable_gaussConv_integrand {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (w : ℂ) :
    Integrable (fun t : ℝ => gaussKernel s (w - (t : ℂ)) * a t) := by
  obtain ⟨C, hC, hbound⟩ := ha.exists_bound
  refine Integrable.mono' ((integrable_gaussKernel_sub hs w).norm.const_mul C) ?_ ?_
  · exact (integrable_gaussKernel_sub hs w).aestronglyMeasurable.mul
      ha.contDiff.continuous.aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)).trans_eq (by ring)

/-- On the real axis, the complex-parameter convolution is the real Gaussian convolution. -/
theorem gaussConv_ofReal {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (x : ℝ) :
    gaussConv s a (x : ℂ) = gaussConvReal s a x := by
  let g : ℝ → ℂ := fun u => gaussKernel s (u : ℂ) * a (x - u)
  have hg : Integrable g := by
    simpa [g] using integrable_gaussConvReal_integrand hs ha x
  have hchange := integral_sub_left_eq_self g volume x
  rw [gaussConv, gaussConvReal]
  simpa [g, Complex.ofReal_sub, sub_sub_cancel] using hchange

/-- The complex Gaussian convolution is complex differentiable in its parameter. -/
theorem differentiable_gaussConv {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) : Differentiable ℂ (gaussConv s a) := by
  intro w₀
  obtain ⟨Cₐ, hCₐ, hboundₐ⟩ := ha.exists_bound
  let C₀ : ℝ := max Cₐ 0
  let R : ℝ := ‖w₀‖ + 1
  let A : ℝ := (Real.sqrt (4 * Real.pi * s))⁻¹
  let D : ℝ := C₀ * A / (2 * s) * Real.exp (R ^ 2 / (2 * s))
  let bound : ℝ → ℝ := fun t =>
    D * (|t| + R) * Real.exp (-t ^ 2 / (8 * s))
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hbound_int : Integrable bound := by
    have h₀ := integrable_exp_neg_mul_sq (b := (1 / (8 * s) : ℝ)) (by positivity)
    have h₁ := (integrable_mul_exp_neg_mul_sq (b := (1 / (8 * s) : ℝ))
      (by positivity)).norm
    have h₁' : Integrable (fun t : ℝ => |t| * Real.exp (-t ^ 2 / (8 * s))) := by
      convert h₁ using 1
      ext t
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul]
      congr 1
      congr 1
      field_simp [ne_of_gt hs] <;> ring
    have hsum : Integrable (fun t : ℝ =>
        (|t| + R) * Real.exp (-t ^ 2 / (8 * s))) := by
      have heq : (fun t : ℝ => (|t| + R) * Real.exp (-t ^ 2 / (8 * s))) =
          (fun t : ℝ => |t| * Real.exp (-t ^ 2 / (8 * s))) +
            (fun t : ℝ => R * Real.exp (-(1 / (8 * s)) * t ^ 2)) := by
        funext t
        have hexp : -t ^ 2 / (8 * s) = -(1 / (8 * s)) * t ^ 2 := by
          field_simp [ne_of_gt hs] <;> ring
        rw [hexp]
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact h₁'.add (h₀.const_mul R)
    simpa [bound, D, mul_assoc] using hsum.const_mul D
  let F : ℂ → ℝ → ℂ := fun w t =>
    gaussKernel s (w - (t : ℂ)) * a t
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (-(w - (t : ℂ)) / (2 * s)) * gaussKernel s (w - (t : ℂ)) * a t
  have hkernel_cont : ∀ z : ℂ, Continuous (fun t : ℝ =>
      gaussKernel s (z - (t : ℂ))) := by
    intro z
    exact (differentiable_gaussKernel hs.ne').continuous.comp
      (continuous_const.sub continuous_ofReal)
  have hF'_meas : AEStronglyMeasurable (F' w₀) volume := by
    change AEStronglyMeasurable (fun t : ℝ =>
      (-(w₀ - (t : ℂ)) / (2 * s)) * gaussKernel s (w₀ - (t : ℂ)) * a t)
    have hlinear : Continuous (fun t : ℝ => -(w₀ - (t : ℂ)) / (2 * s)) := by
      fun_prop
    exact ((hlinear.mul (hkernel_cont w₀)).mul ha.contDiff.continuous).aestronglyMeasurable
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (α := ℝ) (μ := volume) (F := F) (x₀ := w₀) (s := Metric.ball w₀ 1)
    (bound := bound) (F' := F')
    (Metric.ball_mem_nhds w₀ zero_lt_one)
    (Eventually.of_forall fun w => by
      exact (integrable_gaussConv_integrand hs ha w).aestronglyMeasurable)
    (integrable_gaussConv_integrand hs ha w₀)
    hF'_meas
    (by
      filter_upwards [] with t w hw
      have hw' : ‖w - w₀‖ < 1 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hw
      have hw_norm : ‖w‖ ≤ R := by
        dsimp [R]
        calc
          ‖w‖ ≤ ‖w - w₀‖ + ‖w₀‖ := by
            simpa [sub_add_cancel] using (norm_add_le (w - w₀) w₀)
          _ ≤ 1 + ‖w₀‖ := by linarith [hw']
          _ = ‖w₀‖ + 1 := by ring
      have hreal : |w.re| ≤ R :=
        (abs_re_le_norm w).trans hw_norm
      have himag : |w.im| ≤ R :=
        (abs_im_le_norm w).trans hw_norm
      have hreal_sq : w.re ^ 2 ≤ R ^ 2 := by
        have hsq : 0 ≤ (R - |w.re|) * (R + |w.re|) :=
          mul_nonneg (sub_nonneg.mpr hreal) (add_nonneg hR (abs_nonneg _))
        nlinarith [sq_abs w.re, hsq]
      have himag_sq : w.im ^ 2 ≤ R ^ 2 := by
        have hsq : 0 ≤ (R - |w.im|) * (R + |w.im|) :=
          mul_nonneg (sub_nonneg.mpr himag) (add_nonneg hR (abs_nonneg _))
        nlinarith [sq_abs w.im, hsq]
      have hquad : t ^ 2 / 2 - R ^ 2 ≤ (w.re - t) ^ 2 := by
        nlinarith [sq_nonneg (t - 2 * w.re), hreal_sq]
      have hkernel : ‖gaussKernel s (w - (t : ℂ))‖ ≤
          A * Real.exp (R ^ 2 / (2 * s)) * Real.exp (-t ^ 2 / (8 * s)) := by
        rw [norm_gaussKernel hs]
        simp only [sub_re, Complex.ofReal_re, sub_im, Complex.ofReal_im, zero_sub, sub_zero,
          zero_pow]
        have hexp : (w.im ^ 2 - (w.re - t) ^ 2) / (4 * s) ≤
            R ^ 2 / (2 * s) - t ^ 2 / (8 * s) := by
          have hnum : w.im ^ 2 - (w.re - t) ^ 2 ≤ 2 * R ^ 2 - t ^ 2 / 2 := by
            linarith [hquad, himag_sq]
          calc
            (w.im ^ 2 - (w.re - t) ^ 2) / (4 * s) ≤
                (2 * R ^ 2 - t ^ 2 / 2) / (4 * s) :=
              (div_le_div_iff₀ (by positivity) (by positivity)).2
                (mul_le_mul_of_nonneg_right hnum (by positivity))
            _ = R ^ 2 / (2 * s) - t ^ 2 / (8 * s) := by
              field_simp [ne_of_gt hs]
              ring
        change A * Real.exp ((w.im ^ 2 - (w.re - t) ^ 2) / (4 * s)) ≤ _
        calc
          A * Real.exp ((w.im ^ 2 - (w.re - t) ^ 2) / (4 * s)) ≤
              A * Real.exp (R ^ 2 / (2 * s) - t ^ 2 / (8 * s)) := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hA
          _ = A * Real.exp (R ^ 2 / (2 * s)) * Real.exp (-t ^ 2 / (8 * s)) := by
            have hexp : R ^ 2 / (2 * s) - t ^ 2 / (8 * s) =
                R ^ 2 / (2 * s) + (-t ^ 2 / (8 * s)) := by ring
            rw [hexp, Real.exp_add]
            ring
      have hnorm : ‖w - (t : ℂ)‖ ≤ R + |t| := by
        calc
          ‖w - (t : ℂ)‖ ≤ ‖w‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
          _ ≤ R + |t| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact add_le_add_left hw_norm _
      have hmul : ‖a t‖ ≤ C₀ := (hboundₐ t).trans (le_max_left _ _)
      have hden : ‖(2 : ℂ) * (s : ℂ)‖ = 2 * s := by
        rw [norm_mul]
        norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      have hscalar : ‖-(w - (t : ℂ)) / (2 * s)‖ = ‖w - (t : ℂ)‖ / (2 * s) := by
        rw [norm_div, norm_neg, hden]
      change ‖(-(w - (t : ℂ)) / (2 * s)) *
          gaussKernel s (w - (t : ℂ)) * a t‖ ≤ bound t
      rw [norm_mul, norm_mul, hscalar]
      calc
        (‖w - (t : ℂ)‖ / (2 * s)) * ‖gaussKernel s (w - (t : ℂ))‖ * ‖a t‖ ≤
            ((R + |t|) / (2 * s)) *
              (A * Real.exp (R ^ 2 / (2 * s)) *
                Real.exp (-t ^ 2 / (8 * s))) * C₀ := by
                  gcongr
        _ = bound t := by
          dsimp [bound, D, A]
          ring_nf)
    (hbound_int)
    (by
      filter_upwards [] with t w hw
      have hsub : HasDerivAt (fun z : ℂ => z - (t : ℂ)) 1 w := by
        simpa using (hasDerivAt_id w).sub_const (t : ℂ)
      have hterm := ((hasDerivAt_gaussKernel hs.ne' (w - (t : ℂ))).comp w hsub).mul_const (a t)
      have heq : (-(w - (t : ℂ)) / (2 * (s : ℂ))) * gaussKernel s (w - (t : ℂ)) * a t =
          -((w - (t : ℂ)) / (2 * (s : ℂ))) * gaussKernel s (w - (t : ℂ)) * 1 * a t := by
        ring
      show HasDerivAt (fun x : ℂ => gaussKernel s (x - (t : ℂ)) * a t)
        ((-(w - (t : ℂ)) / (2 * (s : ℂ))) * gaussKernel s (w - (t : ℂ)) * a t) w
      rw [heq]
      exact hterm)
  change DifferentiableAt ℂ (fun w : ℂ => ∫ t : ℝ,
    gaussKernel s (w - (t : ℂ)) * a t) w₀
  exact hparam.2.differentiableAt

/-- Gaussian convolution has rapid exponential decay uniformly on every horizontal strip. -/
theorem exists_norm_gaussConv_le {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (N : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.im| ≤ B →
      ‖gaussConv s a w‖ ≤ C * Real.exp (-(N : ℝ) * |w.re|) := by
  obtain ⟨Cₐ, hCₐ⟩ := ha.decay 0 N
  let C₀ : ℝ := max Cₐ 0
  let I : ℝ := ∫ t : ℝ,
    ‖gaussKernel s (t : ℂ)‖ * Real.exp ((N : ℝ) * |t|)
  let C : ℝ := C₀ * Real.exp (B ^ 2 / (4 * s)) * I
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg (fun t => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
  refine ⟨C, mul_nonneg (mul_nonneg hC₀ (Real.exp_nonneg _)) hI, ?_⟩
  intro w hw
  have hB : 0 ≤ B := (abs_nonneg w.im).trans hw
  have himag_sq : w.im ^ 2 ≤ B ^ 2 := by
    have hsq : 0 ≤ (B - |w.im|) * (B + |w.im|) :=
      mul_nonneg (sub_nonneg.mpr hw) (add_nonneg hB (abs_nonneg _))
    nlinarith [sq_abs w.im, hsq]
  have hdecay : ∀ t : ℝ, ‖a t‖ ≤ C₀ * Real.exp (-(N : ℝ) * |t|) := by
    intro t
    have hCt : ‖a t‖ ≤ Cₐ * Real.exp (-(N : ℝ) * |t|) := by
      simpa using hCₐ t
    exact hCt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hweight : Integrable (fun t : ℝ =>
      ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
        Real.exp ((N : ℝ) * |w.re - t|)) := by
    have hweight' := (integrable_gaussKernel_mul_exp N s hs).comp_sub_right w.re
    convert hweight' using 1
    ext t
    rw [norm_gaussKernel hs, norm_gaussKernel hs]
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_pow, neg_zero, zero_sub]
    rw [sub_sq_comm, abs_sub_comm]
  have hweight_eq : (∫ t : ℝ, ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
      Real.exp ((N : ℝ) * |w.re - t|)) = I := by
    have hchange := integral_sub_left_eq_self
      (fun t : ℝ => ‖gaussKernel s (t : ℂ)‖ * Real.exp ((N : ℝ) * |t|)) volume w.re
    simpa [I] using hchange
  have hmajor : ∀ t : ℝ,
      ‖gaussKernel s (w - (t : ℂ))‖ * ‖a t‖ ≤
        (C₀ * Real.exp (B ^ 2 / (4 * s)) *
          Real.exp (-(N : ℝ) * |w.re|)) *
          (‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
            Real.exp ((N : ℝ) * |w.re - t|)) := by
    intro t
    have hkernel : ‖gaussKernel s (w - (t : ℂ))‖ ≤
        Real.exp (B ^ 2 / (4 * s)) *
          ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ := by
      rw [norm_gaussKernel hs, norm_gaussKernel hs]
      simp only [sub_re, Complex.ofReal_re, sub_im, Complex.ofReal_im, zero_sub, sub_zero]
      have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [hzero, zero_sub]
      have hexp : (w.im ^ 2 - (w.re - t) ^ 2) / (4 * s) ≤
          B ^ 2 / (4 * s) - (w.re - t) ^ 2 / (4 * s) := by
        have hnum : w.im ^ 2 - (w.re - t) ^ 2 ≤
            B ^ 2 - (w.re - t) ^ 2 := by
          linarith [himag_sq]
        calc
          (w.im ^ 2 - (w.re - t) ^ 2) / (4 * s) ≤
              (B ^ 2 - (w.re - t) ^ 2) / (4 * s) :=
            (div_le_div_iff₀ (by positivity) (by positivity)).2
              (mul_le_mul_of_nonneg_right hnum (by positivity))
          _ = B ^ 2 / (4 * s) - (w.re - t) ^ 2 / (4 * s) := by ring
      change (Real.sqrt (4 * Real.pi * s))⁻¹ *
          Real.exp ((w.im ^ 2 - (w.re - t) ^ 2) / (4 * s)) ≤
        Real.exp (B ^ 2 / (4 * s)) *
          ((Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp (-(w.re - t) ^ 2 / (4 * s)))
      calc
        (Real.sqrt (4 * Real.pi * s))⁻¹ *
            Real.exp ((w.im ^ 2 - (w.re - t) ^ 2) / (4 * s)) ≤
            (Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (B ^ 2 / (4 * s) - (w.re - t) ^ 2 / (4 * s)) := by
                exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = Real.exp (B ^ 2 / (4 * s)) *
            ((Real.sqrt (4 * Real.pi * s))⁻¹ *
              Real.exp (-(w.re - t) ^ 2 / (4 * s))) := by
                have hexp : B ^ 2 / (4 * s) - (w.re - t) ^ 2 / (4 * s) =
                    B ^ 2 / (4 * s) + (-(w.re - t) ^ 2 / (4 * s)) := by ring
                rw [hexp, Real.exp_add]
                ring
    have hexp : Real.exp (-(N : ℝ) * |t|) ≤
        Real.exp (-(N : ℝ) * |w.re|) *
          Real.exp ((N : ℝ) * |w.re - t|) := by
      rw [← Real.exp_add]
      gcongr
      have htri : |w.re| ≤ |t| + |w.re - t| := by
        calc
          |w.re| = |t + (w.re - t)| := by congr 1 <;> ring
          _ ≤ |t| + |w.re - t| := abs_add_le _ _
      have hdiff : |w.re| - |w.re - t| ≤ |t| := by
        linarith [htri]
      have hc : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hmul : -(N : ℝ) * |t| ≤ -(N : ℝ) * (|w.re| - |w.re - t|) := by
        nlinarith [hdiff, hc]
      calc
        -(N : ℝ) * |t| ≤ -(N : ℝ) * (|w.re| - |w.re - t|) := hmul
        _ = -(N : ℝ) * |w.re| + (N : ℝ) * |w.re - t| := by ring
    calc
      ‖gaussKernel s (w - (t : ℂ))‖ * ‖a t‖ ≤
          (Real.exp (B ^ 2 / (4 * s)) *
            ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖) *
            (C₀ * Real.exp (-(N : ℝ) * |t|)) := by
              exact mul_le_mul hkernel (hdecay t) (norm_nonneg _) (by positivity)
      _ ≤ (C₀ * Real.exp (B ^ 2 / (4 * s)) *
            Real.exp (-(N : ℝ) * |w.re|)) *
          (‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
            Real.exp ((N : ℝ) * |w.re - t|)) := by
              calc
                (Real.exp (B ^ 2 / (4 * s)) *
                    ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖) *
                    (C₀ * Real.exp (-(N : ℝ) * |t|)) =
                    (C₀ * Real.exp (B ^ 2 / (4 * s)) *
                      ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖) *
                      Real.exp (-(N : ℝ) * |t|) := by ring
                _ ≤ (C₀ * Real.exp (B ^ 2 / (4 * s)) *
                      ‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖) *
                      (Real.exp (-(N : ℝ) * |w.re|) *
                        Real.exp ((N : ℝ) * |w.re - t|)) :=
                  mul_le_mul_of_nonneg_left hexp (by positivity)
                _ = _ := by ring
      _ = _ := by ring
  have hnorm_int := integrable_gaussConv_integrand hs ha w
  have hmajor_int : Integrable (fun t : ℝ =>
      (C₀ * Real.exp (B ^ 2 / (4 * s)) * Real.exp (-(N : ℝ) * |w.re|)) *
        (‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
          Real.exp ((N : ℝ) * |w.re - t|))) := hweight.const_mul _
  calc
    ‖gaussConv s a w‖ ≤ ∫ t : ℝ,
        ‖gaussKernel s (w - (t : ℂ)) * a t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C₀ * Real.exp (B ^ 2 / (4 * s)) *
        Real.exp (-(N : ℝ) * |w.re|)) *
        (‖gaussKernel s ((w.re - t : ℝ) : ℂ)‖ *
          Real.exp ((N : ℝ) * |w.re - t|)) := by
      apply integral_mono hnorm_int.norm hmajor_int
      intro t
      simpa only [norm_mul] using hmajor t
    _ = C₀ * Real.exp (B ^ 2 / (4 * s)) *
        Real.exp (-(N : ℝ) * |w.re|) * I := by
      rw [integral_const_mul, hweight_eq]
    _ = C * Real.exp (-(N : ℝ) * |w.re|) := by
      dsimp [C]
      ring

end ComplexConvolution

end

end MobiusCPT
