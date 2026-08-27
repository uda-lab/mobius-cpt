import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Finset
import MobiusCPT.TestFunctions.Complete
import MobiusCPT.TestFunctions.Monomial

/-!
# MobiusCPT.TestFunctions.Fourier

Fourier coefficients, rapid decay, and Fourier convergence in the `C^∞` topology of the
smooth test-function space on the circle.
-/

namespace MobiusCPT

open Filter Function MeasureTheory Set
open AddCircle
open scoped ContDiff Interval Topology

noncomputable section

/-- Positivity of the period used for the additive-circle Fourier model. -/
instance fact_pos_two_mul_pi : Fact ((0 : ℝ) < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- The angle picture of a test function, descended to `ℝ / (2πℤ)`. -/
def toAddCircle (f : TestFn) : AddCircle (2 * Real.pi) → ℂ :=
  (periodic_toAngle f).lift

/-- Evaluation of the descended angle picture at a real representative. -/
@[simp] theorem toAddCircle_coe (f : TestFn) (θ : ℝ) :
    toAddCircle f (θ : AddCircle (2 * Real.pi)) = toAngle f θ :=
  Function.Periodic.lift_coe _ _

/-- The descended angle picture is continuous on the additive circle. -/
theorem continuous_toAddCircle (f : TestFn) : Continuous (toAddCircle f) := by
  unfold toAddCircle Function.Periodic.lift
  exact (contDiff_toAngle f).continuous.quotient_liftOn' _

/-- [T26], §3; the `j`-th angle derivative as a continuous function on `ℝ / (2πℤ)`. -/
def angleDerivCircle (j : ℕ) (f : TestFn) : C(AddCircle (2 * Real.pi), ℂ) where
  toFun := (periodic_angleDeriv j f).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (contDiff_angleDeriv j f).continuous.quotient_liftOn' _

/-- Evaluation of a descended angle derivative at a real representative. -/
@[simp] theorem angleDerivCircle_coe (j : ℕ) (f : TestFn) (θ : ℝ) :
    angleDerivCircle j f (θ : AddCircle (2 * Real.pi)) = angleDeriv j f θ :=
  rfl

/-- The zeroth descended angle derivative is the descended angle picture. -/
theorem angleDerivCircle_zero (f : TestFn) :
    ⇑(angleDerivCircle 0 f) = toAddCircle f := by
  funext x
  refine Quotient.inductionOn' x ?_
  intro θ
  simp [angleDeriv, iteratedDeriv_zero]

/-- [T26], §3; the `n`-th Fourier coefficient of a smooth test function, defined through
mathlib's normalized-Haar `fourierCoeff` on `AddCircle (2 * Real.pi)`. -/
def fourierCoef (f : TestFn) (n : ℤ) : ℂ :=
  fourierCoeff (toAddCircle f) n

/-- The Fourier coefficient of the `j`-th angle derivative. -/
def fourierCoefDeriv (j : ℕ) (f : TestFn) (n : ℤ) : ℂ :=
  fourierCoeff (angleDerivCircle j f) n

/-- The derivative coefficient at order zero is the original Fourier coefficient. -/
theorem fourierCoefDeriv_zero (f : TestFn) (n : ℤ) :
    fourierCoefDeriv 0 f n = fourierCoef f n := by
  rw [fourierCoefDeriv, fourierCoef, angleDerivCircle_zero]

/-- The additive-circle Fourier character is the angle picture of the corresponding monomial. -/
theorem fourier_eq_toAngle_monomial (n : ℤ) (θ : ℝ) :
    fourier n (θ : AddCircle (2 * Real.pi)) = toAngle (monomial n) θ := by
  rw [fourier_coe_apply, toAngle_monomial]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

/-- Descending a monomial to the additive circle gives mathlib's Fourier character. -/
theorem toAddCircle_monomial (n : ℤ) :
    toAddCircle (monomial n) = fourier n := by
  funext x
  refine Quotient.inductionOn' x ?_
  intro θ
  rw [toAddCircle_coe, fourier_eq_toAngle_monomial]

/-- The Fourier coefficient of a monomial is the corresponding Kronecker delta. -/
theorem fourierCoef_monomial (m n : ℤ) :
    fourierCoef (monomial m) n = if n = m then 1 else 0 := by
  rw [fourierCoef, toAddCircle_monomial, fourierCoeff_fourier, Pi.single_apply]

/-- A Fourier coefficient of an angle derivative is bounded by its uniform norm. -/
theorem norm_fourierCoefDeriv_le (j : ℕ) (f : TestFn) (n : ℤ) :
    ‖fourierCoefDeriv j f n‖ ≤ ‖angleDerivB j f‖ := by
  unfold fourierCoefDeriv fourierCoeff
  calc
    ‖∫ t : AddCircle (2 * Real.pi), fourier (-n) t • angleDerivCircle j f t
        ∂haarAddCircle‖ ≤
        ‖angleDerivB j f‖ * (@haarAddCircle (2 * Real.pi) _).real univ := by
      apply norm_integral_le_of_norm_le_const
      apply Eventually.of_forall
      intro t
      refine Quotient.inductionOn' t ?_
      intro θ
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, angleDerivCircle_coe]
      exact norm_angleDeriv_le j f θ
    _ = ‖angleDerivB j f‖ := by simp

/-- A Fourier coefficient is bounded by the uniform norm of the original angle function. -/
theorem norm_fourierCoef_le (f : TestFn) (n : ℤ) :
    ‖fourierCoef f n‖ ≤ ‖angleDerivB 0 f‖ := by
  rw [← fourierCoefDeriv_zero f n]
  exact norm_fourierCoefDeriv_le 0 f n

private theorem angleDerivCircle_eq_liftIoc (j : ℕ) (f : TestFn) :
    ⇑(angleDerivCircle j f) =
      AddCircle.liftIoc (2 * Real.pi) 0 (angleDeriv j f) := by
  funext x
  obtain ⟨θ, hθ, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [angleDerivCircle_coe, AddCircle.liftIoc_coe_apply]
  simpa only [zero_add] using hθ

private theorem fourierCoefDeriv_eq_fourierCoeffOn (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv j f n =
      fourierCoeffOn (show (0 : ℝ) < 2 * Real.pi by positivity) (angleDeriv j f) n := by
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0) (angleDeriv j f) n
  simp only [zero_add] at h
  rw [fourierCoefDeriv, angleDerivCircle_eq_liftIoc, h]

private theorem hasDerivAt_angleDeriv (j : ℕ) (f : TestFn) (θ : ℝ) :
    HasDerivAt (angleDeriv j f) (angleDeriv (j + 1) f θ) θ := by
  rw [angleDeriv, angleDeriv, iteratedDeriv_succ]
  exact ((contDiff_angleDeriv j f).differentiable (by simp)).differentiableAt.hasDerivAt

/-- [T26], §3; differentiation multiplies the `n`-th Fourier coefficient by `n i`.
This identity includes the zero mode. -/
theorem fourierCoefDeriv_succ (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv (j + 1) f n =
      (n : ℂ) * Complex.I * fourierCoefDeriv j f n := by
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, zero_mul]
    rw [fourierCoefDeriv, fourierCoeff_eq_intervalIntegral _ 0 0]
    simp only [neg_zero, fourier_zero, one_smul, zero_add]
    simp_rw [angleDerivCircle_coe]
    have hderiv : deriv (angleDeriv j f) = angleDeriv (j + 1) f := by
      funext θ
      exact (hasDerivAt_angleDeriv j f θ).deriv
    have hftc :
        ∫ θ in (0 : ℝ)..2 * Real.pi, angleDeriv (j + 1) f θ =
          angleDeriv j f (2 * Real.pi) - angleDeriv j f 0 := by
      apply intervalIntegral.integral_deriv_eq_sub' (angleDeriv j f) hderiv
      · intro θ _
        exact ((contDiff_angleDeriv j f).differentiable (by simp)).differentiableAt
      · exact (contDiff_angleDeriv (j + 1) f).continuous.continuousOn
    rw [hftc]
    have hperiod := periodic_angleDeriv j f 0
    simp only [zero_add] at hperiod
    rw [hperiod, sub_self, smul_zero]
  · have hibp := fourierCoeffOn_of_hasDerivAt
        (show (0 : ℝ) < 2 * Real.pi by positivity) hn
        (fun θ _ => hasDerivAt_angleDeriv j f θ)
        ((contDiff_angleDeriv (j + 1) f).continuous.intervalIntegrable 0 (2 * Real.pi))
    have hperiod := periodic_angleDeriv j f 0
    simp only [zero_add] at hperiod
    simp only [hperiod, sub_self, mul_zero, zero_sub] at hibp
    rw [fourierCoefDeriv_eq_fourierCoeffOn,
      fourierCoefDeriv_eq_fourierCoeffOn, hibp]
    field_simp [hn, Real.pi_ne_zero, Complex.I_ne_zero]
    push_cast
    ring

/-- [T26], §3; the `j`-th derivative coefficient is `(n i)^j` times the original
coefficient. -/
theorem fourierCoefDeriv_eq (j : ℕ) (f : TestFn) (n : ℤ) :
    fourierCoefDeriv j f n =
      ((n : ℂ) * Complex.I) ^ j * fourierCoef f n := by
  induction j with
  | zero =>
      simp only [pow_zero, one_mul]
      exact fourierCoefDeriv_zero f n
  | succ j ih =>
      rw [fourierCoefDeriv_succ, ih, pow_succ]
      ring

/-- [T26], §3; Fourier coefficients decay with every prescribed polynomial weight. -/
theorem norm_fourierCoef_mul_pow_le (j : ℕ) (f : TestFn) (n : ℤ) :
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ ≤ ‖angleDerivB j f‖ := by
  have h := norm_fourierCoefDeriv_le j f n
  rw [fourierCoefDeriv_eq, norm_mul, norm_pow, norm_mul,
    Complex.norm_intCast, Complex.norm_I, mul_one] at h
  exact h

/-- [T26], §3; rapid decay bounded by the literal `C^j` seminorm. -/
theorem norm_fourierCoef_mul_pow_le_cnorm (j : ℕ) (f : TestFn) (n : ℤ) :
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ ≤ (cnorm j f : ℝ) := by
  refine (norm_fourierCoef_mul_pow_le j f n).trans ?_
  rw [cnorm_eq]
  exact Finset.single_le_sum (fun k _ => norm_nonneg (angleDerivB k f)) (by simp)

/-- [T26], §3; every polynomially weighted sequence of Fourier coefficients is summable. -/
theorem summable_norm_fourierCoef_mul_pow (j : ℕ) (f : TestFn) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ j * ‖fourierCoef f n‖) := by
  let C : ℝ := ‖angleDerivB (j + 2) f‖
  have hmajor : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left C
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnreal
  have hdecay := norm_fourierCoef_mul_pow_le (j + 2) f n
  have hnonneg : 0 ≤ |(n : ℝ)| ^ j * ‖fourierCoef f n‖ :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  calc
    |(n : ℝ)| ^ j * ‖fourierCoef f n‖ =
        (|(n : ℝ)| ^ (j + 2) * ‖fourierCoef f n‖) / |(n : ℝ)| ^ 2 := by
          field_simp [habs]
          ring
    _ ≤ C / |(n : ℝ)| ^ 2 :=
      div_le_div_of_nonneg_right hdecay (sq_nonneg _)
    _ = C * (1 / (n : ℝ) ^ 2) := by rw [sq_abs]; ring

private theorem hasDerivAt_toAngle_monomial (n : ℤ) (θ : ℝ) :
    HasDerivAt (toAngle (monomial n))
      (((n : ℂ) * Complex.I) * toAngle (monomial n) θ) θ := by
  have h := hasDerivAt_fourier (2 * Real.pi) n θ
  convert h using 1
  · funext x
    exact (fourier_eq_toAngle_monomial n x).symm
  · rw [fourier_eq_toAngle_monomial]
    field_simp [Real.pi_ne_zero]
    push_cast
    ring

/-- The `j`-th angle derivative of a monomial is `(n i)^j exp(n θ i)`. -/
theorem angleDeriv_monomial (j : ℕ) (n : ℤ) (θ : ℝ) :
    angleDeriv j (monomial n) θ =
      ((n : ℂ) * Complex.I) ^ j *
        Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
  induction j generalizing θ with
  | zero => simp [angleDeriv, iteratedDeriv_zero, toAngle_monomial]
  | succ j ih =>
      rw [angleDeriv, iteratedDeriv_succ]
      have hfun :
          iteratedDeriv j (toAngle (monomial n)) =
            fun x => ((n : ℂ) * Complex.I) ^ j * toAngle (monomial n) x := by
        funext x
        simpa only [angleDeriv, toAngle_monomial] using ih x
      rw [hfun]
      have h := (hasDerivAt_toAngle_monomial n θ).const_mul
        (((n : ℂ) * Complex.I) ^ j)
      rw [h.deriv, toAngle_monomial, pow_succ]
      ring

/-- Every angle derivative is the pointwise sum of its differentiated Fourier series. -/
theorem hasSum_angleDeriv (j : ℕ) (f : TestFn) (θ : ℝ) :
    HasSum
      (fun n : ℤ => fourierCoef f n * ((n : ℂ) * Complex.I) ^ j *
        Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
      (angleDeriv j f θ) := by
  have hs : Summable (fun n : ℤ => ((n : ℂ) * Complex.I) ^ j * fourierCoef f n) := by
    apply (summable_norm_fourierCoef_mul_pow j f).of_norm_bounded
    intro n
    rw [norm_mul, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_I, mul_one]
  have hcoeff :
      fourierCoeff (angleDerivCircle j f) =
        fun n : ℤ => ((n : ℂ) * Complex.I) ^ j * fourierCoef f n := by
    funext n
    exact fourierCoefDeriv_eq j f n
  have hs' : Summable (fourierCoeff (angleDerivCircle j f)) := by
    rw [hcoeff]
    exact hs
  have h := has_pointwise_sum_fourier_series_of_summable
    (f := angleDerivCircle j f) hs' (θ : AddCircle (2 * Real.pi))
  have h' :
      HasSum
        (fun n : ℤ => fourierCoef f n * ((n : ℂ) * Complex.I) ^ j *
          fourier n (θ : AddCircle (2 * Real.pi)))
        (angleDerivCircle j f (θ : AddCircle (2 * Real.pi))) := by
    apply h.congr_fun
    intro n
    rw [hcoeff]
    simp only [smul_eq_mul]
    ring
  simpa only [angleDerivCircle_coe, fourier_eq_toAngle_monomial, toAngle_monomial] using h'

private theorem norm_angleDerivB_smul_monomial_le
    (j : ℕ) (c : ℂ) (n : ℤ) :
    ‖angleDerivB j (c • monomial n)‖ ≤ |(n : ℝ)| ^ j * ‖c‖ := by
  rw [BoundedContinuousFunction.norm_le (mul_nonneg (pow_nonneg (abs_nonneg _) _)
    (norm_nonneg _))]
  intro θ
  rw [angleDerivB_apply]
  have hsmul := congrFun (angleDeriv_smul j c (monomial n)) θ
  rw [hsmul, Pi.smul_apply, smul_eq_mul, angleDeriv_monomial]
  rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_I,
    mul_one]
  have hexp :
      ‖Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
    convert Complex.norm_exp_ofReal_mul_I ((n : ℝ) * θ) using 1
    congr 1
    push_cast
    ring
  rw [hexp, mul_one]
  exact le_of_eq (by ring)

private theorem hasSum_angleDerivB (j : ℕ) (f : TestFn) :
    HasSum (fun n : ℤ => angleDerivB j (fourierCoef f n • monomial n))
      (angleDerivB j f) := by
  have hs : Summable (fun n : ℤ => angleDerivB j (fourierCoef f n • monomial n)) := by
    apply (summable_norm_fourierCoef_mul_pow j f).of_norm_bounded
    intro n
    exact norm_angleDerivB_smul_monomial_le j (fourierCoef f n) n
  have htarget :
      ∑' n : ℤ, angleDerivB j (fourierCoef f n • monomial n) = angleDerivB j f := by
    apply BoundedContinuousFunction.ext
    intro θ
    have heval := (BoundedContinuousFunction.evalCLM ℂ θ).hasSum hs.hasSum
    have hpoint := hasSum_angleDeriv j f θ
    apply HasSum.unique heval
    convert hpoint using 1
    · funext n
      simp only [BoundedContinuousFunction.evalCLM_apply]
      rw [angleDerivB_apply]
      have hsmul := congrFun (angleDeriv_smul j (fourierCoef f n) (monomial n)) θ
      rw [hsmul, Pi.smul_apply, smul_eq_mul, angleDeriv_monomial]
      ring
    · exact angleDerivB_apply j f θ
  rw [← htarget]
  exact hs.hasSum

/-- [T26], §3; the symmetric Fourier sum through frequency `N`. -/
def fourierPartialSum (f : TestFn) (N : ℕ) : TestFn :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoef f n • monomial n

/-- [T26], §3; the Fourier series of a test function sums to it in the `C^∞(S¹)` topology. -/
theorem hasSum_fourierSeries (f : TestFn) :
    HasSum (fun n : ℤ => fourierCoef f n • monomial n) f := by
  refine (isInducing_angleDerivs.tendsto_nhds_iff).mpr ?_
  rw [tendsto_pi_nhds]
  intro j
  have hswap : ∀ i : Finset ℤ,
      angleDerivB j (∑ x ∈ i, fourierCoef f x • monomial x)
        = ∑ x ∈ i, angleDerivB j (fourierCoef f x • monomial x) := by
    intro i
    exact map_sum (angleDerivBₗ j) _ i
  simp only [Function.comp_apply, angleDerivsₗ, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, hswap]
  exact hasSum_angleDerivB j f

/-- [T26], §3; symmetric Fourier partial sums converge in the `C^∞(S¹)` topology. -/
theorem tendsto_fourierPartialSum (f : TestFn) :
    Tendsto (fourierPartialSum f) atTop (𝓝 f) := by
  have hfinset :
      Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (β := ℕ) ?_ ?_
    · intro M N hMN
      exact Finset.Icc_subset_Icc (neg_le_neg (Int.ofNat_le.2 hMN))
        (Int.ofNat_le.2 hMN)
    · intro n
      refine ⟨n.natAbs, ?_⟩
      rw [Finset.mem_Icc]
      constructor
      · simpa only [Int.natCast_natAbs] using neg_abs_le n
      · simpa only [Int.natCast_natAbs] using le_abs_self n
  exact (hasSum_fourierSeries f).comp hfinset

/-- Convergence of symmetric Fourier partial sums in every literal `C^N` seminorm. -/
theorem tendsto_cnorm_fourierPartialSum (N : ℕ) (f : TestFn) :
    Tendsto
      (fun M => ((cnorm N (fourierPartialSum f M - f) : NNReal) : ℝ))
      atTop (𝓝 0) :=
  (tendsto_iff_cnorm (fourierPartialSum f) f).mp
    (tendsto_fourierPartialSum f) N

end

end MobiusCPT
