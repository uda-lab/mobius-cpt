import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import MobiusCPT.Analysis.BoostChart
import MobiusCPT.Analysis.FlatCalculus
import MobiusCPT.Analysis.GaussianConv
import MobiusCPT.TestFunctions.Analytic

/-!
# Gaussian analytic approximants

This file transports the Gaussian convolution from the boost coordinate to the exterior of the
unit disc.  The estimates at the two ends of the boost strip are used twice: first for the values
of the approximant, and then, through Cauchy's estimate, for all of its complex derivatives.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/- The complement of the branch cut is open. -/
/-- The branch cut is a closed subset of the complex plane. -/
theorem isClosed_cutSegment : IsClosed cutSegment := by
  change IsClosed ({z : ℂ | z.im = 0} ∩
    ({z : ℂ | -1 ≤ z.re} ∩ {z : ℂ | z.re ≤ 1}))
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const))

/- This name is used repeatedly when constructing neighbourhoods on which the branch is fixed. -/
/-- The complement of the branch cut is open. -/
theorem isOpen_compl_cutSegment : IsOpen cutSegmentᶜ := isClosed_cutSegment.isOpen_compl

/- The value at either endpoint is filled in by zero. -/
/-- [T26], Lemma 3.4; the Gaussian smoothing transported from the boost strip to the exterior. -/
noncomputable def stripApprox (s : ℝ) (a : ℝ → ℂ) (z : ℂ) : ℂ :=
  if z = 1 ∨ z = -1 then 0 else gaussConv s a (boostCoord z) / z

/-- Off the two filled-in endpoints, the approximant has its quotient formula. -/
theorem stripApprox_of_notMem_cutSegment {s : ℝ} {a : ℝ → ℂ} {z : ℂ}
    (hz : z ∉ cutSegment) :
    stripApprox s a z = gaussConv s a (boostCoord z) / z := by
  have hz1 : z ≠ 1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzneg : z ≠ -1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  simp [stripApprox, hz1, hzneg]

/-- The quotient formula is holomorphic on the complement of the branch cut. -/
theorem analyticAt_stripApprox {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) {z : ℂ} (hz : z ∉ cutSegment) :
    AnalyticAt ℂ (stripApprox s a) z := by
  have hz1 : z ≠ 1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzneg : z ≠ -1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hgauss : AnalyticAt ℂ (gaussConv s a) (boostCoord z) := by
    apply (differentiable_gaussConv hs ha).differentiableOn.analyticAt
    exact univ_mem
  have hquot : AnalyticAt ℂ
      (fun w : ℂ => gaussConv s a (boostCoord w) / w) z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_compl_cutSegment.mem_nhds hz,
      isOpen_ne.mem_nhds hz0] with w hw hw0
    have hb : AnalyticAt ℂ boostCoord w := analyticAt_boostCoord hw
    have hnum : DifferentiableAt ℂ (fun u : ℂ => gaussConv s a (boostCoord u)) w :=
      ((differentiable_gaussConv hs ha) (boostCoord w)).comp w hb.differentiableAt
    exact hnum.div differentiableAt_id hw0
  apply hquot.congr
  filter_upwards [isOpen_compl_cutSegment.mem_nhds hz] with w hw
  exact (stripApprox_of_notMem_cutSegment hw).symm

/-- The exponential identity used to turn the strip estimate into a natural power estimate. -/
theorem real_exp_neg_nat_mul (t : ℝ) (N : ℕ) :
    Real.exp (-(N : ℝ) * t) = (Real.exp (-t)) ^ N := by
  rw [show -(N : ℝ) * t = (N : ℝ) * (-t) by ring, Real.exp_nat_mul]

/-- The exponential identity used at the negative end of the boost strip. -/
theorem real_exp_nat_mul (t : ℝ) (N : ℕ) :
    Real.exp ((N : ℝ) * t) = (Real.exp t) ^ N := by
  exact Real.exp_nat_mul t N

/-- A lower norm bound near `1`. -/
private theorem norm_ge_half_of_norm_sub_one_le {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ ‖z‖ := by
  have htriangle : (1 : ℝ) ≤ ‖1 - z‖ + ‖z‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - z) + z‖ := by congr 1 <;> ring
      _ ≤ ‖1 - z‖ + ‖z‖ := norm_add_le _ _
  rw [norm_sub_rev] at htriangle
  linarith

/-- A lower norm bound near `-1`. -/
private theorem norm_ge_half_of_norm_add_one_le {z : ℂ} (h : ‖z + 1‖ ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ ‖z‖ := by
  have htriangle : (1 : ℝ) ≤ ‖1 + z‖ + ‖z‖ := by
    calc
      (1 : ℝ) = ‖(-1 : ℂ)‖ := by norm_num
      _ = ‖(-1 - z) + z‖ := by congr 1 <;> ring
      _ ≤ ‖-1 - z‖ + ‖z‖ := norm_add_le _ _
      _ = ‖1 + z‖ + ‖z‖ := by
        rw [show -1 - z = -(1 + z) by ring, norm_neg]
  rw [add_comm] at h
  linarith

/-- A lower norm bound for `1 + z` near the endpoint `1`. -/
private theorem norm_add_one_ge_three_halves_of_norm_sub_one_le {z : ℂ}
    (h : ‖z - 1‖ ≤ 1 / 2) :
    (3 : ℝ) / 2 ≤ ‖1 + z‖ := by
  have htriangle : (2 : ℝ) ≤ ‖1 + z‖ + ‖1 - z‖ := by
    calc
      (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
      _ = ‖(1 + z) + (1 - z)‖ := by congr 1 <;> ring
      _ ≤ ‖1 + z‖ + ‖1 - z‖ := norm_add_le _ _
  rw [norm_sub_rev] at htriangle
  linarith

/-- A lower norm bound for `1 - z` near the endpoint `-1`. -/
private theorem norm_sub_one_ge_three_halves_of_norm_add_one_le {z : ℂ}
    (h : ‖z + 1‖ ≤ 1 / 2) :
    (3 : ℝ) / 2 ≤ ‖1 - z‖ := by
  have htriangle : (2 : ℝ) ≤ ‖1 - z‖ + ‖1 + z‖ := by
    calc
      (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
      _ = ‖(1 - z) + (1 + z)‖ := by congr 1 <;> ring
      _ ≤ ‖1 - z‖ + ‖1 + z‖ := norm_add_le _ _
  rw [add_comm] at h
  linarith

/-- Gaussian decay at the `1` end gives arbitrary natural powers of `‖z - 1‖`. -/
theorem exists_norm_stripApprox_le_one {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ∉ cutSegment → ‖z - 1‖ ≤ 1 / 2 →
      ‖stripApprox s a z‖ ≤ C * ‖z - 1‖ ^ N := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    exists_norm_gaussConv_le hs ha N (3 * Real.pi / 2)
  refine ⟨2 * C₀ * (2 / 3 : ℝ) ^ N, by positivity, ?_⟩
  intro z hz hsmall
  have hz1 : z ≠ 1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzneg : z ≠ -1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzlower : (1 : ℝ) / 2 ≤ ‖z‖ := norm_ge_half_of_norm_sub_one_le hsmall
  have hplus : (3 : ℝ) / 2 ≤ ‖1 + z‖ :=
    norm_add_one_ge_three_halves_of_norm_sub_one_le hsmall
  have hminuspos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  have hpluspos : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hzneg
    apply Complex.ext
    · have := congrArg Complex.re h
      norm_num at this ⊢
      linarith
    · have := congrArg Complex.im h
      simpa using this
  have hre : 0 ≤ (boostCoord z).re := by
    rw [re_boostCoord hz]
    apply Real.log_nonneg
    rw [le_div_iff₀ hminuspos]
    have hminus : ‖1 - z‖ ≤ (1 : ℝ) / 2 := by
      simpa [norm_sub_rev] using hsmall
    nlinarith
  have hgauss := hC₀bound (boostCoord z)
    (by simpa using (abs_im_boostCoord_le z))
  rw [abs_of_nonneg hre] at hgauss
  have hexp : Real.exp (-(N : ℝ) * (boostCoord z).re) =
      (‖1 - z‖ / ‖1 + z‖) ^ N := by
    rw [real_exp_neg_nat_mul, exp_neg_re_boostCoord hz hzneg]
  have hfrac : ‖1 - z‖ / ‖1 + z‖ ≤ (2 / 3 : ℝ) * ‖z - 1‖ := by
    apply (div_le_iff₀ hpluspos).2
    rw [norm_sub_rev]
    have hmul := mul_le_mul_of_nonneg_left hplus
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) (norm_nonneg (z - 1)))
    nlinarith
  have hpow : (‖1 - z‖ / ‖1 + z‖) ^ N ≤
      ((2 / 3 : ℝ) * ‖z - 1‖) ^ N := by
    gcongr
  calc
    ‖stripApprox s a z‖ = ‖gaussConv s a (boostCoord z)‖ / ‖z‖ := by
      rw [stripApprox_of_notMem_cutSegment hz, norm_div]
    _ ≤ (C₀ * Real.exp (-(N : ℝ) * (boostCoord z).re)) / ‖z‖ :=
      div_le_div_of_nonneg_right hgauss (norm_nonneg _)
    _ = (C₀ * (‖1 - z‖ / ‖1 + z‖) ^ N) / ‖z‖ := by rw [hexp]
    _ ≤ (C₀ * (‖1 - z‖ / ‖1 + z‖) ^ N) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hzlower
    _ = 2 * C₀ * (‖1 - z‖ / ‖1 + z‖) ^ N := by ring
    _ ≤ 2 * C₀ * ((2 / 3 : ℝ) * ‖z - 1‖) ^ N := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * C₀ * (2 / 3 : ℝ) ^ N) * ‖z - 1‖ ^ N := by
      rw [mul_pow]
      ring

/-- Gaussian decay at the `-1` end gives arbitrary natural powers of `‖z + 1‖`. -/
theorem exists_norm_stripApprox_le_neg_one {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ∉ cutSegment → ‖z + 1‖ ≤ 1 / 2 →
      ‖stripApprox s a z‖ ≤ C * ‖z + 1‖ ^ N := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    exists_norm_gaussConv_le hs ha N (3 * Real.pi / 2)
  refine ⟨2 * C₀ * (2 / 3 : ℝ) ^ N, by positivity, ?_⟩
  intro z hz hsmall
  have hz1 : z ≠ 1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzneg : z ≠ -1 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hz0 : z ≠ 0 := by
    intro h
    apply hz
    rw [h]
    norm_num [cutSegment]
  have hzlower : (1 : ℝ) / 2 ≤ ‖z‖ := norm_ge_half_of_norm_add_one_le hsmall
  have hminus : (3 : ℝ) / 2 ≤ ‖1 - z‖ :=
    norm_sub_one_ge_three_halves_of_norm_add_one_le hsmall
  have hminuspos : 0 < ‖1 - z‖ := lt_of_lt_of_le (by norm_num) hminus
  have hpluspos : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hzneg
    apply Complex.ext
    · have h' := congrArg Complex.re h
      norm_num at h' ⊢
      linarith
    · have h' := congrArg Complex.im h
      simpa using h'
  have hre : (boostCoord z).re ≤ 0 := by
    rw [re_boostCoord hz]
    apply Real.log_nonpos
    · exact div_nonneg (norm_nonneg _) hminuspos.le
    · rw [div_le_iff₀ hminuspos]
      have hplus' : ‖1 + z‖ = ‖z + 1‖ := by rw [add_comm]
      rw [hplus']
      nlinarith [hsmall, hminus]
  have hgauss := hC₀bound (boostCoord z)
    (by simpa using (abs_im_boostCoord_le z))
  have hexp : Real.exp (-(N : ℝ) * |(boostCoord z).re|) =
      (‖1 + z‖ / ‖1 - z‖) ^ N := by
    rw [abs_of_nonpos hre]
    have hrewrite : -(N : ℝ) * -(boostCoord z).re =
        (N : ℝ) * (boostCoord z).re := by ring
    rw [hrewrite, real_exp_nat_mul, exp_re_boostCoord hz]
  have hfrac : ‖1 + z‖ / ‖1 - z‖ ≤ (2 / 3 : ℝ) * ‖z + 1‖ := by
    apply (div_le_iff₀ hminuspos).2
    have hplus' : ‖1 + z‖ = ‖z + 1‖ := by rw [add_comm]
    rw [hplus']
    have hmul := mul_le_mul_of_nonneg_left hminus
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) (norm_nonneg (z + 1)))
    nlinarith
  have hpow : (‖1 + z‖ / ‖1 - z‖) ^ N ≤
      ((2 / 3 : ℝ) * ‖z + 1‖) ^ N := by
    gcongr
  calc
    ‖stripApprox s a z‖ = ‖gaussConv s a (boostCoord z)‖ / ‖z‖ := by
      rw [stripApprox_of_notMem_cutSegment hz, norm_div]
    _ ≤ (C₀ * Real.exp (-(N : ℝ) * |(boostCoord z).re|)) / ‖z‖ :=
      div_le_div_of_nonneg_right hgauss (norm_nonneg _)
    _ = (C₀ * (‖1 + z‖ / ‖1 - z‖) ^ N) / ‖z‖ := by rw [hexp]
    _ ≤ (C₀ * (‖1 + z‖ / ‖1 - z‖) ^ N) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hzlower
    _ = 2 * C₀ * (‖1 + z‖ / ‖1 - z‖) ^ N := by ring
    _ ≤ 2 * C₀ * ((2 / 3 : ℝ) * ‖z + 1‖) ^ N := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * C₀ * (2 / 3 : ℝ) ^ N) * ‖z + 1‖ ^ N := by
      rw [mul_pow]
      ring

/-- The distance from an exterior point near `1` to the branch cut has the required lower bound. -/
theorem le_dist_cutSegment_one {z : ℂ} (hz : 1 ≤ ‖z‖) (hre : 0 ≤ z.re) {p : ℂ}
    (hp : p ∈ cutSegment) : ‖z - 1‖ / 2 ≤ ‖z - p‖ := by
  change p.im = 0 ∧ -1 ≤ p.re ∧ p.re ≤ 1 at hp
  have hzsq : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have hnorm : (1 : ℝ) ≤ ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - 1)]
    have hnorm' : (1 : ℝ) ≤ Complex.normSq z := by
      calc
        (1 : ℝ) ≤ ‖z‖ * ‖z‖ := by simpa [pow_two] using hnorm
        _ = Complex.normSq z := Complex.norm_mul_self_eq_normSq z
    simpa [Complex.normSq_apply, pow_two] using hnorm'
  have hcenter : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    calc
      ‖z - 1‖ ^ 2 = ‖z - 1‖ * ‖z - 1‖ := by rw [pow_two]
      _ = Complex.normSq (z - 1) := Complex.norm_mul_self_eq_normSq _
      _ = (z.re - 1) ^ 2 + z.im ^ 2 := by
        simp [Complex.normSq_apply, pow_two]
  have hdist : ‖z - p‖ ^ 2 = (z.re - p.re) ^ 2 + (z.im - p.im) ^ 2 := by
    calc
      ‖z - p‖ ^ 2 = ‖z - p‖ * ‖z - p‖ := by rw [pow_two]
      _ = Complex.normSq (z - p) := Complex.norm_mul_self_eq_normSq _
      _ = (z.re - p.re) ^ 2 + (z.im - p.im) ^ 2 := by
        simp [Complex.normSq_apply, pow_two]
  by_cases hright : 1 < z.re
  · have hcoord : z.re - 1 ≤ z.re - p.re := by linarith
    have hcoordnonneg : 0 ≤ z.re - 1 := by linarith
    have hcoord' : 0 ≤ z.re - p.re := by linarith
    have hsq : (z.re - 1) ^ 2 ≤ (z.re - p.re) ^ 2 := by
      exact (sq_le_sq₀ hcoordnonneg hcoord').2 hcoord
    have hsqdist : ‖z - 1‖ ^ 2 ≤ ‖z - p‖ ^ 2 := by
      rw [hcenter, hdist, hp.1]
      nlinarith
    have hnonneg : 0 ≤ ‖z - p‖ := norm_nonneg _
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [le_of_sq_le_sq hsqdist hnonneg]
  · have hleft : z.re ≤ 1 := le_of_not_gt hright
    have hleft_nonneg : 0 ≤ 1 - z.re := by linarith
    have hfactor : 1 - z.re ≤ 3 * (1 + z.re) := by linarith
    have hv : (1 - z.re) * (1 + z.re) ≤ z.im ^ 2 := by
      nlinarith [hzsq]
    have hthree : (z.re - 1) ^ 2 ≤ 3 * z.im ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hfactor hleft_nonneg
      nlinarith [hv, hmul]
    have hfour : (z.re - 1) ^ 2 + z.im ^ 2 ≤ 4 * z.im ^ 2 := by
      nlinarith [hthree]
    have hsqdist : ‖z - 1‖ ^ 2 ≤ 4 * ‖z - p‖ ^ 2 := by
      rw [hcenter, hdist, hp.1]
      nlinarith [sq_nonneg (z.re - p.re)]
    have hnonneg : 0 ≤ ‖z - p‖ := norm_nonneg _
    apply le_of_sq_le_sq (b := ‖z - p‖) ?_ hnonneg
    nlinarith [hsqdist]

/-- The distance from an exterior point near `-1` to the branch cut has the required lower bound. -/
theorem le_dist_cutSegment_neg_one {z : ℂ} (hz : 1 ≤ ‖z‖) (hre : z.re ≤ 0) {p : ℂ}
    (hp : p ∈ cutSegment) : ‖z + 1‖ / 2 ≤ ‖z - p‖ := by
  change p.im = 0 ∧ -1 ≤ p.re ∧ p.re ≤ 1 at hp
  have hzsq : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have hnorm : (1 : ℝ) ≤ ‖z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - 1)]
    have hnorm' : (1 : ℝ) ≤ Complex.normSq z := by
      calc
        (1 : ℝ) ≤ ‖z‖ * ‖z‖ := by simpa [pow_two] using hnorm
        _ = Complex.normSq z := Complex.norm_mul_self_eq_normSq z
    simpa [Complex.normSq_apply, pow_two] using hnorm'
  have hcenter : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
    calc
      ‖z + 1‖ ^ 2 = ‖z + 1‖ * ‖z + 1‖ := by rw [pow_two]
      _ = Complex.normSq (z + 1) := Complex.norm_mul_self_eq_normSq _
      _ = (z.re + 1) ^ 2 + z.im ^ 2 := by
        simp [Complex.normSq_apply, pow_two]
  have hdist : ‖z - p‖ ^ 2 = (z.re - p.re) ^ 2 + (z.im - p.im) ^ 2 := by
    calc
      ‖z - p‖ ^ 2 = ‖z - p‖ * ‖z - p‖ := by rw [pow_two]
      _ = Complex.normSq (z - p) := Complex.norm_mul_self_eq_normSq _
      _ = (z.re - p.re) ^ 2 + (z.im - p.im) ^ 2 := by
        simp [Complex.normSq_apply, pow_two]
  by_cases hleft : z.re < -1
  · have hcoord : z.re - p.re ≤ z.re + 1 := by linarith
    have hcoordnonpos : z.re + 1 ≤ 0 := by linarith
    have hcoord' : z.re - p.re ≤ 0 := by linarith
    have hsq : (z.re + 1) ^ 2 ≤ (z.re - p.re) ^ 2 := by
      have hsqneg : (-(z.re + 1)) ^ 2 ≤ (-(z.re - p.re)) ^ 2 := by
        apply (sq_le_sq₀ (by linarith) (by linarith)).2
        linarith
      nlinarith [hsqneg]
    have hsqdist : ‖z + 1‖ ^ 2 ≤ ‖z - p‖ ^ 2 := by
      rw [hcenter, hdist, hp.1]
      nlinarith
    have hnonneg : 0 ≤ ‖z - p‖ := norm_nonneg _
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [le_of_sq_le_sq hsqdist hnonneg]
  · have hright : -1 ≤ z.re := le_of_not_gt hleft
    have hleft_nonneg : 0 ≤ z.re + 1 := by linarith
    have hfactor : z.re + 1 ≤ 3 * (1 - z.re) := by linarith
    have hv : (1 - z.re) * (1 + z.re) ≤ z.im ^ 2 := by
      nlinarith [hzsq]
    have hthree : (z.re + 1) ^ 2 ≤ 3 * z.im ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hfactor hleft_nonneg
      nlinarith [hv, hmul]
    have hfour : (z.re + 1) ^ 2 + z.im ^ 2 ≤ 4 * z.im ^ 2 := by
      nlinarith [hthree]
    have hsqdist : ‖z + 1‖ ^ 2 ≤ 4 * ‖z - p‖ ^ 2 := by
      rw [hcenter, hdist, hp.1]
      nlinarith [sq_nonneg (z.re - p.re)]
    have hnonneg : 0 ≤ ‖z - p‖ := norm_nonneg _
    apply le_of_sq_le_sq (b := ‖z - p‖) ?_ hnonneg
    nlinarith [hsqdist]

/-- Complex derivatives of the approximant vanish to every prescribed power at `1`. -/
theorem exists_norm_iteratedDeriv_stripApprox_le_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z - 1‖ ≤ 1 / 4 → z ≠ 1 →
      ‖iteratedDeriv n (stripApprox s a) z‖ ≤ C * ‖z - 1‖ ^ N := by
  obtain ⟨C₁, hC₁, hC₁bound⟩ :=
    exists_norm_stripApprox_le_one hs ha (N + n)
  let C : ℝ := (n.factorial : ℝ) * C₁ * (5 / 4 : ℝ) ^ (N + n) * 4 ^ n
  refine ⟨C, by positivity, ?_⟩
  intro z hz hsmall hz1
  have hdpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hdnonneg : 0 ≤ ‖z - 1‖ := hdpos.le
  have hre : 0 ≤ z.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (z - 1))).1
    simp only [Complex.sub_re, Complex.one_re] at h
    linarith
  let R : ℝ := ‖z - 1‖ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall z R ⊆ cutSegmentᶜ := by
    intro w hw hwcut
    have hdistw : ‖z - w‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
    have hcutdist := le_dist_cutSegment_one hz hre hwcut
    dsimp [R] at hdistw hcutdist ⊢
    nlinarith
  have hdiffcut : DifferentiableOn ℂ (stripApprox s a) cutSegmentᶜ := by
    intro w hw
    exact (analyticAt_stripApprox hs ha hw).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (stripApprox s a) (Metric.ball z R) :=
    hdiffcut.diffContOnCl_ball hclosed
  have hsphere : ∀ w ∈ Metric.sphere z R,
      ‖stripApprox s a w‖ ≤ C₁ * ((5 / 4 : ℝ) * ‖z - 1‖) ^ (N + n) := by
    intro w hw
    have hdistw : ‖w - z‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hwone : ‖w - 1‖ ≤ (5 / 4 : ℝ) * ‖z - 1‖ := by
      have htriangle : ‖w - 1‖ ≤ ‖w - z‖ + ‖z - 1‖ := by
        calc
          ‖w - 1‖ = ‖(w - z) + (z - 1)‖ := by congr 1 <;> ring
          _ ≤ ‖w - z‖ + ‖z - 1‖ := norm_add_le _ _
      rw [hdistw] at htriangle
      dsimp [R] at htriangle
      ring_nf at htriangle ⊢
      linarith
    have hwsmall : ‖w - 1‖ ≤ 1 / 2 := by
      have : ‖z - 1‖ ≤ (1 : ℝ) / 4 := hsmall
      nlinarith
    have hwcut : w ∉ cutSegment := hclosed (Metric.sphere_subset_closedBall hw)
    have hb := hC₁bound w hwcut hwsmall
    exact hb.trans (mul_le_mul_of_nonneg_left (by gcongr) hC₁)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdc hsphere
  have hcancel :
      (n.factorial : ℝ) * (C₁ * ((5 / 4 : ℝ) * ‖z - 1‖) ^ (N + n)) /
          R ^ n = C * ‖z - 1‖ ^ N := by
    dsimp [C, R]
    rw [mul_pow, pow_add, div_pow]
    field_simp [ne_of_gt hdpos]
    ring_nf
    have h4 : ∀ x : ℝ, x * ((1 : ℝ) / 4) ^ n * 4 ^ n = x := by
      intro x
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [h4]
  exact hcauchy.trans_eq hcancel

/-- Complex derivatives of the approximant vanish to every prescribed power at `-1`. -/
theorem exists_norm_iteratedDeriv_stripApprox_le_neg_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z + 1‖ ≤ 1 / 4 → z ≠ -1 →
      ‖iteratedDeriv n (stripApprox s a) z‖ ≤ C * ‖z + 1‖ ^ N := by
  obtain ⟨C₁, hC₁, hC₁bound⟩ :=
    exists_norm_stripApprox_le_neg_one hs ha (N + n)
  let C : ℝ := (n.factorial : ℝ) * C₁ * (5 / 4 : ℝ) ^ (N + n) * 4 ^ n
  refine ⟨C, by positivity, ?_⟩
  intro z hz hsmall hzneg
  have hdpos : 0 < ‖z + 1‖ := norm_pos_iff.mpr (by
    intro h
    apply hzneg
    apply Complex.ext
    · have h' := congrArg Complex.re h
      norm_num at h' ⊢
      linarith
    · have h' := congrArg Complex.im h
      simpa using h')
  have hdnonneg : 0 ≤ ‖z + 1‖ := hdpos.le
  have hre : z.re ≤ 0 := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (z + 1))).2
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  let R : ℝ := ‖z + 1‖ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall z R ⊆ cutSegmentᶜ := by
    intro w hw hwcut
    have hdistw : ‖z - w‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
    have hcutdist := le_dist_cutSegment_neg_one hz hre hwcut
    dsimp [R] at hdistw hcutdist ⊢
    nlinarith
  have hdiffcut : DifferentiableOn ℂ (stripApprox s a) cutSegmentᶜ := by
    intro w hw
    exact (analyticAt_stripApprox hs ha hw).differentiableAt.differentiableWithinAt
  have hdc : DiffContOnCl ℂ (stripApprox s a) (Metric.ball z R) :=
    hdiffcut.diffContOnCl_ball hclosed
  have hsphere : ∀ w ∈ Metric.sphere z R,
      ‖stripApprox s a w‖ ≤ C₁ * ((5 / 4 : ℝ) * ‖z + 1‖) ^ (N + n) := by
    intro w hw
    have hdistw : ‖w - z‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hwone : ‖w + 1‖ ≤ (5 / 4 : ℝ) * ‖z + 1‖ := by
      have htriangle : ‖w + 1‖ ≤ ‖w - z‖ + ‖z + 1‖ := by
        calc
          ‖w + 1‖ = ‖(w - z) + (z + 1)‖ := by congr 1 <;> ring
          _ ≤ ‖w - z‖ + ‖z + 1‖ := norm_add_le _ _
      rw [hdistw] at htriangle
      dsimp [R] at htriangle
      ring_nf at htriangle ⊢
      linarith
    have hwsmall : ‖w + 1‖ ≤ 1 / 2 := by
      have : ‖z + 1‖ ≤ (1 : ℝ) / 4 := hsmall
      nlinarith
    have hwcut : w ∉ cutSegment := hclosed (Metric.sphere_subset_closedBall hw)
    have hb := hC₁bound w hwcut hwsmall
    exact hb.trans (mul_le_mul_of_nonneg_left (by gcongr) hC₁)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hdc hsphere
  have hcancel :
      (n.factorial : ℝ) * (C₁ * ((5 / 4 : ℝ) * ‖z + 1‖) ^ (N + n)) /
          R ^ n = C * ‖z + 1‖ ^ N := by
    dsimp [C, R]
    rw [mul_pow, pow_add, div_pow]
    field_simp [ne_of_gt hdpos]
    ring_nf
    have h4 : ∀ x : ℝ, x * ((1 : ℝ) / 4) ^ n * 4 ^ n = x := by
      intro x
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [h4]
  exact hcauchy.trans_eq hcancel

/-- The approximant tends to zero at the point at infinity. -/
theorem tendsto_stripApprox {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) :
    Filter.Tendsto (stripApprox s a) (Filter.cocompact ℂ) (nhds 0) := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_norm_gaussConv_le hs ha 0 (3 * Real.pi / 2)
  have hupper : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖stripApprox s a z‖ ≤ C₀ * (‖z‖)⁻¹ := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop 2] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hzneg : z ≠ -1 := by
      intro h
      rw [h] at hz
      norm_num at hz
    have hzcut := notMem_cutSegment_of_one_le_norm (by linarith) hz1 hzneg
    have hb := hC₀bound (boostCoord z)
      (by simpa using (abs_im_boostCoord_le z))
    have hb' : ‖gaussConv s a (boostCoord z)‖ ≤ C₀ := by
      simpa using hb
    rw [stripApprox_of_notMem_cutSegment hzcut, norm_div]
    simpa [div_eq_mul_inv] using
      (div_le_div_of_nonneg_right hb' (norm_nonneg z))
  have hlim : Tendsto (fun z : ℂ => C₀ * (‖z‖)⁻¹)
      (Filter.cocompact ℂ) (nhds 0) := by
    simpa using
      ((tendsto_norm_cocompact_atTop (E := ℂ)).inv_tendsto_atTop.const_mul C₀)
  exact squeeze_zero_norm' hupper hlim

/-- The approximant is holomorphic on the open exterior. -/
theorem differentiableOn_stripApprox {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) :
    DifferentiableOn ℂ (stripApprox s a) OexteriorInterior := by
  intro z hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    change (1 : ℝ) < ‖(1 : ℂ)‖ at hz
    norm_num at hz
  have hzneg : z ≠ -1 := by
    intro h
    rw [h] at hz
    change (1 : ℝ) < ‖(-1 : ℂ)‖ at hz
    norm_num at hz
  exact (analyticAt_stripApprox hs ha
    (notMem_cutSegment_of_one_le_norm hz.le hz1 hzneg)).differentiableAt.differentiableWithinAt

/-- The hypotheses needed to apply flat extension at the endpoint `1`. -/
private theorem contDiffWithinAt_stripApprox_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) :
    ContDiffWithinAt ℝ ∞ (stripApprox s a) Oexterior 1 := by
  have hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ w ∈ Oexterior ∩ Metric.ball (1 : ℂ) (1 / 4),
      w ≠ 1 → ‖iteratedDeriv n (stripApprox s a) w‖ ≤ C * ‖w - 1‖ ^ 2 := by
    intro n
    obtain ⟨C, hC, hCbound⟩ := exists_norm_iteratedDeriv_stripApprox_le_one hs ha n 2
    refine ⟨C, ?_⟩
    intro w hw hwne
    exact hCbound w hw.1 (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw.2)) hwne
  apply contDiffWithinAt_of_flat_holomorphic (r := (1 : ℝ) / 4) (by norm_num)
    (by change (1 : ℝ) ≤ ‖(1 : ℂ)‖; norm_num)
    (by simp [stripApprox])
  · intro w hw hwne
    have hwneg : w ≠ -1 := by
      intro h
      have hwball := hw.2
      rw [h, Metric.mem_ball, dist_eq_norm] at hwball
      norm_num at hwball
    exact analyticAt_stripApprox hs ha
      (notMem_cutSegment_of_one_le_norm hw.1 hwne hwneg)
  · exact hbound

/-- The hypotheses needed to apply flat extension at the endpoint `-1`. -/
private theorem contDiffWithinAt_stripApprox_neg_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) :
    ContDiffWithinAt ℝ ∞ (stripApprox s a) Oexterior (-1) := by
  have hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ w ∈ Oexterior ∩ Metric.ball (-1 : ℂ) (1 / 4),
      w ≠ -1 → ‖iteratedDeriv n (stripApprox s a) w‖ ≤ C * ‖w + 1‖ ^ 2 := by
    intro n
    obtain ⟨C, hC, hCbound⟩ := exists_norm_iteratedDeriv_stripApprox_le_neg_one hs ha n 2
    refine ⟨C, ?_⟩
    intro w hw hwne
    exact hCbound w hw.1 (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw.2)) hwne
  apply contDiffWithinAt_of_flat_holomorphic (r := (1 : ℝ) / 4) (by norm_num)
    (by change (1 : ℝ) ≤ ‖(-1 : ℂ)‖; norm_num)
    (by simp [stripApprox])
  · intro w hw hwne
    have hwone : w ≠ 1 := by
      intro h
      have hwball := hw.2
      rw [h, Metric.mem_ball, dist_eq_norm] at hwball
      norm_num at hwball
    exact analyticAt_stripApprox hs ha
      (notMem_cutSegment_of_one_le_norm hw.1 hwone hwne)
  · simpa [sub_neg_eq_add] using hbound

/-- The approximant is smooth on the closed exterior, including its two flat endpoints. -/
theorem contDiffOn_stripApprox {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) :
    ContDiffOn ℝ ∞ (stripApprox s a) Oexterior := by
  intro z hz
  by_cases hz1 : z = 1
  · simpa [hz1] using contDiffWithinAt_stripApprox_one hs ha
  by_cases hzneg : z = -1
  · simpa [hzneg] using contDiffWithinAt_stripApprox_neg_one hs ha
  exact (analyticAt_stripApprox hs ha
    (notMem_cutSegment_of_one_le_norm hz hz1 hzneg)).restrictScalars.contDiffAt.contDiffWithinAt

/-- Every real jet of the approximant vanishes at `1`. -/
theorem iteratedFDerivWithin_stripApprox_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (n : ℕ) :
    iteratedFDerivWithin ℝ n (stripApprox s a) Oexterior 1 = 0 := by
  have hbound : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ Oexterior ∩ Metric.ball (1 : ℂ) (1 / 4),
      w ≠ 1 → ‖iteratedDeriv m (stripApprox s a) w‖ ≤ C * ‖w - 1‖ ^ 2 := by
    intro m
    obtain ⟨C, hC, hCbound⟩ := exists_norm_iteratedDeriv_stripApprox_le_one hs ha m 2
    refine ⟨C, ?_⟩
    intro w hw hwne
    exact hCbound w hw.1 (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw.2)) hwne
  apply iteratedFDerivWithin_eq_zero_of_flat_holomorphic (r := (1 : ℝ) / 4) (by norm_num)
    uniqueDiffOn_Oexterior (by change (1 : ℝ) ≤ ‖(1 : ℂ)‖; norm_num)
    (by simp [stripApprox])
  · intro w hw hwne
    have hwneg : w ≠ -1 := by
      intro h
      have hwball := hw.2
      rw [h, Metric.mem_ball, dist_eq_norm] at hwball
      norm_num at hwball
    exact analyticAt_stripApprox hs ha
      (notMem_cutSegment_of_one_le_norm hw.1 hwne hwneg)
  · exact hbound

/-- Every real jet of the approximant vanishes at `-1`. -/
theorem iteratedFDerivWithin_stripApprox_neg_one {s : ℝ} (hs : 0 < s)
    {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) (n : ℕ) :
    iteratedFDerivWithin ℝ n (stripApprox s a) Oexterior (-1) = 0 := by
  have hbound : ∀ m : ℕ, ∃ C : ℝ, ∀ w ∈ Oexterior ∩ Metric.ball (-1 : ℂ) (1 / 4),
      w ≠ -1 → ‖iteratedDeriv m (stripApprox s a) w‖ ≤ C * ‖w + 1‖ ^ 2 := by
    intro m
    obtain ⟨C, hC, hCbound⟩ := exists_norm_iteratedDeriv_stripApprox_le_neg_one hs ha m 2
    refine ⟨C, ?_⟩
    intro w hw hwne
    exact hCbound w hw.1 (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw.2)) hwne
  apply iteratedFDerivWithin_eq_zero_of_flat_holomorphic (r := (1 : ℝ) / 4) (by norm_num)
    uniqueDiffOn_Oexterior (by change (1 : ℝ) ≤ ‖(-1 : ℂ)‖; norm_num)
    (by simp [stripApprox])
  · intro w hw hwne
    have hwone : w ≠ 1 := by
      intro h
      have hwball := hw.2
      rw [h, Metric.mem_ball, dist_eq_norm] at hwball
      norm_num at hwball
    exact analyticAt_stripApprox hs ha
      (notMem_cutSegment_of_one_le_norm hw.1 hwone hwne)
  · simpa [sub_neg_eq_add] using hbound

/-- [T26], Lemma 3.4; the Gaussian approximant packaged as an element of `𝓧`. -/
noncomputable def stripApproxX {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ}
    (ha : IsRapidlyDecaying a) : AnalyticTestFn :=
  ⟨stripApprox s a, contDiffOn_stripApprox hs ha, differentiableOn_stripApprox hs ha,
    tendsto_stripApprox hs ha, iteratedFDerivWithin_stripApprox_one hs ha,
    iteratedFDerivWithin_stripApprox_neg_one hs ha⟩

/-- [T26], Lemma 3.4; on the open upper semicircle the approximant is read in boost coordinates. -/
theorem stripApprox_circleExp {s : ℝ} {a : ℝ → ℂ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    stripApprox s a (Complex.exp (θ * Complex.I)) =
      gaussConv s a ((angleToBoost θ : ℝ) : ℂ) / Complex.exp (θ * Complex.I) := by
  have him : (Complex.exp (θ * Complex.I)).im = Real.sin θ := by
    exact Complex.exp_ofReal_mul_I_im θ
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hzcut : Complex.exp (θ * Complex.I) ∉ cutSegment := by
    intro hz
    have hzsin : Real.sin θ = 0 := by simpa [him] using hz.1
    exact (ne_of_gt hsin) hzsin
  rw [stripApprox_of_notMem_cutSegment hzcut, boostCoord_circleExp hθ]

end
end MobiusCPT
