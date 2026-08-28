import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Compactification.OnePoint.Basic
import MobiusCPT.TestFunctions.Support

/-!
# The complex-parameter Möbius boost

This file records the closed form of the complexified boost used in [T26], together with its
geometry on the closed strip between imaginary parts `0` and `π`.
-/

namespace MobiusCPT

open Set
open scoped OnePoint

noncomputable section

/-- [T26], §3, eq. (3.4): the numerator of `v_τ · z`. -/
def cnum (τ z : ℂ) : ℂ :=
  Complex.cosh (τ / 2) * z - Complex.sinh (τ / 2)

/-- [T26], §3, eq. (3.4): the denominator of `v_τ · z`. -/
def cden (τ z : ℂ) : ℂ :=
  -Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2)

/-- [T26], §3: the complex boost `v_τ` as a fractional-linear map, `v_τ · z`. -/
def vApply (τ z : ℂ) : ℂ :=
  cnum τ z / cden τ z

/-- [T26], §3, eq. (3.4): the numerator of `v_{-τ} · z`. -/
@[simp]
theorem cnum_neg (τ z : ℂ) :
    cnum (-τ) z = Complex.cosh (τ / 2) * z + Complex.sinh (τ / 2) := by
  rw [cnum, show -τ / 2 = -(τ / 2) by ring, Complex.cosh_neg, Complex.sinh_neg]
  ring

/-- [T26], §3, eq. (3.4): the denominator of `v_{-τ} · z`. -/
@[simp]
theorem cden_neg (τ z : ℂ) :
    cden (-τ) z = Complex.sinh (τ / 2) * z + Complex.cosh (τ / 2) := by
  rw [cden, show -τ / 2 = -(τ / 2) by ring, Complex.cosh_neg, Complex.sinh_neg]
  ring

/-- [T26], §3, eq. (3.4): the numerator and denominator of the complex boost cannot
simultaneously degenerate. -/
theorem cosh_mul_cden_add_sinh_mul_cnum (τ z : ℂ) :
    Complex.cosh (τ / 2) * cden τ z + Complex.sinh (τ / 2) * cnum τ z = 1 := by
  calc
    Complex.cosh (τ / 2) * cden τ z + Complex.sinh (τ / 2) * cnum τ z =
        Complex.cosh (τ / 2) ^ 2 - Complex.sinh (τ / 2) ^ 2 := by
          simp only [cnum, cden]
          ring
    _ = 1 := Complex.cosh_sq_sub_sinh_sq (τ / 2)

/-- [T26], §3, eq. (3.4): the numerator and denominator of the complex boost are not
simultaneously zero. -/
theorem not_and_cnum_cden_eq_zero (τ z : ℂ) :
    ¬(cnum τ z = 0 ∧ cden τ z = 0) := by
  rintro ⟨hnum, hden⟩
  have h := cosh_mul_cden_add_sinh_mul_cnum τ z
  rw [hnum, hden] at h
  simp at h

/-- [T26], Definition 3.5: the algebraic norm-square identity underlying the strip geometry. -/
theorem normSq_sub_normSq_general (c s w : ℂ) :
    Complex.normSq (c * w + s) - Complex.normSq (s * w + c) =
      (Complex.normSq c - Complex.normSq s) * (Complex.normSq w - 1) -
        4 * (c * (starRingEnd ℂ) s).im * w.im := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- [T26], Definition 3.5: the imaginary part of the product of a complex hyperbolic
half-angle and the conjugate of its hyperbolic sine. -/
theorem im_cosh_mul_conj_sinh (w : ℂ) :
    (Complex.cosh w * (starRingEnd ℂ) (Complex.sinh w)).im =
      -(Real.sin (2 * w.im)) / 2 := by
  have hadd : (starRingEnd ℂ) w + w = ((2 * w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hsub : (starRingEnd ℂ) w - w = ((-2 * w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  have hsinh :
      Complex.sinh ((starRingEnd ℂ) w) * Complex.cosh w =
        (Complex.sinh ((starRingEnd ℂ) w + w) +
          Complex.sinh ((starRingEnd ℂ) w - w)) / 2 := by
    rw [Complex.sinh_add, Complex.sinh_sub]
    ring
  calc
    (Complex.cosh w * (starRingEnd ℂ) (Complex.sinh w)).im =
        (Complex.sinh ((starRingEnd ℂ) w) * Complex.cosh w).im := by
          rw [Complex.sinh_conj]
          ring
    _ = ((Complex.sinh ((starRingEnd ℂ) w + w) +
          Complex.sinh ((starRingEnd ℂ) w - w)) / 2).im := by rw [hsinh]
    _ = -(Real.sin (2 * w.im)) / 2 := by
      rw [hadd, hsub, Complex.sinh_mul_I]
      simp [Real.sin_neg]
      have hre : (2 : ℂ) * (w.re : ℂ) = ((2 * w.re : ℝ) : ℂ) := by
        push_cast
        ring
      have him : (2 : ℂ) * (w.im : ℂ) = ((2 * w.im : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hre, him, Complex.sinh_ofReal_im, Complex.sin_ofReal_re]
      ring

/-- [T26], Definition 3.5: on the unit circle the numerator-minus-denominator norm square
of `v_{-τ}` is controlled by the imaginary parts of `τ` and `z`. -/
theorem normSq_cnum_neg_sub_normSq_cden_neg (τ : ℂ) (z : Circle) :
    Complex.normSq (cnum (-τ) z) - Complex.normSq (cden (-τ) z) =
      2 * Real.sin τ.im * (z : ℂ).im := by
  have him : 2 * (τ / 2).im = τ.im := by
    rw [Complex.div_ofNat_im]
    ring
  calc
    Complex.normSq (cnum (-τ) z) - Complex.normSq (cden (-τ) z) =
        Complex.normSq (Complex.cosh (τ / 2) * (z : ℂ) + Complex.sinh (τ / 2)) -
          Complex.normSq (Complex.sinh (τ / 2) * (z : ℂ) +
            Complex.cosh (τ / 2)) := by rw [cnum_neg, cden_neg]
    _ = (Complex.normSq (Complex.cosh (τ / 2)) -
          Complex.normSq (Complex.sinh (τ / 2))) * (Complex.normSq (z : ℂ) - 1) -
        4 * (Complex.cosh (τ / 2) *
          (starRingEnd ℂ) (Complex.sinh (τ / 2))).im * (z : ℂ).im :=
      normSq_sub_normSq_general (Complex.cosh (τ / 2))
        (Complex.sinh (τ / 2)) (z : ℂ)
    _ = 2 * Real.sin τ.im * (z : ℂ).im := by
      rw [Circle.normSq_coe, sub_self, mul_zero, zero_sub,
        im_cosh_mul_conj_sinh, him]
      ring

/-- [T26], Definition 3.5: for `0 ≤ Im τ ≤ π` and `z` in the closed upper semicircle,
`|v_{-τ} · z| ≥ 1`, expressed before division so that the pole is included. -/
theorem norm_cden_neg_le_norm_cnum_neg {τ : ℂ} (h₀ : 0 ≤ τ.im)
    (h₁ : τ.im ≤ Real.pi) {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    ‖cden (-τ) z‖ ≤ ‖cnum (-τ) z‖ := by
  -- `hsin` is where the closed-strip hypotheses `h₀`, `h₁` do their work, and `hz` is where the
  -- closed-semicircle hypothesis does: the difference of norm squares is `2 sin(Im τ) · Im z`.
  have hsin : 0 ≤ Real.sin τ.im := Real.sin_nonneg_of_nonneg_of_le_pi h₀ h₁
  have hdiff : 0 ≤ Complex.normSq (cnum (-τ) z) - Complex.normSq (cden (-τ) z) := by
    rw [normSq_cnum_neg_sub_normSq_cden_neg]
    exact mul_nonneg (mul_nonneg (by norm_num) hsin) hz
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  linarith

/-- [T26], Definition 3.5: away from its pole, `v_{-τ}` has norm at least one on the closed
upper semicircle throughout the closed strip. -/
theorem one_le_norm_vApply_neg {τ : ℂ} (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) (hden : cden (-τ) z ≠ 0) :
    1 ≤ ‖vApply (-τ) (z : ℂ)‖ := by
  rw [vApply, Complex.norm_div]
  exact (le_div_iff₀ (norm_pos_iff.mpr hden)).2
    (by simpa using norm_cden_neg_le_norm_cnum_neg h₀ h₁ hz)

/-- [T26], Definition 3.5: away from its pole, `v_{-τ}` maps the open upper semicircle into
the finite part of `𝕆`. -/
theorem one_le_norm_vApply_neg_of_mem_upperArc {τ : ℂ} (h₀ : 0 ≤ τ.im)
    (h₁ : τ.im ≤ Real.pi) {z : Circle} (hz : z ∈ upperArc)
    (hden : cden (-τ) z ≠ 0) :
    1 ≤ ‖vApply (-τ) (z : ℂ)‖ :=
  one_le_norm_vApply_neg h₀ h₁ hz.le hden

/-- [T26], Definition 3.2: `𝕆 = { z : |z| ≥ 1 } ∪ {∞}`. -/
def Oset : Set (OnePoint ℂ) :=
  insert ∞ (((↑) : ℂ → OnePoint ℂ) '' {w : ℂ | 1 ≤ ‖w‖})

/-- [T26], §3: `v_{-τ} · z` as a point of the Riemann sphere, `∞` at the pole. -/
def vApplyNegSphere (τ : ℂ) (z : Circle) : OnePoint ℂ :=
  if cden (-τ) z = 0 then ∞
  else ((cnum (-τ) z / cden (-τ) z : ℂ) : OnePoint ℂ)

/-- [T26], Definition 3.5: `v_{-τ}(I_+) ⊆ 𝕆` for `τ` in the closed strip
`0 ≤ Im τ ≤ π`, including the boundary of the strip and the endpoints of the semicircle. -/
theorem vApplyNegSphere_mem_Oset {τ : ℂ} (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    vApplyNegSphere τ z ∈ Oset := by
  by_cases hden : cden (-τ) z = 0
  · simp [vApplyNegSphere, hden, Oset]
  · have hv : 1 ≤ ‖cnum (-τ) z / cden (-τ) z‖ := by
      simpa [vApply] using one_le_norm_vApply_neg h₀ h₁ hz hden
    rw [vApplyNegSphere, if_neg hden]
    exact Or.inr ⟨_, hv, rfl⟩

/-- [T26], Definition 3.5: the difference of the hyperbolic norm squares depends only on
the imaginary part of the complex parameter. -/
theorem normSq_cosh_sub_normSq_sinh (w : ℂ) :
    Complex.normSq (Complex.cosh w) - Complex.normSq (Complex.sinh w) =
      Real.cos (2 * w.im) := by
  apply Complex.ofReal_injective
  calc
    ((Complex.normSq (Complex.cosh w) - Complex.normSq (Complex.sinh w) : ℝ) : ℂ) =
        Complex.cosh w * (starRingEnd ℂ) (Complex.cosh w) -
          Complex.sinh w * (starRingEnd ℂ) (Complex.sinh w) := by
            rw [Complex.ofReal_sub, Complex.mul_conj, Complex.mul_conj]
    _ = Complex.cosh w * Complex.cosh ((starRingEnd ℂ) w) -
          Complex.sinh w * Complex.sinh ((starRingEnd ℂ) w) := by
            rw [Complex.cosh_conj, Complex.sinh_conj]
    _ = Complex.cosh (w - (starRingEnd ℂ) w) :=
      (Complex.cosh_sub w ((starRingEnd ℂ) w)).symm
    _ = ((Real.cos (2 * w.im) : ℝ) : ℂ) := by
      rw [Complex.sub_conj, Complex.cosh_mul_I]
      simp

/-- [T26], Definition 3.5: if `cos (Im τ) ≠ 0`, the denominator of `v_{-τ}` has no pole
on the unit circle. -/
theorem cden_neg_ne_zero_of_im_ne {τ : ℂ} (h : Real.cos τ.im ≠ 0) (z : Circle) :
    cden (-τ) z ≠ 0 := by
  intro hden
  have hc : Complex.cosh (τ / 2) = -(Complex.sinh (τ / 2) * (z : ℂ)) := by
    rw [cden_neg] at hden
    linear_combination hden
  have hnorm : Complex.normSq (Complex.cosh (τ / 2)) =
      Complex.normSq (Complex.sinh (τ / 2)) := by
    rw [hc, Complex.normSq_neg, Complex.normSq_mul, Circle.normSq_coe, mul_one]
  have hcos := normSq_cosh_sub_normSq_sinh (τ / 2)
  rw [hnorm, sub_self] at hcos
  have him : 2 * (τ / 2).im = τ.im := by
    rw [Complex.div_ofNat_im]
    ring
  rw [him] at hcos
  exact h hcos.symm

/-- [T26], Lemma 3.7: `cosh (iπ/2) = 0`. -/
theorem cosh_I_mul_pi_div_two :
    Complex.cosh (Complex.I * Real.pi / 2) = 0 := by
  rw [show Complex.I * Real.pi / 2 = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  simp [Complex.cosh_mul_I, Real.cos_pi_div_two]

/-- [T26], Lemma 3.7: `sinh (iπ/2) = i`. -/
theorem sinh_I_mul_pi_div_two :
    Complex.sinh (Complex.I * Real.pi / 2) = Complex.I := by
  rw [show Complex.I * Real.pi / 2 = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  simp [Complex.sinh_mul_I, Real.sin_pi_div_two]

/-- [T26], Lemma 3.7: the denominator of `v_{iπ}` is nonzero on the unit circle. -/
theorem cden_I_mul_pi_ne_zero (z : Circle) :
    cden (Complex.I * Real.pi) (z : ℂ) ≠ 0 := by
  rw [cden, cosh_I_mul_pi_div_two, sinh_I_mul_pi_div_two, add_zero]
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Circle.coe_ne_zero z)

/-- [T26], Lemma 3.7: `v_{iπ} · z = z⁻¹`. -/
theorem vApply_I_mul_pi (z : Circle) :
    vApply (Complex.I * Real.pi) (z : ℂ) = ((z : ℂ))⁻¹ := by
  rw [vApply, cnum, cden, cosh_I_mul_pi_div_two, sinh_I_mul_pi_div_two]
  field_simp [Complex.I_ne_zero, Circle.coe_ne_zero z]
  ring

/-- [T26], Lemma 3.7: the endpoint boost is inversion as a circle-valued operation. -/
theorem vApply_I_mul_pi_circle (z : Circle) :
    vApply (Complex.I * Real.pi) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
  simpa using vApply_I_mul_pi z

/-- [T26], eq. (3.5): `cosh τ + Re(z) sinh τ` factors through the denominator of
`v_{-τ}` and its reflected factor. -/
theorem cosh_add_re_mul_sinh (τ : ℂ) (z : Circle) :
    Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ =
      cden (-τ) z *
        (Complex.sinh (τ / 2) * (starRingEnd ℂ) (z : ℂ) + Complex.cosh (τ / 2)) := by
  have hcosh : Complex.cosh τ =
      Complex.cosh (τ / 2) ^ 2 + Complex.sinh (τ / 2) ^ 2 := by
    calc
      Complex.cosh τ = Complex.cosh (2 * (τ / 2)) := by congr 1 <;> ring
      _ = Complex.cosh (τ / 2) ^ 2 + Complex.sinh (τ / 2) ^ 2 :=
        Complex.cosh_two_mul (τ / 2)
  have hsinh : Complex.sinh τ =
      2 * Complex.sinh (τ / 2) * Complex.cosh (τ / 2) := by
    calc
      Complex.sinh τ = Complex.sinh (2 * (τ / 2)) := by congr 1 <;> ring
      _ = 2 * Complex.sinh (τ / 2) * Complex.cosh (τ / 2) :=
        Complex.sinh_two_mul (τ / 2)
  have hnorm : (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = 1 := by
    simpa using Complex.mul_conj (z : ℂ)
  have hadd : (z : ℂ) + (starRingEnd ℂ) (z : ℂ) = ((2 * (z : ℂ).re : ℝ) : ℂ) :=
    Complex.add_conj (z : ℂ)
  calc
    Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ =
        (Complex.cosh (τ / 2) ^ 2 + Complex.sinh (τ / 2) ^ 2) +
          ((z : ℂ).re : ℂ) *
            (2 * Complex.sinh (τ / 2) * Complex.cosh (τ / 2)) := by
              rw [hcosh, hsinh]
    _ = Complex.sinh (τ / 2) ^ 2 *
          ((z : ℂ) * (starRingEnd ℂ) (z : ℂ)) +
        (Complex.sinh (τ / 2) * Complex.cosh (τ / 2)) *
          ((z : ℂ) + (starRingEnd ℂ) (z : ℂ)) +
        Complex.cosh (τ / 2) ^ 2 := by
          rw [hnorm, hadd]
          push_cast
          ring
    _ = (Complex.sinh (τ / 2) * (z : ℂ) + Complex.cosh (τ / 2)) *
          (Complex.sinh (τ / 2) * (starRingEnd ℂ) (z : ℂ) +
            Complex.cosh (τ / 2)) := by ring
    _ = cden (-τ) z *
          (Complex.sinh (τ / 2) * (starRingEnd ℂ) (z : ℂ) +
            Complex.cosh (τ / 2)) := by rw [cden_neg]

/-- [T26], eq. (3.5): `|sinh(t/2) z + cosh(t/2)|² = cosh t + Re(z) sinh t`
for a real boost parameter. -/
theorem normSq_cden_neg_ofReal (t : ℝ) (z : Circle) :
    Complex.normSq (cden (-(t : ℂ)) z) =
      Real.cosh t + (z : ℂ).re * Real.sinh t := by
  apply Complex.ofReal_injective
  rw [← Complex.mul_conj]
  have h := (cosh_add_re_mul_sinh (t : ℂ) z).symm
  have hhalf : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) := by
    exact (Complex.ofReal_div t 2).symm
  have hconj :
      (starRingEnd ℂ)
          (Complex.sinh ((t : ℂ) / 2) * (z : ℂ) + Complex.cosh ((t : ℂ) / 2)) =
        Complex.sinh ((t : ℂ) / 2) * (starRingEnd ℂ) (z : ℂ) +
          Complex.cosh ((t : ℂ) / 2) := by
    rw [map_add, map_mul, hhalf, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
    simp only [Complex.conj_ofReal]
  calc
    cden (-(t : ℂ)) z * (starRingEnd ℂ) (cden (-(t : ℂ)) z) =
        cden (-(t : ℂ)) z *
          (Complex.sinh ((t : ℂ) / 2) * (starRingEnd ℂ) (z : ℂ) +
            Complex.cosh ((t : ℂ) / 2)) := by
      rw [cden_neg (t : ℂ) z, hconj]
    _ = ((Real.cosh t + (z : ℂ).re * Real.sinh t : ℝ) : ℂ) := by
      rw [h, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
        Complex.ofReal_add, Complex.ofReal_mul]

end

end MobiusCPT
