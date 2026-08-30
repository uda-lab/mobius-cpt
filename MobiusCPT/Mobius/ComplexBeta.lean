import MobiusCPT.Mobius.ComplexBetaCore

/-!
# The complex boost on analytic test functions, pointwise

[T26], Definition 3.5, equations (3.4)-(3.5).  This file gives the pointwise value of
`β_d(v_τ)F|_{I_+}` on the closed upper semicircle for `τ` in the closed strip `0 ≤ Im τ ≤ π`, in
the pole-free form that builds in the removable singularity of the `d = 0` case, and proves that
it agrees with the literal source expression wherever the latter is defined.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Definition 3.5, equations (3.4)-(3.5); the pointwise value of `β_d(v_τ)F|_{I_+}`.

Write `P = cnum (-τ) z` and `Q = cden (-τ) z`.  On the unit circle the source scalar factorises
without a pole as `cosh τ + Re(z) sinh τ = P * Q / z` (`cosh_add_re_mul_sinh_div`), and
`F(v_{-τ}·z) = F(P/Q) = (Q/P) * F.invQuot (Q/P)`, so the source expression
`(cosh τ + Re z sinh τ)^{d-1} F(v_{-τ}·z)` equals `P^{d-2} Q^d z^{1-d} F.invQuot (Q/P)`.  The
latter is taken as the definition: its only negative powers are powers of `P` and of `z`, and both
are nonvanishing on the closed strip over the closed upper semicircle
(`cnum_neg_ne_zero_of_upper`, `Circle.coe_ne_zero`), whereas `Q` — whose vanishing is exactly the
pole `v_{-τ}·z = ∞` — occurs only to the nonnegative power `d`.

For `d = 0` the source factor `(cosh τ + Re z sinh τ)^{-1}` genuinely has a simple pole, and the
definition reads `z * F.invQuot (Q/P) / P^2`, which is regular there.  This is the
removable-singularity extension [T26] Definition 3.5 prescribes, built into the definition rather
than imposed afterwards; `betaBoostVal_eq_source` and `betaBoostVal_unique_of_eqOn` record that it
is the source expression off the pole and the only continuous function that is. -/
def betaBoostVal (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) (z : Circle) : ℂ :=
  cnum (-τ) z ^ ((d : ℤ) - 2) * cden (-τ) z ^ d * (z : ℂ) ^ (1 - (d : ℤ)) *
    F.invQuot (cden (-τ) z / cnum (-τ) z)

/-- The `zpow` bookkeeping behind the source correspondence: away from the poles, the source
scalar `(Q·P/z)^{d-1}` times the factor `Q/P` coming from `F(P/Q) = (Q/P)·F.invQuot(Q/P)` is the
pole-free monomial `P^{d-2} Q^d z^{1-d}` used in the definition. -/
theorem zpow_boost_identity {P Q w : ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) (hw : w ≠ 0) (d : ℕ) :
    P ^ ((d : ℤ) - 2) * Q ^ d * w ^ (1 - (d : ℤ)) =
      (Q * P / w) ^ ((d : ℤ) - 1) * (Q / P) := by
  have hPd : P ^ ((d : ℤ)) ≠ 0 := zpow_ne_zero _ hP
  have hQd : Q ^ ((d : ℤ)) ≠ 0 := zpow_ne_zero _ hQ
  have hwd : w ^ ((d : ℤ)) ≠ 0 := zpow_ne_zero _ hw
  have hP2 : P ^ (2 : ℤ) = P * P := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    ring
  rw [← zpow_natCast Q d, div_zpow, mul_zpow,
    zpow_sub₀ hP (d : ℤ) 2, zpow_sub₀ hQ (d : ℤ) 1, zpow_sub₀ hP (d : ℤ) 1,
    zpow_sub₀ hw (d : ℤ) 1, zpow_sub₀ hw 1 (d : ℤ), hP2]
  simp only [zpow_one]
  field_simp

/-- [T26], Definition 3.5; the pointwise value written with only natural-number powers and
inverses of the two nonvanishing quantities, the form in which its smoothness is proved. -/
theorem betaBoostVal_eq_mul_inv (d : ℕ) (F : AnalyticTestFn) {τ : ℂ} {z : Circle}
    (hP : cnum (-τ) z ≠ 0) :
    betaBoostVal d τ F z =
      cnum (-τ) z ^ d * (cnum (-τ) z * cnum (-τ) z)⁻¹ * cden (-τ) z ^ d *
        ((z : ℂ) * ((z : ℂ) ^ d)⁻¹) *
        F.invQuot (cden (-τ) z / cnum (-τ) z) := by
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hPz : cnum (-τ) z ^ ((d : ℤ) - 2) =
      cnum (-τ) z ^ d * (cnum (-τ) z * cnum (-τ) z)⁻¹ := by
    rw [show ((d : ℤ) - 2) = ((d : ℤ) - 1) - 1 by ring, zpow_sub_one₀ hP,
      zpow_sub_one₀ hP, zpow_natCast, mul_inv]
    ring
  have hzz : (z : ℂ) ^ (1 - (d : ℤ)) = (z : ℂ) * ((z : ℂ) ^ d)⁻¹ := by
    rw [show (1 - (d : ℤ)) = (1 : ℤ) + (-(d : ℤ)) by ring, zpow_add₀ hz, zpow_one,
      zpow_neg, zpow_natCast]
  rw [betaBoostVal, hPz, hzz]

/-- [T26], Definition 3.5; away from the pole the definition is the literal source expression
`(cosh τ + Re z sinh τ)^{d-1} F(v_{-τ}·z)` of equations (3.4)-(3.5). -/
theorem betaBoostVal_eq_source (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi) {z : Circle} (hz : 0 ≤ (z : ℂ).im)
    (hden : cden (-τ) z ≠ 0) :
    betaBoostVal d τ F z =
      (Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ) ^ ((d : ℤ) - 1) *
        F.evalSphere (vApplyNegSphere τ z) := by
  have hP : cnum (-τ) z ≠ 0 := cnum_neg_ne_zero_of_upper h₀ h₁ hz
  have hzc : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  -- the value of `F` at `v_{-τ}·z`, rewritten through the divided inverted function
  have hsphere : F.evalSphere (vApplyNegSphere τ z) =
      cden (-τ) z / cnum (-τ) z * F.invQuot (cden (-τ) z / cnum (-τ) z) := by
    have hQP : cden (-τ) z / cnum (-τ) z ≠ 0 := div_ne_zero hden hP
    rw [F.mul_invQuot, F.invExt_of_ne hQP, inv_div, vApplyNegSphere, if_neg hden]
    rfl
  have hscalar : Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ =
      cden (-τ) z * cnum (-τ) z / (z : ℂ) := cosh_add_re_mul_sinh_div τ z
  rw [hsphere, hscalar, betaBoostVal,
    show (cden (-τ) z * cnum (-τ) z / (z : ℂ)) ^ ((d : ℤ) - 1) *
        (cden (-τ) z / cnum (-τ) z * F.invQuot (cden (-τ) z / cnum (-τ) z)) =
      ((cden (-τ) z * cnum (-τ) z / (z : ℂ)) ^ ((d : ℤ) - 1) *
        (cden (-τ) z / cnum (-τ) z)) * F.invQuot (cden (-τ) z / cnum (-τ) z) by ring]
  congr 1
  exact zpow_boost_identity hP hden hzc d

/-- [T26], Definition 3.5; for `d ≥ 1` the definition is the literal source expression at every
point of the closed upper semicircle, the pole included: there both sides vanish, because
`F(∞) = 0`. -/
theorem betaBoostVal_eq_source_of_one_le {d : ℕ} (hd : 1 ≤ d) (F : AnalyticTestFn) {τ : ℂ}
    (h₀ : 0 ≤ τ.im) (h₁ : τ.im ≤ Real.pi) {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    betaBoostVal d τ F z =
      (Complex.cosh τ + ((z : ℂ).re : ℂ) * Complex.sinh τ) ^ ((d : ℤ) - 1) *
        F.evalSphere (vApplyNegSphere τ z) := by
  by_cases hden : cden (-τ) z = 0
  · have hP : cnum (-τ) z ≠ 0 := cnum_neg_ne_zero_of_upper h₀ h₁ hz
    have hleft : betaBoostVal d τ F z = 0 := by
      rw [betaBoostVal, hden, zero_pow (by omega)]
      ring
    have hright : F.evalSphere (vApplyNegSphere τ z) = 0 := by
      rw [vApplyNegSphere, if_pos hden]
      exact F.evalSphere_infty
    rw [hleft, hright, mul_zero]
  · exact betaBoostVal_eq_source d F h₀ h₁ hz hden

/-- [T26], Definition 3.5; the pole of the source expression is a single point of the circle, so
the closed upper semicircle minus the pole is dense in it.  This is what makes the
removable-singularity extension unique, hence what makes `betaBoostVal` *the* extension rather
than *an* extension. -/
theorem subsingleton_cden_neg_eq_zero (τ : ℂ) :
    {z : Circle | cden (-τ) z = 0}.Subsingleton := by
  intro z hz w hw
  have hz' : Complex.sinh (τ / 2) * (z : ℂ) + Complex.cosh (τ / 2) = 0 := by
    have hz2 : cden (-τ) z = 0 := hz
    rwa [cden_neg] at hz2
  have hw' : Complex.sinh (τ / 2) * (w : ℂ) + Complex.cosh (τ / 2) = 0 := by
    have hw2 : cden (-τ) w = 0 := hw
    rwa [cden_neg] at hw2
  have hsinh : Complex.sinh (τ / 2) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hz'
    have hone := Complex.cosh_sq_sub_sinh_sq (τ / 2)
    rw [hz', h0] at hone
    simp at hone
  apply Circle.coe_injective
  have hdiff : Complex.sinh (τ / 2) * ((z : ℂ) - (w : ℂ)) = 0 := by
    have : Complex.sinh (τ / 2) * (z : ℂ) = Complex.sinh (τ / 2) * (w : ℂ) := by
      linear_combination hz' - hw'
    linear_combination this
  rcases mul_eq_zero.mp hdiff with h | h
  · exact absurd h hsinh
  · linear_combination h

end

end MobiusCPT
