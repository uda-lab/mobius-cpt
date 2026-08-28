import MobiusCPT.Mobius.ComplexBetaDef
import MobiusCPT.Mobius.ComplexBetaLawsCore
import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.Inv

/-!
# Boundary and composition laws for the complex boost

This file promotes the pointwise boundary identities for the complex boost to identities of
smooth test functions.  It also proves the real-translation cocycle directly in the pole-free
form of `betaBoostVal`, so the removable singularity at conformal dimension zero is retained.
-/

namespace MobiusCPT

open Set

noncomputable section

/-- [T26], Definition 3.5; on the closed upper semicircle the packaged complex boost agrees with
its pointwise formula. -/
theorem betaBoost_apply_of_mem_upper (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    betaBoost d τ F z = betaBoostVal d τ F z := by
  rw [← Circle.exp_arg z]
  exact betaBoost_apply_circleExp d F hτ
    ⟨Complex.arg_nonneg_iff.mpr hz, Complex.arg_le_pi (z : ℂ)⟩

private theorem xRestrictUpper_apply_of_im_nonneg (F : AnalyticTestFn) {z : Circle}
    (hz : 0 ≤ (z : ℂ).im) : xRestrictUpper F z = F.toFun z := by
  rw [← Circle.exp_arg z]
  change toAngle (xRestrictUpper F) (Complex.arg (z : ℂ)) =
    F.toFun (Circle.exp (Complex.arg (z : ℂ)))
  rw [xRestrictUpper,
    toAngle_splitUpper_of_mem F.isEndpointFlat
      ⟨Complex.arg_nonneg_iff.mpr hz, Complex.arg_le_pi (z : ℂ)⟩,
    toAngle_xRestrictS1]

private theorem circle_eq_one_or_neg_one_of_im_eq_zero {z : Circle}
    (hz : (z : ℂ).im = 0) : z = 1 ∨ z = -1 := by
  have hnorm : Complex.normSq (z : ℂ) = 1 := Circle.normSq_coe z
  have hre : (z : ℂ).re ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hz, pow_two] using hnorm
  rcases sq_eq_one_iff.mp hre with hre | hre
  · left
    apply Circle.ext
    apply Complex.ext
    · simpa using hre
    · simpa using hz
  · right
    apply Circle.ext
    apply Complex.ext
    · simpa using hre
    · simpa using hz

private theorem toAngle_splitLower_of_mem {f : TestFn} (h : IsEndpointFlat f) {θ : ℝ}
    (hθ : θ ∈ Set.Icc Real.pi (2 * Real.pi)) :
    toAngle (splitLower f h) θ = toAngle f θ := by
  by_cases htop : θ = 2 * Real.pi
  · subst θ
    have hper := periodic_periodize (2 * Real.pi) Real.two_pi_pos
      (cutIcc Real.pi (2 * Real.pi) (toAngle f))
    have hfzero : toAngle f (2 * Real.pi) = 0 := by
      simpa only [iteratedDeriv_zero] using h.two_pi 0
    rw [toAngle_splitLower]
    calc
      periodize (2 * Real.pi) (cutIcc Real.pi (2 * Real.pi) (toAngle f))
          (2 * Real.pi) =
          periodize (2 * Real.pi) (cutIcc Real.pi (2 * Real.pi) (toAngle f)) 0 := by
            simpa using hper 0
      _ = cutIcc Real.pi (2 * Real.pi) (toAngle f) 0 :=
        periodize_eq_self Real.two_pi_pos ⟨le_rfl, Real.two_pi_pos⟩
      _ = 0 := cutIcc_eq_zero_of_notMem _ (by
        intro hmem
        exact (not_le_of_gt Real.pi_pos) hmem.1)
      _ = toAngle f (2 * Real.pi) := hfzero.symm
  · rw [toAngle_splitLower, periodize_eq_self Real.two_pi_pos]
    · exact cutIcc_eq_of_mem (toAngle f) hθ
    · exact ⟨Real.pi_pos.le.trans hθ.1,
        lt_of_le_of_ne hθ.2 htop⟩

private theorem xRestrictLower_apply_of_im_nonpos (F : AnalyticTestFn) {z : Circle}
    (hz : (z : ℂ).im ≤ 0) : xRestrictLower F z = F.toFun z := by
  by_cases hzlt : (z : ℂ).im < 0
  · let θ := Complex.arg (z : ℂ) + 2 * Real.pi
    have hθ : θ ∈ Set.Icc Real.pi (2 * Real.pi) := by
      constructor
      · dsimp [θ]
        linarith [Complex.neg_pi_lt_arg (z : ℂ)]
      · dsimp [θ]
        have hneg : (z : ℂ).arg < 0 := Complex.arg_neg_iff.mpr hzlt
        linarith
    have hexp : Circle.exp θ = z := by
      dsimp [θ]
      simpa only [Circle.exp_add, Circle.exp_two_pi, mul_one] using Circle.exp_arg z
    rw [← hexp]
    change toAngle (xRestrictLower F) θ = F.toFun (Circle.exp θ)
    rw [xRestrictLower, toAngle_splitLower_of_mem F.isEndpointFlat hθ,
      toAngle_xRestrictS1]
  · have hzim : (z : ℂ).im = 0 := le_antisymm hz (le_of_not_gt hzlt)
    rcases circle_eq_one_or_neg_one_of_im_eq_zero hzim with rfl | rfl
    · have hexp : Circle.exp (2 * Real.pi) = (1 : Circle) := Circle.exp_two_pi
      rw [← hexp]
      change toAngle (xRestrictLower F) (2 * Real.pi) =
        F.toFun (Circle.exp (2 * Real.pi))
      rw [xRestrictLower,
        toAngle_splitLower_of_mem F.isEndpointFlat
          ⟨by linarith [Real.pi_pos], le_rfl⟩,
        toAngle_xRestrictS1]
    · have hexp : Circle.exp Real.pi = (-1 : Circle) := by
        apply Circle.ext
        simp [Circle.coe_exp, Complex.exp_pi_mul_I]
      rw [← hexp]
      change toAngle (xRestrictLower F) Real.pi = F.toFun (Circle.exp Real.pi)
      rw [xRestrictLower,
        toAngle_splitLower_of_mem F.isEndpointFlat
          ⟨le_rfl, by linarith [Real.pi_pos]⟩,
        toAngle_xRestrictS1]

/-- [T26], equations (3.4)-(3.5); for a real parameter the complex boost is the ordinary conformal
action `β_d(v_t)` applied to the upper restriction `F|_{I_+}`.  This is the compatibility that
makes the complexified expression a continuation of the real one. -/
theorem betaBoost_ofReal (d : ℕ) (t : ℝ) (F : AnalyticTestFn) :
    betaBoost d (t : ℂ) F = beta d (boostMat t) (xRestrictUpper F) := by
  apply TestFn.ext
  intro z
  by_cases hz : 0 ≤ (z : ℂ).im
  · have hw : 0 ≤ ((boostMat (-t) • z : Circle) : ℂ).im := by
      rw [im_boostMat_smul]
      exact div_nonneg hz (Complex.normSq_nonneg _)
    rw [betaBoost_apply_of_mem_upper d F (ofReal_mem_strip_I_mul_pi t) hz,
      betaBoostVal_eq_source d F (by simp) (by simp [Real.pi_pos.le]) hz
        (cden_neg_ofReal_ne_zero t z),
      cosh_add_re_mul_sinh_ofReal, vApplyNegSphere_ofReal,
      F.evalSphere_coe, beta_boostMat_apply,
      xRestrictUpper_apply_of_im_nonneg F hw, Complex.ofReal_zpow]
  · have hzlower : z ∈ lowerArc := by
      exact lt_of_not_ge hz
    rw [suppUpper_betaBoost d (t : ℂ) F z hzlower, beta_boostMat_apply,
      (xRestrictUpper_supp F) (boostMat (-t) • z)
        (boostMat_smul_mem_lowerArc (-t) hzlower), mul_zero]

/-- [T26], equations (3.4)-(3.5), at the level of `Möb = PSU(1,1)`. -/
theorem betaBoost_ofReal_mob (d : ℕ) (t : ℝ) (F : AnalyticTestFn) :
    betaBoost d (t : ℂ) F = Mob.beta d (Mob.boost t) (xRestrictUpper F) := by
  rw [Mob.boost, Mob.beta_mk]
  exact betaBoost_ofReal d t F

/-- [T26], equation (3.5); the numerator cocycle for translating a complex boost parameter by a
real boost. -/
theorem cnum_neg_add_ofReal (τ : ℂ) (t : ℝ) (z : Circle) :
    cnum (-(τ + t)) z =
      cnum (-τ) ((boostMat (-t) • z : Circle) : ℂ) * cden (-(t : ℂ)) z := by
  have hden : Complex.sinh ((t : ℂ) / 2) * (z : ℂ) + Complex.cosh ((t : ℂ) / 2) ≠ 0 := by
    simpa only [cden_neg] using cden_neg_ofReal_ne_zero t z
  simp only [cnum_neg, cden_neg]
  rw [coe_boostMat_smul, Complex.ofReal_neg, vApply]
  simp only [cnum_neg, cden_neg]
  rw [show (τ + (t : ℂ)) / 2 = τ / 2 + (t : ℂ) / 2 by ring,
    Complex.cosh_add, Complex.sinh_add]
  field_simp [hden]
  ring

/-- [T26], equation (3.5); the denominator cocycle for translating a complex boost parameter by a
real boost. -/
theorem cden_neg_add_ofReal (τ : ℂ) (t : ℝ) (z : Circle) :
    cden (-(τ + t)) z =
      cden (-τ) ((boostMat (-t) • z : Circle) : ℂ) * cden (-(t : ℂ)) z := by
  have hden : Complex.sinh ((t : ℂ) / 2) * (z : ℂ) + Complex.cosh ((t : ℂ) / 2) ≠ 0 := by
    simpa only [cden_neg] using cden_neg_ofReal_ne_zero t z
  simp only [cnum_neg, cden_neg]
  rw [coe_boostMat_smul, Complex.ofReal_neg, vApply]
  simp only [cnum_neg, cden_neg]
  rw [show (τ + (t : ℂ)) / 2 = τ / 2 + (t : ℂ) / 2 by ring,
    Complex.cosh_add, Complex.sinh_add]
  field_simp [hden]
  ring

private theorem betaBoost_monomial_cocycle (d : ℕ) {P Q A R W z : ℂ}
    (hP : P ≠ 0) (hA : A ≠ 0) (hR : R ≠ 0) (hz : z ≠ 0) (hW : W = A / R) :
    (R * A / z) ^ ((d : ℤ) - 1) *
        (P ^ ((d : ℤ) - 2) * Q ^ d * W ^ (1 - (d : ℤ))) =
      (P * R) ^ ((d : ℤ) - 2) * (Q * R) ^ d * z ^ (1 - (d : ℤ)) := by
  subst hW
  have hRAz : R * A / z ≠ 0 := div_ne_zero (mul_ne_zero hR hA) hz
  have hPR : P * R ≠ 0 := mul_ne_zero hP hR
  have hAR : A / R ≠ 0 := div_ne_zero hA hR
  have key1 : ∀ x : ℂ, x ≠ 0 → x ^ ((d : ℤ) - 1) = x ^ (d : ℕ) / x := by
    intro x hx
    rw [zpow_sub₀ hx, zpow_natCast, zpow_one]
  have key2 : ∀ x : ℂ, x ≠ 0 → x ^ ((d : ℤ) - 2) = x ^ (d : ℕ) / (x * x) := by
    intro x hx
    rw [zpow_sub₀ hx, zpow_natCast]
    congr 1
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    ring
  have key3 : ∀ x : ℂ, x ≠ 0 → x ^ (1 - (d : ℤ)) = x / x ^ (d : ℕ) := by
    intro x hx
    rw [zpow_sub₀ hx, zpow_natCast, zpow_one]
  have hzd : z ^ (d : ℕ) ≠ 0 := pow_ne_zero d hz
  have hRd : R ^ (d : ℕ) ≠ 0 := pow_ne_zero d hR
  rw [key1 _ hRAz, key2 _ hP, key3 _ hAR, key2 _ hPR, key3 _ hz]
  field_simp
  simp only [div_pow, mul_pow]
  field_simp

/-- [T26], equation (3.5); the pole-free pointwise complex boost obeys the real-translation
cocycle, including the removable-singularity value when `d = 0`. -/
theorem betaBoostVal_add_ofReal (d : ℕ) (t : ℝ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) (F : AnalyticTestFn) {z : Circle}
    (hz : 0 ≤ (z : ℂ).im) :
    (((Real.cosh t + (z : ℂ).re * Real.sinh t) ^ ((d : ℤ) - 1) : ℝ) : ℂ) *
        betaBoostVal d τ F (boostMat (-t) • z) =
      betaBoostVal d (τ + (t : ℂ)) F z := by
  have hw : 0 ≤ ((boostMat (-t) • z : Circle) : ℂ).im := by
    rw [im_boostMat_smul]
    exact div_nonneg hz (Complex.normSq_nonneg _)
  have hstrip := mem_strip_I_mul_pi.mp hτ
  have hP : cnum (-τ) ((boostMat (-t) • z : Circle) : ℂ) ≠ 0 :=
    cnum_neg_ne_zero_of_upper hstrip.1 hstrip.2 hw
  have hR : cden (-(t : ℂ)) z ≠ 0 := cden_neg_ofReal_ne_zero t z
  have hwcoe : ((boostMat (-t) • z : Circle) : ℂ) =
      cnum (-(t : ℂ)) z / cden (-(t : ℂ)) z := by
    rw [coe_boostMat_smul, Complex.ofReal_neg, vApply]
  have hA : cnum (-(t : ℂ)) z ≠ 0 := by
    intro hA
    rw [hA, zero_div] at hwcoe
    exact Circle.coe_ne_zero (boostMat (-t) • z) hwcoe
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have hnum := cnum_neg_add_ofReal τ t z
  have hden := cden_neg_add_ofReal τ t z
  have hratio :
      cden (-(τ + (t : ℂ))) z / cnum (-(τ + (t : ℂ))) z =
        cden (-τ) ((boostMat (-t) • z : Circle) : ℂ) /
          cnum (-τ) ((boostMat (-t) • z : Circle) : ℂ) := by
    rw [hnum, hden]
    field_simp [hP, hR]
  have hscalar :
      ((Real.cosh t + (z : ℂ).re * Real.sinh t : ℝ) : ℂ) =
        cden (-(t : ℂ)) z * cnum (-(t : ℂ)) z / (z : ℂ) := by
    calc
      ((Real.cosh t + (z : ℂ).re * Real.sinh t : ℝ) : ℂ) =
          Complex.cosh (t : ℂ) + ((z : ℂ).re : ℂ) * Complex.sinh (t : ℂ) :=
        (cosh_add_re_mul_sinh_ofReal t z).symm
      _ = cden (-(t : ℂ)) z * cnum (-(t : ℂ)) z / (z : ℂ) :=
        cosh_add_re_mul_sinh_div (t : ℂ) z
  have hcancel :
      cden (-τ) ((boostMat (-t) • z : Circle) : ℂ) * cden (-(t : ℂ)) z /
          (cnum (-τ) ((boostMat (-t) • z : Circle) : ℂ) * cden (-(t : ℂ)) z) =
        cden (-τ) ((boostMat (-t) • z : Circle) : ℂ) /
          cnum (-τ) ((boostMat (-t) • z : Circle) : ℂ) := by
    field_simp
  rw [Complex.ofReal_zpow, betaBoostVal, betaBoostVal, hnum, hden, hscalar, hcancel,
    ← mul_assoc]
  congr 1
  exact betaBoost_monomial_cocycle d hP hA hR hz0 hwcoe

/-- [T26], equation (3.5); a real boost composes with the complex one by translating the strip
parameter.  Only this order is stated because it is the only one the source states and the only
one that composes: `β_d(v_τ)` consumes an element of `𝓧`, not of `C_0^∞(I_+)`. -/
theorem beta_boostMat_betaBoost (d : ℕ) (t : ℝ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) (F : AnalyticTestFn) :
    beta d (boostMat t) (betaBoost d τ F) = betaBoost d (τ + (t : ℂ)) F := by
  have hτadd : τ + (t : ℂ) ∈ strip (Complex.I * Real.pi) :=
    (add_ofReal_mem_strip_iff (Complex.I * Real.pi) t τ).mpr hτ
  apply TestFn.ext
  intro z
  rw [beta_boostMat_apply]
  by_cases hz : 0 ≤ (z : ℂ).im
  · have hw : 0 ≤ ((boostMat (-t) • z : Circle) : ℂ).im := by
      rw [im_boostMat_smul]
      exact div_nonneg hz (Complex.normSq_nonneg _)
    rw [betaBoost_apply_of_mem_upper d F hτ hw,
      betaBoost_apply_of_mem_upper d F hτadd hz]
    exact betaBoostVal_add_ofReal d t hτ F hz
  · have hzlower : z ∈ lowerArc := lt_of_not_ge hz
    have hwlower : boostMat (-t) • z ∈ lowerArc :=
      boostMat_smul_mem_lowerArc (-t) hzlower
    rw [suppUpper_betaBoost d τ F _ hwlower,
      suppUpper_betaBoost d (τ + (t : ℂ)) F z hzlower, mul_zero]

/-- [T26], Definition 3.5, equation (3.4) and Lemma 3.7; at the top of the strip the complex boost
is inversion composed with the lower restriction, up to the conformal-dimension sign.  The
restriction is the lower one because inversion exchanges the semicircles: the source uses
`(F ∘ z⁻¹)|_{I_+} = F|_{I_-} ∘ z⁻¹`.  The source scalar `(-1)^{d-1}` is written `(-1)^{d+1}`, the
same element of `ℂ` for `d : ℕ`. -/
theorem betaBoost_I_mul_pi (d : ℕ) (F : AnalyticTestFn) :
    betaBoost d (Complex.I * Real.pi) F =
      (-1 : ℂ) ^ (d + 1) • inv (xRestrictLower F) := by
  apply TestFn.ext
  intro z
  change betaBoost d (Complex.I * Real.pi) F z =
    (-1 : ℂ) ^ (d + 1) * inv (xRestrictLower F) z
  by_cases hz : 0 ≤ (z : ℂ).im
  · have hzinv : ((z⁻¹ : Circle) : ℂ).im ≤ 0 := by
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_nonpos.mpr hz
    rw [betaBoost_apply_of_mem_upper d F I_mul_pi_mem_strip hz,
      betaBoostVal_eq_source d F (by simp [Real.pi_pos.le]) (by simp) hz
        (cden_neg_I_mul_pi_ne_zero z),
      cosh_add_re_mul_sinh_I_mul_pi, neg_one_zpow_sub_one,
      vApplyNegSphere_I_mul_pi, F.evalSphere_coe, inv_apply,
      xRestrictLower_apply_of_im_nonpos F hzinv]
    simp only [Circle.coe_inv]
  · have hzlower : z ∈ lowerArc := lt_of_not_ge hz
    have hzinv : z⁻¹ ∈ upperArc := by
      change 0 < ((z⁻¹ : Circle) : ℂ).im
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_pos.mpr hzlower
    rw [suppUpper_betaBoost d (Complex.I * Real.pi) F z hzlower, inv_apply,
      (xRestrictLower_supp F) z⁻¹ hzinv, mul_zero]

end

end MobiusCPT
