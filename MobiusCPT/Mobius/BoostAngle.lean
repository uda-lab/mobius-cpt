import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MobiusCPT.Mobius.Factor
import MobiusCPT.Mobius.BoostContinuity

/-!
# MobiusCPT.Mobius.BoostAngle

The real angle lift of the negative real boost `v_{-t}` acting on the circle, [T26], §3
(eq. (3.4)-(3.5)). This is deliberately not the boost-chart route
(`MobiusCPT.Analysis.BoostChart`), which only covers the open upper semicircle: this file builds
a genuinely global lift, valid for every `t θ : ℝ`, as the antiderivative of the reciprocal
automorphy-factor base, and identifies it with the boost action by an elementary algebraic
computation together with `hasDerivAt_smul_circleExp` (already on `main`, `MobiusCPT.Mobius.Factor`)
-- no covering-space theory, no `Complex.arg` branch cuts.
-/

namespace MobiusCPT

noncomputable section

open scoped ComplexConjugate

/-! ### The elementary circle identity `z^2 + 1 = 2 Re(z) z` -/

/-- Every point of the unit circle satisfies its own real quadratic: `z^2 + 1 = 2 Re(z) z`. -/
theorem sq_add_one_eq_two_mul_re (z : Circle) :
    (z : ℂ) ^ 2 + 1 = 2 * ((z : ℂ).re : ℂ) * (z : ℂ) := by
  have h1 : (z : ℂ) * conj (z : ℂ) = 1 := by
    have hnormsq : Complex.normSq (z : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num
    rw [Complex.mul_conj]
    exact_mod_cast hnormsq
  have h2 : (z : ℂ) + conj (z : ℂ) = 2 * ((z : ℂ).re : ℂ) := by
    have := Complex.add_conj (z : ℂ)
    push_cast at this
    exact this
  have h3 : conj (z : ℂ) = 2 * ((z : ℂ).re : ℂ) - (z : ℂ) := by linear_combination h2
  rw [h3] at h1
  linear_combination -h1

/-! ### The automorphy-factor base -/

/-- [T26], eq. (3.5): the automorphy-factor base `cosh t + Re(z) sinh t`, for a general
`z : Circle`. -/
def boostPz (t : ℝ) (z : Circle) : ℝ := Real.cosh t + (z : ℂ).re * Real.sinh t

/-- [T26], eq. (3.5): `boostPz` at `z = Circle.exp θ`. -/
def boostP (t θ : ℝ) : ℝ := boostPz t (Circle.exp θ)

/-- `boostPz` is strictly positive: `cosh t - |sinh t| ≤ boostPz t z` and
`cosh t - |sinh t| = exp(-|t|) > 0`. -/
theorem boostPz_pos (t : ℝ) (z : Circle) : 0 < boostPz t z := by
  have hre_le : |(z : ℂ).re| ≤ 1 := by
    have hnorm : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
    calc |(z : ℂ).re| ≤ ‖(z : ℂ)‖ := Complex.abs_re_le_norm _
      _ = 1 := hnorm
  have hbound : Real.cosh t - |Real.sinh t| ≤ boostPz t z := by
    rcases abs_le.mp hre_le with ⟨hlo, hhi⟩
    rcases le_or_gt 0 (Real.sinh t) with hs | hs
    · rw [abs_of_nonneg hs]
      simp only [boostPz]
      nlinarith [mul_le_mul_of_nonneg_right hhi hs]
    · rw [abs_of_neg hs]
      simp only [boostPz]
      nlinarith [mul_le_mul_of_nonpos_right hlo hs.le]
  have heq2 : Real.cosh t - |Real.sinh t| = Real.exp (-|t|) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
      rw [Real.cosh_eq, Real.sinh_eq]; ring_nf
    · rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr h)]
      rw [Real.cosh_eq, Real.sinh_eq]; ring_nf
  linarith [heq2 ▸ hbound, Real.exp_pos (-|t|)]

theorem boostP_pos (t θ : ℝ) : 0 < boostP t θ := boostPz_pos t (Circle.exp θ)

theorem continuous_boostP (t : ℝ) : Continuous (boostP t) := by
  have hre : Continuous (fun θ : ℝ => (Circle.exp θ : ℂ).re) :=
    Complex.reCLM.continuous.comp contDiff_circle_map.continuous
  exact continuous_const.add (hre.mul continuous_const)

theorem continuous_boostPInv (t : ℝ) : Continuous fun θ => (boostP t θ)⁻¹ :=
  (continuous_boostP t).inv₀ (fun θ => (boostP_pos t θ).ne')

/-! ### The angle lift, as an antiderivative -/

/-- The real angle lift of `v_{-t}`, defined as the antiderivative of `1 / boostP t`, based at
`θ = 0`. -/
def boostAngle (t θ : ℝ) : ℝ := ∫ x in (0 : ℝ)..θ, (boostP t x)⁻¹

@[simp] theorem boostAngle_zero (t : ℝ) : boostAngle t 0 = 0 :=
  intervalIntegral.integral_same

/-- FTC: `boostAngle t` differentiates to `1 / boostP t`. -/
theorem hasDerivAt_boostAngle (t θ : ℝ) : HasDerivAt (boostAngle t) (boostP t θ)⁻¹ θ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_boostPInv t).intervalIntegrable 0 θ)
    ((continuous_boostPInv t).stronglyMeasurableAtFilter _ _)
    (continuous_boostPInv t).continuousAt

/-! ### The key algebraic identity -/

/-- [T26], eq. (3.4)-(3.5), the core algebraic identity behind the ODE match: `boostPz t z * z =
(α z + β)(β z + α)` where `α = cosh(t/2)`, `β = sinh(t/2)` are the (real) entries of
`boostMat (-t)`. Consequence of `sq_add_one_eq_two_mul_re` and the double-angle identities
`cosh t = α^2+β^2`, `sinh t = 2 α β`. -/
theorem boostPz_smul_eq (t : ℝ) (z : Circle) :
    ((boostPz t z : ℝ) : ℂ) * (z : ℂ) =
      ((boostMat (-t)).α * (z : ℂ) + (boostMat (-t)).β) *
        ((boostMat (-t)).β * (z : ℂ) + (boostMat (-t)).α) := by
  have hα : (boostMat (-t)).α = (Real.cosh (t / 2) : ℂ) := boostMat_neg_alpha t
  have hβ : (boostMat (-t)).β = (Real.sinh (t / 2) : ℂ) := boostMat_neg_beta t
  have hcosh : Real.cosh t = Real.cosh (t / 2) ^ 2 + Real.sinh (t / 2) ^ 2 := by
    have h := Real.cosh_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t by ring] at h
  have hsinh : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
    have h := Real.sinh_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t by ring] at h
  have hre2 : 2 * ((z : ℂ).re : ℂ) * (z : ℂ) = (z : ℂ) ^ 2 + 1 :=
    (sq_add_one_eq_two_mul_re z).symm
  rw [hα, hβ]
  have hPz : ((boostPz t z : ℝ) : ℂ) =
      ((Real.cosh (t / 2) : ℂ) ^ 2 + (Real.sinh (t / 2) : ℂ) ^ 2) +
        ((z : ℂ).re : ℂ) * (2 * (Real.sinh (t / 2) : ℂ) * (Real.cosh (t / 2) : ℂ)) := by
    unfold boostPz
    push_cast [hcosh, hsinh]
    ring
  rw [hPz]
  have : (((Real.cosh (t / 2) : ℂ) ^ 2 + (Real.sinh (t / 2) : ℂ) ^ 2) +
        ((z : ℂ).re : ℂ) * (2 * (Real.sinh (t / 2) : ℂ) * (Real.cosh (t / 2) : ℂ))) * (z : ℂ) =
      (Real.cosh (t / 2) : ℂ) ^ 2 * (z:ℂ) + (Real.sinh (t / 2) : ℂ) ^ 2 * (z:ℂ) +
        (Real.sinh (t / 2) : ℂ) * (Real.cosh (t / 2) : ℂ) *
          (2 * ((z : ℂ).re : ℂ) * (z : ℂ)) := by ring
  rw [this, hre2]
  ring

/-- The negative boost fixes the basepoint `1 : Circle`, matching `boostAngle t 0 = 0`. -/
theorem boostMat_neg_smul_one (t : ℝ) : boostMat (-t) • (1 : Circle) = 1 := by
  apply Circle.ext
  rw [coe_smul, boostMat_neg_alpha, boostMat_neg_beta, j_boostMat_neg_eq, Circle.coe_one, mul_one,
    mul_one]
  have hnum : (Real.cosh (t / 2) : ℂ) + (Real.sinh (t / 2) : ℂ) = ((Real.exp (t / 2) : ℝ) : ℂ) := by
    have h : Real.cosh (t / 2) + Real.sinh (t / 2) = Real.exp (t / 2) := by
      rw [add_comm]; exact Real.sinh_add_cosh (t / 2)
    exact_mod_cast h
  have hden : (Real.sinh (t / 2) : ℂ) + (Real.cosh (t / 2) : ℂ) = ((Real.exp (t / 2) : ℝ) : ℂ) := by
    exact_mod_cast Real.sinh_add_cosh (t / 2)
  rw [hnum, hden]
  exact div_self (by exact_mod_cast (Real.exp_pos (t / 2)).ne')

/-! ### The identification with the boost action -/

/-- `θ ↦ (boostMat (-t) • Circle.exp θ : ℂ)` solves the linear ODE `y' = I y / boostP t`. -/
theorem hasDerivAt_boostSmulExp (t θ : ℝ) :
    HasDerivAt (fun θ' => ((boostMat (-t) • Circle.exp θ' : Circle) : ℂ))
      (Complex.I * ((boostMat (-t) • Circle.exp θ : Circle) : ℂ) / (boostP t θ : ℂ)) θ := by
  have hraw := hasDerivAt_smul_circleExp (boostMat (-t)) θ
  have hJ : j (boostMat (-t)) (Circle.exp θ) ≠ 0 := j_ne_zero (boostMat (-t)) (Circle.exp θ)
  have hP : (boostP t θ : ℂ) ≠ 0 := by exact_mod_cast (boostP_pos t θ).ne'
  have hj_eq : (boostMat (-t)).β * (Circle.exp θ : ℂ) + (boostMat (-t)).α =
      j (boostMat (-t)) (Circle.exp θ) := by
    rw [boostMat_neg_alpha, boostMat_neg_beta, j_boostMat_neg_eq]
  have hkey : ((boostP t θ : ℝ) : ℂ) * (Circle.exp θ : ℂ) =
      ((boostMat (-t)).α * (Circle.exp θ : ℂ) + (boostMat (-t)).β) *
        j (boostMat (-t)) (Circle.exp θ) := by
    have h := boostPz_smul_eq t (Circle.exp θ)
    rwa [hj_eq] at h
  have heq : Complex.I * (Circle.exp θ : ℂ) / (j (boostMat (-t)) (Circle.exp θ)) ^ 2 =
      Complex.I * ((boostMat (-t) • Circle.exp θ : Circle) : ℂ) / (boostP t θ : ℂ) := by
    rw [coe_smul, ← mul_div_assoc, div_div, div_eq_div_iff (pow_ne_zero 2 hJ) (mul_ne_zero hJ hP)]
    linear_combination (Complex.I * j (boostMat (-t)) (Circle.exp θ)) * hkey
  rwa [heq] at hraw

/-- `θ ↦ (Circle.exp (boostAngle t θ) : ℂ)` solves the same linear ODE `y' = I y / boostP t`. -/
theorem hasDerivAt_circleExp_boostAngle (t θ : ℝ) :
    HasDerivAt (fun θ' => (Circle.exp (boostAngle t θ') : ℂ))
      (Complex.I * (Circle.exp (boostAngle t θ) : ℂ) / (boostP t θ : ℂ)) θ := by
  have hexp : HasDerivAt (fun x : ℝ => (Circle.exp x : ℂ)) (Complex.I * (Circle.exp (boostAngle t θ) : ℂ)) (boostAngle t θ) := by
    have hraw := hasDerivAt_smul_circleExp (1 : SU11) (boostAngle t θ)
    simp only [one_smul, j_one, one_pow, div_one] at hraw
    exact hraw
  have hcomp := HasDerivAt.scomp θ hexp (hasDerivAt_boostAngle t θ)
  have hderiv_eq : (boostP t θ)⁻¹ • (Complex.I * (Circle.exp (boostAngle t θ) : ℂ)) =
      Complex.I * (Circle.exp (boostAngle t θ) : ℂ) / (boostP t θ : ℂ) := by
    rw [Complex.real_smul, div_eq_mul_inv]
    push_cast
    ring
  rwa [hderiv_eq] at hcomp

/-- The key identity: `boostAngle` reproduces the boost action, for every `t θ : ℝ`. Both
`θ ↦ (boostMat (-t) • Circle.exp θ : ℂ)` and `θ ↦ (Circle.exp (boostAngle t θ) : ℂ)` solve the
linear ODE `y' = I y / boostP t` with the same value `1` at `θ = 0`; their ratio therefore has
derivative `0` everywhere and equals its value `1` at `θ = 0`. -/
theorem circleExp_boostAngle (t θ : ℝ) :
    (Circle.exp (boostAngle t θ) : ℂ) = ((boostMat (-t) • Circle.exp θ : Circle) : ℂ) := by
  set w : ℝ → ℂ := fun θ' => ((boostMat (-t) • Circle.exp θ' : Circle) : ℂ) with hw_def
  set e : ℝ → ℂ := fun θ' => (Circle.exp (boostAngle t θ') : ℂ) with he_def
  have he_ne : ∀ x, e x ≠ 0 := fun x => by
    rw [he_def]
    exact Circle.coe_ne_zero _
  set ratio : ℝ → ℂ := fun θ' => w θ' * (e θ')⁻¹ with hratio_def
  have hratio' : ∀ x, HasDerivAt ratio 0 x := by
    intro x
    have hw' : HasDerivAt w (Complex.I * w x / (boostP t x : ℂ)) x :=
      hasDerivAt_boostSmulExp t x
    have he' : HasDerivAt e (Complex.I * e x / (boostP t x : ℂ)) x :=
      hasDerivAt_circleExp_boostAngle t x
    have hei' := he'.inv (he_ne x)
    have hprod := hw'.mul hei'
    have hP : (boostP t x : ℂ) ≠ 0 := by exact_mod_cast (boostP_pos t x).ne'
    have hzero : Complex.I * w x / (boostP t x : ℂ) * (e x)⁻¹ +
        w x * (-(Complex.I * e x / (boostP t x : ℂ)) / (e x) ^ 2) = 0 := by
      field_simp
      ring
    have hratio_eq : ratio = w * fun y => (e y)⁻¹ := by funext y; rfl
    rw [hratio_eq, ← hzero]
    exact hprod
  have hconst : ∀ x y, ratio x = ratio y := by
    intro x y
    exact is_const_of_fderiv_eq_zero (𝕜 := ℝ)
      (fun x => (hratio' x).differentiableAt)
      (fun x => by simpa using (hratio' x).hasFDerivAt.fderiv) x y
  have hratio0 : ratio 0 = 1 := by
    rw [hratio_def]
    simp only
    rw [hw_def, he_def]
    simp only [Circle.exp_zero]
    rw [boostAngle_zero, Circle.exp_zero, boostMat_neg_smul_one]
    simp
  have hratioθ : ratio θ = 1 := (hconst θ 0).trans hratio0
  have hwe : w θ * (e θ)⁻¹ = 1 := hratioθ
  have hmul : w θ * (e θ)⁻¹ * e θ = 1 * e θ := by rw [hwe]
  rw [mul_assoc, inv_mul_cancel₀ (he_ne θ), mul_one, one_mul] at hmul
  exact hmul.symm

theorem circleExp_boostAngle' (t θ : ℝ) :
    Circle.exp (boostAngle t θ) = boostMat (-t) • Circle.exp θ :=
  Circle.ext (circleExp_boostAngle t θ)

end

end MobiusCPT
