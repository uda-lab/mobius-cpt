import Mathlib.Analysis.Complex.CauchyIntegral
import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.Fourier
import MobiusCPT.TestFunctions.Inv
import MobiusCPT.Wightman.W3Bridge
import MobiusCPT.Wightman.Bundle

/-!
# Cauchy control of the Fourier coefficients of an inverted analytic test function

The boundary value of `F.invExt` is the angle picture of `inv (xRestrictS1 F)`.  The
Fourier coefficient can therefore be written as a circle integral.  Negative modes are
then Cauchy integrals of holomorphic functions, while the zero mode is evaluated by the
Cauchy integral formula at the origin.
-/

namespace MobiusCPT

open Filter Function MeasureTheory Set
open Complex
open AddCircle
open scoped Interval Topology

noncomputable section

/- The circle inverse in Step 1 is proved in `ℂ`, rather than by using the group API of `Circle`.
   This makes the later identification with the ordinary complex inverse explicit. -/
theorem toAngle_inv_xRestrictS1 (F : AnalyticTestFn) (θ : ℝ) :
    toAngle (inv (xRestrictS1 F)) θ = F.invExt (Circle.exp θ : ℂ) := by
  have h1 : toAngle (inv (xRestrictS1 F)) θ = F.toFun (Circle.exp (-θ) : ℂ) := by
    rw [toAngle_inv]
    exact congrFun (toAngle_xRestrictS1 F) (-θ)
  have hne : (Circle.exp θ : ℂ) ≠ 0 := by
    rw [Circle.coe_exp]
    exact Complex.exp_ne_zero _
  have hinv : (Circle.exp (-θ) : ℂ) = (Circle.exp θ : ℂ)⁻¹ := by
    rw [Circle.coe_exp, Circle.coe_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [h1, hinv, AnalyticTestFn.invExt_of_ne hne]

/- The two normalisations in the bridge are recorded pointwise.  `hfourier` is the
   additive-circle character at period `2π`; `hexp` is the integer-power identity that
   accounts for the extra derivative factor in the circle integral. -/
theorem fourierCoef_inv_xRestrictS1_eq (F : AnalyticTestFn) (n : ℤ) :
    (2 * Real.pi * Complex.I : ℂ) * fourierCoef (inv (xRestrictS1 F)) n =
      ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-(n + 1)) := by
  rw [fourierCoef,
    fourierCoeff_eq_intervalIntegral
      (T := 2 * Real.pi) (toAddCircle (inv (xRestrictS1 F))) n 0]
  simp only [zero_add, Complex.real_smul, smul_eq_mul]
  calc
    (2 * Real.pi * Complex.I : ℂ) *
        ((↑(1 / (2 * Real.pi)) : ℂ) *
          ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
            fourier (-n) (θ : AddCircle (2 * Real.pi)) *
              toAddCircle (inv (xRestrictS1 F)) (θ : AddCircle (2 * Real.pi))) =
      Complex.I *
        ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          fourier (-n) (θ : AddCircle (2 * Real.pi)) *
            toAddCircle (inv (xRestrictS1 F)) (θ : AddCircle (2 * Real.pi)) := by
      rw [← mul_assoc]
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero] <;> ring
    _ = ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          Complex.I *
            (fourier (-n) (θ : AddCircle (2 * Real.pi)) *
              toAddCircle (inv (xRestrictS1 F)) (θ : AddCircle (2 * Real.pi))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
          (circleMap 0 1 θ * Complex.I) *
            (F.invExt (circleMap 0 1 θ) *
              circleMap 0 1 θ ^ (-(n + 1))) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only
      have hfourier :
          fourier (-n) (θ : AddCircle (2 * Real.pi)) =
            Complex.exp (((-n : ℤ) : ℂ) * ((θ : ℂ) * Complex.I)) := by
        rw [fourier_coe_apply]
        congr 1
        field_simp [Real.pi_ne_zero]
        push_cast
        ring
      have hcircle : circleMap 0 1 θ = (Circle.exp θ : ℂ) := by
        rw [circleMap_zero, Circle.coe_exp]
        simp
      have hexp :
          Complex.exp (((-n : ℤ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            Complex.exp ((θ : ℂ) * Complex.I) *
              (Complex.exp ((θ : ℂ) * Complex.I)) ^ (-(n + 1)) := by
        rw [← Complex.exp_int_mul ((θ : ℂ) * Complex.I) (-(n + 1))]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hfourier, toAddCircle_coe, toAngle_inv_xRestrictS1, hcircle, hexp, ← Circle.coe_exp θ]
      ring
    _ = ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-(n + 1)) := by
      rw [circleIntegral]
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [deriv_circleMap, smul_eq_mul]

/- The non-positive exponent in the negative-mode case is a natural power.  We package
   that conversion separately so that the holomorphic function supplied to Cauchy–Goursat
   is visibly a product of the given extension and a monomial. -/
private theorem fourierCoef_inv_xRestrictS1_eq_zero_of_neg
    (F : AnalyticTestFn) (n : ℤ) (hn : n < 0) :
    fourierCoef (inv (xRestrictS1 F)) n = 0 := by
  have hnonneg : 0 ≤ -(n + 1) := by omega
  let k : ℕ := (-(n + 1)).toNat
  have hk : (k : ℤ) = -(n + 1) := by
    change ((-(n + 1)).toNat : ℤ) = -(n + 1)
    exact Int.toNat_of_nonneg hnonneg
  have hpow :
      (fun z : ℂ => F.invExt z * z ^ (-(n + 1))) =
        (fun z : ℂ => F.invExt z * z ^ k) := by
    funext z
    rw [← hk, zpow_natCast]
  have hmonomial :
      DiffContOnCl ℂ (fun z : ℂ => z ^ k) (Metric.ball (0 : ℂ) 1) := by
    refine ⟨differentiableOn_pow k, ?_⟩
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact continuousOn_pow k
  have hprod :
      DiffContOnCl ℂ (fun z : ℂ => F.invExt z * z ^ k)
        (Metric.ball (0 : ℂ) 1) := by
    refine ⟨?_, ?_⟩
    · exact F.diffContOnCl_invExt.differentiableOn.mul hmonomial.differentiableOn
    · exact F.diffContOnCl_invExt.continuousOn.mul hmonomial.continuousOn
  have hcirclezero :
      (∮ z in C((0 : ℂ), 1), F.invExt z * z ^ k) = 0 :=
    hprod.circleIntegral_eq_zero (by positivity)
  have hzero :
      (2 * Real.pi * Complex.I : ℂ) *
          fourierCoef (inv (xRestrictS1 F)) n = 0 := by
    calc
      (2 * Real.pi * Complex.I : ℂ) *
          fourierCoef (inv (xRestrictS1 F)) n =
          ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-(n + 1)) :=
        fourierCoef_inv_xRestrictS1_eq F n
      _ = ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ k := by rw [hpow]
      _ = 0 := hcirclezero
  exact (mul_eq_zero.mp hzero).resolve_left (by simp [Real.pi_ne_zero])

/- The zero mode cannot be obtained from Cauchy–Goursat: its integrand has a simple
   pole at the origin.  The Cauchy integral formula evaluates that pole instead, and
   `F.invExt 0 = 0` supplies the required vanishing. -/
private theorem fourierCoef_inv_xRestrictS1_eq_zero_of_zero (F : AnalyticTestFn) :
    fourierCoef (inv (xRestrictS1 F)) 0 = 0 := by
  have hc : ContinuousOn F.invExt (Metric.closedBall (0 : ℂ) 1) := by
    rw [← closure_ball (0 : ℂ) one_ne_zero]
    exact F.diffContOnCl_invExt.continuousOn
  have hd :
      ∀ x ∈ Metric.ball (0 : ℂ) 1 \ (∅ : Set ℂ),
        DifferentiableAt ℂ F.invExt x := by
    intro x hx
    exact F.diffContOnCl_invExt.differentiableAt Metric.isOpen_ball hx.1
  have hcauchy :=
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (R := (1 : ℝ)) (c := (0 : ℂ)) (w := (0 : ℂ)) (f := F.invExt)
      (s := (∅ : Set ℂ)) Set.countable_empty (by simpa [Metric.mem_ball]) hc hd
  have hF0 : F.invExt (0 : ℂ) = 0 := by
    simp [AnalyticTestFn.invExt]
  have hcauchy0 :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C((0 : ℂ), 1), (z - 0)⁻¹ • F.invExt z) = 0 := by
    simpa [hF0] using hcauchy
  have hkernel :
      (∮ z in C((0 : ℂ), 1), (z - 0)⁻¹ • F.invExt z) =
        ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-1 : ℤ) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    simp [sub_zero, zpow_neg_one, mul_comm]
  rw [hkernel] at hcauchy0
  have hcauchy1 :
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          (∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-1 : ℤ)) = 0 := by
    simpa only [smul_eq_mul] using hcauchy0
  have hscalar : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hI :
      (∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-1 : ℤ)) = 0 :=
    (mul_eq_zero.mp hcauchy1).resolve_left (inv_ne_zero hscalar)
  have hzero :
      (2 * Real.pi * Complex.I : ℂ) *
          fourierCoef (inv (xRestrictS1 F)) 0 = 0 := by
    calc
      (2 * Real.pi * Complex.I : ℂ) *
          fourierCoef (inv (xRestrictS1 F)) 0 =
          ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-(0 + 1)) :=
        fourierCoef_inv_xRestrictS1_eq F 0
      _ = ∮ z in C((0 : ℂ), 1), F.invExt z * z ^ (-1 : ℤ) := by norm_num
      _ = 0 := hI
  exact (mul_eq_zero.mp hzero).resolve_left hscalar

theorem fourierCoef_inv_xRestrictS1_eq_zero_of_le_zero (F : AnalyticTestFn) (n : ℤ)
    (hn : n ≤ 0) : fourierCoef (inv (xRestrictS1 F)) n = 0 := by
  rcases hn.lt_or_eq with h | h
  · exact fourierCoef_inv_xRestrictS1_eq_zero_of_neg F n h
  · subst n
    exact fourierCoef_inv_xRestrictS1_eq_zero_of_zero F

/-- [T26], the (W3) vacuum-annihilation bridge used in the proof of Lemma 3.7: `F ∈ 𝓧`
supplies exactly the `n ≤ 0` Fourier-vanishing hypothesis `smear_vac_eq_zero_of_fourierCoef_eq_zero'`
(#26) needs, via `fourierCoef_inv_xRestrictS1_eq_zero_of_le_zero` above. -/
theorem WightmanData.w3_vacuum_annihilation {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT) (φ : 𝓕) (F : AnalyticTestFn) :
    W.smear φ (inv (xRestrictS1 F)) W.vac = 0 :=
  W.smear_vac_eq_zero_of_fourierCoef_eq_zero' hW φ (inv (xRestrictS1 F))
    (fun n hn => fourierCoef_inv_xRestrictS1_eq_zero_of_le_zero F n hn)

/-- [T26], the (W3) vacuum-annihilation bridge. Issue #9 discharges `MobiusCPT.Contract`'s
`theorem_wanted w3_vacuum_annihilation`, byte-identical statement text. -/
theorem WightmanBundle.w3_vacuum_annihilation (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (φ : W.𝓕) (F : AnalyticTestFn) :
    W.data.smear φ (inv (xRestrictS1 F)) W.data.vac = 0 :=
  WightmanData.w3_vacuum_annihilation W.data h φ F

end
end MobiusCPT
