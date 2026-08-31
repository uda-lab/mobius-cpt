import MobiusCPT.Analysis.Strip
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# A maximum principle for Gaussian-weighted functions on a strip

This file packages the Phragmén–Lindelöf estimate needed later in the PCT argument.  It is
independent of the Wightman and Möbius layers.
-/

noncomputable section

open Asymptotics Complex Filter Set
open scoped Topology

namespace MobiusCPT

private theorem sq_re (z : ℂ) : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
  rw [pow_two, Complex.mul_re]
  ring

private theorem linear_abs_sub_sq_le (a x : ℝ) :
    a * |x| - x ^ 2 ≤ a ^ 2 / 4 := by
  nlinarith [sq_nonneg (2 * |x| - a), sq_abs x]

private theorem I_mul_pi_im : (Complex.I * (Real.pi : ℂ)).im = Real.pi := by
  simp [Complex.mul_im]

/-- A Gaussian-weighted Phragmén–Lindelöf estimate on the strip of height `π`. -/
theorem strip_max_principle {h : ℂ → ℂ}
    (hd : DiffContOnCl ℂ h (Complex.im ⁻¹' Set.Ioo 0 Real.pi))
    (hgrowth : ∃ A a : ℝ, ∀ τ ∈ strip (Complex.I * Real.pi),
      ‖h τ‖ ≤ A * Real.exp (a * |τ.re|))
    {k₁ k₂ X : ℝ} (hX : 0 ≤ X)
    (hlower : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ k₁ * Real.exp (k₂ * |t|) * X)
    (hupper : ∀ t : ℝ,
      ‖h ((t : ℂ) + Complex.I * Real.pi)‖ ≤ k₁ * Real.exp (k₂ * |t|) * X) :
    ∀ τ ∈ strip (Complex.I * Real.pi),
      ‖h τ‖ ≤
        (Real.exp (Real.pi ^ 2) * k₁ * Real.exp (k₂ ^ 2 / 4)) *
          Real.exp (τ.re ^ 2) * X := by
  let g : ℂ → ℂ := fun z ↦ Complex.exp (-(z ^ 2)) * h z
  let C : ℝ := Real.exp (Real.pi ^ 2) * k₁ * Real.exp (k₂ ^ 2 / 4) * X

  have hd_g : DiffContOnCl ℂ g (Complex.im ⁻¹' Set.Ioo 0 Real.pi) := by
    have he : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (-(z ^ 2))) :=
      (differentiable_id.pow 2).neg.cexp
    simpa only [g, smul_eq_mul] using he.diffContOnCl.smul hd

  have hkX : 0 ≤ k₁ * X := by
    have h0 := (norm_nonneg (h (0 : ℂ))).trans (hlower 0)
    simpa using h0

  have hB :
      ∃ c < Real.pi / (Real.pi - 0), ∃ B,
        g =O[Filter.comap (_root_.abs ∘ Complex.re) Filter.atTop ⊓
            Filter.principal (Complex.im ⁻¹' Set.Ioo 0 Real.pi)]
          fun z ↦ Real.exp (B * Real.exp (c * |z.re|)) := by
    rcases hgrowth with ⟨A, a, hgrowth⟩
    have hA : 0 ≤ A := by
      have h0 := (norm_nonneg (h (0 : ℂ))).trans
        (hgrowth (0 : ℂ) (ofReal_mem_strip (Complex.I * Real.pi) 0))
      simpa using h0
    refine ⟨1 / 2, ?_, 0, ?_⟩
    · rw [sub_zero, div_self Real.pi_ne_zero]
      norm_num
    · refine IsBigO.of_bound
        (Real.exp (Real.pi ^ 2) * A * Real.exp (a ^ 2 / 4)) ?_
      refine eventually_inf_principal.2 <| Eventually.of_forall fun z hz ↦ ?_
      change 0 < z.im ∧ z.im < Real.pi at hz
      have hzstrip : z ∈ strip (Complex.I * Real.pi) := by
        rw [mem_strip, I_mul_pi_im, min_eq_left Real.pi_pos.le,
          max_eq_right Real.pi_pos.le]
        exact ⟨hz.1.le, hz.2.le⟩
      have him_sq : z.im ^ 2 ≤ Real.pi ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hz.2.le)
          (add_nonneg Real.pi_pos.le hz.1.le)]
      have hquad : a * |z.re| - z.re ^ 2 ≤ a ^ 2 / 4 :=
        linear_abs_sub_sq_le a z.re
      have hnorm_exp :
          ‖Complex.exp (-(z ^ 2))‖ =
            Real.exp (z.im ^ 2 - z.re ^ 2) := by
        rw [Complex.norm_exp, Complex.neg_re, sq_re]
        congr 1
        ring
      simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
      calc
        ‖g z‖ = Real.exp (z.im ^ 2 - z.re ^ 2) * ‖h z‖ := by
          simp only [g]; rw [Complex.norm_mul, hnorm_exp]
        _ ≤ Real.exp (z.im ^ 2 - z.re ^ 2) *
              (A * Real.exp (a * |z.re|)) :=
          mul_le_mul_of_nonneg_left (hgrowth z hzstrip) (Real.exp_nonneg _)
        _ = A * Real.exp (z.im ^ 2 + (a * |z.re| - z.re ^ 2)) := by
          calc
            Real.exp (z.im ^ 2 - z.re ^ 2) *
                  (A * Real.exp (a * |z.re|)) =
                A * (Real.exp (z.im ^ 2 - z.re ^ 2) *
                  Real.exp (a * |z.re|)) := by ring
            _ = A * Real.exp ((z.im ^ 2 - z.re ^ 2) + a * |z.re|) := by
              rw [← Real.exp_add]
            _ = A * Real.exp (z.im ^ 2 + (a * |z.re| - z.re ^ 2)) := by
              congr 2
              ring
        _ ≤ A * Real.exp (Real.pi ^ 2 + a ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (add_le_add him_sq hquad)) hA
        _ = Real.exp (Real.pi ^ 2) * A * Real.exp (a ^ 2 / 4) := by
          rw [Real.exp_add]
          ring

  have hle_lower : ∀ z : ℂ, z.im = 0 → ‖g z‖ ≤ C := by
    intro z hz
    have hz_eq : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [hz_eq]
    have hnorm_exp :
        ‖Complex.exp (-((z.re : ℂ) ^ 2))‖ =
          Real.exp (-(z.re ^ 2)) := by
      rw [Complex.norm_exp, Complex.neg_re, sq_re]
      simp
    have hquad : k₂ * |z.re| - z.re ^ 2 ≤ k₂ ^ 2 / 4 :=
      linear_abs_sub_sq_le k₂ z.re
    have hnonneg : 0 ≤ (k₁ * X) * Real.exp (k₂ ^ 2 / 4) :=
      mul_nonneg hkX (Real.exp_nonneg _)
    calc
      ‖g (z.re : ℂ)‖ = Real.exp (-(z.re ^ 2)) * ‖h (z.re : ℂ)‖ := by
        simp only [g]; rw [Complex.norm_mul, hnorm_exp]
      _ ≤ Real.exp (-(z.re ^ 2)) *
            (k₁ * Real.exp (k₂ * |z.re|) * X) :=
        mul_le_mul_of_nonneg_left (hlower z.re) (Real.exp_nonneg _)
      _ = (k₁ * X) * Real.exp (k₂ * |z.re| - z.re ^ 2) := by
        calc
          Real.exp (-(z.re ^ 2)) *
                (k₁ * Real.exp (k₂ * |z.re|) * X) =
              (k₁ * X) *
                (Real.exp (-(z.re ^ 2)) * Real.exp (k₂ * |z.re|)) := by ring
          _ = (k₁ * X) * Real.exp (k₂ * |z.re| - z.re ^ 2) := by
            rw [← Real.exp_add]
            congr 2
            ring
      _ ≤ (k₁ * X) * Real.exp (k₂ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) hkX
      _ ≤ Real.exp (Real.pi ^ 2) *
            ((k₁ * X) * Real.exp (k₂ ^ 2 / 4)) := by
        calc
          (k₁ * X) * Real.exp (k₂ ^ 2 / 4) =
              1 * ((k₁ * X) * Real.exp (k₂ ^ 2 / 4)) := by ring
          _ ≤ Real.exp (Real.pi ^ 2) *
                ((k₁ * X) * Real.exp (k₂ ^ 2 / 4)) :=
            mul_le_mul_of_nonneg_right (Real.one_le_exp (sq_nonneg Real.pi)) hnonneg
      _ = C := by
        dsimp [C]
        ring

  have hle_upper : ∀ z : ℂ, z.im = Real.pi → ‖g z‖ ≤ C := by
    intro z hz
    have hz_eq : z = (z.re : ℂ) + Complex.I * Real.pi := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]
    rw [hz_eq]
    have hnorm_exp :
        ‖Complex.exp (-(((z.re : ℂ) + Complex.I * Real.pi) ^ 2))‖ =
          Real.exp (Real.pi ^ 2 - z.re ^ 2) := by
      rw [Complex.norm_exp, Complex.neg_re, sq_re]
      congr 1
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    have hquad : k₂ * |z.re| - z.re ^ 2 ≤ k₂ ^ 2 / 4 :=
      linear_abs_sub_sq_le k₂ z.re
    have hcoeff : 0 ≤ Real.exp (Real.pi ^ 2) * (k₁ * X) :=
      mul_nonneg (Real.exp_nonneg _) hkX
    calc
      ‖g ((z.re : ℂ) + Complex.I * Real.pi)‖ =
          Real.exp (Real.pi ^ 2 - z.re ^ 2) *
            ‖h ((z.re : ℂ) + Complex.I * Real.pi)‖ := by
        simp only [g]; rw [Complex.norm_mul, hnorm_exp]
      _ ≤ Real.exp (Real.pi ^ 2 - z.re ^ 2) *
            (k₁ * Real.exp (k₂ * |z.re|) * X) :=
        mul_le_mul_of_nonneg_left (hupper z.re) (Real.exp_nonneg _)
      _ = (Real.exp (Real.pi ^ 2) * (k₁ * X)) *
            Real.exp (k₂ * |z.re| - z.re ^ 2) := by
        calc
          Real.exp (Real.pi ^ 2 - z.re ^ 2) *
                (k₁ * Real.exp (k₂ * |z.re|) * X) =
              (k₁ * X) *
                (Real.exp (Real.pi ^ 2 - z.re ^ 2) *
                  Real.exp (k₂ * |z.re|)) := by ring
          _ = (k₁ * X) *
                Real.exp (Real.pi ^ 2 + (k₂ * |z.re| - z.re ^ 2)) := by
            rw [← Real.exp_add]
            congr 2
            ring
          _ = (Real.exp (Real.pi ^ 2) * (k₁ * X)) *
                Real.exp (k₂ * |z.re| - z.re ^ 2) := by
            rw [Real.exp_add]
            ring
      _ ≤ (Real.exp (Real.pi ^ 2) * (k₁ * X)) *
            Real.exp (k₂ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) hcoeff
      _ = C := by
        dsimp [C]
        ring

  intro τ hτ
  rw [mem_strip, I_mul_pi_im, min_eq_left Real.pi_pos.le,
    max_eq_right Real.pi_pos.le] at hτ
  have hg_le : ‖g τ‖ ≤ C :=
    PhragmenLindelof.horizontal_strip (a := 0) (b := Real.pi) (C := C)
      (z := τ) hd_g hB hle_lower hle_upper hτ.1 hτ.2
  have hre_sq : (τ ^ 2).re ≤ τ.re ^ 2 := by
    rw [sq_re]
    nlinarith [sq_nonneg τ.im]
  have hrecover : h τ = Complex.exp (τ ^ 2) * g τ := by
    symm
    calc
      Complex.exp (τ ^ 2) * g τ =
          (Complex.exp (τ ^ 2) * Complex.exp (-(τ ^ 2))) * h τ := by
        simp only [g]; rw [mul_assoc]
      _ = Complex.exp (τ ^ 2 + -(τ ^ 2)) * h τ := by
        rw [Complex.exp_add]
      _ = h τ := by simp
  calc
    ‖h τ‖ = Real.exp ((τ ^ 2).re) * ‖g τ‖ := by
      rw [hrecover, Complex.norm_mul, Complex.norm_exp]
    _ ≤ Real.exp (τ.re ^ 2) * C :=
      mul_le_mul (Real.exp_le_exp.mpr hre_sq) hg_le
        (norm_nonneg (g τ)) (Real.exp_nonneg _)
    _ = (Real.exp (Real.pi ^ 2) * k₁ * Real.exp (k₂ ^ 2 / 4)) *
          Real.exp (τ.re ^ 2) * X := by
      dsimp [C]
      ring

end MobiusCPT
