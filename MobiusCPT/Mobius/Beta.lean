import MobiusCPT.Mobius.Factor
import MobiusCPT.TestFunctions.Monomial
import MobiusCPT.TestFunctions.WightmanInstance
import MobiusCPT.Wightman.Mobius

/-!
# The conformal action on test functions

This file constructs the conformal action `β_d` of `SU(1,1)` on smooth test functions,
descends it to `Möb = PSU(1,1)`, and supplies the concrete `MobiusAction` instance used by the
Wightman interface.
-/

namespace MobiusCPT

open scoped ComplexConjugate ContDiff Manifold Topology

attribute [local instance] finrank_real_complex_fact'

noncomputable section

/-- [T26], §1: the Möbius action on `S¹` is smooth. -/
theorem contMDiff_smul (g : SU11) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => g • z) := by
  apply ContMDiff.codRestrict_sphere
  · intro z
    have hnum :
        ContDiff ℝ ∞ (fun w : ℂ => g.α * w + g.β) := by
      simpa only [smul_eq_mul] using
        ((contDiff_const_smul (𝕜 := ℝ) (F := ℂ) g.α).add
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => g.β)))
    have hden :
        ContDiff ℝ ∞ (fun w : ℂ => conj g.β * w + conj g.α) := by
      simpa only [smul_eq_mul] using
        ((contDiff_const_smul (𝕜 := ℝ) (F := ℂ) (conj g.β)).add
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => conj g.α)))
    have hj : conj g.β * (z : ℂ) + conj g.α ≠ 0 := by
      simpa only [j] using j_ne_zero g z
    have hquot :
        ContDiffAt ℝ ∞
          (fun w : ℂ => (g.α * w + g.β) / (conj g.β * w + conj g.α))
          (z : ℂ) := by
      simp only [div_eq_mul_inv]
      exact hnum.contDiffAt.mul (hden.contDiffAt.inv hj)
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((fun w : ℂ => (g.α * w + g.β) / (conj g.β * w + conj g.α)) ∘
        ((↑) : Circle → ℂ)) z
    exact hquot.comp_contMDiffAt
      (contMDiff_coe_sphere :
        ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ))).contMDiffAt

/-- [T26], Definition 2.4, eq. (2.2):
`(β_d(γ)f)(z) = X_γ(γ⁻¹ z)^{d-1} f(γ⁻¹ z)`. -/
def betaFun (d : ℕ) (g : SU11) (f : TestFn) : Circle → ℂ :=
  fun z => ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z)

/-- [T26], Definition 2.4, eq. (2.2): the conformal scalar can be computed from the
inverse automorphy factor. -/
theorem betaFun_eq (d : ℕ) (g : SU11) (f : TestFn) (z : Circle) :
    betaFun d g f z =
      ((Complex.normSq (j g⁻¹ z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z) := by
  rw [betaFun, X_inv_smul]

/-- [T26], Definition 2.4: the pointwise formula defining `β_d(γ)f` is smooth. -/
theorem contMDiff_betaFun (d : ℕ) (g : SU11) (f : TestFn) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (betaFun d g f) := by
  rw [show betaFun d g f = fun z : Circle =>
      ((Complex.normSq (j g⁻¹ z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z) by
    funext z
    exact betaFun_eq d g f z]
  intro z
  let q : ℂ → ℂ := fun w => conj (g⁻¹).β * w + conj (g⁻¹).α
  have hq : ContDiff ℝ ∞ q := by
    dsimp only [q]
    simpa only [smul_eq_mul] using
      ((contDiff_const_smul (𝕜 := ℝ) (F := ℂ) (conj (g⁻¹).β)).add
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => conj (g⁻¹).α)))
  have hre : ContDiff ℝ ∞ (fun w : ℂ => (q w).re) :=
    Complex.reCLM.contDiff.comp hq
  have him : ContDiff ℝ ∞ (fun w : ℂ => (q w).im) :=
    Complex.imCLM.contDiff.comp hq
  have hnorm : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (q w)) := by
    simpa only [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)
  have hq_ne : q (z : ℂ) ≠ 0 := by
    simpa only [q, j] using j_ne_zero g⁻¹ z
  have hnorm_ne : Complex.normSq (q (z : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr hq_ne).ne'
  have hzpow :
      ContDiffAt ℝ ∞
        (fun w : ℂ => Complex.normSq (q w) ^ ((d : ℤ) - 1)) (z : ℂ) := by
    have hrewrite :
        ContDiffAt ℝ ∞
          (fun w : ℂ =>
            Complex.normSq (q w) ^ d * (Complex.normSq (q w))⁻¹) (z : ℂ) :=
      (hnorm.contDiffAt.pow d).mul (hnorm.contDiffAt.inv hnorm_ne)
    refine hrewrite.congr_of_eventuallyEq ?_
    filter_upwards [hnorm.continuous.continuousAt.eventually_ne hnorm_ne] with w hw
    exact zpow_sub_one₀ hw (d : ℤ)
  have hzpow_circle :
      ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
        (fun w : Circle => Complex.normSq (j g⁻¹ w) ^ ((d : ℤ) - 1)) z := by
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      ((fun w : ℂ => Complex.normSq (q w) ^ ((d : ℤ) - 1)) ∘
        ((↑) : Circle → ℂ)) z
    exact hzpow.comp_contMDiffAt
      (contMDiff_coe_sphere :
        ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ))).contMDiffAt
  have hscalar :
      ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
        (fun w : Circle =>
          ((Complex.normSq (j g⁻¹ w) ^ ((d : ℤ) - 1) : ℝ) : ℂ)) z := by
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (Complex.ofRealCLM ∘
        (fun w : Circle => Complex.normSq (j g⁻¹ w) ^ ((d : ℤ) - 1))) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp_contMDiffAt hzpow_circle
  have hf :
      ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => f (g⁻¹ • w)) := by
    change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((f : Circle → ℂ) ∘ (fun w : Circle => g⁻¹ • w))
    exact (ContMDiffMap.contMDiff f).comp (contMDiff_smul g⁻¹)
  have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact hmul.contDiffAt.comp_contMDiffAt
    (hscalar.prodMk_space hf.contMDiffAt)

/-- [T26], Definition 2.4: `β_d(γ)` as a linear endomorphism of `C^∞(S¹)`. -/
def beta (d : ℕ) (g : SU11) : TestFn →ₗ[ℂ] TestFn where
  toFun f := ⟨betaFun d g f, contMDiff_betaFun d g f⟩
  map_add' f h := by
    apply TestFn.ext
    intro z
    change
      ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) *
          (f (g⁻¹ • z) + h (g⁻¹ • z)) =
        ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z) +
          ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * h (g⁻¹ • z)
    ring
  map_smul' c f := by
    apply TestFn.ext
    intro z
    change
      ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * (c * f (g⁻¹ • z)) =
        c * (((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z))
    ring

/-- [T26], Definition 2.4, eq. (2.2): evaluation of the bundled conformal action. -/
@[simp]
theorem beta_apply (d : ℕ) (g : SU11) (f : TestFn) (z : Circle) :
    beta d g f z = ((X g (g⁻¹ • z) ^ ((d : ℤ) - 1) : ℝ) : ℂ) * f (g⁻¹ • z) :=
  rfl

/-- [T26], Definition 2.4: the identity element acts trivially under `β_d`. -/
theorem beta_one (d : ℕ) : beta d (1 : SU11) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply TestFn.ext
  intro z
  simp

private theorem real_mul_zpow_sub_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (d : ℕ) :
    (a * b) ^ ((d : ℤ) - 1) = a ^ ((d : ℤ) - 1) * b ^ ((d : ℤ) - 1) := by
  rw [zpow_sub_one₀ (mul_ne_zero ha hb), zpow_sub_one₀ ha, zpow_sub_one₀ hb]
  simp only [zpow_natCast, mul_pow, mul_inv_rev]
  ring

/-- [T26], Definition 2.4: the conformal action respects multiplication in `SU(1,1)`. -/
theorem beta_mul (d : ℕ) (g h : SU11) :
    beta d (g * h) = (beta d g).comp (beta d h) := by
  apply LinearMap.ext
  intro f
  apply TestFn.ext
  intro z
  simp only [beta_apply, LinearMap.comp_apply]
  have hw : (g * h)⁻¹ • z = h⁻¹ • (g⁻¹ • z) := by
    simp [mul_inv_rev, mul_smul]
  have hhw : h • ((g * h)⁻¹ • z) = g⁻¹ • z := by
    simp [mul_inv_rev, mul_smul]
  rw [X_mul, hhw, hw]
  rw [real_mul_zpow_sub_one
    (X g (g⁻¹ • z)) (X h (h⁻¹ • (g⁻¹ • z)))
    (X_pos g (g⁻¹ • z)).ne' (X_pos h (h⁻¹ • (g⁻¹ • z))).ne' d]
  simp only [Complex.ofReal_mul, mul_assoc]

private theorem neg_inv (g : SU11) :
    (SU11.neg g)⁻¹ = SU11.neg (g⁻¹) := by
  apply SU11.ext <;> simp

/-- [T26], Definition 2.4: simultaneous sign change does not change `β_d`. -/
theorem beta_neg (d : ℕ) (g : SU11) : beta d (SU11.neg g) = beta d g := by
  apply LinearMap.ext
  intro f
  apply TestFn.ext
  intro z
  simp [neg_inv]

namespace Mob

/-- [T26], Definition 2.4: `β_d` descends to `Möb = PSU(1,1)`. -/
def beta (d : ℕ) : Mob → (TestFn →ₗ[ℂ] TestFn) :=
  fun γ =>
    Quotient.liftOn' (show SU11 ⧸ signSubgroup from γ) (MobiusCPT.beta d) (by
      intro g h hrel
      have hmk : mk g = mk h := by
        change QuotientGroup.mk g = QuotientGroup.mk h
        exact Quotient.sound' hrel
      rcases mk_eq_mk.mp hmk with rfl | rfl
      · rfl
      · exact (MobiusCPT.beta_neg d g).symm)

/-- [T26], Definition 2.4: a representative computes the descended conformal action. -/
@[simp]
theorem beta_mk (d : ℕ) (g : SU11) : beta d (mk g) = MobiusCPT.beta d g :=
  rfl

end Mob

/-- [T26], Definitions 2.4-2.5: the Möbius group `Möb = PSU(1,1)` acts on `C^∞(S¹)` by the
conformal action `β_d`; this is the instance Issue #4's interface was stated against. -/
noncomputable instance : MobiusAction Mob TestFn where
  rot := Mob.rot
  boostElt := Mob.boost
  beta := Mob.beta
  rot_zero := Mob.rot_zero
  rot_add := Mob.rot_add
  boostElt_zero := Mob.boost_zero
  boostElt_add := Mob.boost_add
  beta_one := by
    intro d
    rw [← Mob.mk_one, Mob.beta_mk]
    exact MobiusCPT.beta_one d
  beta_mul := by
    intro d γ δ
    obtain ⟨g, rfl⟩ := Mob.mk_surjective γ
    obtain ⟨h, rfl⟩ := Mob.mk_surjective δ
    simpa only [← Mob.mk_mul, Mob.beta_mk] using MobiusCPT.beta_mul d g h

private theorem rotMat_inv (theta : ℝ) :
    (rotMat theta)⁻¹ = rotMat (-theta) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rotMat_add, add_neg_cancel, rotMat_zero]

/-- [T26], Definition 2.4 and the Issue #2 source gate:
`β_d(r_θ) z^n = e^{-inθ} z^n`. -/
theorem beta_rotMat_monomial (d : ℕ) (theta : ℝ) (n : ℤ) :
    beta d (rotMat theta) (monomial n) =
      Complex.exp (-(n : ℂ) * (theta : ℂ) * Complex.I) • monomial n := by
  apply toAngle_injective
  funext phi
  change
    beta d (rotMat theta) (monomial n) (Circle.exp phi) =
      Complex.exp (-(n : ℂ) * (theta : ℂ) * Complex.I) *
        monomial n (Circle.exp phi)
  rw [beta_apply, X_rotMat]
  simp only [one_zpow, Complex.ofReal_one, one_mul, rotMat_inv, rotMat_smul]
  rw [← Circle.exp_add]
  change
    toAngle (monomial n) (-theta + phi) =
      Complex.exp (-(n : ℂ) * (theta : ℂ) * Complex.I) * toAngle (monomial n) phi
  rw [toAngle_monomial, toAngle_monomial, ← Complex.exp_add]
  congr 1
  push_cast
  ring

namespace Mob

/-- [T26], Definition 2.4 and the Issue #2 source gate: the descended rotation action on an
integer monomial is multiplication by `e^{-inθ}`. -/
theorem beta_rot_monomial (d : ℕ) (theta : ℝ) (n : ℤ) :
    beta d (rot theta) (monomial n) =
      Complex.exp (-(n : ℂ) * (theta : ℂ) * Complex.I) • monomial n := by
  rw [rot, beta_mk]
  exact beta_rotMat_monomial d theta n

end Mob

/-- [T26], eq. (3.4)-(3.5):
`(β_d(v_t)f)(z) = (cosh t + Re(z) sinh t)^{d-1} f(v_{-t} · z)`. -/
theorem beta_boostMat_apply (d : ℕ) (t : ℝ) (f : TestFn) (z : Circle) :
    beta d (boostMat t) f z =
      (((Real.cosh t + (z : ℂ).re * Real.sinh t) ^ ((d : ℤ) - 1) : ℝ) : ℂ) *
        f (boostMat (-t) • z) := by
  rw [beta_apply, X_boostMat_inv_smul, boostMat_inv]

end

end MobiusCPT
