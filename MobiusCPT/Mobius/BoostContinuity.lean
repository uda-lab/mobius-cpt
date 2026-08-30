import MobiusCPT.Analysis.ParamCurve
import MobiusCPT.Mobius.Beta
import MobiusCPT.TestFunctions.Analytic

/-!
# Continuity of the boost and rotation orbits on test functions

[CRTT25], Lemma 2.10(i): for every `d : ℕ` and `f : TestFn`, the maps `t ↦ β_d(v_t) f` and
`θ ↦ β_d(r_θ) f` are continuous into the Fréchet topology of `C^∞(S¹)`. The route (orchestrator
ruling on Issue #38, 2026-08-30) is joint smoothness in `(t, θ)` of the pointwise formula for
`β_d(v_t) f` (resp. `β_d(r_θ) f`) evaluated at `e^{iθ}`, together with `continuous_of_jointlySmooth_periodic`.

The rotation case has no conformal prefactor (`X (rotMat θ) z = 1`), so its joint function is a
translation of the angle picture of `f` and is smooth immediately. The boost case has a strictly
positive prefactor for every `d`, including `d = 0`, and its second factor is smooth because the
negative-boost action on the circle is jointly smooth in `(t, z)`, proved directly from the
fractional-linear formula the way `contMDiff_smul` proves it for a fixed group element.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology Manifold

attribute [local instance] finrank_real_complex_fact'

noncomputable section

/-! ### Rotations -/

/-- [T26], Definition 2.4; the rotation automorphy factor is trivial, so `β_d(r_θ) f` is `f`
rotated, for every `f`, not only monomials. -/
theorem beta_rotMat_apply (d : ℕ) (theta : ℝ) (f : TestFn) (z : Circle) :
    beta d (rotMat theta) f z = f (Circle.exp (-theta) * z) := by
  rw [beta_apply, X_rotMat, one_zpow, Complex.ofReal_one, one_mul, rotMat_inv, rotMat_smul]

namespace Mob

/-- [T26], Definition 2.4; the descended form of `beta_rotMat_apply`, for every `f`. -/
theorem beta_rot_apply (d : ℕ) (theta : ℝ) (f : TestFn) (z : Circle) :
    beta d (rot theta) f z = f (Circle.exp (-theta) * z) := by
  rw [rot, beta_mk]
  exact beta_rotMat_apply d theta f z

end Mob

/-- [CRTT25], Lemma 2.10(i); the joint rotation function is a shift of the angle picture of
`f`, hence jointly smooth. -/
theorem contDiff_betaRotJoint (d : ℕ) (f : TestFn) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Mob.beta d (Mob.rot p.1) f (Circle.exp p.2)) := by
  have heq : (fun p : ℝ × ℝ => Mob.beta d (Mob.rot p.1) f (Circle.exp p.2)) =
      toAngle f ∘ fun p : ℝ × ℝ => p.2 - p.1 := by
    funext p
    rw [Function.comp_apply, Mob.beta_rot_apply]
    congr 1
    rw [← Circle.exp_add]
    congr 1
    ring
  rw [heq]
  exact (contDiff_toAngle f).comp (contDiff_snd.sub contDiff_fst)

/-- [CRTT25], Lemma 2.10(i); rotations act continuously on test functions. -/
theorem continuous_beta_rot (d : ℕ) (f : TestFn) :
    Continuous fun theta : ℝ => Mob.beta d (Mob.rot theta) f := by
  apply continuous_of_jointlySmooth_periodic (contDiff_betaRotJoint d f)
  intro t θ
  rfl

/-! ### Boosts -/

/-- The negated boost matrix has real, hence self-conjugate, coordinates. -/
theorem boostMat_neg_alpha (t : ℝ) : (boostMat (-t)).α = (Real.cosh (t / 2) : ℂ) := by
  rw [boostMat_alpha, neg_div, Real.cosh_neg]

theorem boostMat_neg_beta (t : ℝ) : (boostMat (-t)).β = (Real.sinh (t / 2) : ℂ) := by
  rw [boostMat_beta, neg_div, Real.sinh_neg, Complex.ofReal_neg, neg_neg]

/-- The automorphy factor of a negated boost, in real coordinates. -/
theorem j_boostMat_neg_eq (t : ℝ) (z : Circle) :
    j (boostMat (-t)) z = (Real.sinh (t / 2) : ℂ) * (z : ℂ) + (Real.cosh (t / 2) : ℂ) := by
  rw [j, boostMat_neg_alpha, boostMat_neg_beta, Complex.conj_ofReal, Complex.conj_ofReal]

/-- [T26], §3; joint smoothness, in `(t, θ) : ℝ × ℝ`, of the negative-boost action on
`Circle.exp θ`. Proved directly from the fractional-linear formula, the way `contMDiff_smul`
proves it for a single fixed group element: here the coefficients `cosh(t/2)`, `sinh(t/2)` vary
smoothly with `t`, `Circle.exp θ` is smooth in `θ`, and the automorphy factor is nonvanishing
for every `t` by `j_ne_zero`. Working directly over `ℝ × ℝ` (rather than the `ℝ × Circle`
product manifold, composed afterwards) avoids an expensive `Function.comp` defeq check through
the product-manifold instances. -/
theorem contMDiff_boostAngleNegSmul :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 1) ∞
      (fun p : ℝ × ℝ => boostMat (-p.1) • Circle.exp p.2) := by
  have hα : ContDiff ℝ ∞ (fun t : ℝ => (Real.cosh (t / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cosh.comp (contDiff_id.div_const 2))
  have hβ : ContDiff ℝ ∞ (fun t : ℝ => (Real.sinh (t / 2) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sinh.comp (contDiff_id.div_const 2))
  have hnum : ContDiff ℝ ∞
      (fun q : ℝ × ℂ => (Real.cosh (q.1 / 2) : ℂ) * q.2 + (Real.sinh (q.1 / 2) : ℂ)) :=
    ((hα.comp contDiff_fst).mul contDiff_snd).add (hβ.comp contDiff_fst)
  have hden : ContDiff ℝ ∞
      (fun q : ℝ × ℂ => (Real.sinh (q.1 / 2) : ℂ) * q.2 + (Real.cosh (q.1 / 2) : ℂ)) :=
    ((hβ.comp contDiff_fst).mul contDiff_snd).add (hα.comp contDiff_fst)
  have hmap : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × ℝ =>
        ((Real.cosh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.sinh (p.1 / 2) : ℂ)) /
          ((Real.sinh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.cosh (p.1 / 2) : ℂ))) := by
    intro p
    have hjeq := j_boostMat_neg_eq p.1 (Circle.exp p.2)
    have hjne : (Real.sinh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.cosh (p.1 / 2) : ℂ)
        ≠ 0 := hjeq ▸ j_ne_zero (boostMat (-p.1)) (Circle.exp p.2)
    have hquot : ContDiffAt ℝ ∞
        (fun q : ℝ × ℂ =>
          ((Real.cosh (q.1 / 2) : ℂ) * q.2 + (Real.sinh (q.1 / 2) : ℂ)) /
            ((Real.sinh (q.1 / 2) : ℂ) * q.2 + (Real.cosh (q.1 / 2) : ℂ)))
        (p.1, (Circle.exp p.2 : ℂ)) := by
      simp only [div_eq_mul_inv]
      exact hnum.contDiffAt.mul (hden.contDiffAt.inv hjne)
    have hcoe : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℂ) ∞
        (fun q : ℝ × ℝ => (q.1, (Circle.exp q.2 : ℂ))) p :=
      contDiff_fst.contMDiff.contMDiffAt.prodMk_space
        (contDiff_circle_map.comp contDiff_snd).contMDiff.contMDiffAt
    exact ContDiffAt.comp_contMDiffAt
      (f := fun q : ℝ × ℝ => (q.1, (Circle.exp q.2 : ℂ))) (x := p) hquot hcoe
  have hmem : ∀ p : ℝ × ℝ,
      ((Real.cosh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.sinh (p.1 / 2) : ℂ)) /
        ((Real.sinh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.cosh (p.1 / 2) : ℂ)) ∈
        Metric.sphere (0 : ℂ) 1 := by
    intro p
    have hval : ((Real.cosh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.sinh (p.1 / 2) : ℂ)) /
        ((Real.sinh (p.1 / 2) : ℂ) * (Circle.exp p.2 : ℂ) + (Real.cosh (p.1 / 2) : ℂ)) =
        ((boostMat (-p.1)).α * (Circle.exp p.2 : ℂ) + (boostMat (-p.1)).β) /
          j (boostMat (-p.1)) (Circle.exp p.2) := by
      rw [boostMat_neg_alpha, boostMat_neg_beta, j_boostMat_neg_eq]
    rw [hval]
    exact (boostMat (-p.1) • Circle.exp p.2).2
  have hgoal : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 1) ∞
      (Set.codRestrict _ (Metric.sphere (0 : ℂ) 1) hmem) :=
    hmap.codRestrict_sphere hmem
  have heqfun : (fun p : ℝ × ℝ => boostMat (-p.1) • Circle.exp p.2) =
      Set.codRestrict _ (Metric.sphere (0 : ℂ) 1) hmem := by
    funext p
    apply Circle.ext
    rw [coe_smul, boostMat_neg_alpha, boostMat_neg_beta, j_boostMat_neg_eq,
      Set.val_codRestrict_apply]
  rw [heqfun]
  exact hgoal

/-- [T26], eq. (3.4)-(3.5); the joint boost function, `(t, θ) ↦ (β_d(v_t) f)(e^{iθ})`, is
smooth for every `d` including `d = 0`. The conformal prefactor `cosh t + Re(z) sinh t` is
strictly positive for every `t, z`, since `cosh t + Re(z) sinh t ≥ cosh t - |sinh t| = e^{-|t|}`
because `|Re z| ≤ 1` on the circle. -/
theorem contDiff_betaBoostJoint (d : ℕ) (f : TestFn) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Mob.beta d (Mob.boost p.1) f (Circle.exp p.2)) := by
  have heq : (fun p : ℝ × ℝ => Mob.beta d (Mob.boost p.1) f (Circle.exp p.2)) =
      fun p : ℝ × ℝ =>
        (((Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) ^ ((d : ℤ) - 1) : ℝ) : ℂ) *
          f (boostMat (-p.1) • Circle.exp p.2) := by
    funext p
    rw [Mob.beta_boost_apply, Mob.boost, Mob.mk_smul]
  rw [heq]
  have hprefactor_pos : ∀ p : ℝ × ℝ,
      0 < Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1 := by
    intro p
    have hre_le : |(Circle.exp p.2 : ℂ).re| ≤ 1 := by
      have hnorm : ‖(Circle.exp p.2 : ℂ)‖ = 1 := Circle.norm_coe _
      calc |(Circle.exp p.2 : ℂ).re| ≤ ‖(Circle.exp p.2 : ℂ)‖ := Complex.abs_re_le_norm _
        _ = 1 := hnorm
    have hbound : Real.cosh p.1 - |Real.sinh p.1| ≤
        Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1 := by
      rcases abs_le.mp hre_le with ⟨hlo, hhi⟩
      rcases le_or_gt 0 (Real.sinh p.1) with hs | hs
      · rw [abs_of_nonneg hs]
        nlinarith [mul_le_mul_of_nonneg_right hhi hs]
      · rw [abs_of_neg hs]
        nlinarith [mul_le_mul_of_nonpos_right hlo hs.le]
    have heq2 : Real.cosh p.1 - |Real.sinh p.1| = Real.exp (-|p.1|) := by
      rcases le_or_gt 0 p.1 with h | h
      · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h)]
        rw [Real.cosh_eq, Real.sinh_eq]
        ring_nf
      · rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr h)]
        rw [Real.cosh_eq, Real.sinh_eq]
        ring_nf
    have hexp_pos : 0 < Real.exp (-|p.1|) := Real.exp_pos _
    linarith [heq2 ▸ hbound]
  have hcircle : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Circle.exp p.2 : Circle) : ℂ)) :=
    contDiff_circle_map.comp contDiff_snd
  have hre : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Circle.exp p.2 : ℂ).re) :=
    Complex.reCLM.contDiff.comp hcircle
  have hcosh : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.cosh p.1) :=
    Real.contDiff_cosh.comp contDiff_fst
  have hsinh : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.sinh p.1) :=
    Real.contDiff_sinh.comp contDiff_fst
  have hprefactor_real : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) :=
    hcosh.add (hre.mul hsinh)
  have hzpow : ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        ((Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) ^ ((d : ℤ) - 1) : ℝ)) := by
    have hzpow_eq : (fun p : ℝ × ℝ =>
          (Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) ^ ((d : ℤ) - 1)) =
        fun p : ℝ × ℝ =>
          (Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) ^ d *
            (Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1)⁻¹ := by
      funext p
      exact zpow_sub_one₀ (hprefactor_pos p).ne' d
    rw [hzpow_eq]
    exact (hprefactor_real.pow d).mul
      (hprefactor_real.inv (fun p => (hprefactor_pos p).ne'))
  have hprefactor : ContDiff ℝ ∞
      (fun p : ℝ × ℝ =>
        (((Real.cosh p.1 + (Circle.exp p.2 : ℂ).re * Real.sinh p.1) ^ ((d : ℤ) - 1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hzpow
  have hf_comp : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (boostMat (-p.1) • Circle.exp p.2)) :=
    ((ContMDiffMap.contMDiff f).comp contMDiff_boostAngleNegSmul).contDiff
  exact hprefactor.mul hf_comp

/-- [CRTT25], Lemma 2.10(i); boosts act continuously on test functions. -/
theorem continuous_beta_boost (d : ℕ) (f : TestFn) :
    Continuous fun t : ℝ => Mob.beta d (Mob.boost t) f := by
  apply continuous_of_jointlySmooth_periodic (contDiff_betaBoostJoint d f)
  intro t θ
  rfl

/-! ### The instance form used by `boostOrbitContinuous_of_beta_continuous` -/

/-- [CRTT25], Lemma 2.10(i); the syntactic form `boostOrbitContinuous_of_beta_continuous`
consumes, for the concrete instance `mobiusActionMobTestFn`. -/
theorem hbeta_mobiusActionMobTestFn :
    ∀ (d : ℕ) (f : TestFn),
      Continuous fun t : ℝ =>
        MobiusAction.beta (G := Mob) (TF := TestFn) d
          (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) f :=
  continuous_beta_boost

end

end MobiusCPT
