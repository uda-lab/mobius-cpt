import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MobiusCPT.Mobius.Basic
import MobiusCPT.Mobius.ComplexBoost

/-!
# The Möbius conformal factor

This file constructs the positive real conformal factor of a Möbius transformation, proves its
cocycle and logarithmic-derivative characterisations, and records the closed forms for rotations
and boosts used in [T26].
-/

namespace MobiusCPT

open scoped ComplexConjugate

noncomputable section

/-- [T26], Definition 2.4, eq. (2.2): the conformal factor `X_γ` of a Möbius transformation,
`X_γ(z) = |j(γ,z)|⁻²` with `j(γ,z) = β̄ z + ᾱ`; positive and real. -/
def X (g : SU11) (z : Circle) : ℝ := (Complex.normSq (j g z))⁻¹

/-- [T26], Definition 2.4: the conformal factor is strictly positive on the circle. -/
theorem X_pos (g : SU11) (z : Circle) : 0 < X g z := by
  exact inv_pos.mpr (Complex.normSq_pos.mpr (j_ne_zero g z))

/-- [T26], Definition 2.4: the conformal factor of the identity is one. -/
@[simp]
theorem X_one (z : Circle) : X 1 z = 1 := by
  simp [X]

/-- [T26], Definition 2.4: simultaneous sign change does not change the conformal factor. -/
@[simp]
theorem X_neg (g : SU11) (z : Circle) : X (SU11.neg g) z = X g z := by
  simp [X, j_neg]

/-- [T26], Definition 2.4: the conformal factor satisfies its multiplicative cocycle identity. -/
theorem X_mul (g h : SU11) (z : Circle) :
    X (g * h) z = X g (h • z) * X h z := by
  rw [X, X, X, j_mul, Complex.normSq_mul, mul_inv]

/-- [T26], Definition 2.4: evaluating at the inverse translate turns the conformal factor into
the squared norm of the inverse automorphy factor. -/
theorem X_inv_smul (g : SU11) (z : Circle) :
    X g (g⁻¹ • z) = Complex.normSq (j g⁻¹ z) := by
  have h : X g (g⁻¹ • z) * X g⁻¹ z = 1 := by
    rw [← X_mul, mul_inv_cancel, X_one]
  simp only [X] at h
  change (Complex.normSq (j g (g⁻¹ • z)))⁻¹ = Complex.normSq (j g⁻¹ z)
  exact (mul_inv_eq_one₀ (Complex.normSq_pos.mpr (j_ne_zero g⁻¹ z)).ne').mp h

/-- [T26], Definition 2.4, eq. (2.2): derivative of the circle-valued Möbius orbit, in the
branch-free form used to identify the conformal factor with a logarithmic derivative. -/
theorem hasDerivAt_smul_circleExp (g : SU11) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => ((g • Circle.exp t : Circle) : ℂ))
      (Complex.I * (Circle.exp θ : ℂ) / (j g (Circle.exp θ)) ^ 2) θ := by
  have he :
      HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
        (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := by
    simpa using (((hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I).cexp)
  have hn :
      HasDerivAt
        (fun t : ℝ => g.α * Complex.exp ((t : ℂ) * Complex.I) + g.β)
        (g.α * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ :=
    (he.const_mul g.α).add_const g.β
  have hd :
      HasDerivAt
        (fun t : ℝ => conj g.β * Complex.exp ((t : ℂ) * Complex.I) + conj g.α)
        (conj g.β * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) θ :=
    (he.const_mul (conj g.β)).add_const (conj g.α)
  have hj :
      conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α ≠ 0 := by
    simpa only [Circle.coe_exp, j] using j_ne_zero g (Circle.exp θ)
  have hdet : g.α * conj g.α - g.β * conj g.β = (1 : ℂ) := by
    calc
      g.α * conj g.α - g.β * conj g.β =
          (Complex.normSq g.α : ℂ) - Complex.normSq g.β := by
            rw [Complex.mul_conj, Complex.mul_conj]
      _ = ((Complex.normSq g.α - Complex.normSq g.β : ℝ) : ℂ) := by
        exact (Complex.ofReal_sub _ _).symm
      _ = 1 := by rw [g.normSq_sub_normSq]; simp
  have hfun : (fun t : ℝ => ((g • Circle.exp t : Circle) : ℂ)) =
      fun t : ℝ => (g.α * Complex.exp ((t : ℂ) * Complex.I) + g.β) /
        (conj g.β * Complex.exp ((t : ℂ) * Complex.I) + conj g.α) := by
    funext t
    simp [coe_smul, Circle.coe_exp, j, mul_comm]
  rw [hfun]
  have hval :
      (g.α * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
            (conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α) -
          (g.α * Complex.exp ((θ : ℂ) * Complex.I) + g.β) *
            (conj g.β * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) /
        (conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α) ^ 2 =
      Complex.I * ((Circle.exp θ : Circle) : ℂ) / (j g (Circle.exp θ)) ^ 2 := by
    rw [j, Circle.coe_exp]
    have hnum :
        g.α * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
              (conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α) -
            (g.α * Complex.exp ((θ : ℂ) * Complex.I) + g.β) *
              (conj g.β * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I)) =
          Complex.I * Complex.exp ((θ : ℂ) * Complex.I) := by
      calc
        _ = (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) *
              (g.α * conj g.α - g.β * conj g.β) := by ring
        _ = Complex.I * Complex.exp ((θ : ℂ) * Complex.I) := by rw [hdet, mul_one]
    rw [hnum]
  rw [← hval]
  show HasDerivAt
    ((fun t : ℝ => g.α * Complex.exp ((t : ℂ) * Complex.I) + g.β) /
      (fun t : ℝ => conj g.β * Complex.exp ((t : ℂ) * Complex.I) + conj g.α))
    ((g.α * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) *
          (conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α) -
        (g.α * Complex.exp ((θ : ℂ) * Complex.I) + g.β) *
          (conj g.β * (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I))) /
      (conj g.β * Complex.exp ((θ : ℂ) * Complex.I) + conj g.α) ^ 2) θ
  exact hn.div hd hj

/-- [T26], Definition 2.4, eq. (2.2): `X_γ(e^{iθ}) = -i (d/dθ) log γ(e^{iθ})`, in the
branch-free logarithmic-derivative form `-i · γ(e^{iθ})⁻¹ · (d/dθ) γ(e^{iθ})`. -/
theorem X_eq_logDeriv (g : SU11) (θ : ℝ) :
    ((X g (Circle.exp θ) : ℝ) : ℂ) =
      -Complex.I * (deriv (fun t : ℝ => ((g • Circle.exp t : Circle) : ℂ)) θ) /
        ((g • Circle.exp θ : Circle) : ℂ) := by
  rw [(hasDerivAt_smul_circleExp g θ).deriv, coe_smul, num_eq]
  simp only [X, Complex.ofReal_inv, Complex.normSq_eq_conj_mul_self]
  rw [show
    -Complex.I *
          (Complex.I * (Circle.exp θ : ℂ) / (j g (Circle.exp θ)) ^ 2) =
        (Circle.exp θ : ℂ) / (j g (Circle.exp θ)) ^ 2 by
      calc
        _ = (-(Complex.I * Complex.I) * (Circle.exp θ : ℂ)) /
            (j g (Circle.exp θ)) ^ 2 := by ring
        _ = (Circle.exp θ : ℂ) / (j g (Circle.exp θ)) ^ 2 := by
          rw [Complex.I_mul_I]
          ring]
  field_simp [j_ne_zero, Circle.coe_ne_zero]

/-- [T26], §3: inversion reverses the real boost parameter. -/
@[simp]
theorem boostMat_inv (t : ℝ) : (boostMat t)⁻¹ = boostMat (-t) := by
  apply SU11.ext
  · simp [boostMat]
    rw [← Complex.cosh_conj]
    calc
      Complex.cosh (conj ((t : ℂ) / 2)) = Complex.cosh ((t : ℂ) / 2) := by
        rw [show conj ((t : ℂ) / 2) = (t : ℂ) / 2 by
          rw [map_div₀, Complex.conj_ofReal, Complex.conj_ofNat]]
      _ = Complex.cosh (-((t : ℂ) / 2)) := by rw [Complex.cosh_neg]
      _ = Complex.cosh (-(t : ℂ) / 2) := by
        rw [show -((t : ℂ) / 2) = -(t : ℂ) / 2 by ring]
  · simp [boostMat]
    rw [show (-(t : ℂ)) / 2 = -((t : ℂ) / 2) by ring, Complex.sinh_neg]
    simp

/-- [T26], §3, eq. (3.4): the automorphy factor of a real boost is the denominator of the
complex-parameter boost at the corresponding real parameter. -/
theorem j_boostMat_eq_cden (t : ℝ) (z : Circle) :
    j (boostMat t) z = cden (t : ℂ) z := by
  have hhalf : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div t 2).symm
  rw [j_boostMat, cden, hhalf, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]

/-- [T26], eq. (3.5): `X_{v_t}(v_{-t} · z) = cosh t + Re(z) sinh t`. -/
theorem X_boostMat_inv_smul (t : ℝ) (z : Circle) :
    X (boostMat t) ((boostMat t)⁻¹ • z) =
      Real.cosh t + (z : ℂ).re * Real.sinh t := by
  rw [X_inv_smul, boostMat_inv, j_boostMat_eq_cden]
  simpa using normSq_cden_neg_ofReal t z

/-- [T26], §3: for real `t` the group action of `v_t` is the `τ = t` case of the
complex-boost formula. -/
theorem coe_boostMat_smul (t : ℝ) (z : Circle) :
    ((boostMat t • z : Circle) : ℂ) = vApply (t : ℂ) (z : ℂ) := by
  have hhalf : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div t 2).symm
  rw [coe_smul, j_boostMat_eq_cden, vApply]
  congr 1
  simp only [boostMat, cnum]
  rw [hhalf, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  ring

/-- [T26], Definition 2.4: rotations have unit conformal factor. -/
@[simp]
theorem X_rotMat (θ : ℝ) (z : Circle) : X (rotMat θ) z = 1 := by
  simp only [X, rotMat, j, map_zero, zero_mul, mul_zero, zero_add, add_zero]
  rw [Complex.normSq_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_I_mul_ofReal]
  simp

namespace Mob

/-- [T26], Definition 2.4: the conformal factor descends to `Möb = PSU(1,1)`. -/
def X (γ : Mob) (z : Circle) : ℝ :=
  Quotient.liftOn' (show SU11 ⧸ signSubgroup from γ) (fun g : SU11 => MobiusCPT.X g z) (by
    intro g h hrel
    have hmk : mk g = mk h := by
      change QuotientGroup.mk g = QuotientGroup.mk h
      exact Quotient.sound' hrel
    rcases mk_eq_mk.mp hmk with rfl | rfl
    · rfl
    · exact (MobiusCPT.X_neg g z).symm)

/-- [T26], Definition 2.4: a representative computes the descended conformal factor. -/
@[simp]
theorem X_mk (g : SU11) (z : Circle) : X (mk g) z = MobiusCPT.X g z := rfl

/-- [T26], Definition 2.4: the descended conformal factor is strictly positive. -/
theorem X_pos (γ : Mob) (z : Circle) : 0 < X γ z := by
  obtain ⟨g, rfl⟩ := mk_surjective γ
  rw [X_mk]
  exact MobiusCPT.X_pos g z

/-- [T26], Definition 2.4: the descended conformal factor satisfies the Möbius cocycle. -/
theorem X_mul (γ δ : Mob) (z : Circle) : X (γ * δ) z = X γ (δ • z) * X δ z := by
  obtain ⟨g, rfl⟩ := mk_surjective γ
  obtain ⟨h, rfl⟩ := mk_surjective δ
  simpa only [← mk_mul, X_mk, mk_smul] using MobiusCPT.X_mul g h z

/-- [T26], Definition 2.4: the descended conformal factor of the identity is one. -/
@[simp]
theorem X_one (z : Circle) : X (1 : Mob) z = 1 := by
  rw [← mk_one, X_mk]
  exact MobiusCPT.X_one z

end Mob

end

end MobiusCPT
