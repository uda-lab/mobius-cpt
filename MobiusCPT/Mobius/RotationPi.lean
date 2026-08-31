import MobiusCPT.Mobius.Beta
import MobiusCPT.TestFunctions.Inv
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.Support

/-!
# Rotation by pi

This file supplies Block L1 of Issue #12.  The names corresponding to parts (a)--(e) are:
`Mob.rot_pi_conj_boost`, `beta_rot_pi_eq_negTestFn`, the two
`suppLower_iff_suppUpper_negTestFn`/`suppUpper_iff_suppLower_negTestFn` lemmas,
`inv_negTestFn`, and `cnorm_negTestFn`/`continuous_negTestFn`.
-/

namespace MobiusCPT

open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

private theorem rotMat_pi_alpha :
    (rotMat Real.pi).α = Complex.I := by
  change Complex.exp (Complex.I * (Real.pi / 2 : ℝ)) = Complex.I
  rw [show Complex.I * (Real.pi / 2 : ℝ) =
      (Real.pi / 2 : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_pi_div_two_mul_I]

/-- At the `SU(1,1)` level, conjugation by the rotation matrix at `pi` reverses a boost. -/
private theorem rotMat_pi_conj_boostMat (t : ℝ) :
    rotMat Real.pi * boostMat t * (rotMat Real.pi)⁻¹ = boostMat (-t) := by
  have hhalf : (-t) / 2 = -(t / 2) := by ring
  apply SU11.ext
  · simp only [SU11.mul_alpha, SU11.mul_beta, SU11.inv_alpha, SU11.inv_beta]
    rw [rotMat_pi_alpha]
    simp only [rotMat, boostMat, map_zero, map_neg, Complex.conj_I,
      Complex.conj_ofReal]
    rw [hhalf, Real.cosh_neg]
    linear_combination (-(Real.cosh (t / 2) : ℂ)) * Complex.I_sq
  · simp only [SU11.mul_alpha, SU11.mul_beta, SU11.inv_alpha, SU11.inv_beta]
    rw [rotMat_pi_alpha]
    simp only [rotMat, boostMat, map_zero, map_neg, Complex.conj_I,
      Complex.conj_ofReal]
    rw [hhalf, Real.sinh_neg]
    simp only [Complex.ofReal_neg]
    linear_combination (-(Real.sinh (t / 2) : ℂ)) * Complex.I_sq

namespace Mob

private theorem mk_inv (g : SU11) : mk g⁻¹ = (mk g)⁻¹ := by
  change QuotientGroup.mk' signSubgroup g⁻¹ =
    (QuotientGroup.mk' signSubgroup g)⁻¹
  exact (QuotientGroup.mk' signSubgroup).map_inv g

/-- Part (a): rotation by `pi` conjugates the boost flow to the oppositely parametrized flow. -/
theorem rot_pi_conj_boost (t : ℝ) :
    rot Real.pi * boost t * (rot Real.pi)⁻¹ = boost (-t) := by
  rw [rot, boost, boost, ← mk_inv, ← mk_mul, ← mk_mul]
  exact congrArg mk (rotMat_pi_conj_boostMat t)

end Mob

/-- Pullback of a test function by the rotation through `pi`, equivalently by `z ↦ -z`. -/
def negTestFn (f : TestFn) : TestFn :=
  ⟨fun z => f (Mob.rot Real.pi • z), by
    change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((f : Circle → ℂ) ∘ (fun z : Circle => Mob.rot Real.pi • z))
    have hrot : (fun z : Circle => Mob.rot Real.pi • z) =
        fun z : Circle => rotMat Real.pi • z := by
      funext z
      rw [Mob.rot, Mob.mk_smul]
    rw [hrot]
    exact (ContMDiffMap.contMDiff f).comp (contMDiff_smul (rotMat Real.pi))⟩

/-- Evaluation of the pullback by rotation through `pi`. -/
@[simp]
theorem negTestFn_apply (f : TestFn) (z : Circle) :
    negTestFn f z = f (Mob.rot Real.pi • z) :=
  rfl

/-- Rotation through `pi` is multiplication by `-1` in the ambient complex plane. -/
theorem coe_smul_rot_pi (z : Circle) :
    ((Mob.rot Real.pi • z : Circle) : ℂ) = -(z : ℂ) := by
  rw [Mob.rot_smul, Circle.coe_mul, Circle.coe_exp, Complex.exp_pi_mul_I]
  exact neg_one_mul (z : ℂ)

private theorem circleExp_neg_pi :
    Circle.exp (-Real.pi) = Circle.exp Real.pi := by
  rw [show -Real.pi = Real.pi - 2 * Real.pi by ring, Circle.exp_sub_two_pi]

/-- Part (b): for every conformal dimension, `β_d(r_pi)` is pullback by `z ↦ -z`. -/
theorem beta_rot_pi_eq_negTestFn (d : ℕ) (f : TestFn) :
    Mob.beta d (Mob.rot Real.pi) f = negTestFn f := by
  apply TestFn.ext
  intro z
  rw [Mob.rot, Mob.beta_mk, beta_apply, X_rotMat]
  simp only [one_zpow, Complex.ofReal_one, one_mul, rotMat_inv,
    negTestFn_apply, rotMat_smul, Mob.rot_smul]
  rw [circleExp_neg_pi]

/-- Pullback by rotation through `pi` is an involution. -/
@[simp]
theorem negTestFn_negTestFn (f : TestFn) : negTestFn (negTestFn f) = f := by
  apply TestFn.ext
  intro z
  simp only [negTestFn_apply]
  rw [← mul_smul]
  have hrot : Mob.rot Real.pi * Mob.rot Real.pi = 1 := by
    rw [← Mob.rot_add, show Real.pi + Real.pi = 2 * Real.pi by ring,
      Mob.rot_two_pi]
  rw [hrot, one_smul]

/-- Part (c): rotation through `pi` exchanges lower-supported and upper-supported test
functions. -/
theorem suppLower_iff_suppUpper_negTestFn (f : TestFn) :
    SuppLower f ↔ SuppUpper (negTestFn f) := by
  constructor
  · intro hf z hz
    change (z : ℂ).im < 0 at hz
    have hz' : Mob.rot Real.pi • z ∈ upperArc := by
      change 0 < ((Mob.rot Real.pi • z : Circle) : ℂ).im
      rw [coe_smul_rot_pi]
      change 0 < -(z : ℂ).im
      exact neg_pos.mpr hz
    have hzero := hf (Mob.rot Real.pi • z) hz'
    simpa only [negTestFn_apply] using hzero
  · intro hf z hz
    change 0 < (z : ℂ).im at hz
    have hz' : Mob.rot Real.pi • z ∈ lowerArc := by
      change ((Mob.rot Real.pi • z : Circle) : ℂ).im < 0
      rw [coe_smul_rot_pi]
      change -(z : ℂ).im < 0
      exact neg_lt_zero.mpr hz
    have hzero := hf (Mob.rot Real.pi • z) hz'
    change negTestFn (negTestFn f) z = 0 at hzero
    simpa only [negTestFn_negTestFn] using hzero

/-- Part (c), with the two semicircles interchanged. -/
theorem suppUpper_iff_suppLower_negTestFn (f : TestFn) :
    SuppUpper f ↔ SuppLower (negTestFn f) := by
  simpa only [negTestFn_negTestFn] using
    (suppLower_iff_suppUpper_negTestFn (negTestFn f)).symm

private theorem rot_pi_smul_inv (z : Circle) :
    Mob.rot Real.pi • z⁻¹ = (Mob.rot Real.pi • z)⁻¹ := by
  apply Circle.coe_injective
  rw [coe_smul_rot_pi, Circle.coe_inv, Circle.coe_inv, coe_smul_rot_pi]
  simpa only [neg_inv]

/-- Part (d): pullback by rotation through `pi` commutes with circle inversion. -/
theorem inv_negTestFn (f : TestFn) : inv (negTestFn f) = negTestFn (inv f) := by
  apply TestFn.ext
  intro z
  simp only [inv_apply, negTestFn_apply]
  rw [rot_pi_smul_inv]

/-- In the angle picture, pullback by rotation through `pi` is translation by `pi`. -/
theorem toAngle_negTestFn (f : TestFn) :
    toAngle (negTestFn f) = fun θ => toAngle f (θ + Real.pi) := by
  funext θ
  calc
    toAngle (negTestFn f) θ =
        f (Mob.rot Real.pi • Circle.exp θ) := by rfl
    _ = f (Circle.exp Real.pi * Circle.exp θ) := by rw [Mob.rot_smul]
    _ = f (Circle.exp (Real.pi + θ)) := by rw [Circle.exp_add]
    _ = f (Circle.exp (θ + Real.pi)) := by rw [add_comm]
    _ = toAngle f (θ + Real.pi) := by rfl

/-- Angle derivatives are translated, without a reflection sign, by rotation through `pi`. -/
theorem angleDeriv_negTestFn (j : ℕ) (f : TestFn) :
    angleDeriv j (negTestFn f) = fun θ => angleDeriv j f (θ + Real.pi) := by
  funext θ
  change iteratedDeriv j (toAngle (negTestFn f)) θ =
    iteratedDeriv j (toAngle f) (θ + Real.pi)
  rw [toAngle_negTestFn]
  exact congrFun (iteratedDeriv_comp_add_const j (toAngle f) Real.pi) θ

/-- The sup norm of every angle derivative is invariant under rotation through `pi`. -/
theorem norm_angleDerivB_negTestFn (j : ℕ) (f : TestFn) :
    ‖angleDerivB j (negTestFn f)‖ = ‖angleDerivB j f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j (negTestFn f)) (C := ‖angleDerivB j f‖)
        (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply, angleDeriv_negTestFn]
    exact norm_angleDeriv_le j f (θ + Real.pi)
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j f) (C := ‖angleDerivB j (negTestFn f)‖)
        (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply]
    have hθ := norm_angleDeriv_le j (negTestFn f) (θ - Real.pi)
    rw [angleDeriv_negTestFn] at hθ
    simpa only [sub_add_cancel] using hθ

/-- Part (e): every `C^N` seminorm is invariant under rotation through `pi`. -/
theorem cnorm_negTestFn (N : ℕ) (f : TestFn) :
    cnorm N (negTestFn f) = cnorm N f := by
  apply NNReal.eq
  rw [cnorm_eq, cnorm_eq]
  exact Finset.sum_congr rfl (fun j _ => norm_angleDerivB_negTestFn j f)

/-- Pullback by rotation through `pi` as a complex-linear endomorphism of test functions. -/
def negTestFnₗ : TestFn →ₗ[ℂ] TestFn where
  toFun := negTestFn
  map_add' f g := by
    apply TestFn.ext
    intro z
    rfl
  map_smul' c f := by
    apply TestFn.ext
    intro z
    rfl

/-- Part (e): pullback by rotation through `pi` is continuous in the test-function topology. -/
theorem continuous_negTestFn : Continuous negTestFn := by
  change Continuous (negTestFnₗ : TestFn → TestFn)
  refine WithSeminorms.continuous_of_isBounded withSeminorms_cnorm
    withSeminorms_cnorm negTestFnₗ ?_
  apply Seminorm.IsBounded.of_real
  intro N
  refine ⟨{N}, 1, fun f => ?_⟩
  change cnormSeminorm N (negTestFn f) ≤
    1 * (({N} : Finset ℕ).sup cnormSeminorm) f
  simp only [Finset.sup_singleton, one_mul]
  have heq : cnormSeminorm N (negTestFn f) = cnormSeminorm N f := by
    calc
      cnormSeminorm N (negTestFn f) = (cnorm N (negTestFn f) : ℝ) :=
        (cnorm_coe N (negTestFn f)).symm
      _ = (cnorm N f : ℝ) := by rw [cnorm_negTestFn]
      _ = cnormSeminorm N f := cnorm_coe N f
  exact heq.le

end

end MobiusCPT
