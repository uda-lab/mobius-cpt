import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import MobiusCPT.TestFunctions.Basic
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.Support

/-!
# MobiusCPT.TestFunctions.Inv

The inversion of the circle and its action on smooth test functions.
-/

namespace MobiusCPT

open scoped ContDiff Manifold Topology

noncomputable section

/-- [T26], §3; the inversion `z ↦ z⁻¹` transported to test functions, `f ↦ f ∘ z⁻¹`. -/
def inv (f : TestFn) : TestFn :=
  ⟨fun z => f z⁻¹, by
    change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((f : Circle → ℂ) ∘ (fun z : Circle => z⁻¹))
    exact (ContMDiffMap.contMDiff f).comp (contMDiff_inv (𝓡 1) ∞)⟩

/-- [T26], §3; evaluation of test-function inversion is pointwise circle inversion. -/
@[simp] theorem inv_apply (f : TestFn) (z : Circle) : inv f z = f z⁻¹ :=
  rfl

/-- [T26], §3; in the angle picture inversion is the reflection `θ ↦ -θ`. -/
theorem toAngle_inv (f : TestFn) : toAngle (inv f) = fun θ => toAngle f (-θ) := by
  funext θ
  simp [toAngle]

/-- [T26], §3; inversion preserves addition of test functions. -/
theorem inv_add (f g : TestFn) : inv (f + g) = inv f + inv g := by
  apply TestFn.ext
  intro z
  change (f + g) z⁻¹ = f z⁻¹ + g z⁻¹
  rfl

/-- [T26], §3; inversion commutes with complex scalar multiplication. -/
theorem inv_smul (c : ℂ) (f : TestFn) : inv (c • f) = c • inv f := by
  apply TestFn.ext
  intro z
  change (c • f) z⁻¹ = c * f z⁻¹
  rfl

/-- [T26], §3; inversion preserves the zero test function. -/
theorem inv_zero : inv (0 : TestFn) = 0 := by
  apply TestFn.ext
  intro z
  rfl

/-- [T26], §3; circle inversion induces an involution on test functions. -/
theorem inv_involutive (f : TestFn) : inv (inv f) = f := by
  apply TestFn.ext
  intro z
  simp

/-- [T26], §3; inversion as a `ℂ`-linear map on `C^∞(S¹)`. -/
def invₗ : TestFn →ₗ[ℂ] TestFn where
  toFun := inv
  map_add' := inv_add
  map_smul' := inv_smul

/-- [T26], §3; inversion exchanges the two open semicircles. -/
theorem inv_supp (f : TestFn) : SuppUpper f ↔ SuppLower (inv f) := by
  constructor
  · intro hf z hz
    change 0 < (z : ℂ).im at hz
    have hz' : z⁻¹ ∈ lowerArc := by
      change ((z⁻¹ : Circle) : ℂ).im < 0
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_lt_zero.mpr hz
    have hzero := hf z⁻¹ hz'
    simpa only [inv_apply] using hzero
  · intro hf z hz
    change (z : ℂ).im < 0 at hz
    have hz' : z⁻¹ ∈ upperArc := by
      change 0 < ((z⁻¹ : Circle) : ℂ).im
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_pos.mpr hz
    have hzero := hf z⁻¹ hz'
    simpa only [inv_apply, inv_inv] using hzero

/-- [T26], §3; inversion exchanges the two open semicircles in the reverse direction. -/
theorem inv_supp' (f : TestFn) : SuppLower f ↔ SuppUpper (inv f) := by
  simpa only [inv_involutive] using (inv_supp (inv f)).symm

/-- [T26], §3; angle derivatives transform under inversion by reflection and a sign. -/
theorem angleDeriv_inv (j : ℕ) (f : TestFn) :
    angleDeriv j (inv f) = fun θ => (-1 : ℂ) ^ j * angleDeriv j f (-θ) := by
  funext θ
  change iteratedDeriv j (toAngle (inv f)) θ =
    (-1 : ℂ) ^ j * iteratedDeriv j (toAngle f) (-θ)
  rw [toAngle_inv]
  simpa [Complex.real_smul] using iteratedDeriv_comp_neg j (toAngle f) θ

/-- [T26], Lemma 3.9; the sup norm of an angle derivative is invariant under test-function
inversion. -/
theorem norm_angleDerivB_inv (j : ℕ) (f : TestFn) :
    ‖angleDerivB j (inv f)‖ = ‖angleDerivB j f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j (inv f)) (C := ‖angleDerivB j f‖) (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply, angleDeriv_inv]
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
      norm_angleDeriv_le j f (-θ)
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j f) (C := ‖angleDerivB j (inv f)‖) (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply]
    have hθ := norm_angleDeriv_le j (inv f) (-θ)
    rw [angleDeriv_inv] at hθ
    simpa only [neg_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using hθ

/-- [T26], Lemma 3.9; the angle-derivative `C^N` norm is invariant under inversion. -/
theorem cnorm_inv (N : ℕ) (f : TestFn) : cnorm N (inv f) = cnorm N f := by
  apply NNReal.eq
  rw [cnorm_eq, cnorm_eq]
  exact Finset.sum_congr rfl (fun j hj => norm_angleDerivB_inv j f)

end

end MobiusCPT
