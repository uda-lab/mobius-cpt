import MobiusCPT.TestFunctions.Inv
import MobiusCPT.TestFunctions.Support

/-!
# MobiusCPT.TestFunctions.Monomial

The integer monomials on the circle as smooth test functions.
-/

namespace MobiusCPT

open scoped Topology Manifold ContDiff

attribute [local instance] finrank_real_complex_fact'

noncomputable section

/-- [T26], §2.2; the monomial test function `z ↦ z^n`, for `n : ℤ`. These are the functions
used in the Fourier expansion of an element of `C^∞(S¹)` and in the (W3) spectrum condition. -/
def monomial (n : ℤ) : TestFn :=
  ⟨fun z => ((z ^ n : Circle) : ℂ), by
    have hzpow : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ n) := by
      cases n with
      | ofNat k =>
          simpa only [Int.ofNat_eq_natCast, zpow_natCast, id_eq] using
            (contMDiff_id : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z)).pow k
      | negSucc k =>
          simpa only [zpow_negSucc, id_eq] using
            ((contMDiff_id : ContMDiff (𝓡 1) (𝓡 1) ∞
              (fun z : Circle => z)).pow (k + 1)).inv
    have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
      contMDiff_coe_sphere
    exact hcoe.comp hzpow⟩

/-- Evaluation of a monomial is integer exponentiation inside `Circle`, followed by coercion. -/
@[simp] theorem monomial_apply (n : ℤ) (z : Circle) :
    monomial n z = ((z ^ n : Circle) : ℂ) :=
  rfl

/-- Evaluation of a monomial agrees with integer exponentiation in `ℂ`. -/
theorem monomial_apply' (n : ℤ) (z : Circle) : monomial n z = (z : ℂ) ^ n := by
  rw [monomial_apply, Circle.coe_zpow]

/-- The zeroth monomial is pointwise equal to one. -/
theorem monomial_zero (z : Circle) : monomial 0 z = 1 := by
  rw [monomial_apply, zpow_zero, Circle.coe_one]

/-- [T26], §2.2; in the angle picture the `n`-th monomial is `θ ↦ exp(nθi)`. -/
theorem toAngle_monomial (n : ℤ) (θ : ℝ) :
    toAngle (monomial n) θ = Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
  change monomial n (Circle.exp θ) =
    Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)
  rw [monomial_apply', Circle.coe_exp]
  simpa only [mul_assoc] using
    (Complex.exp_int_mul ((θ : ℂ) * Complex.I) n).symm

/-- Every monomial is nonzero at every point of the circle. -/
theorem monomial_ne_zero (n : ℤ) (z : Circle) : monomial n z ≠ 0 := by
  rw [monomial_apply]
  exact Circle.coe_ne_zero (z ^ n)

/-- Every monomial has full closed support. -/
theorem support_monomial (n : ℤ) : support (monomial n) = Set.univ := by
  rw [support_def]
  have hnonzero : {z : Circle | monomial n z ≠ 0} = Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact monomial_ne_zero n z
  rw [hnonzero, closure_univ]

/-- Inversion sends the `n`-th monomial to the `(-n)`-th monomial. -/
theorem inv_monomial (n : ℤ) : inv (monomial n) = monomial (-n) := by
  apply TestFn.ext
  intro z
  rw [inv_apply, monomial_apply, monomial_apply, inv_zpow']

end

end MobiusCPT
