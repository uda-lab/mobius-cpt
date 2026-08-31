import MobiusCPT.Analysis.ParamSlice
import MobiusCPT.Analysis.TestFnCurve
import MobiusCPT.Mobius.ComplexBetaDef

/-!
# Continuity of the complex boost on the closed strip

[T26], Lemma 3.6, first clause.  The map `τ ↦ β_d(v_τ)F|_{I_+}` is continuous on the closed strip
`0 ≤ Im τ ≤ π` with values in `C^∞(S¹)`, i.e. for its Fréchet topology.  The proof reads every
angle derivative of the boost off the jointly smooth function of `(τ, θ)`, and turns joint
continuity into uniformity in `θ` by compactness of the closed semicircle.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], Definition 3.5; the `j`-th angle derivative of the complex boost, as a function of the
strip parameter and the angle jointly. -/
def betaBoostSlice (d : ℕ) (F : AnalyticTestFn) (j : ℕ) : ℂ × ℝ → ℂ :=
  sliceDeriv stripUpper j (betaBoostJoint d F)

/-- [T26], Lemma 3.6; every angle derivative of the complex boost is jointly continuous in the
strip parameter and the angle. -/
theorem continuousOn_betaBoostSlice (d : ℕ) (F : AnalyticTestFn) (j : ℕ) :
    ContinuousOn (betaBoostSlice d F j) stripUpper :=
  continuousOn_sliceDeriv uniqueDiffOn_stripUpper (contDiffOn_betaBoostJoint d F) j

/-- [T26], Definition 3.5; the joint slice derivative computes the angle derivative of the
pointwise boost formula. -/
theorem betaBoostSlice_eq (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    betaBoostSlice d F j (τ, θ) =
      iteratedDerivWithin j (fun t : ℝ => betaBoostVal d τ F (Circle.exp t))
        (Set.Icc 0 Real.pi) θ := by
  have h := sliceDeriv_eq_iteratedDerivWithin uniqueDiffOn_strip_I_mul_pi
    (uniqueDiffOn_Icc Real.pi_pos) (contDiffOn_betaBoostJoint d F) j hτ hθ
  exact h

/-- [T26], Definition 3.5; on the closed upper semicircle the angle derivatives of the complex
boost are the angle derivatives of its defining formula. -/
theorem angleDeriv_betaBoost_of_mem (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    angleDeriv j (betaBoost d τ F) θ = betaBoostSlice d F j (τ, θ) := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 (2 * Real.pi / 2) → betaBoostCut d τ F x = 0 := by
    intro x hx
    refine zeroExtend_eq_zero_of_notMem _ ?_
    intro hmem
    exact hx (by simpa using hmem)
  have hper := iteratedDeriv_periodize_eqOn (T := 2 * Real.pi) Real.two_pi_pos hsupp j
  have hmemIoo : θ ∈ Set.Ioo (-(2 * Real.pi / 2)) (2 * Real.pi) := by
    constructor
    · have := hθ.1
      nlinarith [Real.pi_pos]
    · have := hθ.2
      nlinarith [Real.pi_pos]
  have hcut :=
    iteratedDeriv_zeroExtendIcc Real.pi_pos (contDiffOn_betaBoostAngle d F hτ)
      (fun n => iteratedDerivWithin_betaBoostVal_circleExp_zero d F hτ n)
      (fun n => iteratedDerivWithin_betaBoostVal_circleExp_pi d F hτ n) j
  calc
    angleDeriv j (betaBoost d τ F) θ
        = iteratedDeriv j (periodize (2 * Real.pi) (betaBoostCut d τ F)) θ := by
          rw [angleDeriv, toAngle_betaBoost d F hτ]
    _ = iteratedDeriv j (betaBoostCut d τ F) θ := hper hmemIoo
    _ = zeroExtendIcc 0 Real.pi
          (iteratedDerivWithin j (fun t : ℝ => betaBoostVal d τ F (Circle.exp t))
            (Set.Icc 0 Real.pi)) θ := by
          rw [betaBoostCut, hcut]
    _ = iteratedDerivWithin j (fun t : ℝ => betaBoostVal d τ F (Circle.exp t))
          (Set.Icc 0 Real.pi) θ := zeroExtend_eq_of_mem _ hθ
    _ = betaBoostSlice d F j (τ, θ) := (betaBoostSlice_eq d F j hτ hθ).symm

/-- [T26], Definition 3.5; off the closed upper semicircle, within one period, every angle
derivative of the complex boost vanishes: the boost is supported in `I_+`. -/
theorem angleDeriv_betaBoost_of_notMem (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi)) :
    angleDeriv j (betaBoost d τ F) θ = 0 := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 (2 * Real.pi / 2) → betaBoostCut d τ F x = 0 := by
    intro x hx
    refine zeroExtend_eq_zero_of_notMem _ ?_
    intro hmem
    exact hx (by simpa using hmem)
  have hper := iteratedDeriv_periodize_eqOn (T := 2 * Real.pi) Real.two_pi_pos hsupp j
  have hmemIoo : θ ∈ Set.Ioo (-(2 * Real.pi / 2)) (2 * Real.pi) := by
    constructor
    · have := hθ.1
      nlinarith [Real.pi_pos]
    · exact hθ.2
  have hcut :=
    iteratedDeriv_zeroExtendIcc Real.pi_pos (contDiffOn_betaBoostAngle d F hτ)
      (fun n => iteratedDerivWithin_betaBoostVal_circleExp_zero d F hτ n)
      (fun n => iteratedDerivWithin_betaBoostVal_circleExp_pi d F hτ n) j
  have hnot : θ ∉ Set.Icc 0 Real.pi := by
    intro hmem
    exact absurd hmem.2 (not_le_of_gt hθ.1)
  calc
    angleDeriv j (betaBoost d τ F) θ
        = iteratedDeriv j (periodize (2 * Real.pi) (betaBoostCut d τ F)) θ := by
          rw [angleDeriv, toAngle_betaBoost d F hτ]
    _ = iteratedDeriv j (betaBoostCut d τ F) θ := hper hmemIoo
    _ = zeroExtendIcc 0 Real.pi
          (iteratedDerivWithin j (fun t : ℝ => betaBoostVal d τ F (Circle.exp t))
            (Set.Icc 0 Real.pi)) θ := by
          rw [betaBoostCut, hcut]
    _ = 0 := zeroExtend_eq_zero_of_notMem _ hnot

/-- Every real number is congruent modulo `2π` to a point of `[0, 2π)`. -/
theorem exists_sub_int_mul_mem_Ico (θ : ℝ) :
    ∃ n : ℤ, θ - n * (2 * Real.pi) ∈ Set.Ico 0 (2 * Real.pi) := by
  refine ⟨⌊θ / (2 * Real.pi)⌋, ⟨?_, ?_⟩⟩
  · have h := Int.floor_le (θ / (2 * Real.pi))
    have hpos := Real.two_pi_pos
    have hmul : (⌊θ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ θ := by
      calc
        (⌊θ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ (θ / (2 * Real.pi)) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h hpos.le
        _ = θ := by field_simp
    linarith
  · have h := Int.lt_floor_add_one (θ / (2 * Real.pi))
    have hpos := Real.two_pi_pos
    have hmul : θ < ((⌊θ / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
      calc
        θ = (θ / (2 * Real.pi)) * (2 * Real.pi) := by field_simp
        _ < ((⌊θ / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right h hpos
    nlinarith [hmul]

/-- [T26], Lemma 3.6; a bound on the angle derivatives of the difference of two boosts over the
closed upper semicircle bounds them over the whole circle, by periodicity together with the
support property. -/
theorem forall_norm_angleDeriv_betaBoost_sub_lt (d : ℕ) (F : AnalyticTestFn) (j : ℕ)
    {τ σ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi))
    (hσ : σ ∈ strip (Complex.I * Real.pi)) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ θ ∈ Set.Icc 0 Real.pi,
      ‖betaBoostSlice d F j (τ, θ) - betaBoostSlice d F j (σ, θ)‖ < ε) :
    ∀ θ : ℝ, ‖angleDeriv j (betaBoost d τ F) θ - angleDeriv j (betaBoost d σ F) θ‖ < ε := by
  intro θ
  obtain ⟨n, hmem⟩ := exists_sub_int_mul_mem_Ico θ
  set θ' : ℝ := θ - n * (2 * Real.pi) with hθ'
  have hred (ρ : ℂ) :
      angleDeriv j (betaBoost d ρ F) θ' = angleDeriv j (betaBoost d ρ F) θ :=
    (periodic_angleDeriv j (betaBoost d ρ F)).sub_int_mul_eq n
  rw [← hred τ, ← hred σ]
  by_cases hle : θ' ≤ Real.pi
  · have hτeq : angleDeriv j (betaBoost d τ F) θ' = betaBoostSlice d F j (τ, θ') :=
      angleDeriv_betaBoost_of_mem d F j hτ ⟨hmem.1, hle⟩
    have hσeq : angleDeriv j (betaBoost d σ F) θ' = betaBoostSlice d F j (σ, θ') :=
      angleDeriv_betaBoost_of_mem d F j hσ ⟨hmem.1, hle⟩
    calc
      ‖angleDeriv j (betaBoost d τ F) θ' - angleDeriv j (betaBoost d σ F) θ'‖
          = ‖betaBoostSlice d F j (τ, θ') - betaBoostSlice d F j (σ, θ')‖ := by
            rw [hτeq, hσeq]
      _ < ε := h θ' ⟨hmem.1, hle⟩
  · have hIoo : θ' ∈ Set.Ioo Real.pi (2 * Real.pi) := ⟨lt_of_not_ge hle, hmem.2⟩
    rw [angleDeriv_betaBoost_of_notMem d F j hτ hIoo,
      angleDeriv_betaBoost_of_notMem d F j hσ hIoo]
    simpa using hε

/-- [T26], Lemma 3.6, first clause; the complex boost is continuous on the closed strip as a curve
of test functions, for the Fréchet topology of `C^∞(S¹)`.  No topology on `𝓧` is used: the source's
"continuous on `𝕊_{iπ}`" is read in `C^∞(S¹)`, which is where `β_d(v_τ)F|_{I_+}` lives. -/
theorem continuousOn_betaBoost (d : ℕ) (F : AnalyticTestFn) :
    ContinuousOn (fun τ : ℂ => betaBoost d τ F) (strip (Complex.I * Real.pi)) := by
  intro τ₀ hτ₀
  rw [ContinuousWithinAt]
  refine tendsto_testFn_of_forall_eventually ?_
  intro N ε hε
  have hslice : ∀ j : ℕ,
      ∀ᶠ τ in nhdsWithin τ₀ (strip (Complex.I * Real.pi)),
        ∀ θ ∈ Set.Icc 0 Real.pi,
          ‖betaBoostSlice d F j (τ, θ) - betaBoostSlice d F j (τ₀, θ)‖ < ε := by
    intro j
    exact eventually_forall_norm_sub_lt isCompact_Icc
      (continuousOn_betaBoostSlice d F j) hτ₀ hε
  have hfin :
      ∀ᶠ τ in nhdsWithin τ₀ (strip (Complex.I * Real.pi)),
        ∀ j ∈ Finset.range (N + 1), ∀ θ ∈ Set.Icc 0 Real.pi,
          ‖betaBoostSlice d F j (τ, θ) - betaBoostSlice d F j (τ₀, θ)‖ < ε :=
    (Filter.eventually_all_finset _).mpr fun j _ => hslice j
  filter_upwards [hfin, self_mem_nhdsWithin] with τ hτfin hτmem
  intro j hj θ
  exact forall_norm_angleDeriv_betaBoost_sub_lt d F j hτmem hτ₀ hε
    (hτfin j (Finset.mem_range.mpr (by omega))) θ

end

end MobiusCPT
