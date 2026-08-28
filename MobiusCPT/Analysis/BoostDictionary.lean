import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import MobiusCPT.Analysis.BoostChart
import MobiusCPT.Analysis.FlatCalculus
import MobiusCPT.Analysis.GaussianConv
import MobiusCPT.TestFunctions.Support

/-!
# The boost dictionary

This file records the real-line dictionary for smooth functions supported in the upper
semicircle.  The first part is the endpoint-flatness argument in [T26], Lemma 3.4.
-/

namespace MobiusCPT

noncomputable section

open Filter Set
open scoped ContDiff Topology

/-! ### Elementary iterated-derivative bookkeeping -/

/-- Iterated derivatives commute when their two orders are composed. -/
private theorem iteratedDeriv_iteratedDeriv_add_local {f : ℝ → ℂ} (m i : ℕ) :
    iteratedDeriv m (iteratedDeriv i f) = iteratedDeriv (m + i) f := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [iteratedDeriv_succ, ih, ← iteratedDeriv_succ]
      congr 1
      omega

/-- A flat outer function remains flat after composition at a point where the inner function
vanishes.  The zero outer bound is supplied to `norm_iteratedFDeriv_comp_le`; the finite inner
bound is included only to satisfy that theorem's hypotheses. -/
private theorem iteratedDeriv_comp_eq_zero_of_flat {g : ℝ → ℂ} {q : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hq : ContDiff ℝ ∞ q) (hq0 : q 0 = 0)
    (hflat : ∀ j : ℕ, iteratedDeriv j g 0 = 0) (n : ℕ) :
    iteratedDeriv n (g ∘ q) 0 = 0 := by
  let D : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i q 0‖
  have hsum (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i q 0‖ ≤
        ∑ l ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ l q 0‖ := by
    exact Finset.single_le_sum (f := fun l : ℕ => ‖iteratedFDeriv ℝ l q 0‖)
      (fun l _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i q 0‖ :=
      Finset.sum_nonneg (fun i hi => norm_nonneg _)
    linarith
  have hD_one : 1 ≤ D := by
    dsimp [D]
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i q 0‖ :=
      Finset.sum_nonneg (fun i hi => norm_nonneg _)
    linarith
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i q 0‖ ≤ D ^ i := by
    intro i hi_one hi
    have hleD : ‖iteratedFDeriv ℝ i q 0‖ ≤ D := by
      dsimp [D]
      linarith [hsum i hi]
    exact hleD.trans (le_self_pow₀ hD_one (Nat.ne_of_gt hi_one))
  have hC : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDeriv ℝ i g (q 0)‖ ≤ (0 : ℝ) := by
    intro i hi
    rw [hq0, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hflat i, norm_zero]
  have hcomp := norm_iteratedFDeriv_comp_le hg hq (by exact_mod_cast le_top) 0 hC hD
  have hnorm : ‖iteratedDeriv n (g ∘ q) 0‖ ≤ (0 : ℝ) := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa using hcomp
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

/-! ### The two half-line estimates -/

/-- The positive half-line estimate for the boost pullback of an upper-flat function. -/
theorem exists_norm_iteratedDeriv_comp_boostToAngle_nonneg {g : ℝ → ℂ} (hg : IsUpperFlat g)
    (k N : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv k (fun y : ℝ => g (boostToAngle y)) x‖ ≤
        C * Real.exp (-(N : ℝ) * |x|) := by
  let ψ : ℝ → ℂ := fun r => g (2 * Real.arctan r)
  let q : ℝ → ℝ := fun x => Real.exp (-x)
  let q₀ : ℝ → ℝ := fun r => 2 * Real.arctan r
  have hq : ContDiff ℝ ∞ q := by
    simpa [q, Function.comp_def] using
      (Real.contDiff_exp.comp (contDiff_neg : ContDiff ℝ ∞ (fun x : ℝ => -x)))
  have hq₀ : ContDiff ℝ ∞ q₀ := by
    have h : ContDiff ℝ ∞ fun r : ℝ => Real.arctan r := Real.contDiff_arctan
    exact contDiff_const.mul h
  have hψ : ContDiff ℝ ∞ ψ := by
    simpa [ψ, q₀, Function.comp_def, smul_eq_mul] using hg.contDiff.comp hq₀
  have hψ_flat : ∀ j : ℕ, iteratedDeriv j ψ 0 = 0 := by
    intro j
    have hzero := iteratedDeriv_comp_eq_zero_of_flat hg.contDiff hq₀ (by simp [q₀])
      (fun i => (hg.iteratedDeriv_zero i).1) j
    simpa [ψ, q₀, Function.comp_def] using hzero
  have hψ_deriv : ∀ i : ℕ, ContDiff ℝ ∞ (iteratedDeriv i ψ) := by
    intro i
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv i hψ
  have hψ_deriv_flat : ∀ i m : ℕ,
      iteratedDeriv m (iteratedDeriv i ψ) 0 = 0 := by
    intro i m
    rw [iteratedDeriv_iteratedDeriv_add_local]
    exact hψ_flat (m + i)
  have hbounds : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDeriv i ψ r‖ ≤ K * r ^ N := by
    intro i
    have h := exists_norm_le_pow_of_iteratedDeriv_eq_zero (hψ_deriv i) (p := 0) (r := 1)
      (by norm_num) (hψ_deriv_flat i) N
    simpa using h
  choose K hK_nonneg hK using hbounds
  let K₀ : ℝ := ∑ i ∈ Finset.range (k + 1), K i
  have hK₀_nonneg : 0 ≤ K₀ := by
    dsimp [K₀]
    exact Finset.sum_nonneg (fun i hi => hK_nonneg i)
  refine ⟨(Nat.factorial k : ℝ) * K₀, ?_⟩
  intro x hx
  have hqx : q x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Real.exp_pos _ |>.le
    · exact Real.exp_le_one_iff.mpr (by linarith)
  have hK_le_K₀ (i : ℕ) (hi : i ≤ k) : K i ≤ K₀ := by
    dsimp [K₀]
    apply Finset.single_le_sum
    · intro l hl
      exact hK_nonneg l
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi)
  have hC : ∀ i : ℕ, i ≤ k →
      ‖iteratedFDeriv ℝ i ψ (q x)‖ ≤ K₀ * (q x) ^ N := by
    intro i hi
    have hi_bound := hK i (q x) hqx
    have hi_mul : K i * (q x) ^ N ≤ K₀ * (q x) ^ N := by
      exact mul_le_mul_of_nonneg_right (hK_le_K₀ i hi)
        (pow_nonneg hqx.1 N)
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hi_bound.trans hi_mul
  have hq_deriv : ∀ i : ℕ, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i q x‖ ≤ (1 : ℝ) ^ i := by
    intro i hi_one hi
    have hq_formula : ∀ (m : ℕ) (y : ℝ), iteratedDeriv m q y = (-1 : ℝ) ^ m * Real.exp (-y) := by
      intro m
      induction m with
      | zero => intro y; simp [q]
      | succ m ih =>
          intro y
          rw [iteratedDeriv_succ]
          have hfun : iteratedDeriv m q = fun t : ℝ => (-1 : ℝ) ^ m * Real.exp (-t) := by
            funext t
            exact ih t
          rw [hfun]
          have hd : HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ m * Real.exp (-t))
              ((-1 : ℝ) ^ m * (-Real.exp (-y))) y := by
            have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-y)) y := by
              simpa using (hasDerivAt_neg' y).exp
            exact h1.const_mul _
          rw [hd.deriv]
          ring
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hq_formula i x, norm_mul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hcomp := norm_iteratedFDeriv_comp_le hψ hq (by exact_mod_cast le_top) x hC hq_deriv
  have hcomp' :
      ‖iteratedDeriv k (ψ ∘ q) x‖ ≤
        (Nat.factorial k : ℝ) * K₀ * (q x) ^ N := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa [one_pow, mul_assoc] using hcomp
  have hq_pow : (q x) ^ N = Real.exp (-(N : ℝ) * x) := by
    have hpow : Real.exp (-x) ^ N = Real.exp ((N : ℝ) * (-x)) := (Real.exp_nat_mul (-x) N).symm
    dsimp [q]
    rw [hpow]
    congr 1
    ring
  have hfun : (fun y : ℝ => g (boostToAngle y)) = ψ ∘ q := by
    funext y
    simp [ψ, q, boostToAngle, Function.comp_def]
  rw [hfun]
  calc
    ‖iteratedDeriv k (ψ ∘ q) x‖ ≤
        (Nat.factorial k : ℝ) * K₀ * (q x) ^ N := hcomp'
    _ = ((Nat.factorial k : ℝ) * K₀) * Real.exp (-(N : ℝ) * |x|) := by
      rw [hq_pow, abs_of_nonneg hx]

/-- Reflection transports the positive half-line estimate to the negative half-line. -/
theorem exists_norm_iteratedDeriv_comp_boostToAngle_nonpos {g : ℝ → ℂ} (hg : IsUpperFlat g)
    (k N : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, x ≤ 0 →
      ‖iteratedDeriv k (fun y : ℝ => g (boostToAngle y)) x‖ ≤
        C * Real.exp (-(N : ℝ) * |x|) := by
  let gᵣ : ℝ → ℂ := fun y => g (Real.pi - y)
  have hgᵣ : IsUpperFlat gᵣ := by
    refine ⟨?_, ?_⟩
    · simpa [gᵣ, Function.comp_def] using
        hg.contDiff.comp (contDiff_const.sub (contDiff_id : ContDiff ℝ ∞ id))
    · intro y hy
      apply hg.zero_outside
      intro h
      rcases lt_or_ge y 0 with hyneg | hypos
      · linarith [h.2]
      · by_cases hyzero : y = 0
        · subst y
          linarith [h.2]
        · have hypos' : 0 < y := lt_of_le_of_ne hypos (Ne.symm hyzero)
          have hpi_le : Real.pi ≤ y :=
            le_of_not_gt (fun hy_lt => hy ⟨hypos', hy_lt⟩)
          linarith [h.1]
  obtain ⟨C, hC⟩ := exists_norm_iteratedDeriv_comp_boostToAngle_nonneg hgᵣ k N
  have hfun :
      (fun y : ℝ => gᵣ (boostToAngle y)) =
        (fun y : ℝ => g (boostToAngle (-y))) := by
    funext y
    change g (Real.pi - boostToAngle y) = g (boostToAngle (-y))
    rw [boostToAngle_eq_pi_sub y]
    simp [boostToAngle]
  refine ⟨C, ?_⟩
  intro x hx
  have hC' := hC (-x) (neg_nonneg.mpr hx)
  rw [hfun] at hC'
  have hneg := iteratedDeriv_comp_neg k (fun t : ℝ => g (boostToAngle t)) (-x)
  rw [hneg] at hC'
  simpa [abs_neg, neg_neg, norm_smul, Real.norm_eq_abs] using hC'

/-- [T26], proof of Lemma 3.4; the boost picture of an upper-flat function decays faster than
every exponential, together with all its derivatives. -/
theorem isRapidlyDecaying_comp_boostToAngle {g : ℝ → ℂ} (hg : IsUpperFlat g) :
    IsRapidlyDecaying (fun x : ℝ => g (boostToAngle x)) := by
  have hcont : ContDiff ℝ ∞ (fun x : ℝ => g (boostToAngle x)) := by
    simpa [Function.comp_def] using hg.contDiff.comp contDiff_boostToAngle
  refine ⟨hcont, ?_⟩
  intro k N
  obtain ⟨Cpos, hCpos⟩ := exists_norm_iteratedDeriv_comp_boostToAngle_nonneg hg k N
  obtain ⟨Cneg, hCneg⟩ := exists_norm_iteratedDeriv_comp_boostToAngle_nonpos hg k N
  refine ⟨max Cpos Cneg, ?_⟩
  intro x
  rcases le_total 0 x with hx | hx
  · exact (hCpos x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · exact (hCneg x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _))

end
end MobiusCPT
