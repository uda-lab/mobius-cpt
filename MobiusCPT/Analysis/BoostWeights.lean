import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import MobiusCPT.Analysis.BoostChart

/-!
# Weighted derivative bounds along the boost chart

Along the boost chart of [T26], §3 one has `∂_θ = -cosh(x) ∂_x`, so a `θ`-derivative costs one
factor `e^{|x|}`.  This file turns that into the bound used in the proof of Lemma 3.4: the `j`-th
`θ`-derivative of a function is controlled by the first `j` `x`-derivatives of its boost picture,
weighted by `e^{j|x|}`.  Nothing here refers to test functions or to the Gaussian construction.
-/

namespace MobiusCPT

noncomputable section

open Set
open scoped ContDiff Topology

/-- Every derivative of the hyperbolic cosine and sine is bounded by `e^{|x|}`. -/
private theorem norm_iteratedDeriv_cosh_le (p : ℕ) (y : ℝ) :
    ‖iteratedDeriv p Real.cosh y‖ ≤ Real.exp |y| ∧
      ‖iteratedDeriv p Real.sinh y‖ ≤ Real.exp |y| := by
  have hcosh : ∀ t : ℝ, ‖Real.cosh t‖ ≤ Real.exp |t| := by
    intro t
    have h : Real.cosh t = (Real.exp t + Real.exp (-t)) / 2 := Real.cosh_eq t
    have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
    have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.cosh_pos t).le, h]
    linarith
  have hsinh : ∀ t : ℝ, ‖Real.sinh t‖ ≤ Real.exp |t| := by
    intro t
    have h : Real.sinh t = (Real.exp t - Real.exp (-t)) / 2 := Real.sinh_eq t
    have h1 : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
    have h2 : Real.exp (-t) ≤ Real.exp |t| := Real.exp_le_exp.mpr (neg_le_abs t)
    have h3 : (0 : ℝ) < Real.exp t := Real.exp_pos t
    have h4 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos (-t)
    rw [Real.norm_eq_abs, h, abs_le]
    constructor <;> linarith
  induction p generalizing y with
  | zero => exact ⟨by simpa using hcosh y, by simpa using hsinh y⟩
  | succ p ih =>
      constructor
      · rw [iteratedDeriv_succ', Real.deriv_cosh]
        exact (ih y).2
      · rw [iteratedDeriv_succ', Real.deriv_sinh]
        exact (ih y).1

private theorem norm_iteratedFDeriv_cosh_le (p : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ p Real.cosh y‖ ≤ Real.exp |y| := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (norm_iteratedDeriv_cosh_le p y).1

/-- The chart identity `∂_θ = -cosh(x) ∂_x`, in the form used by the induction below. -/
private theorem iteratedDeriv_succ_comp_boostToAngle {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (j : ℕ)
    (y : ℝ) :
    iteratedDeriv (j + 1) w (boostToAngle y) =
      (-Real.cosh y) • deriv (fun t : ℝ => iteratedDeriv j w (boostToAngle t)) y := by
  have hcosh : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hinner : HasDerivAt boostToAngle (-(Real.cosh y)⁻¹) y := hasDerivAt_boostToAngle y
  have hiter : ContDiff ℝ ∞ (iteratedDeriv j w) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv j hw
  have houter : HasDerivAt (iteratedDeriv j w) (iteratedDeriv (j + 1) w (boostToAngle y))
      (boostToAngle y) := by
    have hd : DifferentiableAt ℝ (iteratedDeriv j w) (boostToAngle y) :=
      ((contDiff_infty_iff_deriv.mp hiter).1) (boostToAngle y)
    rw [iteratedDeriv_succ]
    exact hd.hasDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => iteratedDeriv j w (boostToAngle t))
      ((-(Real.cosh y)⁻¹) • iteratedDeriv (j + 1) w (boostToAngle y)) y :=
    houter.scomp y hinner
  rw [hcomp.deriv, smul_smul]
  have hone : (-Real.cosh y) * (-(Real.cosh y)⁻¹) = 1 := by
    field_simp
  rw [hone, one_smul]

/-- [T26], proof of Lemma 3.4; the boost-chart weight bound.  The `m`-th `x`-derivative of the
`j`-th `θ`-derivative of `w`, read along the chart, is bounded by `e^{j|x|}` times the first
`j + m` `x`-derivatives of the boost picture `v` of `w`. -/
theorem exists_bound_boostChart (j m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w v : ℝ → ℂ, ContDiff ℝ ∞ w → ContDiff ℝ ∞ v →
      (∀ y : ℝ, w (boostToAngle y) = v y) → ∀ x : ℝ,
        ‖iteratedDeriv m (fun y : ℝ => iteratedDeriv j w (boostToAngle y)) x‖ ≤
          K * Real.exp ((j : ℝ) * |x|) *
            ∑ i ∈ Finset.range (j + m + 1), ‖iteratedDeriv i v x‖ := by
  induction j generalizing m with
  | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro w v hw hv hwv x
      have hfun : (fun y : ℝ => iteratedDeriv 0 w (boostToAngle y)) = v := by
        funext y
        simpa using hwv y
      rw [hfun]
      have hmem : m ∈ Finset.range (0 + m + 1) := Finset.mem_range.mpr (by omega)
      have hle : ‖iteratedDeriv m v x‖ ≤
          ∑ i ∈ Finset.range (0 + m + 1), ‖iteratedDeriv i v x‖ :=
        Finset.single_le_sum (f := fun i : ℕ => ‖iteratedDeriv i v x‖)
          (fun i _ => norm_nonneg _) hmem
      simpa using hle
  | succ j ih =>
      choose K hK0 hK using ih
      refine ⟨(∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ)) *
        ∑ q ∈ Finset.range (m + 2), K q, ?_, ?_⟩
      · have h1 : (0 : ℝ) ≤ ∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) :=
          Finset.sum_nonneg fun p _ => by positivity
        have h2 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (m + 2), K q :=
          Finset.sum_nonneg fun q _ => hK0 q
        exact mul_nonneg h1 h2
      intro w v hw hv hwv x
      set S : ℝ := ∑ i ∈ Finset.range (j + 1 + m + 1), ‖iteratedDeriv i v x‖ with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
      -- the chart identity `∂_θ = -cosh(x) ∂_x`
      have hbase : ContDiff ℝ ∞ (fun t : ℝ => iteratedDeriv j w (boostToAngle t)) := by
        have h1 : ContDiff ℝ ∞ (iteratedDeriv j w) := by
          rw [iteratedDeriv_eq_iterate]
          exact ContDiff.iterate_deriv j hw
        simpa [Function.comp_def] using h1.comp contDiff_boostToAngle
      set D : ℝ → ℂ := deriv (fun t : ℝ => iteratedDeriv j w (boostToAngle t)) with hD
      have hDdiff : ContDiff ℝ ∞ D := (contDiff_infty_iff_deriv.mp hbase).2
      have hchart : (fun y : ℝ => iteratedDeriv (j + 1) w (boostToAngle y)) =
          fun y : ℝ => (-Real.cosh y) • D y := by
        funext y
        rw [iteratedDeriv_succ_comp_boostToAngle hw j y, hD]
      rw [hchart]
      -- Leibniz for the `m`-fold derivative of the product
      have hneg : ContDiff ℝ ∞ (fun y : ℝ => -Real.cosh y) := Real.contDiff_cosh.neg
      have hleib := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (f := fun y : ℝ => -Real.cosh y)
        (g := D) hneg hDdiff x (n := m) (by exact_mod_cast le_top)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
      refine hleib.trans ?_
      -- bound each Leibniz term
      have hterm : ∀ p ∈ Finset.range (m + 1),
          (m.choose p : ℝ) * ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
              ‖iteratedFDeriv ℝ (m - p) D x‖ ≤
            (m.choose p : ℝ) * ((∑ q ∈ Finset.range (m + 2), K q) *
              (Real.exp ((j + 1 : ℝ) * |x|) * S)) := by
        intro p hp
        have hpm : p ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        have hcosh : ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ ≤ Real.exp |x| := by
          have hfun : (fun y : ℝ => -Real.cosh y) = -Real.cosh := rfl
          rw [hfun, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
          exact norm_iteratedFDeriv_cosh_le p x
        -- the inductive bound for the `(m - p + 1)`-st `x`-derivative
        have hDbound : ‖iteratedFDeriv ℝ (m - p) D x‖ ≤
            K (m - p + 1) * Real.exp ((j : ℝ) * |x|) * S := by
          have hrw : iteratedFDeriv ℝ (m - p) D x =
              iteratedFDeriv ℝ (m - p) (deriv
                (fun t : ℝ => iteratedDeriv j w (boostToAngle t))) x := by rw [hD]
          rw [hrw, norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ']
          refine (hK (m - p + 1) w v hw hv hwv x).trans ?_
          have hnum : j + (m - p + 1) + 1 ≤ j + 1 + m + 1 := by
            have h1 : m - p ≤ m := Nat.sub_le m p
            calc j + (m - p + 1) + 1 ≤ j + (m + 1) + 1 :=
                  Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right h1 1) j) 1
              _ = j + 1 + m + 1 := by ring
          have hsub : Finset.range (j + (m - p + 1) + 1) ⊆
              Finset.range (j + 1 + m + 1) := by
            intro i hi
            simp only [Finset.mem_range] at hi ⊢
            exact lt_of_lt_of_le hi hnum
          have hsum : ∑ i ∈ Finset.range (j + (m - p + 1) + 1), ‖iteratedDeriv i v x‖ ≤ S := by
            rw [hS]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => norm_nonneg _
          have hpos : (0 : ℝ) ≤ K (m - p + 1) * Real.exp ((j : ℝ) * |x|) :=
            mul_nonneg (hK0 _) (Real.exp_nonneg _)
          calc
            K (m - p + 1) * Real.exp ((j : ℝ) * |x|) *
                ∑ i ∈ Finset.range (j + (m - p + 1) + 1), ‖iteratedDeriv i v x‖
                ≤ K (m - p + 1) * Real.exp ((j : ℝ) * |x|) * S :=
              mul_le_mul_of_nonneg_left hsum hpos
            _ = K (m - p + 1) * Real.exp ((j : ℝ) * |x|) * S := rfl
        have hKle : K (m - p + 1) ≤ ∑ q ∈ Finset.range (m + 2), K q := by
          apply Finset.single_le_sum (f := K) (fun q _ => hK0 q)
          exact Finset.mem_range.mpr (by omega)
        have hexp : Real.exp |x| * Real.exp ((j : ℝ) * |x|) =
            Real.exp ((j + 1 : ℝ) * |x|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hchoose : (0 : ℝ) ≤ (m.choose p : ℝ) := by positivity
        have hmain : ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
            ‖iteratedFDeriv ℝ (m - p) D x‖ ≤
            (∑ q ∈ Finset.range (m + 2), K q) * (Real.exp ((j + 1 : ℝ) * |x|) * S) := by
          calc
            ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
                ‖iteratedFDeriv ℝ (m - p) D x‖
                ≤ Real.exp |x| * (K (m - p + 1) * Real.exp ((j : ℝ) * |x|) * S) := by
                  apply mul_le_mul hcosh hDbound (norm_nonneg _) (Real.exp_nonneg _)
            _ = K (m - p + 1) * (Real.exp |x| * Real.exp ((j : ℝ) * |x|)) * S := by ring
            _ = K (m - p + 1) * Real.exp ((j + 1 : ℝ) * |x|) * S := by rw [hexp]
            _ ≤ (∑ q ∈ Finset.range (m + 2), K q) * Real.exp ((j + 1 : ℝ) * |x|) * S := by
                  apply mul_le_mul_of_nonneg_right
                  · exact mul_le_mul_of_nonneg_right hKle (Real.exp_nonneg _)
                  · exact hS0
            _ = (∑ q ∈ Finset.range (m + 2), K q) * (Real.exp ((j + 1 : ℝ) * |x|) * S) := by ring
        calc
          (m.choose p : ℝ) * ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
              ‖iteratedFDeriv ℝ (m - p) D x‖
              = (m.choose p : ℝ) * (‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
                ‖iteratedFDeriv ℝ (m - p) D x‖) := by ring
          _ ≤ (m.choose p : ℝ) * ((∑ q ∈ Finset.range (m + 2), K q) *
                (Real.exp ((j + 1 : ℝ) * |x|) * S)) :=
              mul_le_mul_of_nonneg_left hmain hchoose
      calc
        ∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) *
              ‖iteratedFDeriv ℝ p (fun y : ℝ => -Real.cosh y) x‖ *
              ‖iteratedFDeriv ℝ (m - p) D x‖
            ≤ ∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) *
              ((∑ q ∈ Finset.range (m + 2), K q) *
                (Real.exp ((j + 1 : ℝ) * |x|) * S)) := Finset.sum_le_sum hterm
        _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ)) *
              (∑ q ∈ Finset.range (m + 2), K q) *
              (Real.exp ((j + 1 : ℝ) * |x|) * S) := by
              rw [← Finset.sum_mul]
              ring
        _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ)) *
              (∑ q ∈ Finset.range (m + 2), K q) *
              Real.exp (((j : ℝ) + 1) * |x|) * S := by ring
        _ = (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ)) *
              (∑ q ∈ Finset.range (m + 2), K q) *
              Real.exp (((j + 1 : ℕ) : ℝ) * |x|) * S := by push_cast; ring

/-- [T26], proof of Lemma 3.4; the case of the previous bound used for the `C^N` seminorms. -/
theorem exists_norm_iteratedDeriv_boostChart_le (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w v : ℝ → ℂ, ContDiff ℝ ∞ w → ContDiff ℝ ∞ v →
      (∀ y : ℝ, w (boostToAngle y) = v y) → ∀ x : ℝ,
        ‖iteratedDeriv j w (boostToAngle x)‖ ≤
          K * Real.exp ((j : ℝ) * |x|) *
            ∑ i ∈ Finset.range (j + 1), ‖iteratedDeriv i v x‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_boostChart j 0
  refine ⟨K, hK0, ?_⟩
  intro w v hw hv hwv x
  simpa using hK w v hw hv hwv x

end

end MobiusCPT
