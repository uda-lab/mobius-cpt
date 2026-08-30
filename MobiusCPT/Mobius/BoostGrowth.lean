import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import MobiusCPT.Mobius.BoostPBounds

/-!
# Exponential growth of boosted test functions

This file completes the quantitative part of [T26], Lemma 3.8.  All constants below are
deliberately crude: only uniformity in the angle and exponential dependence on the boost
parameter are needed by the Wightman-functional argument.
-/

namespace MobiusCPT

noncomputable section

open scoped ContDiff

/-! ### The boost in real-angle coordinates -/

theorem toAngle_beta_boost_eq (t : ℝ) (d : ℕ) (f : TestFn) (θ : ℝ) :
    toAngle (Mob.beta d (Mob.boost t) f) θ =
      ((boostP t θ ^ ((d : ℤ) - 1) : ℝ) : ℂ) * toAngle f (boostAngle t θ) := by
  rw [toAngle, Mob.beta_boost_apply, Mob.boost, Mob.mk_smul,
    ← circleExp_boostAngle' t θ]
  rfl

/-- The integer power in the boost multiplier is a natural power times one reciprocal. -/
private theorem boostP_zpow_sub_one_eq (t : ℝ) (d : ℕ) (θ : ℝ) :
    boostP t θ ^ ((d : ℤ) - 1) = boostP t θ ^ d * (boostP t θ)⁻¹ := by
  exact zpow_sub_one₀ (boostP_pos t θ).ne' d

/-- The zeroth derivative of `boostP` obeys the same exponential scale as its higher
derivatives, up to the harmless factor two. -/
private theorem boostP_le_two_mul_exp_abs (t θ : ℝ) :
    boostP t θ ≤ 2 * Real.exp |t| := by
  have hcosh : Real.cosh t ≤ Real.exp |t| := by
    rw [← Real.cosh_abs t, ← Real.sinh_add_cosh]
    exact le_add_of_nonneg_left (Real.sinh_nonneg_iff.mpr (abs_nonneg t))
  calc
    boostP t θ = Real.cosh t + Real.sinh t * Real.cos θ := boostP_eq t θ
    _ ≤ Real.cosh t + |Real.sinh t * Real.cos θ| := by
      linarith [le_abs_self (Real.sinh t * Real.cos θ)]
    _ = Real.cosh t + |Real.sinh t| * |Real.cos θ| := by rw [abs_mul]
    _ ≤ Real.cosh t + |Real.sinh t| := by
      nlinarith [Real.abs_cos_le_one θ, abs_nonneg (Real.sinh t)]
    _ ≤ Real.exp |t| + Real.exp |t| :=
      add_le_add hcosh (abs_sinh_le_exp_abs t)
    _ = 2 * Real.exp |t| := by ring

/-- Differentiating the reciprocal of `boostP` is the same as taking one more derivative of
`boostAngle`. -/
private theorem iteratedDeriv_boostP_inv_eq (t : ℝ) (m : ℕ) (θ : ℝ) :
    iteratedDeriv m (fun x => (boostP t x)⁻¹) θ =
      iteratedDeriv (m + 1) (boostAngle t) θ := by
  rw [iteratedDeriv_succ']
  congr 1
  funext x
  exact (hasDerivAt_boostAngle t x).deriv.symm

/-! ### Coarse constants and elementary product bookkeeping -/

private def powerC (N d : ℕ) : ℝ :=
  (Nat.factorial N : ℝ) * (d + 1 : ℝ) ^ N * 2 ^ d

private def powerRate (N d : ℕ) : ℝ := d + N

private def inverseC (N : ℕ) : ℝ := (Nat.factorial N : ℝ) ^ 2

private def inverseRate (N : ℕ) : ℝ := 2 * N + 1

private def prefactorC (N d : ℕ) : ℝ :=
  2 ^ N * powerC N d * inverseC N

private def prefactorRate (N d : ℕ) : ℝ :=
  powerRate N d + inverseRate N

private def pullbackC (N : ℕ) : ℝ :=
  (Nat.factorial N : ℝ) * (inverseC N + 1) ^ N

private def pullbackRate (N : ℕ) : ℝ := N * inverseRate N

private theorem powerC_pos (N d : ℕ) : 0 < powerC N d := by
  dsimp [powerC]
  have hfac : 0 < (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  exact mul_pos (mul_pos hfac (pow_pos (by positivity) N))
    (pow_pos (by norm_num) d)

private theorem inverseC_pos (N : ℕ) : 0 < inverseC N := by
  dsimp [inverseC]
  exact pow_pos (by exact_mod_cast Nat.factorial_pos N) 2

private theorem prefactorC_pos (N d : ℕ) : 0 < prefactorC N d := by
  dsimp [prefactorC]
  exact mul_pos (mul_pos (pow_pos (by norm_num) N) (powerC_pos N d))
    (inverseC_pos N)

private theorem pullbackC_pos (N : ℕ) : 0 < pullbackC N := by
  dsimp [pullbackC]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos N)
    (pow_pos (add_pos (inverseC_pos N) (by norm_num)) N)

/-- A uniform version of Leibniz' estimate. -/
private theorem norm_iteratedFDeriv_mul_le_uniform
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {u v : ℝ → A} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (m : ℕ) (x C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (huC : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i u x‖ ≤ C)
    (hvD : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i v x‖ ≤ D) :
    ‖iteratedFDeriv ℝ m (fun y => u y * v y) x‖ ≤ 2 ^ m * C * D := by
  calc
    ‖iteratedFDeriv ℝ m (fun y => u y * v y) x‖ ≤
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (m - i) v x‖ :=
      norm_iteratedFDeriv_mul_le hu hv x (by exact_mod_cast le_top)
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C * D := by
      gcongr with i hi
      · exact huC i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      · exact hvD (m - i) (Nat.sub_le _ _)
    _ = 2 ^ m * C * D := by
      simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose,
        Nat.cast_pow, Nat.cast_ofNat]

/-! ### Bounds for the scalar prefactor -/

/-- Step 2 uses the composition estimate for the natural power (rather than induction on `d`). -/
private theorem norm_iteratedFDeriv_boostP_pow_le
    (N d m : ℕ) (hm : m ≤ N) (t θ : ℝ) :
    ‖iteratedFDeriv ℝ m (fun x => boostP t x ^ d) θ‖ ≤
      powerC N d * Real.exp (powerRate N d * |t|) := by
  have houter : ContDiff ℝ ∞ (fun y : ℝ => y ^ d) := contDiff_id.pow d
  have hC : ∀ i, i ≤ m →
      ‖iteratedFDeriv ℝ i (fun y : ℝ => y ^ d) (boostP t θ)‖ ≤
        (d + 1 : ℝ) ^ N * (2 * Real.exp |t|) ^ d := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (pow_nonneg (boostP_pos t θ).le _)]
    have hdesc : (d.descFactorial i : ℝ) ≤ (d + 1 : ℝ) ^ N := by
      norm_cast
      calc
        d.descFactorial i ≤ d ^ i := Nat.descFactorial_le_pow d i
        _ ≤ (d + 1) ^ i := by
          gcongr
          omega
        _ ≤ (d + 1) ^ N := by
          exact pow_le_pow_right₀ (by omega) (hi.trans hm)
    have hpow : boostP t θ ^ (d - i) ≤ (2 * Real.exp |t|) ^ d := by
      calc
        boostP t θ ^ (d - i) ≤ (2 * Real.exp |t|) ^ (d - i) := by
          exact pow_le_pow_left₀ (boostP_pos t θ).le (boostP_le_two_mul_exp_abs t θ) _
        _ ≤ (2 * Real.exp |t|) ^ d := by
          apply pow_le_pow_right₀
          · have : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
            nlinarith
          · omega
    exact mul_le_mul hdesc hpow (pow_nonneg (boostP_pos t θ).le _) (by positivity)
  have hD : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i (boostP t) θ‖ ≤ Real.exp |t| ^ i := by
    intro i hi _
    have hieq : i = (i - 1) + 1 := by omega
    calc
      ‖iteratedFDeriv ℝ i (boostP t) θ‖ = ‖iteratedDeriv i (boostP t) θ‖ :=
        norm_iteratedFDeriv_eq_norm_iteratedDeriv
      _ ≤ Real.exp |t| := by
        rw [hieq]
        exact norm_iteratedDeriv_boostP_le t (i - 1) θ
      _ ≤ Real.exp |t| ^ i :=
        le_self_pow₀ (Real.one_le_exp (abs_nonneg t)) (Nat.ne_of_gt hi)
  have hcomp := norm_iteratedFDeriv_comp_le houter (contDiff_boostP t)
    (by exact_mod_cast le_top) θ hC hD
  change ‖iteratedFDeriv ℝ m ((fun y : ℝ => y ^ d) ∘ boostP t) θ‖ ≤ _ at hcomp
  calc
    ‖iteratedFDeriv ℝ m (fun x => boostP t x ^ d) θ‖ ≤
        (Nat.factorial m : ℝ) *
          ((d + 1 : ℝ) ^ N * (2 * Real.exp |t|) ^ d) * Real.exp |t| ^ m := hcomp
    _ ≤ powerC N d * Real.exp (powerRate N d * |t|) := by
      have hfac : (Nat.factorial m : ℝ) ≤ (Nat.factorial N : ℝ) := by
        exact_mod_cast Nat.factorial_le hm
      have hexp : Real.exp ((d : ℝ) * |t|) * Real.exp ((m : ℝ) * |t|) ≤
          Real.exp (((d : ℝ) + N) * |t|) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp_of_le
        have hm' : (m : ℝ) ≤ N := by exact_mod_cast hm
        nlinarith [abs_nonneg t]
      rw [powerC, powerRate, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      calc
        (Nat.factorial m : ℝ) *
              ((d + 1 : ℝ) ^ N * (2 ^ d * Real.exp ((d : ℝ) * |t|))) *
              Real.exp ((m : ℝ) * |t|) =
            (Nat.factorial m : ℝ) * (d + 1 : ℝ) ^ N * 2 ^ d *
              (Real.exp ((d : ℝ) * |t|) * Real.exp ((m : ℝ) * |t|)) := by ring
        _ ≤ (Nat.factorial N : ℝ) * (d + 1 : ℝ) ^ N * 2 ^ d *
              Real.exp (((d : ℝ) + N) * |t|) := by gcongr

private theorem norm_iteratedFDeriv_boostP_inv_le
    (N m : ℕ) (hm : m ≤ N) (t θ : ℝ) :
    ‖iteratedFDeriv ℝ m (fun x => (boostP t x)⁻¹) θ‖ ≤
      inverseC N * Real.exp (inverseRate N * |t|) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_boostP_inv_eq]
  calc
    ‖iteratedDeriv (m + 1) (boostAngle t) θ‖ ≤
        (Nat.factorial m : ℝ) ^ 2 *
          Real.exp (((m + 1 : ℕ) : ℝ) * |t| + (m : ℝ) * |t|) :=
      norm_iteratedDeriv_boostAngle_le t m θ
    _ ≤ inverseC N * Real.exp (inverseRate N * |t|) := by
      have hfac : (Nat.factorial m : ℝ) ^ 2 ≤ (Nat.factorial N : ℝ) ^ 2 := by
        gcongr
      have hexp : Real.exp (((m + 1 : ℕ) : ℝ) * |t| + (m : ℝ) * |t|) ≤
          Real.exp (inverseRate N * |t|) := by
        apply Real.exp_le_exp_of_le
        simp only [inverseRate]
        have hm' : (m : ℝ) ≤ N := by exact_mod_cast hm
        push_cast
        nlinarith [abs_nonneg t]
      exact mul_le_mul hfac hexp (Real.exp_nonneg _) (sq_nonneg _)

private def boostPrefactor (t : ℝ) (d : ℕ) : ℝ → ℝ :=
  fun θ => boostP t θ ^ d * (boostP t θ)⁻¹

private theorem contDiff_boostPrefactor (t : ℝ) (d : ℕ) :
    ContDiff ℝ ∞ (boostPrefactor t d) := by
  exact ((contDiff_boostP t).pow d).mul
    ((contDiff_boostP t).inv (fun θ => (boostP_pos t θ).ne'))

private theorem norm_iteratedFDeriv_boostPrefactor_le
    (N d m : ℕ) (hm : m ≤ N) (t θ : ℝ) :
    ‖iteratedFDeriv ℝ m (boostPrefactor t d) θ‖ ≤
      prefactorC N d * Real.exp (prefactorRate N d * |t|) := by
  have hmul := norm_iteratedFDeriv_mul_le_uniform
    ((contDiff_boostP t).pow d)
    ((contDiff_boostP t).inv (fun x => (boostP_pos t x).ne')) m θ
    (powerC N d * Real.exp (powerRate N d * |t|))
    (inverseC N * Real.exp (inverseRate N * |t|))
    (mul_nonneg (powerC_pos N d).le (Real.exp_nonneg _))
    (mul_nonneg (inverseC_pos N).le (Real.exp_nonneg _))
    (fun i hi => norm_iteratedFDeriv_boostP_pow_le N d i (hi.trans hm) t θ)
    (fun i hi => norm_iteratedFDeriv_boostP_inv_le N i (hi.trans hm) t θ)
  change ‖iteratedFDeriv ℝ m (boostPrefactor t d) θ‖ ≤ _ at hmul
  calc
    ‖iteratedFDeriv ℝ m (boostPrefactor t d) θ‖ ≤
        2 ^ m * (powerC N d * Real.exp (powerRate N d * |t|)) *
          (inverseC N * Real.exp (inverseRate N * |t|)) := hmul
    _ ≤ prefactorC N d * Real.exp (prefactorRate N d * |t|) := by
      have htwo : (2 : ℝ) ^ m ≤ 2 ^ N := by
        gcongr
        norm_num
      calc
        2 ^ m * (powerC N d * Real.exp (powerRate N d * |t|)) *
              (inverseC N * Real.exp (inverseRate N * |t|)) =
            2 ^ m * powerC N d * inverseC N *
              Real.exp ((powerRate N d + inverseRate N) * |t|) := by
          rw [show (powerRate N d + inverseRate N) * |t| =
            powerRate N d * |t| + inverseRate N * |t| by ring, Real.exp_add]
          ring
        _ ≤ 2 ^ N * powerC N d * inverseC N *
              Real.exp ((powerRate N d + inverseRate N) * |t|) := by
          gcongr
          all_goals first
            | exact htwo
            | exact (powerC_pos N d).le
            | exact (inverseC_pos N).le
        _ = prefactorC N d * Real.exp (prefactorRate N d * |t|) := by
          rw [prefactorC, prefactorRate]

/-! ### The composed test function -/

private theorem norm_angleDeriv_le_cnorm {i N : ℕ} (hi : i ≤ N) (f : TestFn) (x : ℝ) :
    ‖angleDeriv i f x‖ ≤ (cnorm N f : ℝ) := by
  rw [cnorm_eq]
  exact (norm_angleDeriv_le i f x).trans
    (Finset.single_le_sum (fun j _ => norm_nonneg (angleDerivB j f))
      (by simp only [Finset.mem_range]; omega))

private theorem norm_iteratedFDeriv_boostAngle_le_uniform
    (N i : ℕ) (hi0 : 1 ≤ i) (hiN : i ≤ N) (t θ : ℝ) :
    ‖iteratedFDeriv ℝ i (boostAngle t) θ‖ ≤
      inverseC N * Real.exp (inverseRate N * |t|) := by
  have hieq : i = (i - 1) + 1 := by omega
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hieq]
  calc
    ‖iteratedDeriv ((i - 1) + 1) (boostAngle t) θ‖ ≤
        (Nat.factorial (i - 1) : ℝ) ^ 2 *
          Real.exp ((((i - 1) + 1 : ℕ) : ℝ) * |t| + ((i - 1 : ℕ) : ℝ) * |t|) :=
      norm_iteratedDeriv_boostAngle_le t (i - 1) θ
    _ ≤ inverseC N * Real.exp (inverseRate N * |t|) := by
      have hsub : i - 1 ≤ N := (Nat.sub_le i 1).trans hiN
      have hfac : (Nat.factorial (i - 1) : ℝ) ^ 2 ≤
          (Nat.factorial N : ℝ) ^ 2 := by
        gcongr
      have hexp : Real.exp ((((i - 1) + 1 : ℕ) : ℝ) * |t| +
            ((i - 1 : ℕ) : ℝ) * |t|) ≤ Real.exp (inverseRate N * |t|) := by
        apply Real.exp_le_exp_of_le
        simp only [inverseRate]
        have hi' : (i : ℝ) ≤ N := by exact_mod_cast hiN
        have hsub' : ((i - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hsub
        push_cast
        have hcoef : ((i - 1 : ℕ) : ℝ) + 1 + ((i - 1 : ℕ) : ℝ) ≤
            2 * (N : ℝ) + 1 := by
          nlinarith [hsub']
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg t)
      exact mul_le_mul hfac hexp (Real.exp_nonneg _) (sq_nonneg _)

private theorem norm_iteratedFDeriv_pullback_le
    (N m : ℕ) (hm : m ≤ N) (t : ℝ) (f : TestFn) (θ : ℝ) :
    ‖iteratedFDeriv ℝ m (toAngle f ∘ boostAngle t) θ‖ ≤
      pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ) := by
  let D : ℝ := inverseC N * Real.exp (inverseRate N * |t|) + 1
  have houter : ∀ i, i ≤ m →
      ‖iteratedFDeriv ℝ i (toAngle f) (boostAngle t θ)‖ ≤ (cnorm N f : ℝ) := by
    intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖angleDeriv i f (boostAngle t θ)‖ ≤ (cnorm N f : ℝ)
    exact norm_angleDeriv_le_cnorm (hi.trans hm) f (boostAngle t θ)
  have hDinner : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i (boostAngle t) θ‖ ≤ D ^ i := by
    intro i hi0 him
    have hbase : ‖iteratedFDeriv ℝ i (boostAngle t) θ‖ ≤ D := by
      exact (norm_iteratedFDeriv_boostAngle_le_uniform N i hi0 (him.trans hm) t θ).trans
        (le_add_of_nonneg_right zero_le_one)
    have hDone : (1 : ℝ) ≤ D := by
      dsimp [D]
      exact le_add_of_nonneg_left
        (mul_nonneg (inverseC_pos N).le (Real.exp_nonneg _))
    exact hbase.trans (le_self_pow₀ hDone (Nat.ne_of_gt hi0))
  have hcomp := norm_iteratedFDeriv_comp_le (contDiff_toAngle f) (contDiff_boostAngle t)
    (by exact_mod_cast le_top) θ houter hDinner
  calc
    ‖iteratedFDeriv ℝ m (toAngle f ∘ boostAngle t) θ‖ ≤
        (Nat.factorial m : ℝ) * (cnorm N f : ℝ) * D ^ m := hcomp
    _ ≤ pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ) := by
      have hfac : (Nat.factorial m : ℝ) ≤ (Nat.factorial N : ℝ) := by
        exact_mod_cast Nat.factorial_le hm
      have hrate : 0 ≤ inverseRate N := by
        dsimp [inverseRate]
        positivity
      have hD : D ≤ (inverseC N + 1) * Real.exp (inverseRate N * |t|) := by
        dsimp only [D]
        have he : 1 ≤ Real.exp (inverseRate N * |t|) := by
          apply Real.one_le_exp
          exact mul_nonneg hrate (abs_nonneg t)
        nlinarith [inverseC_pos N]
      have hbaseone : 1 ≤ (inverseC N + 1) * Real.exp (inverseRate N * |t|) := by
        exact one_le_mul_of_one_le_of_one_le (by nlinarith [inverseC_pos N])
          (Real.one_le_exp (mul_nonneg hrate (abs_nonneg t)))
      have hpow : D ^ m ≤
          (inverseC N + 1) ^ N * Real.exp (pullbackRate N * |t|) := by
        calc
          D ^ m ≤ ((inverseC N + 1) * Real.exp (inverseRate N * |t|)) ^ m := by
            have hDnonneg : 0 ≤ D := by
              dsimp [D]
              exact add_nonneg
                (mul_nonneg (inverseC_pos N).le (Real.exp_nonneg _)) zero_le_one
            exact pow_le_pow_left₀ hDnonneg hD m
          _ ≤ ((inverseC N + 1) * Real.exp (inverseRate N * |t|)) ^ N :=
            pow_le_pow_right₀ hbaseone hm
          _ = (inverseC N + 1) ^ N * Real.exp (pullbackRate N * |t|) := by
            rw [mul_pow, ← Real.exp_nat_mul]
            simp only [pullbackRate, inverseRate]
            congr 2
            ring
      calc
        (Nat.factorial m : ℝ) * (cnorm N f : ℝ) * D ^ m =
            (Nat.factorial m : ℝ) * D ^ m * (cnorm N f : ℝ) := by ring
        _ ≤ (Nat.factorial N : ℝ) *
              ((inverseC N + 1) ^ N * Real.exp (pullbackRate N * |t|)) *
                (cnorm N f : ℝ) := by
          gcongr
          exact pow_nonneg (by
            dsimp [D]
            exact add_nonneg
              (mul_nonneg (inverseC_pos N).le (Real.exp_nonneg _)) zero_le_one) m
        _ = pullbackC N * Real.exp (pullbackRate N * |t|) *
              (cnorm N f : ℝ) := by rw [pullbackC]; ring

/-! ### Assembly -/

private theorem norm_iteratedFDeriv_boost_le
    (N d m : ℕ) (hm : m ≤ N) (t : ℝ) (f : TestFn) (θ : ℝ) :
    ‖iteratedFDeriv ℝ m (toAngle (Mob.beta d (Mob.boost t) f)) θ‖ ≤
      2 ^ N * prefactorC N d * pullbackC N *
        Real.exp ((prefactorRate N d + pullbackRate N) * |t|) * (cnorm N f : ℝ) := by
  have hfun : toAngle (Mob.beta d (Mob.boost t) f) =
      fun x => ((boostPrefactor t d x : ℝ) : ℂ) * (toAngle f ∘ boostAngle t) x := by
    funext x
    rw [toAngle_beta_boost_eq, boostP_zpow_sub_one_eq]
    rfl
  rw [hfun]
  have hprefComplex : ContDiff ℝ ∞ (fun x => ((boostPrefactor t d x : ℝ) : ℂ)) :=
    Complex.ofRealLI.contDiff.comp (contDiff_boostPrefactor t d)
  have hpref : ∀ i, i ≤ m →
      ‖iteratedFDeriv ℝ i (fun x => ((boostPrefactor t d x : ℝ) : ℂ)) θ‖ ≤
        prefactorC N d * Real.exp (prefactorRate N d * |t|) := by
    intro i hi
    rw [show (fun x => ((boostPrefactor t d x : ℝ) : ℂ)) =
      Complex.ofRealLI ∘ boostPrefactor t d by rfl]
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (contDiff_boostPrefactor t d).contDiffAt (by exact_mod_cast le_top)]
    exact norm_iteratedFDeriv_boostPrefactor_le N d i (hi.trans hm) t θ
  have hpull : ∀ i, i ≤ m →
      ‖iteratedFDeriv ℝ i (toAngle f ∘ boostAngle t) θ‖ ≤
        pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ) :=
    fun i hi => norm_iteratedFDeriv_pullback_le N i (hi.trans hm) t f θ
  have hmul := norm_iteratedFDeriv_mul_le_uniform hprefComplex
    ((contDiff_toAngle f).comp (contDiff_boostAngle t)) m θ
    (prefactorC N d * Real.exp (prefactorRate N d * |t|))
    (pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ))
    (mul_nonneg (prefactorC_pos N d).le (Real.exp_nonneg _))
    (mul_nonneg (mul_nonneg (pullbackC_pos N).le (Real.exp_nonneg _))
      (NNReal.coe_nonneg (cnorm N f)))
    hpref hpull
  calc
    ‖iteratedFDeriv ℝ m
        (fun x => ((boostPrefactor t d x : ℝ) : ℂ) * (toAngle f ∘ boostAngle t) x) θ‖ ≤
        2 ^ m * (prefactorC N d * Real.exp (prefactorRate N d * |t|)) *
          (pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ)) := hmul
    _ ≤ 2 ^ N * prefactorC N d * pullbackC N *
          Real.exp ((prefactorRate N d + pullbackRate N) * |t|) *
            (cnorm N f : ℝ) := by
      have htwo : (2 : ℝ) ^ m ≤ 2 ^ N := by
        gcongr
        norm_num
      calc
        2 ^ m * (prefactorC N d * Real.exp (prefactorRate N d * |t|)) *
              (pullbackC N * Real.exp (pullbackRate N * |t|) * (cnorm N f : ℝ)) =
            2 ^ m * prefactorC N d * pullbackC N *
              Real.exp ((prefactorRate N d + pullbackRate N) * |t|) *
                (cnorm N f : ℝ) := by
          rw [show (prefactorRate N d + pullbackRate N) * |t| =
            prefactorRate N d * |t| + pullbackRate N * |t| by ring, Real.exp_add]
          ring
        _ ≤ 2 ^ N * prefactorC N d * pullbackC N *
              Real.exp ((prefactorRate N d + pullbackRate N) * |t|) *
                (cnorm N f : ℝ) := by
          gcongr
          · exact (pullbackC_pos N).le
          · exact (prefactorC_pos N d).le

theorem cnorm_boost_le (N d : ℕ) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (t : ℝ) (f : TestFn),
        (cnorm N (Mob.beta d (Mob.boost t) f) : ℝ) ≤
          A * Real.exp (a * |t|) * (cnorm N f : ℝ) := by
  let A : ℝ := (N + 1) * 2 ^ N * prefactorC N d * pullbackC N
  let a : ℝ := prefactorRate N d + pullbackRate N
  have hA : 0 < A := by
    dsimp only [A]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact mul_pos (mul_pos (mul_pos hN (pow_pos (by norm_num) N))
      (prefactorC_pos N d)) (pullbackC_pos N)
  have ha : 0 < a := by
    dsimp only [a, prefactorRate, powerRate, inverseRate, pullbackRate]
    positivity
  refine ⟨A, a, hA, ha, ?_⟩
  intro t f
  rw [cnorm_eq]
  have hterm : ∀ m ∈ Finset.range (N + 1),
      ‖angleDerivB m (Mob.beta d (Mob.boost t) f)‖ ≤
        2 ^ N * prefactorC N d * pullbackC N * Real.exp (a * |t|) *
          (cnorm N f : ℝ) := by
    intro m hm
    have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hbound : 0 ≤ (2 : ℝ) ^ N * prefactorC N d * pullbackC N *
        Real.exp (a * |t|) * (cnorm N f : ℝ) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (pow_nonneg (by norm_num) N) (prefactorC_pos N d).le)
            (pullbackC_pos N).le)
          (Real.exp_nonneg _))
        (NNReal.coe_nonneg (cnorm N f))
    apply (BoundedContinuousFunction.norm_le hbound).2
    intro θ
    rw [angleDerivB_apply, angleDeriv]
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simpa only [a] using norm_iteratedFDeriv_boost_le N d m hmN t f θ
  calc
    ∑ m ∈ Finset.range (N + 1), ‖angleDerivB m (Mob.beta d (Mob.boost t) f)‖ ≤
        ∑ _m ∈ Finset.range (N + 1),
          (2 ^ N * prefactorC N d * pullbackC N * Real.exp (a * |t|) *
            (cnorm N f : ℝ)) := Finset.sum_le_sum hterm
    _ = A * Real.exp (a * |t|) * (cnorm N f : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, A]
      push_cast
      ring

end

end MobiusCPT
