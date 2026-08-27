import Mathlib

/-!
# Flat gluing

Auxiliary real-analysis lemmas for the endpoint-flat test-function constructions used in [T26],
§3.  The statements in this file are elementary gluing results rather than numbered results in
the paper itself.
-/

namespace MobiusCPT

open Filter TopologicalSpace Set
open scoped ContDiff Topology

/-- `g` cut off to `[a, ∞)`: equal to `g` there and `0` to the left of `a`. -/
noncomputable def stepRight (a : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if a ≤ x then g x else 0

/-- Evaluation of `stepRight` on its retained half-line. -/
theorem stepRight_of_le {a x : ℝ} (g : ℝ → ℂ) (h : a ≤ x) : stepRight a g x = g x := by
  simp [stepRight, h]

/-- Evaluation of `stepRight` on the half-line where it is cut off. -/
theorem stepRight_of_lt {a x : ℝ} (g : ℝ → ℂ) (h : x < a) : stepRight a g x = 0 := by
  simp [stepRight, not_le.mpr h]

private theorem hasDerivAt_stepRight {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ j : ℕ, iteratedDeriv j g a = 0) (x : ℝ) :
    HasDerivAt (stepRight a g) (stepRight a (deriv g) x) x := by
  have h0g : g a = 0 := by
    have h := h0 0
    simpa only [iteratedDeriv_zero] using h
  have hga : deriv g a = 0 := by
    have h := h0 1
    simpa only [iteratedDeriv_one] using h
  rcases lt_trichotomy x a with hxa | rfl | hax
  · rw [stepRight_of_lt (deriv g) hxa]
    refine (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Iio_mem_nhds hxa) fun y hy =>
      stepRight_of_lt g hy
  · rw [stepRight_of_le (deriv g) le_rfl, hga]
    apply hasDerivAt_iff_tendsto_slope_left_right.mpr
    constructor
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_module, stepRight_of_lt g hy, stepRight_of_le g le_rfl, h0g]
      simp
    · have hg' : HasDerivAt g (deriv g x) x :=
        ((hg.differentiable (by simp)) x).hasDerivAt
      have hs : Tendsto (slope (stepRight x g) x) (𝓝[>] x) (𝓝 (deriv g x)) := by
        refine (hg'.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [slope_def_module, slope_def_module, stepRight_of_le g hy.le,
          stepRight_of_le g le_rfl]
      simpa [hga] using hs
  · rw [stepRight_of_le (deriv g) hax.le]
    refine (((hg.differentiable (by simp)) x).hasDerivAt).congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds hax) fun y hy =>
      stepRight_of_le g hy.le

/-- Differentiating an endpoint-flat right cutoff differentiates the retained function. -/
theorem deriv_stepRight {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ j : ℕ, iteratedDeriv j g a = 0) :
    deriv (stepRight a g) = stepRight a (deriv g) := by
  funext x
  exact (hasDerivAt_stepRight hg h0 x).deriv

/-- An endpoint-flat right cutoff of a smooth function is smooth. -/
theorem contDiff_stepRight {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ j : ℕ, iteratedDeriv j g a = 0) :
    ContDiff ℝ ∞ (stepRight a g) := by
  have hfinite : ∀ n : ℕ, ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      (∀ j : ℕ, iteratedDeriv j f a = 0) → ContDiff ℝ n (stepRight a f) := by
    intro n
    induction n with
    | zero =>
        intro f hf hf0
        change ContDiff ℝ (0 : ℕ∞ω) (stepRight a f)
        rw [contDiff_zero]
        apply continuous_iff_continuousAt.mpr
        intro x
        rcases lt_trichotomy x a with hxa | rfl | hax
        · have hconst : ContinuousAt (fun _ : ℝ => (0 : ℂ)) x := continuousAt_const
          refine hconst.congr_of_eventuallyEq ?_
          exact Filter.eventuallyEq_of_mem (Iio_mem_nhds hxa) fun y hy =>
            stepRight_of_lt f hy
        · exact (hasDerivAt_stepRight hf hf0 x).continuousAt
        · refine hf.continuous.continuousAt.congr_of_eventuallyEq ?_
          exact Filter.eventuallyEq_of_mem (Ioi_mem_nhds hax) fun y hy =>
            stepRight_of_le f hy.le
    | succ n ih =>
        intro f hf hf0
        have hdiff : Differentiable ℝ (stepRight a f) := fun x =>
          (hasDerivAt_stepRight hf hf0 x).differentiableAt
        have hderiv : ContDiff ℝ (n : ℕ∞ω) (deriv (stepRight a f)) := by
          rw [deriv_stepRight hf hf0]
          exact ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2 (by
            intro j
            have hj := hf0 (j + 1)
            rw [iteratedDeriv_succ'] at hj
            exact hj)
        have hs : ContDiff ℝ ((n : ℕ∞ω) + 1) (stepRight a f) :=
          contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, hderiv⟩
        simpa only [Nat.cast_succ] using hs
  exact contDiff_infty.mpr (fun n => hfinite n g hg h0)

/-- The endpoint-flat right cutoff commutes with all iterated derivatives. -/
theorem iteratedDeriv_stepRight {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (h0 : ∀ j : ℕ, iteratedDeriv j g a = 0) (n : ℕ) :
    iteratedDeriv n (stepRight a g) = stepRight a (iteratedDeriv n g) := by
  have haux : ∀ n : ℕ, ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      (∀ j : ℕ, iteratedDeriv j f a = 0) →
        iteratedDeriv n (stepRight a f) = stepRight a (iteratedDeriv n f) := by
    intro n
    induction n with
    | zero =>
        intro f hf hf0
        simp only [iteratedDeriv_zero]
    | succ n ih =>
        intro f hf hf0
        calc
          iteratedDeriv (n + 1) (stepRight a f) =
              iteratedDeriv n (deriv (stepRight a f)) := iteratedDeriv_succ'
          _ = iteratedDeriv n (stepRight a (deriv f)) := by rw [deriv_stepRight hf hf0]
          _ = stepRight a (iteratedDeriv n (deriv f)) :=
            ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2 (by
              intro j
              have hj := hf0 (j + 1)
              rw [iteratedDeriv_succ'] at hj
              exact hj)
          _ = stepRight a (iteratedDeriv (n + 1) f) := by rw [iteratedDeriv_succ']
  exact haux n g hg h0

/-- `g` cut off to `[a, b]`. -/
noncomputable def cutIcc (a b : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => if x ∈ Set.Icc a b then g x else 0

/-- Evaluation of `cutIcc` off its closed interval. -/
theorem cutIcc_eq_zero_of_notMem {a b x : ℝ} (g : ℝ → ℂ) (h : x ∉ Set.Icc a b) :
    cutIcc a b g x = 0 := by
  simp [cutIcc, h]

/-- Evaluation of `cutIcc` on its closed interval. -/
theorem cutIcc_eq_of_mem {a b x : ℝ} (g : ℝ → ℂ) (h : x ∈ Set.Icc a b) :
    cutIcc a b g x = g x := by
  simp [cutIcc, h]

/-- Cutting a smooth function to an interval preserves smoothness when both endpoints are flat. -/
theorem contDiff_cutIcc {a b : ℝ} {g : ℝ → ℂ} (hab : a ≤ b) (hg : ContDiff ℝ ∞ g)
    (ha : ∀ j : ℕ, iteratedDeriv j g a = 0) (hb : ∀ j : ℕ, iteratedDeriv j g b = 0) :
    ContDiff ℝ ∞ (cutIcc a b g) := by
  have hgb : g b = 0 := by
    have h := hb 0
    simpa only [iteratedDeriv_zero] using h
  have hcut : cutIcc a b g = stepRight a g - stepRight b g := by
    funext x
    by_cases hax : a ≤ x
    · by_cases hbx : b ≤ x
      · by_cases hxb : x = b
        · subst x
          simp [cutIcc, stepRight, hab, hgb]
        · have hlt : b < x := lt_of_le_of_ne hbx fun h => hxb h.symm
          have hnot : x ∉ Set.Icc a b := fun hx => (not_lt_of_ge hx.2) hlt
          simp [cutIcc, stepRight, hax, hbx, hnot]
      · have hxb : x < b := lt_of_not_ge hbx
        have hmem : x ∈ Set.Icc a b := ⟨hax, hxb.le⟩
        simp [cutIcc, stepRight, hax, hbx, hmem]
    · have hxa : x < a := lt_of_not_ge hax
      have hxb : x < b := hxa.trans_le hab
      have hbx : ¬b ≤ x := not_le_of_gt hxb
      have hnot : x ∉ Set.Icc a b := fun hx => (not_lt_of_ge hx.1) hxa
      simp [cutIcc, stepRight, hax, hbx, hnot]
  rw [hcut]
  exact (contDiff_stepRight hg ha).sub (contDiff_stepRight hg hb)

/-- The `T`-periodic extension of `h`, for `h` vanishing outside `[0, T]`. -/
noncomputable def periodize (T : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => h (x - T * ⌊x / T⌋)

/-- `periodize T h` is periodic with period `T`. -/
theorem periodic_periodize (T : ℝ) (hT : 0 < T) (h : ℝ → ℂ) :
    Function.Periodic (periodize T h) T := by
  intro x
  have hdiv : (x + T) / T = x / T + 1 := by
    rw [add_div, div_self hT.ne']
  simp only [periodize]
  rw [hdiv, Int.floor_add_one, Int.cast_add, Int.cast_one]
  congr 1
  ring

/-- On the half-open period interval, `periodize` agrees with the original function. -/
theorem periodize_eq_self {T : ℝ} (hT : 0 < T) {h : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ Set.Ico 0 T) : periodize T h x = h x := by
  have hxdiv : x / T ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hx.1 hT.le
    · exact (div_lt_iff₀ hT).2 (by simpa using hx.2)
  have hfloor : ⌊x / T⌋ = 0 := Int.floor_eq_zero_iff.mpr hxdiv
  simp [periodize, hfloor]

/-- A smooth function supported in `(0, T)` periodizes to a smooth function. -/
theorem contDiff_periodize {T : ℝ} (hT : 0 < T) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∀ x : ℝ, x ∉ Set.Ioo 0 T → h x = 0) :
    ContDiff ℝ ∞ (periodize T h) := by
  have flat_left : ∀ f : ℝ → ℂ, (∀ x : ℝ, x ≤ 0 → f x = 0) →
      ∀ j : ℕ, ∀ x : ℝ, x ≤ 0 → iteratedDeriv j f x = 0 := by
    intro f hf j
    induction j with
    | zero =>
        intro x hx
        simpa only [iteratedDeriv_zero] using hf x hx
    | succ j ih =>
        intro x hx
        by_cases hxlt : x < 0
        · have heq : Set.EqOn (iteratedDeriv j f) (fun _ : ℝ => (0 : ℂ)) (Iio 0) := by
            intro y hy
            exact ih y hy.le
          have hderiv := heq.deriv isOpen_Iio
          rw [iteratedDeriv_succ]
          simpa only [deriv_const] using hderiv hxlt
        · have hx0 : x = 0 := le_antisymm hx (le_of_not_gt hxlt)
          subst x
          have heq : Set.EqOn (iteratedDeriv j f) (fun _ : ℝ => (0 : ℂ)) (Iic 0) := by
            intro y hy
            exact ih y hy
          have hwithin : HasDerivWithinAt (iteratedDeriv j f) 0 (Iic 0) 0 := by
            have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) 0 (Iic 0) 0 :=
              hasDerivWithinAt_const 0 (Iic 0) 0
            exact hconst.congr_of_eventuallyEq
              (heq.eventuallyEq_of_mem self_mem_nhdsWithin) (heq (by simp))
          rw [iteratedDeriv_succ]
          exact hwithin.deriv_eq_zero (uniqueDiffWithinAt_Iic 0)
  have flat_right : ∀ f : ℝ → ℂ, (∀ x : ℝ, T ≤ x → f x = 0) →
      ∀ j : ℕ, ∀ x : ℝ, T ≤ x → iteratedDeriv j f x = 0 := by
    intro f hf j
    induction j with
    | zero =>
        intro x hx
        simpa only [iteratedDeriv_zero] using hf x hx
    | succ j ih =>
        intro x hx
        by_cases hxgt : T < x
        · have heq : Set.EqOn (iteratedDeriv j f) (fun _ : ℝ => (0 : ℂ)) (Ioi T) := by
            intro y hy
            exact ih y hy.le
          have hderiv := heq.deriv isOpen_Ioi
          rw [iteratedDeriv_succ]
          simpa only [deriv_const] using hderiv hxgt
        · have hxT : x = T := le_antisymm (le_of_not_gt hxgt) hx
          subst x
          have heq : Set.EqOn (iteratedDeriv j f) (fun _ : ℝ => (0 : ℂ)) (Ici T) := by
            intro y hy
            exact ih y hy
          have hwithin : HasDerivWithinAt (iteratedDeriv j f) 0 (Ici T) T := by
            have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) 0 (Ici T) T :=
              hasDerivWithinAt_const T (Ici T) 0
            exact hconst.congr_of_eventuallyEq
              (heq.eventuallyEq_of_mem self_mem_nhdsWithin) (heq (by simp))
          rw [iteratedDeriv_succ]
          exact hwithin.deriv_eq_zero (uniqueDiffWithinAt_Ici T)
  have hzero_left : ∀ x : ℝ, x ≤ 0 → h x = 0 := by
    intro x hx
    apply hsupp x
    intro hx'
    exact (not_lt_of_ge hx) hx'.1
  have hzero_right : ∀ x : ℝ, T ≤ x → h x = 0 := by
    intro x hx
    apply hsupp x
    intro hx'
    exact (not_lt_of_ge hx) hx'.2
  have hflat0 : ∀ j : ℕ, iteratedDeriv j h 0 = 0 := by
    intro j
    exact flat_left h hzero_left j 0 le_rfl
  have hflatT : ∀ j : ℕ, iteratedDeriv j h T = 0 := by
    intro j
    exact flat_right h hzero_right j T le_rfl
  let r : ℝ → ℂ := fun z => h (T - z)
  have hr : ContDiff ℝ ∞ r := by
    dsimp [r]
    simpa using hh.fun_comp (contDiff_const.sub contDiff_id)
  have hrzero_left : ∀ z : ℝ, z ≤ 0 → r z = 0 := by
    intro z hz
    dsimp [r]
    apply hsupp (T - z)
    intro hz'
    have hTz : T ≤ T - z := by linarith
    exact (not_lt_of_ge hTz) hz'.2
  have hrflat0 : ∀ j : ℕ, iteratedDeriv j r 0 = 0 := by
    intro j
    exact flat_left r hrzero_left j 0 le_rfl
  let q : ℝ → ℂ := fun y => stepRight 0 h y + stepRight 0 r (-y)
  have hq : ContDiff ℝ ∞ q := by
    dsimp [q]
    exact (contDiff_stepRight hh hflat0).add
      ((contDiff_stepRight hr hrflat0).fun_comp contDiff_neg)
  have hh0 : h 0 = 0 := by
    simpa only [iteratedDeriv_zero] using hflat0 0
  have hhT : h T = 0 := by
    simpa only [iteratedDeriv_zero] using hflatT 0
  rw [contDiff_iff_contDiffAt]
  intro x
  let k : ℤ := ⌊x / T⌋
  have floor_eq_k : ∀ z : ℝ, T * (k : ℝ) ≤ z → z < T * ((k : ℝ) + 1) →
      ⌊z / T⌋ = k := by
    intro z hz0 hz1
    apply Int.floor_eq_iff.mpr
    constructor
    · exact (le_div_iff₀ hT).2 (by simpa [mul_comm] using hz0)
    · exact (div_lt_iff₀ hT).2 (by simpa [mul_comm] using hz1)
  have floor_eq_k_sub_one : ∀ z : ℝ, T * ((k : ℝ) - 1) ≤ z → z < T * (k : ℝ) →
      ⌊z / T⌋ = k - 1 := by
    intro z hz0 hz1
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hT).2
      rw [Int.cast_sub, Int.cast_one]
      simpa [mul_sub, mul_comm] using hz0
    · apply (div_lt_iff₀ hT).2
      rw [Int.cast_sub, Int.cast_one]
      simpa [mul_comm] using hz1
  have hxlower : T * (k : ℝ) ≤ x := by
    have hk : (k : ℝ) ≤ x / T := by
      dsimp [k]
      exact Int.floor_le _
    have hk' := (le_div_iff₀ hT).1 hk
    simpa [mul_comm] using hk'
  have hxupper : x < T * (k : ℝ) + T := by
    have hk : x / T < (k : ℝ) + 1 := by
      dsimp [k]
      exact Int.lt_floor_add_one _
    have hk' := (div_lt_iff₀ hT).1 hk
    calc
      x < ((k : ℝ) + 1) * T := hk'
      _ = T * (k : ℝ) + T := by ring
  let w : ℝ := x - T * (k : ℝ)
  have hw0 : 0 ≤ w := by
    dsimp [w]
    exact sub_nonneg.mpr hxlower
  have hwT : w < T := by
    dsimp [w]
    apply (sub_lt_iff_lt_add).2
    simpa [add_comm] using hxupper
  have hshift : ContDiff ℝ ∞ (fun z : ℝ => z - T * (k : ℝ)) :=
    contDiff_id.sub contDiff_const
  have hlocal : ContDiff ℝ ∞ (fun z : ℝ => h (z - T * (k : ℝ))) :=
    hh.fun_comp hshift
  by_cases hwzero : w = 0
  · have hxk : x = T * (k : ℝ) := by
      apply sub_eq_zero.mp
      simpa [w] using hwzero
    have hxU : x ∈ Ioo (T * (k : ℝ) - T / 2) (T * (k : ℝ) + T / 2) := by
      rw [hxk]
      constructor <;> linarith
    have hboundary : Set.EqOn (periodize T h)
        (fun z => q (z - T * (k : ℝ)))
        (Ioo (T * (k : ℝ) - T / 2) (T * (k : ℝ) + T / 2)) := by
      intro z hz
      let wz : ℝ := z - T * (k : ℝ)
      have hwz_lower : -T / 2 < wz := by
        dsimp [wz]
        linarith [hz.1]
      have hwz_upper : wz < T / 2 := by
        dsimp [wz]
        linarith [hz.2]
      have hqz : periodize T h z = q wz := by
        by_cases hwz : 0 ≤ wz
        · have hz0 : T * (k : ℝ) ≤ z := by
            exact sub_nonneg.mp (by simpa [wz] using hwz)
          have hz1 : z < T * ((k : ℝ) + 1) := by
            calc
              z < T * (k : ℝ) + T / 2 := hz.2
              _ < T * (k : ℝ) + T := by linarith [hT]
              _ = T * ((k : ℝ) + 1) := by ring
          have hf := floor_eq_k z hz0 hz1
          calc
            periodize T h z = h wz := by simp [periodize, hf, wz]
            _ = q wz := by
              by_cases hwz0 : wz = 0
              · rw [hwz0]
                simp [q, r, stepRight, hh0, hhT]
              · have hwzpos : 0 < wz := lt_of_le_of_ne hwz (Ne.symm hwz0)
                simp [q, r, stepRight, hwz, hwzpos]
        · have hwzneg : wz < 0 := lt_of_not_ge hwz
          have hz0 : T * ((k : ℝ) - 1) ≤ z := by
            apply le_of_lt
            calc
              T * ((k : ℝ) - 1) = T * (k : ℝ) - T := by ring
              _ < T * (k : ℝ) - T / 2 := by linarith [hT]
              _ < z := hz.1
          have hz1 : z < T * (k : ℝ) := by
            exact sub_neg.mp (by simpa [wz] using hwzneg)
          have hf := floor_eq_k_sub_one z hz0 hz1
          have harg : z - T * ((k - 1 : ℤ) : ℝ) = T - -wz := by
            dsimp [wz]
            rw [Int.cast_sub, Int.cast_one]
            ring
          calc
            periodize T h z = h (z - T * ((k - 1 : ℤ) : ℝ)) := by
              simp [periodize, hf]
            _ = h (T - -wz) := by rw [harg]
            _ = q wz := by
              have hneg : ¬(0 : ℝ) ≤ wz := hwz
              simp [q, r, stepRight, hneg]
              exact fun hc => absurd hc (not_lt.mpr hwzneg.le)
      simpa [wz] using hqz
    exact (hq.fun_comp hshift).contDiffAt.congr_of_eventuallyEq
      (hboundary.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxU))
  · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwzero)
    have hxint : x ∈ Ioo (T * (k : ℝ)) (T * ((k : ℝ) + 1)) := by
      constructor
      · exact sub_pos.mp (by simpa [w] using hwpos)
      · have hxupper' : x < T * (k : ℝ) + T := by
          simpa [add_comm] using (sub_lt_iff_lt_add.mp (by simpa [w] using hwT))
        simpa [mul_add, mul_comm] using hxupper'
    have hinterior : Set.EqOn (periodize T h)
        (fun z => h (z - T * (k : ℝ)))
        (Ioo (T * (k : ℝ)) (T * ((k : ℝ) + 1))) := by
      intro z hz
      have hf := floor_eq_k z hz.1.le hz.2
      simp [periodize, hf]
    exact hlocal.contDiffAt.congr_of_eventuallyEq
      (hinterior.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hxint))

end MobiusCPT
