import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MobiusCPT

open Filter Set Topology
open scoped ContDiff Topology

/-!
This file is deliberately independent of the project-specific test-function spaces.  The
only input used below is a smooth function on `ℝ` which is zero off an open interval.
-/

/- The following is the standard ``differentiate on an open set, then close it`` argument.
   It is useful here because the hypothesis says that the function is zero off an open
   interval, whereas the estimates below need the same assertion for every derivative. -/
private theorem iteratedDeriv_eq_zero_on_closure {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {s : Set ℝ} (hs : IsOpen s) (hzero : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) s) (j : ℕ) :
    closure s ⊆ {x : ℝ | iteratedDeriv j g x = 0} := by
  have hderiv : Set.EqOn (iteratedDeriv j g) (fun _ : ℝ => (0 : ℂ)) s := by
    intro x hx
    have hx' := hzero.iteratedDeriv_of_isOpen hs j hx
    simpa using hx'
  have hclosed : IsClosed {x : ℝ | iteratedDeriv j g x = 0} :=
    isClosed_eq (hg.continuous_iteratedDeriv j (by exact_mod_cast le_top)) continuous_const
  exact closure_minimal hderiv hclosed

private theorem iteratedDeriv_eq_zero_of_not_mem_Ioo {a b : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hzero : ∀ x, x ∉ Set.Ioo a b → g x = 0) (j : ℕ) {x : ℝ}
    (hx : x ∉ Set.Ioo a b) : iteratedDeriv j g x = 0 := by
  have hleft : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Iio a) := by
    intro y hy
    apply hzero y
    intro hy'
    exact (not_lt_of_ge (le_of_lt hy)) hy'.1
  have hright : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Ioi b) := by
    intro y hy
    apply hzero y
    intro hy'
    exact (not_lt_of_ge (le_of_lt hy)) hy'.2
  by_cases hxa : x ≤ a
  · have hmem : x ∈ closure (Set.Iio a) := by
      rw [closure_Iio]
      exact hxa
    exact (iteratedDeriv_eq_zero_on_closure hg isOpen_Iio hleft j) hmem
  · have hax : a < x := lt_of_not_ge hxa
    have hxb : b ≤ x := by
      by_contra hxb
      have hxb' : x < b := lt_of_not_ge hxb
      exact hx ⟨hax, hxb'⟩
    have hmem : x ∈ closure (Set.Ioi b) := by
      rw [closure_Ioi]
      exact hxb
    exact (iteratedDeriv_eq_zero_on_closure hg isOpen_Ioi hright j) hmem

private theorem iteratedDeriv_hasCompactSupport_of_zero_outside {a b : ℝ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hzero : ∀ x, x ∉ Set.Ioo a b → g x = 0) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j g) := by
  apply HasCompactSupport.intro (K := Set.Icc a b) isCompact_Icc
  intro x hx
  apply iteratedDeriv_eq_zero_of_not_mem_Ioo hg hzero j
  intro hmem
  exact hx (Ioo_subset_Icc_self hmem)

private theorem contDiff_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j g) := by
  rw [iteratedDeriv_eq_iterate]
  exact hg.iterate_deriv j

/- The affine chain rule is stated separately so that the main construction only has to
   identify its slope and intercept.  Translation invariance is combined with the
   constant-scalar chain rule from Mathlib. -/
private theorem iteratedDeriv_comp_affine (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ)
  (k p : ℝ) :
    iteratedDeriv n (fun x : ℝ => f (k * x + p)) =
      fun x => k ^ n • iteratedDeriv n f (k * x + p) := by
  have hshift : ContDiff ℝ n (fun y : ℝ => f (y + p)) := by
    simpa [Function.comp_def] using
      (hf.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  funext x
  calc
    iteratedDeriv n (fun x : ℝ => f (k * x + p)) x =
        iteratedDeriv n (fun x : ℝ => (fun y : ℝ => f (y + p)) (k * x)) x := by
          rfl
    _ = k ^ n • iteratedDeriv n (fun y : ℝ => f (y + p)) (k * x) :=
      congrFun (iteratedDeriv_comp_const_smul hshift k) x
    _ = k ^ n • iteratedDeriv n f (k * x + p) := by
      rw [congrFun (iteratedDeriv_comp_add_const n f p) (k * x)]

/-- Given a smooth complex function vanishing outside an open interval, there is a sequence of
smooth functions, each vanishing outside a compact sub-interval strictly inside `(a, b)`,
converging to the original function together with every derivative order, uniformly on `ℝ`. -/
theorem exists_contDiff_zero_outside_compact_tendstoUniformly {a b : ℝ} (hab : a < b)
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hzero : ∀ θ, θ ∉ Set.Ioo a b → g θ = 0) :
    ∃ gSeq : ℕ → ℝ → ℂ,
      (∀ m, ContDiff ℝ ∞ (gSeq m)) ∧
      (∃ c d : ℕ → ℝ, ∀ m, a < c m ∧ c m < d m ∧ d m < b ∧
        (∀ θ, θ ∉ Set.Ioo (c m) (d m) → gSeq m θ = 0)) ∧
      (∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, ∀ θ : ℝ,
        ‖iteratedDeriv N (gSeq m) θ - iteratedDeriv N g θ‖ < ε) := by
  let c : ℝ := (a + b) / 2
  let w : ℝ := (b - a) / 2
  let s : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2)
  let T : ℕ → ℝ → ℝ := fun m θ => c + (θ - c) / s m
  let gSeq : ℕ → ℝ → ℂ := fun m θ => g (T m θ)

  have hw : 0 < w := by
    dsimp [w]
    linarith
  have hcw : c - w = a := by
    dsimp [c, w]
    ring
  have hcp : c + w = b := by
    dsimp [c, w]
    ring
  have hs_pos : ∀ m, 0 < s m := by
    intro m
    dsimp [s]
    have hden : (1 : ℝ) < (m : ℝ) + 2 := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
      linarith
    have hfrac : 1 / ((m : ℝ) + 2) < (1 : ℝ) :=
      (div_lt_one (by linarith)).2 hden
    linarith
  have hs_lt_one : ∀ m, s m < 1 := by
    intro m
    dsimp [s]
    have hfrac : 0 < 1 / ((m : ℝ) + 2) := one_div_pos.mpr (by positivity)
    linarith
  have hsw_lt_w : ∀ m, s m * w < w := by
    intro m
    simpa using mul_lt_mul_of_pos_right (hs_lt_one m) hw
  have hsw_pos : ∀ m, 0 < s m * w := fun m => mul_pos (hs_pos m) hw

  have hT_smooth : ∀ m, ContDiff ℝ ∞ (T m) := by
    intro m
    dsimp [T]
    exact contDiff_const.add ((contDiff_id.sub contDiff_const).div_const (s m))

  refine ⟨gSeq, ?_, ?_, ?_⟩
  · intro m
    simpa [gSeq, Function.comp_def] using hg.comp (hT_smooth m)
  · refine ⟨fun m => c - s m * w, fun m => c + s m * w, ?_⟩
    intro m
    have hcm : a < c - s m * w := by
      rw [← hcw]
      linarith [hsw_lt_w m]
    have hcd : c - s m * w < c + s m * w := by
      linarith [hsw_pos m]
    have hdb : c + s m * w < b := by
      rw [← hcp]
      linarith [hsw_lt_w m]
    refine ⟨hcm, hcd, hdb, ?_⟩
    intro θ hθ
    have houtside : T m θ ∉ Set.Ioo a b := by
      by_cases hleft : θ ≤ c - s m * w
      · have hquot : (θ - c) / s m ≤ -w := by
          apply (div_le_iff₀ (hs_pos m)).2
          nlinarith [hleft]
        have hTle : T m θ ≤ c - w := by
          dsimp [T]
          linarith
        have hTlea : T m θ ≤ a := by simpa [hcw] using hTle
        intro hmem
        exact (not_lt_of_ge hTlea) hmem.1
      · have hmid : c - s m * w < θ := lt_of_not_ge hleft
        have hright : c + s m * w ≤ θ := by
          by_contra hright
          have hright' : θ < c + s m * w := lt_of_not_ge hright
          exact hθ ⟨hmid, hright'⟩
        have hquot : w ≤ (θ - c) / s m := by
          apply (le_div_iff₀ (hs_pos m)).2
          nlinarith [hright]
        have hTge : c + w ≤ T m θ := by
          dsimp [T]
          linarith
        have hTgeb : b ≤ T m θ := by simpa [hcp] using hTge
        intro hmem
        exact (not_lt_of_ge hTgeb) hmem.2
    simpa [gSeq] using hzero (T m θ) houtside
  · intro N ε hε
    have hFN : ContDiff ℝ ∞ (iteratedDeriv N g) := contDiff_iteratedDeriv hg N
    have hFNcont : Continuous (iteratedDeriv N g) := hFN.continuous
    have hFNcompact : HasCompactSupport (iteratedDeriv N g) :=
      iteratedDeriv_hasCompactSupport_of_zero_outside hg hzero N
    obtain ⟨L, hL⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport hFNcompact hFN (by simp)
    obtain ⟨Bsup, hBsup⟩ := hFNcompact.exists_bound_of_continuous hFNcont
    have hFNbound : ∀ x, ‖iteratedDeriv N g x‖ ≤ Bsup := by
      intro x
      exact hBsup x

    /- If the value at `T m θ` is nonzero, the inverse affine map puts `θ` back in
       the original interval.  Thus, whenever one of the two values is nonzero,
       both arguments lie in the fixed compact interval `Icc a b`. -/
    have htheta_mem_of_T_mem : ∀ m θ, T m θ ∈ Set.Ioo a b → θ ∈ Set.Ioo a b := by
      intro m θ hTmem
      have hleftT : c - w < T m θ := by simpa [hcw] using hTmem.1
      have hquotleft : -w < (θ - c) / s m := by
        dsimp [T] at hleftT
        linarith
      have hmulleft : -w * s m < θ - c := (lt_div_iff₀ (hs_pos m)).mp hquotleft
      have hneg : -w < -w * s m := by
        have hpos : w * s m < w := by simpa [mul_comm] using hsw_lt_w m
        simpa [neg_mul] using neg_lt_neg hpos
      have hleft : a < θ := by
        linarith [hmulleft, hneg, hcw]
      have hrightT : T m θ < c + w := by simpa [hcp] using hTmem.2
      have hquotright : (θ - c) / s m < w := by
        dsimp [T] at hrightT
        linarith
      have hmulright : θ - c < w * s m := (div_lt_iff₀ (hs_pos m)).mp hquotright
      have hsw_lt_w' : w * s m < w := by simpa [mul_comm] using hsw_lt_w m
      have hright : θ < b := by
        linarith [hmulright, hsw_lt_w', hcp]
      exact ⟨hleft, hright⟩

    have hterm2_le (m : ℕ) (θ : ℝ) :
        ‖iteratedDeriv N g (T m θ) - iteratedDeriv N g θ‖ ≤
          (L : ℝ) * (|(s m)⁻¹ - 1| * w) := by
      have hmem_of_ne (x : ℝ) (hx : iteratedDeriv N g x ≠ 0) : x ∈ Set.Ioo a b := by
        by_contra hx'
        exact hx (iteratedDeriv_eq_zero_of_not_mem_Ioo hg hzero N hx')
      by_cases hboth : iteratedDeriv N g (T m θ) = 0 ∧ iteratedDeriv N g θ = 0
      · simp only [hboth.1, hboth.2, sub_self, norm_zero]
        positivity
      · have hθmem : θ ∈ Set.Ioo a b := by
          by_cases hθzero : iteratedDeriv N g θ = 0
          · exact htheta_mem_of_T_mem m θ
              (hmem_of_ne (T m θ) (by
                intro hTzero
                exact hboth ⟨hTzero, hθzero⟩))
          · exact hmem_of_ne θ hθzero
        have hθbound : |θ - c| ≤ w := by
          rw [abs_le]
          constructor <;> linarith [hθmem.1, hθmem.2, hcw, hcp]
        have hdist : ‖T m θ - θ‖ ≤ |(s m)⁻¹ - 1| * w := by
          have hident : T m θ - θ = (θ - c) * ((s m)⁻¹ - 1) := by
            dsimp [T]
            ring
          rw [Real.norm_eq_abs, hident, abs_mul]
          calc
            |θ - c| * |(s m)⁻¹ - 1| ≤ w * |(s m)⁻¹ - 1| :=
              mul_le_mul_of_nonneg_right hθbound (abs_nonneg _)
            _ = |(s m)⁻¹ - 1| * w := by ring
        calc
          ‖iteratedDeriv N g (T m θ) - iteratedDeriv N g θ‖ ≤
              (L : ℝ) * ‖T m θ - θ‖ := hL.norm_sub_le _ _
          _ ≤ (L : ℝ) * (|(s m)⁻¹ - 1| * w) :=
            mul_le_mul_of_nonneg_left hdist (by positivity)

    have hfrac : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
      have heq : (fun m : ℕ => 1 / ((m : ℝ) + 2)) =
          (fun n : ℕ => (1 : ℝ) / (n : ℝ)) ∘ (fun a : ℕ => a + 2) := by
        funext m
        simp only [Function.comp_apply]
        push_cast
        ring
      rw [heq]
      exact h
    have hs_tendsto : Tendsto s atTop (𝓝 1) := by
      simpa [s] using tendsto_const_nhds.sub hfrac
    have hsinv : Tendsto (fun m => (s m)⁻¹) atTop (𝓝 1) := by
      simpa using hs_tendsto.inv₀ one_ne_zero
    have hpow : Tendsto (fun m => (s m)⁻¹ ^ N) atTop (𝓝 1) := by
      simpa using hsinv.pow N
    have hcoef : Tendsto (fun m => |(s m)⁻¹ ^ N - 1| * Bsup) atTop (𝓝 0) := by
      simpa using (hpow.sub_const 1).abs.mul_const Bsup
    have hdelta : Tendsto (fun m => |(s m)⁻¹ - 1| * w) atTop (𝓝 0) := by
      simpa using (hsinv.sub_const 1).abs.mul_const w
    have hdelta_scaled : Tendsto
        (fun m => (L : ℝ) * (|(s m)⁻¹ - 1| * w)) atTop (𝓝 0) := by
      simpa using hdelta.const_mul (L : ℝ)
    have hcoef_event : ∀ᶠ m in atTop, |(s m)⁻¹ ^ N - 1| * Bsup < ε / 2 :=
      hcoef.eventually (Iio_mem_nhds (by linarith))
    have hdelta_event : ∀ᶠ m in atTop,
        (L : ℝ) * (|(s m)⁻¹ - 1| * w) < ε / 2 :=
      hdelta_scaled.eventually (Iio_mem_nhds (by linarith))
    have hpoint : ∀ᶠ m in atTop, ∀ θ : ℝ,
        ‖iteratedDeriv N (gSeq m) θ - iteratedDeriv N g θ‖ < ε := by
      have hscale (m : ℕ) (θ : ℝ) :
          iteratedDeriv N (gSeq m) θ =
            (s m)⁻¹ ^ N • iteratedDeriv N g (T m θ) := by
        change iteratedDeriv N (fun x => g (T m x)) θ = _
        have hfun : (fun x => g (T m x)) =
            (fun x => g ((s m)⁻¹ * x + (c - c / s m))) := by
          funext x
          congr 1
          dsimp [T]
          ring
        have harg : (s m)⁻¹ * θ + (c - c / s m) = T m θ := by
          dsimp [T]
          ring
        calc
          iteratedDeriv N (fun x => g (T m x)) θ =
              iteratedDeriv N (fun x => g ((s m)⁻¹ * x + (c - c / s m))) θ := by
                rw [hfun]
          _ = (s m)⁻¹ ^ N •
              iteratedDeriv N g ((s m)⁻¹ * θ + (c - c / s m)) :=
            congrFun (iteratedDeriv_comp_affine g hg N (s m)⁻¹ (c - c / s m)) θ
          _ = (s m)⁻¹ ^ N • iteratedDeriv N g (T m θ) := by rw [harg]
      filter_upwards [hcoef_event, hdelta_event] with m hmcoef hmdelta θ
      have hdecomp :
          (s m)⁻¹ ^ N • iteratedDeriv N g (T m θ) - iteratedDeriv N g θ =
            ((s m)⁻¹ ^ N - 1) • iteratedDeriv N g (T m θ) +
              (iteratedDeriv N g (T m θ) - iteratedDeriv N g θ) := by
        simp only [sub_smul, one_smul]
        abel
      have hterm1 :
          ‖((s m)⁻¹ ^ N - 1) • iteratedDeriv N g (T m θ)‖ ≤
            |(s m)⁻¹ ^ N - 1| * Bsup := by
        calc
          ‖((s m)⁻¹ ^ N - 1) • iteratedDeriv N g (T m θ)‖ =
              |(s m)⁻¹ ^ N - 1| * ‖iteratedDeriv N g (T m θ)‖ := by
                rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |(s m)⁻¹ ^ N - 1| * Bsup :=
            mul_le_mul_of_nonneg_left (hFNbound (T m θ)) (abs_nonneg _)
      calc
        ‖iteratedDeriv N (gSeq m) θ - iteratedDeriv N g θ‖ =
            ‖(s m)⁻¹ ^ N • iteratedDeriv N g (T m θ) -
              iteratedDeriv N g θ‖ := by rw [hscale]
        _ = ‖((s m)⁻¹ ^ N - 1) • iteratedDeriv N g (T m θ) +
              (iteratedDeriv N g (T m θ) - iteratedDeriv N g θ)‖ := by rw [hdecomp]
        _ ≤ ‖((s m)⁻¹ ^ N - 1) • iteratedDeriv N g (T m θ)‖ +
              ‖iteratedDeriv N g (T m θ) - iteratedDeriv N g θ‖ := norm_add_le _ _
        _ ≤ |(s m)⁻¹ ^ N - 1| * Bsup + (L : ℝ) * (|(s m)⁻¹ - 1| * w) :=
          add_le_add hterm1 (hterm2_le m θ)
        _ < ε := by linarith
    rcases (eventually_atTop.1 hpoint) with ⟨M, hM⟩
    exact ⟨M, fun m hm θ => hM m hm θ⟩

end MobiusCPT
