import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Closed complex strips

The geometric strip from [T26, Definition 3.1], together with the boundary-uniqueness
argument needed for the analytic continuation in that definition.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Interval Topology

namespace MobiusCPT

/-- [T26], Definition 3.1; the closed strip bounded by the lines `ℝ` and `ℝ + τ`. It is
determined by `Im τ` alone: a real translation does not make the strip oblique, and for
`Im τ = 0` it degenerates to the real axis. -/
def strip (τ : ℂ) : Set ℂ :=
  {z : ℂ | min 0 τ.im ≤ z.im ∧ z.im ≤ max 0 τ.im}

/-- The defining description of the closed strip. -/
theorem closedStrip_eq :
    ∀ τ : ℂ, strip τ = { z : ℂ | min 0 τ.im ≤ z.im ∧ z.im ≤ max 0 τ.im } := by
  intro τ
  rfl

/-- Membership in the closed strip in terms of the imaginary part. -/
theorem mem_closedStrip {τ z : ℂ} :
    z ∈ strip τ ↔ min 0 τ.im ≤ z.im ∧ z.im ≤ max 0 τ.im := by
  rfl

/-- The closed strip as a product in real and imaginary coordinates. -/
theorem closedStrip_eq_reProdIm (τ : ℂ) :
    strip τ = Set.univ ×ℂ Set.Icc (min 0 τ.im) (max 0 τ.im) := by
  ext z
  simp only [mem_closedStrip, Complex.mem_reProdIm, Set.mem_univ, Set.mem_Icc, true_and]

/-- The interior of the closed strip is obtained by making both imaginary inequalities strict. -/
theorem interior_closedStrip (τ : ℂ) :
    interior (strip τ) =
      { z : ℂ | min 0 τ.im < z.im ∧ z.im < max 0 τ.im } := by
  rw [closedStrip_eq_reProdIm, Complex.interior_reProdIm, interior_univ, interior_Icc]
  ext z
  simp only [Complex.mem_reProdIm, Set.mem_univ, Set.mem_Ioo, Set.mem_setOf_eq, true_and]

/-- [T26], Definition 3.1; the real axis is a boundary line of every strip. -/
theorem ofReal_mem_closedStrip (τ : ℂ) (t : ℝ) : (t : ℂ) ∈ strip τ := by
  rw [mem_closedStrip]
  simp only [Complex.ofReal_im]
  exact ⟨min_le_left 0 τ.im, le_max_left 0 τ.im⟩

/-- [T26], Definition 3.1; `ℝ + τ` is the other boundary line. -/
theorem add_ofReal_mem_closedStrip (τ : ℂ) (t : ℝ) :
    τ + (t : ℂ) ∈ strip τ := by
  rw [mem_closedStrip]
  simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  exact ⟨min_le_right 0 τ.im, le_max_right 0 τ.im⟩

/-- [T26], Definition 3.1 and footnote 7; a real translation of the parameter does not move the
strip. -/
theorem closedStrip_add_ofReal (τ : ℂ) (t : ℝ) :
    strip (τ + (t : ℂ)) = strip τ := by
  ext z
  simp only [mem_closedStrip, Complex.add_im, Complex.ofReal_im, add_zero]

/-- [T26], Definition 3.1; the strip is invariant under real translation of its points. -/
theorem add_ofReal_mem_closedStrip_iff (τ : ℂ) (t : ℝ) (z : ℂ) :
    z + (t : ℂ) ∈ strip τ ↔ z ∈ strip τ := by
  simp only [mem_closedStrip, Complex.add_im, Complex.ofReal_im, add_zero]

/-- [T26], Definition 3.1; negation exchanges the strip of `τ` with the strip of `-τ`. -/
theorem neg_mem_closedStrip_iff (τ z : ℂ) :
    -z ∈ strip (-τ) ↔ z ∈ strip τ := by
  rcases le_total 0 τ.im with hτ | hτ
  · simp only [mem_closedStrip, Complex.neg_im, min_eq_left hτ, max_eq_right hτ,
      min_eq_right (neg_nonpos.mpr hτ), max_eq_left (neg_nonpos.mpr hτ), neg_le_neg_iff]
    constructor <;> intro h <;> constructor <;> linarith
  · simp only [mem_closedStrip, Complex.neg_im, min_eq_right hτ, max_eq_left hτ,
      min_eq_left (neg_nonneg.mpr hτ), max_eq_right (neg_nonneg.mpr hτ), neg_le_neg_iff]
    constructor <;> intro h <;> constructor <;> linarith

/-- [T26], Definition 3.1; a real parameter degenerates the strip to the real axis. -/
theorem closedStrip_ofReal (t : ℝ) : strip (t : ℂ) = { z : ℂ | z.im = 0 } := by
  ext z
  simp only [mem_closedStrip, Complex.ofReal_im, min_self, max_self, Set.mem_setOf_eq]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ by simp [h]⟩

/-- [T26], Definition 3.1; the degenerate strip has empty interior, so holomorphy there is
vacuous. -/
theorem interior_closedStrip_ofReal (t : ℝ) :
    interior (strip (t : ℂ)) = ∅ := by
  rw [interior_closedStrip]
  ext z
  simp only [Set.mem_setOf_eq, Complex.ofReal_im, min_self, max_self,
    Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  exact fun h ↦ h.le

/-- A continuous function that vanishes on a dense subset of its domain vanishes everywhere on
that domain. -/
private theorem eqZero_of_subset_closure {f : ℂ → ℂ} {s t : Set ℂ}
    (hf : ContinuousOn f t) (hst : s ⊆ t) (hts : t ⊆ closure s)
    (h : ∀ z ∈ s, f z = 0) : ∀ z ∈ t, f z = 0 := by
  intro z hz
  haveI : (nhdsWithin z s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hts hz)
  have hf_lim : Tendsto f (nhdsWithin z s) (nhds (f z)) :=
    (hf z hz).mono_left (nhdsWithin_mono z hst)
  have heq : f =ᶠ[nhdsWithin z s] fun _ : ℂ ↦ 0 :=
    eventually_nhdsWithin_of_forall fun y hy ↦ h y hy
  have hzero_lim : Tendsto f (nhdsWithin z s) (nhds 0) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hf_lim hzero_lim

/-- The positive-height case of boundary uniqueness, proved by zero extension and Morera's
theorem. -/
private theorem eqOn_zero_closedStrip_of_im_pos {τ : ℂ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (strip τ))
    (hd : DifferentiableOn ℂ f (interior (strip τ)))
    (h0 : ∀ t : ℝ, f (t : ℂ) = 0) (hb : 0 < τ.im) :
    Set.EqOn f 0 (strip τ) := by
  let b : ℝ := τ.im
  have hb' : 0 < b := hb
  have hbdef : b = τ.im := rfl
  let F : ℂ → ℂ := fun z ↦ if 0 ≤ z.im then f z else 0
  let U : Set ℂ := Set.univ ×ℂ Set.Ioo (-1 : ℝ) b
  have hF_nonpos : ∀ z : ℂ, z.im ≤ 0 → F z = 0 := by
    intro z hz
    by_cases hz' : 0 ≤ z.im
    · have him : z.im = 0 := le_antisymm hz hz'
      have hzreal : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa [him]
      simp only [F, if_pos hz']
      rw [hzreal]
      exact h0 z.re
    · simp only [F, if_neg hz']
  have hF_upper : ∀ z : ℂ, 0 ≤ z.im → F z = f z := by
    intro z hz
    simp only [F, if_pos hz]
  have hU_mem : ∀ z : ℂ, z ∈ U ↔ -1 < z.im ∧ z.im < b := by
    intro z
    simp only [U, Complex.mem_reProdIm, Set.mem_univ, Set.mem_Ioo, true_and]
  have hU_open : IsOpen U := by
    exact IsOpen.reProdIm isOpen_univ isOpen_Ioo
  have hU_conv : Convex ℝ U := by
    have hU_eq : U = {z : ℂ | -1 < z.im} ∩ {z : ℂ | z.im < b} := by
      ext z
      simp only [hU_mem, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hU_eq]
    exact (convex_halfSpace_im_gt (-1 : ℝ)).inter (convex_halfSpace_im_lt b)
  have hU_conn : IsPreconnected U := hU_conv.isPreconnected
  have hFc : ContinuousOn F U := by
    let A : Set ℂ := {z : ℂ | 0 ≤ z.im}
    let B : Set ℂ := {z : ℂ | z.im ≤ 0}
    have hA_closed : IsClosed A := by
      exact isClosed_le continuous_const Complex.continuous_im
    have hB_closed : IsClosed B := by
      exact isClosed_le Complex.continuous_im continuous_const
    have hsplit : U = U ∩ A ∪ U ∩ B := by
      ext z
      simp only [Set.mem_union, Set.mem_inter_iff, A, B, Set.mem_setOf_eq]
      constructor
      · intro hz
        rcases le_total 0 z.im with hz' | hz'
        · exact Or.inl ⟨hz, hz'⟩
        · exact Or.inr ⟨hz, hz'⟩
      · rintro (hz | hz) <;> exact hz.1
    intro z hz
    have hA_at (hzA : 0 ≤ z.im) : ContinuousWithinAt F (U ∩ A) z := by
      have hsub : U ∩ A ⊆ strip τ := by
        intro y hy
        rw [mem_closedStrip, min_eq_left hb.le, max_eq_right hb.le]
        exact ⟨hy.2, ((hU_mem y).mp hy.1).2.le⟩
      have hzstrip : z ∈ strip τ := hsub ⟨hz, hzA⟩
      exact (hc z hzstrip).congr_mono
        (fun y hy ↦ hF_upper y hy.2) hsub (hF_upper z hzA)
    have hB_at (hzB : z.im ≤ 0) : ContinuousWithinAt F (U ∩ B) z := by
      exact continuousWithinAt_const.congr
        (fun y hy ↦ hF_nonpos y hy.2) (hF_nonpos z hzB)
    have hA_away (hzA : z.im < 0) : ContinuousWithinAt F (U ∩ A) z := by
      apply continuousWithinAt_of_notMem_closure
      intro hzcl
      have hzclA : z ∈ closure A := closure_mono inter_subset_right hzcl
      rw [hA_closed.closure_eq] at hzclA
      exact (not_le_of_gt hzA) hzclA
    have hB_away (hzB : 0 < z.im) : ContinuousWithinAt F (U ∩ B) z := by
      apply continuousWithinAt_of_notMem_closure
      intro hzcl
      have hzclB : z ∈ closure B := closure_mono inter_subset_right hzcl
      rw [hB_closed.closure_eq] at hzclB
      exact (not_le_of_gt hzB) hzclB
    rw [hsplit]
    rcases lt_trichotomy z.im 0 with hzneg | hzero | hzpos
    · exact (hA_away hzneg).union (hB_at hzneg.le)
    · exact (hA_at hzero.ge).union (hB_at hzero.le)
    · exact (hA_at hzpos.le).union (hB_away hzpos)
  let R : ℂ → ℂ → ℂ := fun z w ↦
    (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
          I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))
  have Rzero_nonpos : ∀ z w : ℂ, z.im ≤ 0 → w.im ≤ 0 → R z w = 0 := by
    intro z w hz hw
    have hhz : (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) = 0 := by
      calc
        (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) =
            ∫ _x : ℝ in z.re..w.re, (0 : ℂ) :=
          intervalIntegral.integral_congr fun x _ ↦ hF_nonpos _ (by simpa using hz)
        _ = 0 := by simp
    have hhw : (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) = 0 := by
      calc
        (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) =
            ∫ _x : ℝ in z.re..w.re, (0 : ℂ) :=
          intervalIntegral.integral_congr fun x _ ↦ hF_nonpos _ (by simpa using hw)
        _ = 0 := by simp
    have hvw : (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) = 0 := by
      calc
        (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) =
            ∫ _y : ℝ in z.im..w.im, (0 : ℂ) :=
          intervalIntegral.integral_congr fun y hy ↦ hF_nonpos _ (by
            have hy0 : y ≤ 0 := hy.2.trans (max_le hz hw)
            simpa using hy0)
        _ = 0 := by simp
    have hvz : (∫ y : ℝ in z.im..w.im, F (z.re + y * I)) = 0 := by
      calc
        (∫ y : ℝ in z.im..w.im, F (z.re + y * I)) =
            ∫ _y : ℝ in z.im..w.im, (0 : ℂ) :=
          intervalIntegral.integral_congr fun y hy ↦ hF_nonpos _ (by
            have hy0 : y ≤ 0 := hy.2.trans (max_le hz hw)
            simpa using hy0)
        _ = 0 := by simp
    simp only [R, hhz, hhw, hvw, hvz, sub_zero, zero_add, smul_zero]
  have Rzero_nonneg : ∀ z w : ℂ, Complex.Rectangle z w ⊆ U →
      0 ≤ z.im → 0 ≤ w.im → R z w = 0 := by
    intro z w hrect hz hw
    have hzU : z ∈ U := hrect (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨Set.left_mem_uIcc, Set.left_mem_uIcc⟩)
    have hwU : w ∈ U := hrect (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨Set.right_mem_uIcc, Set.right_mem_uIcc⟩)
    have hzbound := (hU_mem z).mp hzU
    have hwbound := (hU_mem w).mp hwU
    have hcont : ContinuousOn F
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
      simpa only [Complex.Rectangle] using hFc.mono hrect
    have hopen_sub :
        Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
            Set.Ioo (min z.im w.im) (max z.im w.im) ⊆
          interior (strip τ) := by
      intro x hx
      rw [interior_closedStrip]
      rw [Complex.mem_reProdIm] at hx
      rw [min_eq_left hb.le, max_eq_right hb.le]
      constructor
      · exact (le_min hz hw).trans_lt hx.2.1
      · exact hx.2.2.trans (max_lt hzbound.2 hwbound.2)
    have hdiff : DifferentiableOn ℂ F
        (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
          Set.Ioo (min z.im w.im) (max z.im w.im)) := by
      apply hd.congr_mono
      · intro x hx
        apply hF_upper
        rw [Complex.mem_reProdIm] at hx
        exact (le_min hz hw).trans hx.2.1.le
      · exact hopen_sub
    exact Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      F z w hcont hdiff
  have hvertical (r a c : ℝ) (ha : -1 < a ∧ a < b) (hc' : -1 < c ∧ c < b) :
      IntervalIntegrable (fun y : ℝ ↦ F (r + y * I)) MeasureTheory.volume a c := by
    apply ContinuousOn.intervalIntegrable
    refine hFc.comp' (by fun_prop) ?_
    intro y hy
    rw [hU_mem]
    rcases Set.mem_uIcc.mp hy with hy | hy
    · have hy' : -1 < y ∧ y < b := by constructor <;> linarith
      simpa using hy'
    · have hy' : -1 < y ∧ y < b := by constructor <;> linarith
      simpa using hy'
  have Rsplit : ∀ z w : ℂ, Complex.Rectangle z w ⊆ U →
      R z w = R z (w.re : ℂ) + R (z.re : ℂ) w := by
    intro z w hrect
    have hzU : z ∈ U := hrect (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨Set.left_mem_uIcc, Set.left_mem_uIcc⟩)
    have hwU : w ∈ U := hrect (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨Set.right_mem_uIcc, Set.right_mem_uIcc⟩)
    have hzbound := (hU_mem z).mp hzU
    have hwbound := (hU_mem w).mp hwU
    have hzero : -1 < (0 : ℝ) ∧ (0 : ℝ) < b := ⟨by norm_num, hb'⟩
    have hwr_z0 := hvertical w.re z.im 0 hzbound hzero
    have hwr_0w := hvertical w.re 0 w.im hzero hwbound
    have hzr_z0 := hvertical z.re z.im 0 hzbound hzero
    have hzr_0w := hvertical z.re 0 w.im hzero hwbound
    simp only [R, Complex.ofReal_re, Complex.ofReal_im]
    rw [← intervalIntegral.integral_add_adjacent_intervals hwr_z0 hwr_0w,
      ← intervalIntegral.integral_add_adjacent_intervals hzr_z0 hzr_0w]
    simp only [smul_add]
    abel
  have hrect_first : ∀ z w : ℂ, 0 ∈ [[z.im, w.im]] →
      Complex.Rectangle z (w.re : ℂ) ⊆ Complex.Rectangle z w := by
    intro z w hzero x hx
    simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.ofReal_re,
      Complex.ofReal_im] at hx ⊢
    exact ⟨hx.1, Set.uIcc_subset_uIcc Set.left_mem_uIcc hzero hx.2⟩
  have hrect_second : ∀ z w : ℂ, 0 ∈ [[z.im, w.im]] →
      Complex.Rectangle (z.re : ℂ) w ⊆ Complex.Rectangle z w := by
    intro z w hzero x hx
    simp only [Complex.Rectangle, Complex.mem_reProdIm, Complex.ofReal_re,
      Complex.ofReal_im] at hx ⊢
    exact ⟨hx.1, Set.uIcc_subset_uIcc hzero Set.right_mem_uIcc hx.2⟩
  have hFcons : Complex.IsConservativeOn F U := by
    intro z w hrect
    rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
    change R z w = 0
    rcases le_total 0 z.im with hz | hz
    · rcases le_total 0 w.im with hw | hw
      · exact Rzero_nonneg z w hrect hz hw
      · have hzero : 0 ∈ [[z.im, w.im]] := Set.mem_uIcc_of_ge hw hz
        rw [Rsplit z w hrect,
          Rzero_nonneg z (w.re : ℂ) ((hrect_first z w hzero).trans hrect) hz (by simp),
          Rzero_nonpos (z.re : ℂ) w (by simp) hw, zero_add]
    · rcases le_total 0 w.im with hw | hw
      · have hzero : 0 ∈ [[z.im, w.im]] := Set.mem_uIcc_of_le hz hw
        rw [Rsplit z w hrect,
          Rzero_nonpos z (w.re : ℂ) hz (by simp),
          Rzero_nonneg (z.re : ℂ) w ((hrect_second z w hzero).trans hrect)
            (by simp) hw,
          add_zero]
      · exact Rzero_nonpos z w hz hw
  have hFd : DifferentiableOn ℂ F U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU_open).mp
      ⟨hFcons, hFc⟩
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hU_open
  let z₀ : ℂ := (-(1 / 2 : ℝ) : ℂ) * I
  have hz₀im : z₀.im = -(1 / 2 : ℝ) := by
    simp [z₀, Complex.mul_im]
  have hz₀U : z₀ ∈ U := by
    rw [hU_mem, hz₀im]
    exact ⟨by norm_num, by linarith [hb']⟩
  have hopen_neg : IsOpen {z : ℂ | z.im < 0} :=
    isOpen_lt Complex.continuous_im continuous_const
  have hF_eventually : F =ᶠ[nhds z₀] 0 := by
    refine Filter.eventuallyEq_of_mem (hopen_neg.mem_nhds ?_) ?_
    · show z₀.im < 0
      rw [hz₀im]
      norm_num
    · intro z hz
      exact hF_nonpos z (le_of_lt hz)
  have hFzero : Set.EqOn F 0 U :=
    hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conn hz₀U hF_eventually
  let s : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ z.im < b}
  have hs_zero : ∀ z ∈ s, f z = 0 := by
    intro z hz
    have hzU : z ∈ U := (hU_mem z).mpr ⟨by linarith [hz.1], hz.2⟩
    calc
      f z = F z := (hF_upper z hz.1).symm
      _ = 0 := by simpa only [Pi.zero_apply] using hFzero hzU
  have hs_sub : s ⊆ strip τ := by
    intro z hz
    rw [mem_closedStrip, min_eq_left hb.le, max_eq_right hb.le]
    exact ⟨hz.1, hz.2.le⟩
  have hs_eq : s = Set.univ ×ℂ Set.Ico 0 b := by
    ext z
    simp only [s, Complex.mem_reProdIm, Set.mem_univ, Set.mem_Ico, Set.mem_setOf_eq,
      true_and]
  have hclosure : closure s = strip τ := by
    rw [hs_eq, Complex.closure_reProdIm, closure_univ, closure_Ico (ne_of_lt hb'),
      closedStrip_eq_reProdIm, min_eq_left hb.le, max_eq_right hb.le, hbdef]
  intro z hz
  exact eqZero_of_subset_closure hc hs_sub (fun _ hz' ↦ by rwa [hclosure]) hs_zero z hz

/-- [T26], Definition 3.1; the uniqueness of the continuation. A function continuous on the
closed strip and holomorphic in its interior that vanishes on the real boundary line vanishes on
the whole strip. [T26] records the extension as "necessarily unique" without argument; this is
that argument. Note the hypothesis is genuinely a boundary one: the real axis consists of
non-interior points of the strip, so the identity theorem does not apply to it directly. -/
theorem eqOn_zero_closedStrip_of_ofReal {τ : ℂ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (strip τ))
    (hd : DifferentiableOn ℂ f (interior (strip τ)))
    (h0 : ∀ t : ℝ, f (t : ℂ) = 0) :
    Set.EqOn f 0 (strip τ) := by
  rcases lt_trichotomy τ.im 0 with hb | hb | hb
  · let g : ℂ → ℂ := fun z ↦ f (-z)
    have hmap_closed : Set.MapsTo (fun z : ℂ ↦ -z) (strip (-τ)) (strip τ) := by
      intro z hz
      have := (neg_mem_closedStrip_iff (-τ) z).mpr hz
      simpa only [neg_neg] using this
    have hgc : ContinuousOn g (strip (-τ)) := by
      simpa only [g] using hc.comp' continuous_neg.continuousOn hmap_closed
    have hmap_interior : Set.MapsTo (fun z : ℂ ↦ -z)
        (interior (strip (-τ))) (interior (strip τ)) := by
      intro z hz
      rw [interior_closedStrip, Set.mem_setOf_eq, Complex.neg_im,
        min_eq_left (neg_nonneg.mpr hb.le), max_eq_right (neg_nonneg.mpr hb.le)] at hz
      simp only [interior_closedStrip, Set.mem_setOf_eq, Complex.neg_im,
        min_eq_right hb.le, max_eq_left hb.le]
      constructor <;> linarith [hz.1, hz.2]
    have hgd : DifferentiableOn ℂ g (interior (strip (-τ))) := by
      have hneg : DifferentiableOn ℂ (fun z : ℂ ↦ -z) (interior (strip (-τ))) :=
        (differentiable_id.neg).differentiableOn
      have hcomp := hd.comp hneg hmap_interior
      simpa only [g, Function.comp_def] using hcomp
    have hg0 : ∀ t : ℝ, g (t : ℂ) = 0 := by
      intro t
      dsimp [g]
      simpa using h0 (-t)
    have hpos : 0 < (-τ).im := by simpa only [Complex.neg_im] using neg_pos.mpr hb
    have hgzero := eqOn_zero_closedStrip_of_im_pos hgc hgd hg0 hpos
    intro z hz
    have hnz : -z ∈ strip (-τ) := (neg_mem_closedStrip_iff τ z).mpr hz
    simpa only [g, neg_neg, Pi.zero_apply] using hgzero hnz
  · intro z hz
    have him : z.im = 0 := by
      rw [mem_closedStrip, hb, min_self, max_self] at hz
      exact le_antisymm hz.2 hz.1
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa [him]
    rw [hzreal]
    simpa only [Pi.zero_apply] using h0 z.re
  · exact eqOn_zero_closedStrip_of_im_pos hc hd h0 hb

/-- [T26], Definition 3.1; two continuations agreeing on the real boundary agree on the strip.
This is the uniqueness statement Definition 3.1 needs. -/
theorem eqOn_closedStrip_of_eqOn_ofReal {τ : ℂ} {f g : ℂ → ℂ}
    (hcf : ContinuousOn f (strip τ))
    (hdf : DifferentiableOn ℂ f (interior (strip τ)))
    (hcg : ContinuousOn g (strip τ))
    (hdg : DifferentiableOn ℂ g (interior (strip τ)))
    (h : ∀ t : ℝ, f (t : ℂ) = g (t : ℂ)) :
    Set.EqOn f g (strip τ) := by
  have hzero : Set.EqOn (f - g) 0 (strip τ) :=
    eqOn_zero_closedStrip_of_ofReal (hcf.sub hcg) (hdf.sub hdg) fun t ↦ sub_eq_zero.mpr (h t)
  intro z hz
  exact sub_eq_zero.mp (by simpa only [Pi.sub_apply, Pi.zero_apply] using hzero hz)

end MobiusCPT
