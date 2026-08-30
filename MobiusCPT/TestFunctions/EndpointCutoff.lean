import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import MobiusCPT.Analysis.IntervalShrink
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.Support

namespace MobiusCPT

open Filter Set Topology
open scoped Topology

noncomputable section

/-! The first two utilities keep the two endpoint constructions below concrete while isolating
the only calculus facts which are used by both of them. -/

private theorem angleDeriv_sub (j : ℕ) (f g : TestFn) :
    angleDeriv j (f - g) = angleDeriv j f - angleDeriv j g := by
  funext θ
  change iteratedDeriv j (toAngle (f - g)) θ =
    iteratedDeriv j (toAngle f) θ - iteratedDeriv j (toAngle g) θ
  have hto : toAngle (f - g) = toAngle f - toAngle g := by
    funext x
    rfl
  rw [hto]
  exact iteratedDeriv_sub
    ((contDiff_toAngle f).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_toAngle g).contDiffAt.of_le (by exact_mod_cast le_top))

private theorem iteratedDeriv_periodize_eqOn_Ioo {T : ℝ} (hT : 0 < T)
    {g : ℝ → ℂ} (j : ℕ) :
    Set.EqOn (iteratedDeriv j (periodize T g)) (iteratedDeriv j g) (Set.Ioo 0 T) := by
  have heq : Set.EqOn (periodize T g) g (Set.Ioo 0 T) := by
    intro x hx
    exact periodize_eq_self hT ⟨hx.1.le, hx.2⟩
  intro x hx
  exact Filter.EventuallyEq.iteratedDeriv_eq j
    (heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))

private theorem cnorm_le_of_uniform_bound {N : ℕ} {f : TestFn} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, j ≤ N → ∀ θ : ℝ, ‖angleDeriv j f θ‖ ≤ C) :
    (cnorm N f : ℝ) ≤ (N + 1) * C := by
  rw [cnorm_eq]
  have hterm : ∀ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ ≤ C := by
    intro j hj
    refine (BoundedContinuousFunction.norm_le hC).mpr ?_
    intro θ
    rw [angleDerivB_apply]
    exact hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) θ
  calc
    ∑ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ ≤
        ∑ _j ∈ Finset.range (N + 1), C := Finset.sum_le_sum hterm
    _ = (N + 1) * C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-! A nonzero value of a periodisation has a nonzero value at its canonical representative.
The representative is then strictly between the chosen endpoints, which gives the compact
support bound needed for the topological support. -/

private theorem tsupport_subset_lowerArc_of_periodize {c d : ℝ} {g : ℝ → ℂ} {f : TestFn}
    (hfd : toAngle f = periodize (2 * Real.pi) g)
    (hzero : ∀ θ, θ ∉ Set.Ioo c d → g θ = 0) (hc : Real.pi < c)
    (hd : d < 2 * Real.pi) : tsupport (f : Circle → ℂ) ⊆ lowerArc := by
  have hsupport : Function.support (f : Circle → ℂ) ⊆ Circle.exp '' Set.Icc c d := by
    intro z hz
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
    change f (Circle.exp θ) ≠ 0 at hz
    let k : ℤ := ⌊θ / (2 * Real.pi)⌋
    let θ' : ℝ := θ - 2 * Real.pi * (k : ℝ)
    have hper : periodize (2 * Real.pi) g θ = g θ' := by
      simp [periodize, θ', k]
    have hgnz : g θ' ≠ 0 := by
      intro hz'
      apply hz
      change toAngle f θ = 0
      rw [hfd, hper, hz']
    have hmem : θ' ∈ Set.Ioo c d := by
      by_contra hnot
      exact hgnz (hzero θ' hnot)
    refine ⟨θ', ⟨hmem.1.le, hmem.2.le⟩, ?_⟩
    apply Circle.exp_eq_exp.mpr
    refine ⟨-k, ?_⟩
    rw [Int.cast_neg]
    dsimp [θ']
    ring
  have himage : Circle.exp '' Set.Icc c d ⊆ lowerArc := by
    rintro z ⟨θ, hθ, rfl⟩
    apply (mem_lowerArc_circleExp).2
    refine ⟨0, ?_⟩
    have hθπ : Real.pi < θ := lt_of_lt_of_le hc hθ.1
    have hθT : θ < 2 * Real.pi := lt_of_le_of_lt hθ.2 hd
    simpa using ⟨hθπ, hθT⟩
  have hcompact : IsCompact (Circle.exp '' Set.Icc c d) :=
    isCompact_Icc.image Circle.exp.continuous
  have hts : tsupport (f : Circle → ℂ) ⊆ Circle.exp '' Set.Icc c d := by
    rw [tsupport]
    exact closure_minimal hsupport hcompact.isClosed
  exact hts.trans himage

private theorem tsupport_subset_upperArc_of_periodize {c d : ℝ} {g : ℝ → ℂ} {f : TestFn}
    (hfd : toAngle f = periodize (2 * Real.pi) g)
    (hzero : ∀ θ, θ ∉ Set.Ioo c d → g θ = 0) (hc : 0 < c)
    (hd : d < Real.pi) : tsupport (f : Circle → ℂ) ⊆ upperArc := by
  have hsupport : Function.support (f : Circle → ℂ) ⊆ Circle.exp '' Set.Icc c d := by
    intro z hz
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
    change f (Circle.exp θ) ≠ 0 at hz
    let k : ℤ := ⌊θ / (2 * Real.pi)⌋
    let θ' : ℝ := θ - 2 * Real.pi * (k : ℝ)
    have hper : periodize (2 * Real.pi) g θ = g θ' := by
      simp [periodize, θ', k]
    have hgnz : g θ' ≠ 0 := by
      intro hz'
      apply hz
      change toAngle f θ = 0
      rw [hfd, hper, hz']
    have hmem : θ' ∈ Set.Ioo c d := by
      by_contra hnot
      exact hgnz (hzero θ' hnot)
    refine ⟨θ', ⟨hmem.1.le, hmem.2.le⟩, ?_⟩
    apply Circle.exp_eq_exp.mpr
    refine ⟨-k, ?_⟩
    rw [Int.cast_neg]
    dsimp [θ']
    ring
  have himage : Circle.exp '' Set.Icc c d ⊆ upperArc := by
    rintro z ⟨θ, hθ, rfl⟩
    apply (mem_upperArc_circleExp).2
    refine ⟨0, ?_⟩
    have hθ0 : 0 < θ := lt_of_lt_of_le hc hθ.1
    have hθπ : θ < Real.pi := lt_of_le_of_lt hθ.2 hd
    simpa using ⟨hθ0, hθπ⟩
  have hcompact : IsCompact (Circle.exp '' Set.Icc c d) :=
    isCompact_Icc.image Circle.exp.continuous
  have hts : tsupport (f : Circle → ℂ) ⊆ Circle.exp '' Set.Icc c d := by
    rw [tsupport]
    exact closure_minimal hsupport hcompact.isClosed
  exact hts.trans himage

/-! The convergence proof uses a canonical point in `[0, 2π)`.  At an interior point the
periodisation and its derivatives agree with the unperiodised function.  At the only possible
endpoint, `0`, flatness of the test functions makes the derivative of their difference vanish. -/

private theorem lower_cutoff_tendsto {h : TestFn} {g₀ : ℝ → ℂ} {gSeq : ℕ → ℝ → ℂ}
    {hSeq : ℕ → TestFn} (hh : SuppLower h)
    (h₀ : toAngle h = periodize (2 * Real.pi) g₀)
    (hEq : ∀ m, toAngle (hSeq m) = periodize (2 * Real.pi) (gSeq m))
    (hSupp : ∀ m, SuppLower (hSeq m))
    (hconv : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, ∀ θ : ℝ,
      ‖iteratedDeriv N (gSeq m) θ - iteratedDeriv N g₀ θ‖ < ε) :
    Tendsto hSeq atTop (nhds h) := by
  rw [tendsto_iff_cnorm]
  intro N
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let C : ℝ := ε / (2 * ((N : ℝ) + 1))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hstep : ∀ j ∈ Finset.range (N + 1), ∀ᶠ m : ℕ in atTop, ∀ θ : ℝ,
      ‖angleDeriv j (hSeq m - h) θ‖ < C := by
    intro j hj
    obtain ⟨M, hM⟩ := hconv j C hC
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro m hm θ
    have hper : Function.Periodic (angleDeriv j (hSeq m - h)) (2 * Real.pi) := by
      rw [angleDeriv_sub]
      exact (periodic_angleDeriv j (hSeq m)).sub (periodic_angleDeriv j h)
    obtain ⟨y, hy, hmy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hmy]
    by_cases hy0 : y = 0
    · subst y
      have hzeroSeq := (iteratedDeriv_toAngle_eq_zero_of_suppLower (hSupp m) j).1
      have hzeroH := (iteratedDeriv_toAngle_eq_zero_of_suppLower hh j).1
      rw [angleDeriv_sub]
      simpa [angleDeriv, hzeroSeq, hzeroH] using hC
    · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
      have hyopen : y ∈ Set.Ioo 0 (2 * Real.pi) := ⟨hypos, hy.2⟩
      have hderiv : angleDeriv j (hSeq m - h) y =
          iteratedDeriv j (gSeq m) y - iteratedDeriv j g₀ y := by
        rw [angleDeriv_sub]
        change iteratedDeriv j (toAngle (hSeq m)) y -
          iteratedDeriv j (toAngle h) y = _
        rw [hEq m, h₀]
        rw [iteratedDeriv_periodize_eqOn_Ioo Real.two_pi_pos j hyopen,
          iteratedDeriv_periodize_eqOn_Ioo Real.two_pi_pos j hyopen]
      rw [hderiv]
      exact hM m hm y
  rw [← Filter.eventually_all_finset] at hstep
  rw [← eventually_atTop]
  filter_upwards [hstep] with m hm
  have hcn : (cnorm N (hSeq m - h) : ℝ) ≤ ((N : ℝ) + 1) * C := by
    apply cnorm_le_of_uniform_bound (le_of_lt hC)
    intro j hj θ
    exact le_of_lt (hm j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) θ)
  have hlt : ((N : ℝ) + 1) * C < ε := by
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc
      ((N : ℝ) + 1) * C = ε / 2 := by
        dsimp [C]
        field_simp [ne_of_gt hN]
      _ < ε := by linarith
  have hnonneg : (0 : ℝ) ≤ (cnorm N (hSeq m - h) : ℝ) :=
    (cnorm N _).coe_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hcn hlt

private theorem upper_cutoff_tendsto {h : TestFn} {g₀ : ℝ → ℂ} {gSeq : ℕ → ℝ → ℂ}
    {hSeq : ℕ → TestFn} (hh : SuppUpper h)
    (h₀ : toAngle h = periodize (2 * Real.pi) g₀)
    (hEq : ∀ m, toAngle (hSeq m) = periodize (2 * Real.pi) (gSeq m))
    (hSupp : ∀ m, SuppUpper (hSeq m))
    (hconv : ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ≥ M, ∀ θ : ℝ,
      ‖iteratedDeriv N (gSeq m) θ - iteratedDeriv N g₀ θ‖ < ε) :
    Tendsto hSeq atTop (nhds h) := by
  rw [tendsto_iff_cnorm]
  intro N
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let C : ℝ := ε / (2 * ((N : ℝ) + 1))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hstep : ∀ j ∈ Finset.range (N + 1), ∀ᶠ m : ℕ in atTop, ∀ θ : ℝ,
      ‖angleDeriv j (hSeq m - h) θ‖ < C := by
    intro j hj
    obtain ⟨M, hM⟩ := hconv j C hC
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro m hm θ
    have hper : Function.Periodic (angleDeriv j (hSeq m - h)) (2 * Real.pi) := by
      rw [angleDeriv_sub]
      exact (periodic_angleDeriv j (hSeq m)).sub (periodic_angleDeriv j h)
    obtain ⟨y, hy, hmy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
    rw [hmy]
    by_cases hy0 : y = 0
    · subst y
      have hzeroSeq := (iteratedDeriv_toAngle_eq_zero_of_suppUpper (hSupp m) j).1
      have hzeroH := (iteratedDeriv_toAngle_eq_zero_of_suppUpper hh j).1
      rw [angleDeriv_sub]
      simpa [angleDeriv, hzeroSeq, hzeroH] using hC
    · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
      have hyopen : y ∈ Set.Ioo 0 (2 * Real.pi) := ⟨hypos, hy.2⟩
      have hderiv : angleDeriv j (hSeq m - h) y =
          iteratedDeriv j (gSeq m) y - iteratedDeriv j g₀ y := by
        rw [angleDeriv_sub]
        change iteratedDeriv j (toAngle (hSeq m)) y -
          iteratedDeriv j (toAngle h) y = _
        rw [hEq m, h₀]
        rw [iteratedDeriv_periodize_eqOn_Ioo Real.two_pi_pos j hyopen,
          iteratedDeriv_periodize_eqOn_Ioo Real.two_pi_pos j hyopen]
      rw [hderiv]
      exact hM m hm y
  rw [← Filter.eventually_all_finset] at hstep
  rw [← eventually_atTop]
  filter_upwards [hstep] with m hm
  have hcn : (cnorm N (hSeq m - h) : ℝ) ≤ ((N : ℝ) + 1) * C := by
    apply cnorm_le_of_uniform_bound (le_of_lt hC)
    intro j hj θ
    exact le_of_lt (hm j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)) θ)
  have hlt : ((N : ℝ) + 1) * C < ε := by
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    calc
      ((N : ℝ) + 1) * C = ε / 2 := by
        dsimp [C]
        field_simp [ne_of_gt hN]
      _ < ε := by linarith
  have hnonneg : (0 : ℝ) ≤ (cnorm N (hSeq m - h) : ℝ) :=
    (cnorm N _).coe_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hcn hlt

theorem exists_tendsto_of_suppLower {h : TestFn} (hh : SuppLower h) :
    ∃ hSeq : ℕ → TestFn,
      (∀ m, tsupport (hSeq m : Circle → ℂ) ⊆ lowerArc) ∧
      Tendsto hSeq atTop (nhds h) := by
  obtain ⟨g₀, hg₀, h₀⟩ := (suppLower_iff_zeroExtension h).1 hh
  have hπT : Real.pi < 2 * Real.pi := by linarith [Real.pi_pos]
  obtain ⟨gSeq, hgSeq, ⟨c, d, hcd⟩, hconv⟩ :=
    exists_contDiff_zero_outside_compact_tendstoUniformly hπT
      hg₀.contDiff hg₀.zero_outside
  have hgFlat : ∀ m, IsLowerFlat (gSeq m) := by
    intro m
    refine ⟨hgSeq m, ?_⟩
    intro θ hθ
    exact (hcd m).2.2.2 θ (fun hθ' => hθ ⟨(hcd m).1.trans hθ'.1,
      hθ'.2.trans (hcd m).2.2.1⟩)
  choose hSeq hEq hSupp using
    fun m : ℕ => exists_suppLower_toAngle_eq_periodize (hgFlat m)
  refine ⟨hSeq, ?_, ?_⟩
  · intro m
    exact tsupport_subset_lowerArc_of_periodize (hEq m) (hcd m).2.2.2
      (hcd m).1 (hcd m).2.2.1
  · exact lower_cutoff_tendsto hh h₀ hEq hSupp hconv

theorem exists_tendsto_of_suppUpper {h : TestFn} (hh : SuppUpper h) :
    ∃ hSeq : ℕ → TestFn,
      (∀ m, tsupport (hSeq m : Circle → ℂ) ⊆ upperArc) ∧
      Tendsto hSeq atTop (nhds h) := by
  obtain ⟨g₀, hg₀, h₀⟩ := (suppUpper_iff_zeroExtension h).1 hh
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨gSeq, hgSeq, ⟨c, d, hcd⟩, hconv⟩ :=
    exists_contDiff_zero_outside_compact_tendstoUniformly hπ
      hg₀.contDiff hg₀.zero_outside
  have hgFlat : ∀ m, IsUpperFlat (gSeq m) := by
    intro m
    refine ⟨hgSeq m, ?_⟩
    intro θ hθ
    exact (hcd m).2.2.2 θ (fun hθ' => hθ ⟨(hcd m).1.trans hθ'.1,
      hθ'.2.trans (hcd m).2.2.1⟩)
  choose hSeq hEq hSupp using
    fun m : ℕ => exists_suppUpper_toAngle_eq_periodize (hgFlat m)
  refine ⟨hSeq, ?_, ?_⟩
  · intro m
    exact tsupport_subset_upperArc_of_periodize (hEq m) (hcd m).2.2.2
      (hcd m).1 (hcd m).2.2.1
  · exact upper_cutoff_tendsto hh h₀ hEq hSupp hconv

/-! Closed supports of opposite open arcs can meet at an endpoint.  Replacing one side by the
strictly supported cutoff removes exactly that endpoint ambiguity. -/

theorem disjointSupport_of_suppUpper_of_tsupport_subset_lowerArc {f h' : TestFn}
    (hf : SuppUpper f) (hh' : tsupport (h' : Circle → ℂ) ⊆ lowerArc) :
    DisjointSupport f h' := by
  change Disjoint (tsupport (f : Circle → ℂ)) (tsupport (h' : Circle → ℂ))
  refine Set.disjoint_left.2 ?_
  intro z hzf hzh
  have hzcl := (suppUpper_iff_tsupport f).1 hf hzf
  have hzlower := hh' hzh
  rw [closure_upperArc] at hzcl
  change 0 ≤ (z : ℂ).im at hzcl
  change (z : ℂ).im < 0 at hzlower
  exact (not_lt_of_ge hzcl) hzlower

theorem disjointSupport_of_suppLower_of_tsupport_subset_upperArc {f h' : TestFn}
    (hf : SuppLower f) (hh' : tsupport (h' : Circle → ℂ) ⊆ upperArc) :
    DisjointSupport f h' := by
  change Disjoint (tsupport (f : Circle → ℂ)) (tsupport (h' : Circle → ℂ))
  refine Set.disjoint_left.2 ?_
  intro z hzf hzh
  have hzcl := (suppLower_iff_tsupport f).1 hf hzf
  have hzupper := hh' hzh
  rw [closure_lowerArc] at hzcl
  change (z : ℂ).im ≤ 0 at hzcl
  change 0 < (z : ℂ).im at hzupper
  exact (not_lt_of_ge hzcl) hzupper

end
end MobiusCPT
