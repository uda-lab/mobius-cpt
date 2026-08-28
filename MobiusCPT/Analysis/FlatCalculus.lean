import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.Taylor

/-!
# Flat extension lemmas

Taylor estimates and removable-flat-point results used in the analytic core of [T26, Lemma 3.4].
The plane result records the complex derivatives of a punctured holomorphic function as a real
formal Taylor series, so no comparison between complex and real iterated Frechet derivatives is
needed at the flat point.
-/

noncomputable section

open Asymptotics Filter Set
open scoped ContDiff Topology

namespace MobiusCPT

/-- A smooth function all of whose derivatives vanish at `p` is `O((y - p) ^ M)` to the right of
`p`, for every `M`. -/
theorem exists_norm_le_pow_of_iteratedDeriv_eq_zero {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {p r : ℝ} (hr : 0 < r) (hflat : ∀ j : ℕ, iteratedDeriv j g p = 0) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Set.Icc p (p + r), ‖g y‖ ≤ K * (y - p) ^ M := by
  let s : Set ℝ := Set.Icc p (p + r)
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_Icc (by linarith)
  have hp : p ∈ s := by
    dsimp [s]
    exact ⟨le_rfl, by linarith⟩
  have hderiv (j : ℕ) : iteratedDerivWithin j g s p = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hg.contDiffAt.of_le (by exact_mod_cast le_top)) hp, hflat j]
  cases M with
  | zero =>
      obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuous.continuousOn
      refine ⟨max K 0, le_max_right _ _, ?_⟩
      intro y hy
      calc
        ‖g y‖ ≤ K := hK y hy
        _ ≤ max K 0 * (y - p) ^ 0 := by
          simpa only [pow_zero, mul_one] using le_max_left K 0
  | succ M =>
      have hcont : ContinuousOn (iteratedDerivWithin (M + 1) g s) s :=
        hg.contDiffOn.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) hs
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      have hCnonneg : 0 ≤ C := (norm_nonneg _).trans (hC p hp)
      have htaylor (y : ℝ) : taylorWithinEval g M s p y = 0 := by
        rw [taylor_within_apply]
        apply Finset.sum_eq_zero
        intro j hj
        rw [hderiv j]
        exact smul_zero _
      refine ⟨C / (Nat.factorial M : ℝ), div_nonneg hCnonneg (Nat.cast_nonneg _), ?_⟩
      intro y hy
      have hrem := taylor_mean_remainder_bound (n := M) (show p ≤ p + r by linarith)
        (hg.contDiffOn.of_le (by exact_mod_cast le_top)) hy hC
      rw [htaylor y, sub_zero] at hrem
      calc
        ‖g y‖ ≤ C * (y - p) ^ (M + 1) / (Nat.factorial M : ℝ) := hrem
        _ = (C / (Nat.factorial M : ℝ)) * (y - p) ^ (M + 1) := by ring

/-- A quadratic right-hand bound, together with vanishing on the left, gives derivative zero at
the gluing point. -/
private theorem hasDerivAt_zero_of_quadratic_bound {f : ℝ → ℂ}
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hflat : ∀ k M : ℕ, ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖iteratedDeriv k f x‖ ≤ K * x ^ M) :
    HasDerivAt f 0 0 := by
  have hf0 : f 0 = 0 := hzero 0 le_rfl
  obtain ⟨K, hK⟩ := hflat 0 2
  have hKone := hK 1 zero_lt_one le_rfl
  simp only [iteratedDeriv_zero, one_pow, mul_one] at hKone
  have hKnonneg : 0 ≤ K := (norm_nonneg _).trans hKone
  have hbig : (fun x : ℝ ↦ f x - f 0) =O[𝓝 0] fun x : ℝ ↦ ‖x‖ ^ 2 := by
    apply IsBigO.of_bound K
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with x hx
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    by_cases hxp : 0 < x
    · have hxone : x ≤ 1 := (le_abs_self x).trans (le_of_lt hx)
      have hb := hK x hxp hxone
      simp only [iteratedDeriv_zero] at hb
      simpa [hf0, Real.norm_eq_abs, abs_of_pos hxp] using hb
    · have hxnonpos : x ≤ 0 := le_of_not_gt hxp
      rw [hzero x hxnonpos, hf0, sub_zero, norm_zero]
      exact mul_nonneg hKnonneg (norm_nonneg _)
  have hsmall : (fun x : ℝ ↦ f x - f 0) =o[𝓝 0] fun x : ℝ ↦ x :=
    hbig.trans_isLittleO (isLittleO_norm_pow_id (n := 2) (by norm_num))
  rw [hasDerivAt_iff_isLittleO]
  simpa [hf0] using hsmall

/-- The hypotheses of the real flat-extension theorem imply differentiability at every point. -/
private theorem differentiable_of_flat_at_zero {f : ℝ → ℂ}
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hsmooth : ContDiffOn ℝ ∞ f (Set.Ioi 0))
    (hflat : ∀ k M : ℕ, ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖iteratedDeriv k f x‖ ≤ K * x ^ M) :
    Differentiable ℝ f := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : f =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℂ) :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hx) fun y hy ↦ hzero y hy.le
    exact ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq heq).differentiableAt
  · exact (hasDerivAt_zero_of_quadratic_bound hzero hflat).differentiableAt
  · exact (hsmooth.differentiableOn (by simp) x hx).differentiableAt (Ioi_mem_nhds hx)

/-- A function vanishing on `(-∞, 0]`, smooth on `(0, ∞)`, and vanishing to infinite order at
`0` from the right, is smooth on the whole line. -/
theorem contDiff_of_flat_at_zero {f : ℝ → ℂ}
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hsmooth : ContDiffOn ℝ ∞ f (Set.Ioi 0))
    (hflat : ∀ k M : ℕ, ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖iteratedDeriv k f x‖ ≤ K * x ^ M) :
    ContDiff ℝ ∞ f := by
  have hfinite : ∀ n : ℕ, ∀ f : ℝ → ℂ,
      (∀ x : ℝ, x ≤ 0 → f x = 0) →
      ContDiffOn ℝ ∞ f (Set.Ioi 0) →
      (∀ k M : ℕ, ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖iteratedDeriv k f x‖ ≤ K * x ^ M) →
      ContDiff ℝ n f := by
    intro n
    induction n with
    | zero =>
        intro f hzero hsmooth hflat
        change ContDiff ℝ (0 : ℕ∞ω) f
        rw [contDiff_zero]
        exact (differentiable_of_flat_at_zero hzero hsmooth hflat).continuous
    | succ n ih =>
        intro f hzero hsmooth hflat
        have hdiff : Differentiable ℝ f :=
          differentiable_of_flat_at_zero hzero hsmooth hflat
        have hderiv0 : deriv f 0 = 0 :=
          (hasDerivAt_zero_of_quadratic_bound hzero hflat).deriv
        have hzero' : ∀ x : ℝ, x ≤ 0 → deriv f x = 0 := by
          intro x hx
          rcases lt_or_eq_of_le hx with hlt | rfl
          · have heq : f =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℂ) :=
              Filter.eventuallyEq_of_mem (Iio_mem_nhds hlt) fun y hy ↦ hzero y hy.le
            exact ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq heq).deriv
          · exact hderiv0
        have hsmooth' : ContDiffOn ℝ ∞ (deriv f) (Set.Ioi 0) :=
          (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hsmooth |>.2
        have hflat' : ∀ k M : ℕ, ∃ K : ℝ, ∀ x : ℝ, 0 < x → x ≤ 1 →
            ‖iteratedDeriv k (deriv f) x‖ ≤ K * x ^ M := by
          intro k M
          obtain ⟨K, hK⟩ := hflat (k + 1) M
          refine ⟨K, ?_⟩
          intro x hx hxone
          simpa only [← iteratedDeriv_succ'] using hK x hx hxone
        have hderiv : ContDiff ℝ (n : ℕ∞ω) (deriv f) :=
          ih (deriv f) hzero' hsmooth' hflat'
        have hs : ContDiff ℝ ((n : ℕ∞ω) + 1) f :=
          contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, hderiv⟩
        simpa only [Nat.cast_succ] using hs
  exact contDiff_infty.mpr (fun n ↦ hfinite n f hzero hsmooth hflat)

/-- The candidate real Taylor series of a holomorphic function: the `n`-th term is the complex
`n`-th derivative times the `n`-fold product form, and `0` at the flat point. -/
noncomputable def flatSeries (f : ℂ → ℂ) (p : ℂ) (z : ℂ) :
    FormalMultilinearSeries ℝ ℂ ℂ :=
  fun n ↦ if z = p then 0
    else (iteratedDeriv n f z) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℂ

/-- Currying a complex multiple of the real product form extracts its first factor. -/
private theorem curryLeft_flatSeries_term (m : ℕ) (a : ℂ) :
    (a • ContinuousMultilinearMap.mkPiAlgebraFin ℝ (m + 1) ℂ).curryLeft =
      ((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).smulRight
        (ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ) := by
  ext v x
  change a * (List.ofFn (Fin.cons v x)).prod = (v * a) * (List.ofFn x).prod
  rw [List.ofFn_cons, List.prod_cons]
  ring

/-- Away from the flat point, the candidate series differentiates by shifting its index. -/
private theorem hasFDerivWithinAt_flatSeries_of_ne {S : Set ℂ} {p z : ℂ} {f : ℂ → ℂ}
    (hz : z ≠ p) (ha : AnalyticAt ℂ f z) (m : ℕ) :
    HasFDerivWithinAt (flatSeries f p · m) (flatSeries f p z (m + 1)).curryLeft S z := by
  have ham : AnalyticAt ℂ (iteratedDeriv m f) z := by
    simpa only [iteratedDeriv_eq_iterate] using ha.iterated_deriv m
  have hc : HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f z) z := by
    simpa only [iteratedDeriv_succ] using ham.differentiableAt.hasDerivAt
  have hreal := hc.hasFDerivAt.restrictScalars ℝ
  have hterm := hreal.smul_const (ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ)
  have hterm' : HasFDerivAt
      (fun y ↦ (iteratedDeriv m f y) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ)
      ((iteratedDeriv (m + 1) f z •
        ContinuousMultilinearMap.mkPiAlgebraFin ℝ (m + 1) ℂ).curryLeft) z := by
    rw [curryLeft_flatSeries_term]
    exact hterm
  have hwithin := hterm'.hasFDerivWithinAt.congr_of_eventuallyEq
    (show (flatSeries f p · m) =ᶠ[𝓝[S] z]
      (fun y ↦ (iteratedDeriv m f y) •
        ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ) by
      filter_upwards [eventually_ne_nhdsWithin hz] with y hy
      simp only [flatSeries, if_neg hy])
    (by simp only [flatSeries, if_neg hz])
  simpa only [flatSeries, if_neg hz] using hwithin

/-- At the flat point, the quadratic coefficient estimate makes every candidate series term have
zero real Frechet derivative. -/
private theorem hasFDerivWithinAt_flatSeries_at {S : Set ℂ} {p : ℂ} {f : ℂ → ℂ}
    (_hp : p ∈ S)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ S, z ≠ p →
      ‖iteratedDeriv n f z‖ ≤ C * ‖z - p‖ ^ 2)
    (m : ℕ) :
    HasFDerivWithinAt (flatSeries f p · m) (flatSeries f p p (m + 1)).curryLeft S p := by
  obtain ⟨C, hC⟩ := hbound m
  have hbig : (flatSeries f p · m) =O[𝓝[S] p] fun z : ℂ ↦ ‖z - p‖ ^ 2 := by
    apply IsBigO.of_bound C
    filter_upwards [self_mem_nhdsWithin] with z hz
    by_cases hzp : z = p
    · subst z
      simp [flatSeries]
    · calc
        ‖flatSeries f p z m‖ =
            ‖(iteratedDeriv m f z) •
              ContinuousMultilinearMap.mkPiAlgebraFin ℝ m ℂ‖ := by
              rw [flatSeries, if_neg hzp]
        _ = ‖iteratedDeriv m f z‖ := by
              rw [norm_smul, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
        _ ≤ C * ‖z - p‖ ^ 2 := hC z hz hzp
        _ = C * ‖‖z - p‖ ^ 2‖ := by
              rw [Real.norm_of_nonneg (sq_nonneg ‖z - p‖)]
  have hpow : (fun z : ℂ ↦ ‖z - p‖ ^ 2) =o[𝓝[S] p] fun z : ℂ ↦ z - p :=
    (isLittleO_pow_sub_sub p (m := 2) (by norm_num)).mono nhdsWithin_le_nhds
  have hsmall : (flatSeries f p · m) =o[𝓝[S] p] fun z : ℂ ↦ z - p :=
    hbig.trans_isLittleO hpow
  have hderiv : HasFDerivWithinAt (flatSeries f p · m)
      (0 : ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => ℂ) ℂ) S p := by
    apply HasFDerivWithinAt.of_isLittleO
    simpa [flatSeries] using hsmall
  have hzero : (flatSeries f p p (m + 1)).curryLeft =
      (0 : ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m => ℂ) ℂ) := by
    have hz : flatSeries f p p (m + 1) = 0 := by simp [flatSeries]
    rw [hz]
    ext v x
    simp
  rw [hzero]
  exact hderiv

/-- The candidate series is a real Taylor series on a punctured holomorphic set after filling the
flat point. -/
private theorem hasFTaylorSeriesUpToOn_flatSeries {U : Set ℂ} {p : ℂ} {f : ℂ → ℂ}
    {r : ℝ} (hr : 0 < r) (hp : p ∈ U) (hfp : f p = 0)
    (hholo : ∀ z ∈ U ∩ Metric.ball p r, z ≠ p → AnalyticAt ℂ f z)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ U ∩ Metric.ball p r, z ≠ p →
      ‖iteratedDeriv n f z‖ ≤ C * ‖z - p‖ ^ 2) :
    HasFTaylorSeriesUpToOn ∞ f (flatSeries f p) (U ∩ Metric.ball p r) := by
  apply (hasFTaylorSeriesUpToOn_top_iff' (N := ∞) le_rfl).mpr
  constructor
  · intro z hz
    by_cases hzp : z = p
    · subst z
      simp [flatSeries, hfp]
    · simp [flatSeries, hzp]
  · intro m z hz
    by_cases hzp : z = p
    · subst z
      exact hasFDerivWithinAt_flatSeries_at (S := U ∩ Metric.ball p r)
        ⟨hp, Metric.mem_ball_self hr⟩ hbound m
    · exact hasFDerivWithinAt_flatSeries_of_ne hzp (hholo z hz hzp) m

/-- Let `f` be holomorphic on a punctured neighbourhood of `p` and let every complex derivative of
`f` vanish there to second order. Then `f` is `C^∞` in the real sense within `U` at `p`. -/
theorem contDiffWithinAt_of_flat_holomorphic {U : Set ℂ} {p : ℂ} {f : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hp : p ∈ U) (hfp : f p = 0)
    (hholo : ∀ z ∈ U ∩ Metric.ball p r, z ≠ p → AnalyticAt ℂ f z)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ U ∩ Metric.ball p r, z ≠ p →
      ‖iteratedDeriv n f z‖ ≤ C * ‖z - p‖ ^ 2) :
    ContDiffWithinAt ℝ ∞ f U p := by
  have hseries := hasFTaylorSeriesUpToOn_flatSeries hr hp hfp hholo hbound
  rw [contDiffWithinAt_infty]
  intro n
  rw [contDiffWithinAt_nat]
  refine ⟨U ∩ Metric.ball p r, ?_, flatSeries f p, hseries.of_le (by exact_mod_cast le_top)⟩
  rw [insert_eq_of_mem hp]
  exact inter_mem_nhdsWithin U (Metric.ball_mem_nhds p hr)

/-- Under unique differentiability of `U`, every real Frechet jet of the flat holomorphic extension
at `p` is zero. -/
theorem iteratedFDerivWithin_eq_zero_of_flat_holomorphic {U : Set ℂ} {p : ℂ}
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hU : UniqueDiffOn ℝ U) (hp : p ∈ U)
    (hfp : f p = 0)
    (hholo : ∀ z ∈ U ∩ Metric.ball p r, z ≠ p → AnalyticAt ℂ f z)
    (hbound : ∀ n : ℕ, ∃ C : ℝ, ∀ z ∈ U ∩ Metric.ball p r, z ≠ p →
      ‖iteratedDeriv n f z‖ ≤ C * ‖z - p‖ ^ 2)
    (n : ℕ) :
    iteratedFDerivWithin ℝ n f U p = 0 := by
  have hseries := hasFTaylorSeriesUpToOn_flatSeries hr hp hfp hholo hbound
  have hp' : p ∈ U ∩ Metric.ball p r := ⟨hp, Metric.mem_ball_self hr⟩
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) (by exact_mod_cast le_top)
    (hU.inter Metric.isOpen_ball) hp'
  calc
    iteratedFDerivWithin ℝ n f U p =
        iteratedFDerivWithin ℝ n f (U ∩ Metric.ball p r) p :=
      (iteratedFDerivWithin_inter (f := f) (s := U)
        (Metric.ball_mem_nhds p hr)).symm
    _ = flatSeries f p p n := heq.symm
    _ = 0 := by simp [flatSeries]

end MobiusCPT
