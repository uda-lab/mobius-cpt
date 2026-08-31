import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ClusterPt
import MobiusCPT.TestFunctions.Analytic

/-!
# Complex and real flatness for analytic test functions

This file identifies the real Fréchet-jet flatness stored in `AnalyticTestFn` with the
source-literal formulation of [T26, Definition 3.2], in which every complex derivative tends to
zero at the two boundary points from the open exterior.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- On the open exterior, scalar restriction identifies the real iterated Fréchet derivative of
a holomorphic function with its complex derivative times the product multilinear map. -/
theorem iteratedFDerivWithin_eq_smul_mkPiAlgebraFin_of_contDiffOn_of_differentiableOn
    {toFun : ℂ → ℂ} (_hCD : ContDiffOn ℝ ∞ toFun Oexterior)
    (hDiff : DifferentiableOn ℂ toFun OexteriorInterior) (n : ℕ) {z : ℂ}
    (hz : z ∈ OexteriorInterior) :
    iteratedFDerivWithin ℝ n toFun Oexterior z =
      (iteratedDeriv n toFun z) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℂ := by
  have hzU : OexteriorInterior ∈ 𝓝 z := isOpen_OexteriorInterior.mem_nhds hz
  have hAt : AnalyticAt ℂ toFun z := hDiff.analyticAt hzU
  have hCDAt : ContDiffAt ℂ (n : ℕ) toFun z := hAt.contDiffAt
  have hsets : Oexterior =ᶠ[𝓝 z] OexteriorInterior :=
    Filter.eventuallyEq_of_mem hzU fun y hy =>
      propext ⟨fun _ => hy, fun _ => OexteriorInterior_subset_Oexterior hy⟩
  have hwithin :
      iteratedFDerivWithin ℝ n toFun Oexterior z = iteratedFDeriv ℝ n toFun z := by
    calc
      iteratedFDerivWithin ℝ n toFun Oexterior z =
          iteratedFDerivWithin ℝ n toFun OexteriorInterior z :=
        iteratedFDerivWithin_congr_set hsets n
      _ = iteratedFDeriv ℝ n toFun z :=
        iteratedFDerivWithin_of_isOpen n isOpen_OexteriorInterior hz
  have hrestrict :
      (iteratedFDeriv ℂ n toFun z).restrictScalars ℝ = iteratedFDeriv ℝ n toFun z := by
    simpa only [Function.comp_apply] using
      (hCDAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  rw [hwithin, ← hrestrict]
  ext m
  simp [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, List.prod_ofFn, mul_comm]

/-- On the open interior, the real n-th Fréchet derivative of an analytic test function is the
n-th complex derivative times the fixed product multilinear map. -/
theorem AnalyticTestFn.iteratedFDerivWithin_eq_smul_mkPiAlgebraFin
    (F : AnalyticTestFn) (n : ℕ) {z : ℂ} (hz : z ∈ OexteriorInterior) :
    iteratedFDerivWithin ℝ n F.toFun Oexterior z =
      (iteratedDeriv n F.toFun z) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℂ := by
  exact iteratedFDerivWithin_eq_smul_mkPiAlgebraFin_of_contDiffOn_of_differentiableOn
    F.contDiffOn F.differentiableOn n hz

/-- Real-jet flatness at `1` forces every complex derivative to tend to zero from the open
exterior. -/
theorem AnalyticTestFn.tendsto_iteratedDeriv_one (F : AnalyticTestFn) (n : ℕ) :
    Filter.Tendsto (iteratedDeriv n F.toFun) (nhdsWithin 1 OexteriorInterior) (nhds 0) := by
  let m : Fin n → ℂ := fun _ => 1
  have hcont : ContinuousOn
      (iteratedFDerivWithin ℝ n F.toFun Oexterior) Oexterior :=
    F.contDiffOn.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) uniqueDiffOn_Oexterior
  have hOne : (1 : ℂ) ∈ Oexterior := by simp [Oexterior]
  have htendsto : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ n F.toFun Oexterior z m)
      (nhdsWithin 1 OexteriorInterior) (nhds 0) := by
    have h := (hcont.eval_const m 1 hOne).mono_left
      (nhdsWithin_mono (1 : ℂ) OexteriorInterior_subset_Oexterior)
    simpa [F.flat_one n] using h
  apply htendsto.congr'
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun z hz => ?_
  rw [F.iteratedFDerivWithin_eq_smul_mkPiAlgebraFin n hz]
  simp [m]

/-- Real-jet flatness at `-1` forces every complex derivative to tend to zero from the open
exterior. -/
theorem AnalyticTestFn.tendsto_iteratedDeriv_neg_one (F : AnalyticTestFn) (n : ℕ) :
    Filter.Tendsto (iteratedDeriv n F.toFun) (nhdsWithin (-1 : ℂ) OexteriorInterior) (nhds 0) := by
  let m : Fin n → ℂ := fun _ => 1
  have hcont : ContinuousOn
      (iteratedFDerivWithin ℝ n F.toFun Oexterior) Oexterior :=
    F.contDiffOn.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) uniqueDiffOn_Oexterior
  have hNegOne : (-1 : ℂ) ∈ Oexterior := by simp [Oexterior]
  have htendsto : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ n F.toFun Oexterior z m)
      (nhdsWithin (-1 : ℂ) OexteriorInterior) (nhds 0) := by
    have h := (hcont.eval_const m (-1) hNegOne).mono_left
      (nhdsWithin_mono (-1 : ℂ) OexteriorInterior_subset_Oexterior)
    simpa [F.flat_neg_one n] using h
  apply htendsto.congr'
  refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun z hz => ?_
  rw [F.iteratedFDerivWithin_eq_smul_mkPiAlgebraFin n hz]
  simp [m]

/-- If all complex derivatives tend to `0` at `±1` along the open exterior, then the
corresponding real Fréchet jets vanish there. -/
theorem AnalyticTestFn.iteratedFDerivWithin_eq_zero_of_tendsto_iteratedDeriv
    {toFun : ℂ → ℂ} (hCD : ContDiffOn ℝ ∞ toFun Oexterior)
    (hDiff : DifferentiableOn ℂ toFun OexteriorInterior)
    {p : ℂ} (hp : p = 1 ∨ p = -1) (n : ℕ)
    (hTendsto : Filter.Tendsto (iteratedDeriv n toFun)
      (nhdsWithin p OexteriorInterior) (nhds 0)) :
    iteratedFDerivWithin ℝ n toFun Oexterior p = 0 := by
  have hpnorm : ‖p‖ = 1 := by
    rcases hp with rfl | rfl <;> simp
  have hpO : p ∈ Oexterior := by
    change (1 : ℝ) ≤ ‖p‖
    rw [hpnorm]
  have hcont : ContinuousOn
      (iteratedFDerivWithin ℝ n toFun Oexterior) Oexterior :=
    hCD.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) uniqueDiffOn_Oexterior
  have hpClosure : p ∈ closure OexteriorInterior := by
    have hscalar : Filter.Tendsto
        (fun k : ℕ => (1 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hradial : Filter.Tendsto
        (fun k : ℕ => ((1 : ℝ) + 1 / ((k : ℝ) + 1)) • p) atTop (nhds p) := by
      simpa using hscalar.smul_const p
    apply mem_closure_of_tendsto hradial
    filter_upwards with k
    change (1 : ℝ) < ‖((1 : ℝ) + 1 / ((k : ℝ) + 1)) • p‖
    rw [norm_smul, hpnorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1))]
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have : NeBot (nhdsWithin p OexteriorInterior) :=
    mem_closure_iff_nhdsWithin_neBot.mp hpClosure
  ext m
  have hFromBoundary : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ n toFun Oexterior z m)
      (nhdsWithin p OexteriorInterior)
      (nhds (iteratedFDerivWithin ℝ n toFun Oexterior p m)) :=
    (hcont.eval_const m p hpO).mono_left
      (nhdsWithin_mono p OexteriorInterior_subset_Oexterior)
  have hToZero : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ n toFun Oexterior z m)
      (nhdsWithin p OexteriorInterior) (nhds 0) := by
    have heq : Filter.Tendsto
        (fun z => iteratedDeriv n toFun z * (∏ i, m i))
        (nhdsWithin p OexteriorInterior) (nhds 0) := by
      simpa using hTendsto.mul_const (∏ i, m i)
    apply heq.congr'
    refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun z hz => ?_
    rw [iteratedFDerivWithin_eq_smul_mkPiAlgebraFin_of_contDiffOn_of_differentiableOn
      hCD hDiff n hz]
    simp [smul_eq_mul, List.prod_ofFn]
  simpa using tendsto_nhds_unique hFromBoundary hToZero

/-- [T26], Definition 3.2, literal form: build an analytic test function from smoothness on the
closed exterior, holomorphy on its interior, vanishing at infinity, and complex flatness at the
two boundary points. -/
noncomputable def AnalyticTestFn.ofComplexFlat (toFun : ℂ → ℂ)
    (hCD : ContDiffOn ℝ ∞ toFun Oexterior)
    (hDiff : DifferentiableOn ℂ toFun OexteriorInterior)
    (hZero : Filter.Tendsto toFun (Filter.cocompact ℂ) (nhds 0))
    (hFlatOne : ∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
      (nhdsWithin 1 OexteriorInterior) (nhds 0))
    (hFlatNegOne : ∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
      (nhdsWithin (-1 : ℂ) OexteriorInterior) (nhds 0)) :
    AnalyticTestFn where
  toFun := toFun
  contDiffOn := hCD
  differentiableOn := hDiff
  tendsto_zero := hZero
  flat_one n := AnalyticTestFn.iteratedFDerivWithin_eq_zero_of_tendsto_iteratedDeriv
    hCD hDiff (Or.inl rfl) n (hFlatOne n)
  flat_neg_one n := AnalyticTestFn.iteratedFDerivWithin_eq_zero_of_tendsto_iteratedDeriv
    hCD hDiff (Or.inr rfl) n (hFlatNegOne n)

@[simp] theorem AnalyticTestFn.ofComplexFlat_toFun (toFun : ℂ → ℂ)
    (hCD : ContDiffOn ℝ ∞ toFun Oexterior)
    (hDiff : DifferentiableOn ℂ toFun OexteriorInterior)
    (hZero : Filter.Tendsto toFun (Filter.cocompact ℂ) (nhds 0))
    (hFlatOne : ∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
      (nhdsWithin 1 OexteriorInterior) (nhds 0))
    (hFlatNegOne : ∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
      (nhdsWithin (-1 : ℂ) OexteriorInterior) (nhds 0)) :
    (AnalyticTestFn.ofComplexFlat toFun hCD hDiff hZero hFlatOne hFlatNegOne).toFun = toFun :=
  rfl

/-- [T26], Definition 3.2: membership in the analytic test-function class is equivalent to the
source-literal smoothness, holomorphy, vanishing-at-infinity, and complex-flatness conditions. -/
theorem AnalyticTestFn.exists_iff_complexFlat (toFun : ℂ → ℂ) :
    (∃ F : AnalyticTestFn, F.toFun = toFun) ↔
      ∃ (hCD : ContDiffOn ℝ ∞ toFun Oexterior)
        (hDiff : DifferentiableOn ℂ toFun OexteriorInterior),
        Filter.Tendsto toFun (Filter.cocompact ℂ) (nhds 0) ∧
        (∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
          (nhdsWithin 1 OexteriorInterior) (nhds 0)) ∧
        (∀ n : ℕ, Filter.Tendsto (iteratedDeriv n toFun)
          (nhdsWithin (-1 : ℂ) OexteriorInterior) (nhds 0)) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.contDiffOn, F.differentiableOn, F.tendsto_zero,
      F.tendsto_iteratedDeriv_one, F.tendsto_iteratedDeriv_neg_one⟩
  · rintro ⟨hCD, hDiff, hZero, hFlatOne, hFlatNegOne⟩
    exact ⟨AnalyticTestFn.ofComplexFlat toFun hCD hDiff hZero hFlatOne hFlatNegOne, rfl⟩

end

end MobiusCPT
