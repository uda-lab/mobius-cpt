import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Homeomorph.Lemmas
import MobiusCPT.TestFunctions.AnalyticDensity

/-!
# MobiusCPT.TestFunctions.AnalyticReflect

The reflection `F ↦ conj ∘ F ∘ conj` preserves the class `𝓧`, and its counterpart
`starTestFn : f ↦ conj ∘ f ∘ conj` on test functions exchanges the two semicircle restrictions, so
the upper density statement transports to the lower one.

`starTestFn` is a proof device for that transport only.  It is **not** `TestFn.inv` (precomposition
with `z ↦ z⁻¹`), which is what `MobiusCPT.Contract` uses in `beta_boost_at_ipi`, `lemma_3_7_at_ipi`
and `w3_vacuum_annihilation`: on `S¹` the two differ by a pointwise complex conjugation
(`starTestFn = conj ∘ inv` there), and only `starTestFn` is norm-preserving *and* compatible with
conjugating an element of `𝓧`.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- The reflected angle picture of a smooth test function. -/
private def starAngle (f : TestFn) : ℝ → ℂ :=
  fun θ : ℝ => (starRingEnd ℂ) (toAngle f (-θ))

/-- The reflected angle picture is smooth. -/
private theorem contDiff_starAngle (f : TestFn) : ContDiff ℝ ∞ (starAngle f) := by
  have hinner : ContDiff ℝ ∞ (fun θ : ℝ => toAngle f (-θ)) :=
    (contDiff_toAngle f).comp contDiff_neg
  have houter : ContDiff ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) := by
    have h : ContDiff ℝ ∞ (Complex.conjCLE : ℂ → ℂ) := Complex.conjCLE.contDiff
    exact h
  exact houter.comp hinner

/-- The reflected angle picture has the same period as the original one. -/
private theorem periodic_starAngle (f : TestFn) :
    Function.Periodic (starAngle f) (2 * Real.pi) := by
  have hneg : Function.Periodic (fun θ : ℝ => toAngle f (-θ)) (2 * Real.pi) := by
    simpa only [zero_sub] using (periodic_toAngle f).const_sub 0
  exact hneg.comp (starRingEnd ℂ)

/-- [T26], §3; the reflection `f ↦ conj ∘ f ∘ conj` of a test function, which exchanges
the two semicircles. -/
noncomputable def starTestFn (f : TestFn) : TestFn :=
  Classical.choose (exists_toAngle_eq (contDiff_starAngle f) (periodic_starAngle f))

/-- The angle picture of the reflected test function. -/
theorem toAngle_starTestFn (f : TestFn) :
    toAngle (starTestFn f) =
      fun θ : ℝ => (starRingEnd ℂ) (toAngle f (-θ)) := by
  change toAngle (Classical.choose
      (exists_toAngle_eq (contDiff_starAngle f) (periodic_starAngle f))) =
    fun θ : ℝ => (starRingEnd ℂ) (toAngle f (-θ))
  exact Classical.choose_spec (exists_toAngle_eq (contDiff_starAngle f) (periodic_starAngle f))

/-- Reflection is an involution on smooth test functions. -/
theorem starTestFn_starTestFn (f : TestFn) : starTestFn (starTestFn f) = f := by
  apply toAngle_injective
  calc
    toAngle (starTestFn (starTestFn f)) =
        fun θ : ℝ => (starRingEnd ℂ) (toAngle (starTestFn f) (-θ)) :=
      toAngle_starTestFn (starTestFn f)
    _ = fun θ : ℝ =>
        (starRingEnd ℂ) ((starRingEnd ℂ) (toAngle f (-(-θ)))) := by
      funext θ
      rw [congrFun (toAngle_starTestFn f) (-θ)]
    _ = toAngle f := by
      funext θ
      simp

/-- Reflection is additive on differences of test functions. -/
theorem starTestFn_sub (f g : TestFn) :
    starTestFn (f - g) = starTestFn f - starTestFn g := by
  apply toAngle_injective
  funext θ
  calc
    toAngle (starTestFn (f - g)) θ =
        (starRingEnd ℂ) (toAngle (f - g) (-θ)) :=
      congrFun (toAngle_starTestFn (f - g)) θ
    _ = (starRingEnd ℂ) (toAngle f (-θ) - toAngle g (-θ)) := by
      simp only [toAngle_sub, Pi.sub_apply]
    _ = (starRingEnd ℂ) (toAngle f (-θ)) -
        (starRingEnd ℂ) (toAngle g (-θ)) := by
      exact map_sub (starRingEnd ℂ) _ _
    _ = toAngle (starTestFn f) θ - toAngle (starTestFn g) θ := by
      rw [congrFun (toAngle_starTestFn f) θ, congrFun (toAngle_starTestFn g) θ]
    _ = toAngle (starTestFn f - starTestFn g) θ := by
      simp only [toAngle_sub, Pi.sub_apply]

/-- Iterated real derivatives commute with complex conjugation on the values. -/
private theorem iteratedDeriv_star_comp (q : ℝ → ℂ) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => (starRingEnd ℂ) (q x)) =
      fun x : ℝ => (starRingEnd ℂ) (iteratedDeriv j q x) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [starRingEnd_apply, iteratedDeriv_succ] using
        (deriv.star (f := iteratedDeriv j q) (x := x))

/-- The angle derivatives of reflection are reflected with the expected sign. -/
theorem angleDeriv_starTestFn (j : ℕ) (f : TestFn) (θ : ℝ) :
    angleDeriv j (starTestFn f) θ =
      (-1) ^ j * (starRingEnd ℂ) (angleDeriv j f (-θ)) := by
  rw [angleDeriv, toAngle_starTestFn]
  change iteratedDeriv j
      (fun x : ℝ => (starRingEnd ℂ) (toAngle f (-x))) θ = _
  have hstar := congrFun
    (iteratedDeriv_star_comp (fun x : ℝ => toAngle f (-x)) j) θ
  rw [hstar]
  have hneg := iteratedDeriv_comp_neg j (toAngle f) θ
  rw [hneg]
  rw [angleDeriv]
  simp [Complex.real_smul, smul_eq_mul, Complex.star_def]

/-- Complex conjugation preserves the pointwise norms of reflected angle derivatives. -/
theorem norm_angleDeriv_starTestFn (j : ℕ) (f : TestFn) (θ : ℝ) :
    ‖angleDeriv j (starTestFn f) θ‖ = ‖angleDeriv j f (-θ)‖ := by
  rw [angleDeriv_starTestFn]
  simp

/-- The `C^N` norm is invariant under reflection. -/
theorem cnorm_starTestFn (N : ℕ) (f : TestFn) :
    cnorm N (starTestFn f) = cnorm N f := by
  apply NNReal.eq
  rw [cnorm_eq, cnorm_eq]
  apply Finset.sum_congr rfl
  intro j hj
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro θ
    rw [angleDerivB_apply, norm_angleDeriv_starTestFn]
    exact norm_angleDeriv_le j f (-θ)
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro θ
    calc
      ‖angleDeriv j f θ‖ = ‖angleDeriv j (starTestFn f) (-θ)‖ := by
        rw [norm_angleDeriv_starTestFn]
        simp
      _ = ‖angleDerivB j (starTestFn f) (-θ)‖ := by
        rw [angleDerivB_apply]
      _ ≤ ‖angleDerivB j (starTestFn f)‖ :=
        BoundedContinuousFunction.norm_coe_le_norm
          (angleDerivB j (starTestFn f)) (-θ)

/-- Reflection sends lower-supported test functions to upper-supported ones. -/
theorem suppUpper_starTestFn {f : TestFn} (h : SuppLower f) :
    SuppUpper (starTestFn f) := by
  apply (suppUpper_iff_angle (starTestFn f)).2
  intro θ hθ
  obtain ⟨hθpi, hθtwo⟩ := hθ
  have hperiod := periodic_toAngle f (-θ)
  have harg : toAngle f (-θ) = toAngle f (2 * Real.pi - θ) := by
    calc
      toAngle f (-θ) = toAngle f (-θ + 2 * Real.pi) := hperiod.symm
      _ = toAngle f (2 * Real.pi - θ) := by congr 1 <;> ring
  have hzero : toAngle f (2 * Real.pi - θ) = 0 :=
    (suppLower_iff_angle f).1 h (2 * Real.pi - θ)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [congrFun (toAngle_starTestFn f) θ, harg, hzero]
  simp

/-- Reflection sends upper-supported test functions to lower-supported ones. -/
theorem suppLower_starTestFn {f : TestFn} (h : SuppUpper f) :
    SuppLower (starTestFn f) := by
  apply (suppLower_iff_angle (starTestFn f)).2
  intro θ hθ
  obtain ⟨hθzero, hθpi⟩ := hθ
  have hperiod := periodic_toAngle f (-θ)
  have harg : toAngle f (-θ) = toAngle f (2 * Real.pi - θ) := by
    calc
      toAngle f (-θ) = toAngle f (-θ + 2 * Real.pi) := hperiod.symm
      _ = toAngle f (2 * Real.pi - θ) := by congr 1 <;> ring
  have hzero : toAngle f (2 * Real.pi - θ) = 0 :=
    (suppUpper_iff_angle f).1 h (2 * Real.pi - θ)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [congrFun (toAngle_starTestFn f) θ, harg, hzero]
  simp

/-- Reflection is continuous in the smooth test-function topology. -/
theorem tendsto_starTestFn {u : ℕ → TestFn} {f : TestFn}
    (h : Tendsto u atTop (nhds f)) :
    Tendsto (fun n => starTestFn (u n)) atTop (nhds (starTestFn f)) := by
  apply (tendsto_iff_cnorm (fun n => starTestFn (u n)) (starTestFn f)).2
  intro N
  have hN := (tendsto_iff_cnorm u f).1 h N
  have hEq :
      (fun n => ((cnorm N (starTestFn (u n) - starTestFn f) : NNReal) : ℝ)) =
        (fun n => ((cnorm N (u n - f) : NNReal) : ℝ)) := by
    funext n
    rw [← starTestFn_sub, cnorm_starTestFn]
  rw [hEq]
  exact hN

/-- Conjugation preserves the closed exterior of the unit disk. -/
private theorem conj_preimage_Oexterior :
    (Complex.conjLIE : ℂ → ℂ) ⁻¹' Oexterior = Oexterior := by
  ext z
  change (1 : ℝ) ≤ ‖Complex.conjLIE z‖ ↔ (1 : ℝ) ≤ ‖z‖
  simp [Complex.conjLIE_apply]

/-- Conjugation through its continuous-linear equivalence preserves the closed exterior. -/
private theorem conjCLE_preimage_Oexterior :
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ) : ℂ → ℂ) ⁻¹' Oexterior = Oexterior := by
  ext z
  change (1 : ℝ) ≤ ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ) z‖ ↔ (1 : ℝ) ≤ ‖z‖
  simp

/-- Conjugation preserves the open exterior of the unit disk. -/
private theorem conj_preimage_OexteriorInterior :
    (Complex.conjLIE : ℂ → ℂ) ⁻¹' OexteriorInterior = OexteriorInterior := by
  ext z
  change (1 : ℝ) < ‖Complex.conjLIE z‖ ↔ (1 : ℝ) < ‖z‖
  simp [Complex.conjLIE_apply]

/-- Conjugation of a complex derivative has the conjugated derivative. -/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ}
    (h : HasDerivAt f f' ((starRingEnd ℂ) z)) :
    HasDerivAt
      (fun w : ℂ => (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) f') z := by
  have h2 := h.conj_conj
  have hz : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := Complex.conj_conj z
  rw [hz] at h2
  exact h2

/-- Transport the norms of all real jets through `conj ∘ F ∘ conj`. -/
private theorem norm_iteratedFDerivWithin_conj_conj (F : AnalyticTestFn) (n : ℕ)
    {z : ℂ} (hz : z ∈ Oexterior) :
    ‖iteratedFDerivWithin ℝ n
        (fun w : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))) Oexterior z‖ =
      ‖iteratedFDerivWithin ℝ n F.toFun Oexterior ((starRingEnd ℂ) z)‖ := by
  have hzpre : z ∈ (Complex.conjLIE : ℂ → ℂ) ⁻¹' Oexterior := by
    rw [conj_preimage_Oexterior]
    exact hz
  have hfun :
      (fun w : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))) =
        (Complex.conjLIE : ℂ → ℂ) ∘ F.toFun ∘ (Complex.conjLIE : ℂ → ℂ) := by
    funext w
    change (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w)) =
      (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))
    rfl
  calc
    ‖iteratedFDerivWithin ℝ n
        (fun w : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))) Oexterior z‖ =
      ‖iteratedFDerivWithin ℝ n
          ((Complex.conjLIE : ℂ → ℂ) ∘ F.toFun ∘
            (Complex.conjLIE : ℂ → ℂ)) Oexterior z‖ :=
      by
        rw [hfun]
    _ = ‖iteratedFDerivWithin ℝ n
          (F.toFun ∘ (Complex.conjLIE : ℂ → ℂ)) Oexterior z‖ := by
      exact Complex.conjLIE.norm_iteratedFDerivWithin_comp_left
        (F.toFun ∘ (Complex.conjLIE : ℂ → ℂ)) uniqueDiffOn_Oexterior hz n
    _ = ‖iteratedFDerivWithin ℝ n
          (F.toFun ∘ (Complex.conjLIE : ℂ → ℂ))
          ((Complex.conjLIE : ℂ → ℂ) ⁻¹' Oexterior) z‖ := by
      rw [conj_preimage_Oexterior]
    _ = ‖iteratedFDerivWithin ℝ n F.toFun Oexterior
          ((Complex.conjLIE : ℂ → ℂ) z)‖ := by
      exact Complex.conjLIE.norm_iteratedFDerivWithin_comp_right F.toFun
        uniqueDiffOn_Oexterior hzpre n

/-- [T26], Definition 3.2; the class `𝓧` is stable under the reflection `F ↦ conj ∘ F ∘ conj`. -/
noncomputable def AnalyticTestFn.conj (F : AnalyticTestFn) : AnalyticTestFn where
  toFun := fun z : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) z))
  contDiffOn := by
    have hcomp := F.contDiffOn.comp_continuousLinearMap
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)
    have hout := hcomp.continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)
    rw [conjCLE_preimage_Oexterior] at hout
    have hfun :
        (fun z : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) z))) =
          (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ F.toFun ∘
            (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
      funext z
      change (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) z)) =
        (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) z))
      rfl
    rw [hfun]
    exact hout
  differentiableOn := by
    intro z hz
    have hz' : (starRingEnd ℂ) z ∈ OexteriorInterior := by
      change (1 : ℝ) < ‖(starRingEnd ℂ) z‖
      simpa [OexteriorInterior, Complex.star_def] using hz
    have hF : DifferentiableAt ℂ F.toFun ((starRingEnd ℂ) z) :=
      (F.differentiableOn ((starRingEnd ℂ) z) hz').differentiableAt
        (isOpen_OexteriorInterior.mem_nhds hz')
    exact (hasDerivAt_conj_conj hF.hasDerivAt).differentiableAt.differentiableWithinAt
  tendsto_zero := by
    have hc : Tendsto (Complex.conjLIE.toHomeomorph : ℂ → ℂ)
        (cocompact ℂ) (cocompact ℂ) := by
      change Filter.map (Complex.conjLIE.toHomeomorph : ℂ → ℂ) (cocompact ℂ) ≤
        cocompact ℂ
      rw [Complex.conjLIE.toHomeomorph.map_cocompact]
    have hinner : Tendsto (fun z : ℂ => F.toFun ((starRingEnd ℂ) z))
        (cocompact ℂ) (nhds 0) := by
      have hc' : Tendsto (fun z : ℂ => (starRingEnd ℂ) z)
          (cocompact ℂ) (cocompact ℂ) := by
        have hc0 : Tendsto (Complex.conjLIE : ℂ → ℂ)
            (cocompact ℂ) (cocompact ℂ) := by
          simpa only [LinearIsometryEquiv.coe_toHomeomorph] using hc
        have hfun : (fun z : ℂ => (starRingEnd ℂ) z) =
            (Complex.conjLIE : ℂ → ℂ) := by
          funext z
          change (starRingEnd ℂ) z = (starRingEnd ℂ) z
          rfl
        rw [hfun]
        exact hc0
      simpa only [Function.comp_def] using F.tendsto_zero.comp hc'
    have hout : Tendsto (fun z : ℂ => (starRingEnd ℂ) z) (nhds 0) (nhds 0) := by
      have hcont : Tendsto (Complex.conjLIE : ℂ → ℂ) (nhds 0) (nhds 0) := by
        have h : ContinuousAt (Complex.conjLIE : ℂ → ℂ) 0 :=
          Complex.conjLIE.continuous.continuousAt
        have h2 : Tendsto (Complex.conjLIE : ℂ → ℂ) (nhds 0)
            (nhds (Complex.conjLIE (0 : ℂ))) := h
        simpa using h2
      have hfun : (fun z : ℂ => (starRingEnd ℂ) z) =
          (Complex.conjLIE : ℂ → ℂ) := by
        funext z
        change (starRingEnd ℂ) z = (starRingEnd ℂ) z
        rfl
      rw [hfun]
      exact hcont
    simpa only [Function.comp_def] using hout.comp hinner
  flat_one := by
    intro n
    apply norm_eq_zero.mp
    calc
      ‖iteratedFDerivWithin ℝ n
          (fun w : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))) Oexterior 1‖ =
          ‖iteratedFDerivWithin ℝ n F.toFun Oexterior
            ((starRingEnd ℂ) (1 : ℂ))‖ :=
        norm_iteratedFDerivWithin_conj_conj F n (by simp [Oexterior])
      _ = 0 := by
        rw [show (starRingEnd ℂ) (1 : ℂ) = 1 by simp, F.flat_one n]
        simp
  flat_neg_one := by
    intro n
    apply norm_eq_zero.mp
    calc
      ‖iteratedFDerivWithin ℝ n
          (fun w : ℂ => (starRingEnd ℂ) (F.toFun ((starRingEnd ℂ) w))) Oexterior (-1)‖ =
          ‖iteratedFDerivWithin ℝ n F.toFun Oexterior
            ((starRingEnd ℂ) (-1 : ℂ))‖ :=
        norm_iteratedFDerivWithin_conj_conj F n (by simp [Oexterior])
      _ = 0 := by
        rw [show (starRingEnd ℂ) (-1 : ℂ) = -1 by simp, F.flat_neg_one n]
        simp

/-- The boundary functions of `F.conj` and `F` are related by angular reflection. -/
private theorem boundary_conj (F : AnalyticTestFn) (θ : ℝ) :
    (F.conj).toFun (Circle.exp θ) =
      (starRingEnd ℂ) (F.toFun (Circle.exp (2 * Real.pi - θ))) := by
  have hexp :
      (starRingEnd ℂ) (Circle.exp θ : ℂ) = (Circle.exp (-θ) : ℂ) := by
    calc
      (starRingEnd ℂ) (Circle.exp θ : ℂ) =
          (((Circle.exp θ)⁻¹ : Circle) : ℂ) :=
        by
          exact (Circle.coe_inv_eq_conj (Circle.exp θ)).symm
      _ = (Circle.exp (-θ) : ℂ) := by rw [Circle.exp_neg]
  have hperiod : Circle.exp (-θ) = Circle.exp (2 * Real.pi - θ) := by
    rw [show 2 * Real.pi - θ = -θ + 2 * Real.pi by ring,
      Circle.exp_add, Circle.exp_two_pi, mul_one]
  change (starRingEnd ℂ)
      (F.toFun ((starRingEnd ℂ) (Circle.exp θ : ℂ))) = _
  rw [hexp, hperiod]

/-- Periodization identifies the reflected value at `-θ` with the value at `2π - θ`. -/
private theorem periodize_neg_eq (g : ℝ → ℂ) (θ : ℝ) :
    periodize (2 * Real.pi) g (-θ) = periodize (2 * Real.pi) g (2 * Real.pi - θ) := by
  have hper := periodic_periodize (2 * Real.pi) Real.two_pi_pos g (-θ)
  calc
    periodize (2 * Real.pi) g (-θ) =
        periodize (2 * Real.pi) g (-θ + 2 * Real.pi) := hper.symm
    _ = periodize (2 * Real.pi) g (2 * Real.pi - θ) := by congr 1 <;> ring

/-- [T26], Definition 3.2; the reflection exchanges the two semicircle restrictions. -/
theorem xRestrictLower_conj (F : AnalyticTestFn) :
    xRestrictLower F.conj = starTestFn (xRestrictUpper F) := by
  apply toAngle_injective
  rw [xRestrictLower, toAngle_splitLower, toAngle_starTestFn, xRestrictUpper,
    toAngle_splitUpper]
  simp only [toAngle_xRestrictS1]
  apply periodic_eq_of_eq_on_Ico Real.two_pi_pos
    (periodic_periodize (2 * Real.pi) Real.two_pi_pos
      (cutIcc Real.pi (2 * Real.pi)
        (fun y : ℝ => (F.conj).toFun (Circle.exp y))))
    (by
      have hper := periodic_periodize (2 * Real.pi) Real.two_pi_pos
        (cutIcc 0 Real.pi (fun y : ℝ => F.toFun (Circle.exp y)))
      simpa only [zero_sub, Function.comp_def] using
        (hper.const_sub 0).comp (starRingEnd ℂ))
  intro θ hθ
  have hF0 : F.toFun (Circle.exp 0) = 0 := by
    have h := (F.isEndpointFlat.zero 0)
    rw [iteratedDeriv_zero, toAngle_xRestrictS1] at h
    simpa using h
  have hFpi : F.toFun (Circle.exp Real.pi) = 0 := by
    have h := (F.isEndpointFlat.pi 0)
    rw [iteratedDeriv_zero, toAngle_xRestrictS1] at h
    simpa using h
  have hleft :
      periodize (2 * Real.pi)
          (cutIcc Real.pi (2 * Real.pi)
            (fun y : ℝ => (F.conj).toFun (Circle.exp y))) θ =
        cutIcc Real.pi (2 * Real.pi)
          (fun y : ℝ => (F.conj).toFun (Circle.exp y)) θ :=
    periodize_eq_self Real.two_pi_pos hθ
  by_cases hθ0 : θ = 0
  · subst θ
    rw [hleft, cutIcc_eq_zero_of_notMem _ (by
      intro hmem
      exact not_le_of_gt Real.pi_pos hmem.1)]
    rw [show (-(0 : ℝ)) = 0 by simp, periodize_eq_self Real.two_pi_pos]
    · rw [cutIcc_eq_of_mem _ ⟨by simp, Real.pi_pos.le⟩, hF0]
      simp
    · exact ⟨by simp, by linarith [Real.pi_pos]⟩
  · by_cases hθpi : θ = Real.pi
    · subst θ
      have hCpi : (F.conj).toFun (Circle.exp Real.pi) =
          (starRingEnd ℂ) (F.toFun (Circle.exp (2 * Real.pi - Real.pi))) :=
        boundary_conj F Real.pi
      have hargpi : 2 * Real.pi - Real.pi = Real.pi := by ring
      have hFpi' : F.toFun (Circle.exp (2 * Real.pi - Real.pi)) = 0 := by
        rw [hargpi]
        exact hFpi
      rw [hleft, cutIcc_eq_of_mem _ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
        hCpi]
      rw [periodize_neg_eq, periodize_eq_self Real.two_pi_pos]
      · rw [cutIcc_eq_of_mem (a := 0) (b := Real.pi) (x := 2 * Real.pi - Real.pi) _
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, hFpi']
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · by_cases hθlt : θ < Real.pi
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hleftzero : cutIcc Real.pi (2 * Real.pi)
            (fun y : ℝ => (F.conj).toFun (Circle.exp y)) θ = 0 :=
          cutIcc_eq_zero_of_notMem _ (by intro hmem; linarith [hmem.1, hθlt])
        have hrightzero : cutIcc 0 Real.pi
            (fun y : ℝ => F.toFun (Circle.exp y)) (2 * Real.pi - θ) = 0 :=
          cutIcc_eq_zero_of_notMem _ (by intro hmem; linarith [hmem.2, hθlt])
        rw [hleft, hleftzero]
        rw [periodize_neg_eq, periodize_eq_self Real.two_pi_pos]
        · rw [hrightzero]
          simp
        · exact ⟨by linarith, by linarith⟩
      · have hθgt : Real.pi < θ := lt_of_le_of_ne (le_of_not_gt hθlt) (Ne.symm hθpi)
        have hright : 2 * Real.pi - θ ∈ Set.Ico 0 (2 * Real.pi) := by
          constructor <;> linarith [Real.pi_pos, hθ.1, hθ.2, hθgt]
        have hleftmem : θ ∈ Set.Icc Real.pi (2 * Real.pi) := ⟨hθgt.le, hθ.2.le⟩
        have hrightmem : 2 * Real.pi - θ ∈ Set.Icc 0 Real.pi := by
          constructor <;> linarith [Real.pi_pos, hθ.1, hθ.2, hθgt]
        rw [hleft, cutIcc_eq_of_mem _ hleftmem, boundary_conj]
        rw [periodize_neg_eq, periodize_eq_self Real.two_pi_pos]
        · rw [cutIcc_eq_of_mem _ hrightmem]
        · exact hright

/-- [T26], Lemma 3.4 for `I₋`; every lower-supported test function lies in the closure of the
restrictions to `I₋` of the analytic class `𝓧`. -/
theorem lemma_3_4_density_lower :
    { f : TestFn | SuppLower f } ⊆
      closure { g : TestFn | ∃ F : AnalyticTestFn, xRestrictLower F = g } := by
  intro f hf
  have hupper : SuppUpper (starTestFn f) := suppUpper_starTestFn hf
  obtain ⟨u, hu, hlim⟩ :=
    (mem_closure_iff_seq_limit.mp (lemma_3_4_density_upper hupper))
  have hstar : Tendsto (fun n => starTestFn (u n)) atTop (nhds (starTestFn (starTestFn f))) :=
    tendsto_starTestFn hlim
  have hlim' : Tendsto (fun n => starTestFn (u n)) atTop (nhds f) := by
    simpa [starTestFn_starTestFn] using hstar
  have hseq : ∀ n : ℕ, ∃ F : AnalyticTestFn, xRestrictLower F = starTestFn (u n) := by
    intro n
    obtain ⟨F, hF⟩ := hu n
    refine ⟨F.conj, ?_⟩
    rw [xRestrictLower_conj, hF]
  exact mem_closure_of_tendsto hlim' (by
    filter_upwards with n
    exact hseq n)

end

end MobiusCPT
