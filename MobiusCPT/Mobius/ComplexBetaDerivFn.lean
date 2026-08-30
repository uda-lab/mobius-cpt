import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Constructions.SumProd
import MobiusCPT.Mobius.ComplexBetaDeriv

/-!
# The parameter derivative of the complex boost as a test function

[T26], Lemma 3.6.  The parameter derivative commutes with all angle derivatives by symmetry of
the second derivative, and the resulting angle function is flat at the endpoints of the upper
semicircle.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- The closed-strip product has the closure-of-interior property needed by second-derivative
symmetry. -/
private theorem mem_closure_interior_stripUpper {p : ℂ × ℝ} (hp : p ∈ stripUpper) :
    p ∈ closure (interior stripUpper) := by
  have hstrip : strip (Complex.I * Real.pi) =
      Complex.imLm ⁻¹' Set.Icc (0 : ℝ) Real.pi := by
    ext z
    simpa only [Set.mem_preimage, Set.mem_Icc, Complex.imLm_coe] using
      (mem_strip_I_mul_pi (τ := z))
  have hconvStrip : Convex ℝ (strip (Complex.I * Real.pi)) := by
    rw [hstrip]
    exact (convex_Icc (0 : ℝ) Real.pi).linear_preimage Complex.imLm
  have hconv : Convex ℝ stripUpper := by
    simpa only [stripUpper] using hconvStrip.prod (convex_Icc (0 : ℝ) Real.pi)
  have hnonempty : (interior stripUpper).Nonempty := by
    rw [stripUpper, interior_prod_eq]
    refine ⟨(Complex.I * (Real.pi / 2 : ℝ), Real.pi / 2), ?_⟩
    constructor
    · rw [interior_strip, im_I_mul_pi]
      simp only [Set.mem_setOf_eq, min_eq_left Real.pi_pos.le,
        max_eq_right Real.pi_pos.le, Complex.I_mul_im, Complex.ofReal_re]
      exact ⟨Real.pi_div_two_pos, half_lt_self Real.pi_pos⟩
    · rw [interior_Icc]
      exact ⟨Real.pi_div_two_pos, half_lt_self Real.pi_pos⟩
  have hclosedStrip : IsClosed (strip (Complex.I * Real.pi)) := by
    rw [hstrip]
    simpa only [Complex.imLm_coe] using
      (isClosed_Icc.preimage Complex.continuous_im)
  have hclosed : IsClosed stripUpper := by
    simpa only [stripUpper] using hclosedStrip.prod isClosed_Icc
  have hclosure : closure (interior stripUpper) = stripUpper := by
    calc
      closure (interior stripUpper) = closure stripUpper :=
        hconv.closure_interior_eq_closure_of_nonempty_interior hnonempty
      _ = stripUpper := hclosed.closure_eq
  rw [hclosure]
  exact hp

/-- Every angle successor of a complex-boost slice is the joint derivative of the preceding slice
in the upper-semicircle direction. -/
private theorem betaBoostSlice_succ_eq (d : ℕ) (F : AnalyticTestFn) (j : ℕ) :
    betaBoostSlice d F (j + 1) =
      fun q => fderivWithin ℝ (betaBoostSlice d F j) stripUpper q (0, 1) := rfl

/-- The complex boost slice is jointly smooth on the closed strip and upper semicircle. -/
private theorem contDiffOn_betaBoostSlice_aux (d : ℕ) (F : AnalyticTestFn) (j : ℕ) :
    ContDiffOn ℝ ∞ (betaBoostSlice d F j) stripUpper := by
  simpa only [betaBoostSlice] using
    contDiffOn_sliceDeriv uniqueDiffOn_stripUpper (contDiffOn_betaBoostJoint d F) j

/-- The parameter derivative of every complex-boost slice is jointly smooth on the closed product
strip. -/
private theorem contDiffOn_betaBoostSliceDot_aux (d : ℕ) (F : AnalyticTestFn) (j : ℕ) :
    ContDiffOn ℝ ∞ (betaBoostSliceDot d F j) stripUpper := by
  have hderiv : ContDiffOn ℝ ∞
      (fderivWithin ℝ (betaBoostSlice d F j) stripUpper) stripUpper :=
    ((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_stripUpper).mp
      (contDiffOn_betaBoostSlice_aux d F j)).2
  have hcomp :=
    (ContinuousLinearMap.contDiff (n := ∞)
      (ContinuousLinearMap.apply ℝ ℂ ((1 : ℂ), (0 : ℝ)))).fun_comp_contDiffOn hderiv
  exact hcomp

/-- [T26], Lemma 3.6; differentiating the complex boost in the angle and in the strip parameter
commutes.  Both orders are directional derivatives of the same jointly smooth function, so this is
symmetry of the second derivative. -/
theorem betaBoostSliceDot_succ (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {p : ℂ × ℝ}
    (hp : p ∈ stripUpper) :
    fderivWithin ℝ (betaBoostSliceDot d F j) stripUpper p (0, 1) =
      betaBoostSliceDot d F (j + 1) p := by
  let u : ℂ × ℝ → ℂ := betaBoostSlice d F j
  let S : Set (ℂ × ℝ) := stripUpper
  let L : (ℂ × ℝ) → (ℂ × ℝ →L[ℝ] ℂ) := fderivWithin ℝ u S
  have hu : ContDiffOn ℝ ∞ u S := by
    simpa only [u, S] using contDiffOn_betaBoostSlice_aux d F j
  have hL : ContDiffOn ℝ ∞ L S := by
    dsimp only [L]
    exact ((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_stripUpper).mp hu).2
  have hLdiff : DifferentiableWithinAt ℝ L S p := by
    exact (hL.differentiableOn (by simp)) p hp
  have heval (v w : ℂ × ℝ) :
      fderivWithin ℝ (fun q : ℂ × ℝ => L q v) S p w =
        fderivWithin ℝ L S p w v := by
    have hcomp := fderivWithin_comp (𝕜 := ℝ)
      (f := L) (g := ContinuousLinearMap.apply ℝ ℂ v)
      (s := S) (t := Set.univ) (x := p)
      (ContinuousLinearMap.apply ℝ ℂ v).differentiableWithinAt
      hLdiff
      (mapsTo_univ _ _) (uniqueDiffOn_stripUpper p hp)
    rw [(ContinuousLinearMap.apply ℝ ℂ v).fderivWithin uniqueDiffWithinAt_univ] at hcomp
    have hcomp_apply := congrArg (fun K => K w) hcomp
    simpa only [Function.comp_def, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hcomp_apply
  have hle : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hsymm : IsSymmSndFDerivWithinAt ℝ u S p :=
    (hu p hp).isSymmSndFDerivWithinAt hle
      uniqueDiffOn_stripUpper (mem_closure_interior_stripUpper hp) hp
  have hsymm_eval :
      fderivWithin ℝ L S p (0, 1) (1, 0) =
        fderivWithin ℝ L S p (1, 0) (0, 1) := by
    simpa only [L] using hsymm (0, 1) (1, 0)
  calc
    fderivWithin ℝ (betaBoostSliceDot d F j) stripUpper p (0, 1) =
        fderivWithin ℝ L S p (0, 1) (1, 0) := by
      exact heval (1, 0) (0, 1)
    _ = fderivWithin ℝ L S p (1, 0) (0, 1) := hsymm_eval
    _ = betaBoostSliceDot d F (j + 1) p := by
      rw [betaBoostSliceDot, betaBoostSlice_succ_eq]
      exact (heval (0, 1) (1, 0)).symm

/-- [T26], Lemma 3.6; the `j`-th angle derivative of the parameter derivative is the parameter
derivative of the `j`-th angle derivative. -/
theorem sliceDeriv_betaBoostSliceDot (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {p : ℂ × ℝ}
    (hp : p ∈ stripUpper) :
    sliceDeriv stripUpper j (betaBoostSliceDot d F 0) p = betaBoostSliceDot d F j p := by
  induction j generalizing p with
  | zero => simp only [sliceDeriv_zero]
  | succ j ih =>
      show fderivWithin ℝ (sliceDeriv stripUpper j (betaBoostSliceDot d F 0))
          stripUpper p (0, 1) = betaBoostSliceDot d F (j + 1) p
      have heq : Set.EqOn (sliceDeriv stripUpper j (betaBoostSliceDot d F 0))
          (betaBoostSliceDot d F j) stripUpper := by
        intro q hq
        exact ih hq
      rw [fderivWithin_congr heq (ih hp)]
      exact betaBoostSliceDot_succ d F j hp

/-- [T26], Lemma 3.6; the angle function of the parameter derivative of the complex boost. -/
def betaBoostDerivCut (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) : ℝ → ℂ :=
  zeroExtendIcc 0 Real.pi (fun θ : ℝ => betaBoostSliceDot d F 0 (τ, θ))

/-- [T26], Lemma 3.6; the parameter derivative of the complex boost slice is smooth in the angle
on the closed upper semicircle. -/
theorem contDiffOn_betaBoostSliceDot_angle (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => betaBoostSliceDot d F 0 (τ, θ)) (Set.Icc 0 Real.pi) := by
  have hinsert : ContDiff ℝ ∞ (fun θ : ℝ => (τ, θ)) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : Set.MapsTo (fun θ : ℝ => (τ, θ)) (Set.Icc 0 Real.pi) stripUpper := by
    intro θ hθ
    exact ⟨hτ, hθ⟩
  have hcomp : ContDiffOn ℝ ∞
      (betaBoostSliceDot d F 0 ∘ fun θ : ℝ => (τ, θ)) (Set.Icc 0 Real.pi) :=
    (contDiffOn_betaBoostSliceDot_aux d F 0).comp hinsert.contDiffOn hmaps
  exact hcomp.congr fun θ _ => rfl

/-- [T26], Lemma 3.6; within angle derivatives of the parameter derivative are the corresponding
joint slice derivatives. -/
theorem iteratedDerivWithin_betaBoostSliceDot_angle (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) (j : ℕ) :
    iteratedDerivWithin j (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
        (Set.Icc 0 Real.pi) θ = betaBoostSliceDot d F j (τ, θ) := by
  have hslice := sliceDeriv_eq_iteratedDerivWithin
    uniqueDiffOn_strip_I_mul_pi (uniqueDiffOn_Icc Real.pi_pos)
    (contDiffOn_betaBoostSliceDot_aux d F 0) j hτ hθ
  calc
    iteratedDerivWithin j (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
        (Set.Icc 0 Real.pi) θ = sliceDeriv stripUpper j (betaBoostSliceDot d F 0) (τ, θ) :=
      hslice.symm
    _ = betaBoostSliceDot d F j (τ, θ) :=
      sliceDeriv_betaBoostSliceDot d F j ⟨hτ, hθ⟩

/-- The parameter-derivative angle function is flat at both endpoints of the upper semicircle for
every parameter in the closed strip. -/
private theorem betaBoostSliceDot_eq_zero_of_endpoint_closed (d : ℕ) (F : AnalyticTestFn)
    (j : ℕ) {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ}
    (hθ : θ = 0 ∨ θ = Real.pi) :
    betaBoostSliceDot d F j (τ, θ) = 0 := by
  rcases hθ with rfl | rfl
  · have hzero : Set.EqOn
        (fun σ : ℂ => betaBoostSlice d F j (σ, 0))
        (fun _ : ℂ => (0 : ℂ)) (strip (Complex.I * Real.pi)) := by
      intro σ hσ
      show betaBoostSlice d F j (σ, 0) = 0
      rw [betaBoostSlice_eq d F j hσ ⟨le_rfl, Real.pi_pos.le⟩]
      exact iteratedDerivWithin_betaBoostVal_circleExp_zero d F hσ j
    have hderivzero :
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, 0))
            (strip (Complex.I * Real.pi)) τ = 0 := by
      calc
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, 0))
              (strip (Complex.I * Real.pi)) τ =
            fderivWithin ℝ (0 : ℂ → ℂ) (strip (Complex.I * Real.pi)) τ :=
          fderivWithin_congr hzero (hzero hτ)
        _ = 0 := by simp
    have hjointOn : DifferentiableOn ℝ (betaBoostSlice d F j) stripUpper :=
      (contDiffOn_betaBoostSlice_aux d F j).differentiableOn (by simp)
    have hjointAt : DifferentiableWithinAt ℝ (betaBoostSlice d F j) stripUpper (τ, 0) :=
      hjointOn (τ, 0) ⟨hτ, ⟨le_rfl, Real.pi_pos.le⟩⟩
    have hinsert : HasFDerivAt (fun σ : ℂ => (σ, (0 : ℝ)))
        (ContinuousLinearMap.inl ℝ ℂ ℝ) τ :=
      hasFDerivAt_prodMk_left τ 0
    have hmaps : MapsTo (fun σ : ℂ => (σ, (0 : ℝ)))
        (strip (Complex.I * Real.pi)) stripUpper := by
      intro σ hσ
      exact ⟨hσ, ⟨le_rfl, Real.pi_pos.le⟩⟩
    have hcomp := hjointAt.hasFDerivWithinAt.comp τ
      hinsert.hasFDerivWithinAt hmaps
    have hcomp_deriv :
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, 0))
            (strip (Complex.I * Real.pi)) τ =
          (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, 0)).comp
            (ContinuousLinearMap.inl ℝ ℂ ℝ) := by
      simpa only [Function.comp_def, Function.comp_apply] using
        hcomp.fderivWithin (uniqueDiffOn_strip_I_mul_pi τ hτ)
    have hcomp_eq :
        (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, 0)).comp
            (ContinuousLinearMap.inl ℝ ℂ ℝ) = 0 := by
      calc
        (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, 0)).comp
              (ContinuousLinearMap.inl ℝ ℂ ℝ) =
            fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, 0))
              (strip (Complex.I * Real.pi)) τ := hcomp_deriv.symm
        _ = 0 := hderivzero
    have hcomp_apply := congrArg (fun A : ℂ →L[ℝ] ℂ => A (1 : ℂ)) hcomp_eq
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      betaBoostSliceDot] using hcomp_apply
  · have hzero : Set.EqOn
        (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi))
        (fun _ : ℂ => (0 : ℂ)) (strip (Complex.I * Real.pi)) := by
      intro σ hσ
      show betaBoostSlice d F j (σ, Real.pi) = 0
      rw [betaBoostSlice_eq d F j hσ ⟨Real.pi_pos.le, le_rfl⟩]
      exact iteratedDerivWithin_betaBoostVal_circleExp_pi d F hσ j
    have hderivzero :
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi))
            (strip (Complex.I * Real.pi)) τ = 0 := by
      calc
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi))
              (strip (Complex.I * Real.pi)) τ =
            fderivWithin ℝ (0 : ℂ → ℂ) (strip (Complex.I * Real.pi)) τ :=
          fderivWithin_congr hzero (hzero hτ)
        _ = 0 := by simp
    have hjointOn : DifferentiableOn ℝ (betaBoostSlice d F j) stripUpper :=
      (contDiffOn_betaBoostSlice_aux d F j).differentiableOn (by simp)
    have hjointAt : DifferentiableWithinAt ℝ (betaBoostSlice d F j)
        stripUpper (τ, Real.pi) :=
      hjointOn (τ, Real.pi) ⟨hτ, ⟨Real.pi_pos.le, le_rfl⟩⟩
    have hinsert : HasFDerivAt (fun σ : ℂ => (σ, Real.pi))
        (ContinuousLinearMap.inl ℝ ℂ ℝ) τ :=
      hasFDerivAt_prodMk_left τ Real.pi
    have hmaps : MapsTo (fun σ : ℂ => (σ, Real.pi))
        (strip (Complex.I * Real.pi)) stripUpper := by
      intro σ hσ
      exact ⟨hσ, ⟨Real.pi_pos.le, le_rfl⟩⟩
    have hcomp := hjointAt.hasFDerivWithinAt.comp τ
      hinsert.hasFDerivWithinAt hmaps
    have hcomp_deriv :
        fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi))
            (strip (Complex.I * Real.pi)) τ =
          (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, Real.pi)).comp
            (ContinuousLinearMap.inl ℝ ℂ ℝ) := by
      simpa only [Function.comp_def, Function.comp_apply] using
        hcomp.fderivWithin (uniqueDiffOn_strip_I_mul_pi τ hτ)
    have hcomp_eq :
        (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, Real.pi)).comp
            (ContinuousLinearMap.inl ℝ ℂ ℝ) = 0 := by
      calc
        (fderivWithin ℝ (betaBoostSlice d F j) stripUpper (τ, Real.pi)).comp
              (ContinuousLinearMap.inl ℝ ℂ ℝ) =
            fderivWithin ℝ (fun σ : ℂ => betaBoostSlice d F j (σ, Real.pi))
              (strip (Complex.I * Real.pi)) τ := hcomp_deriv.symm
        _ = 0 := hderivzero
    have hcomp_apply := congrArg (fun A : ℂ →L[ℝ] ℂ => A (1 : ℂ)) hcomp_eq
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      betaBoostSliceDot] using hcomp_apply

/-- [T26], Lemma 3.6; the zero extension of the parameter-derivative angle function is smooth on
the real line. -/
theorem contDiff_betaBoostDerivCut (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) : ContDiff ℝ ∞ (betaBoostDerivCut d τ F) := by
  change ContDiff ℝ ∞
    (zeroExtendIcc 0 Real.pi (fun θ : ℝ => betaBoostSliceDot d F 0 (τ, θ)))
  apply contDiff_zeroExtend_of_flat_contDiffOn Real.pi_pos
  · exact contDiffOn_betaBoostSliceDot_angle d F hτ
  · intro j
    calc
      iteratedDerivWithin j (fun θ : ℝ => betaBoostSliceDot d F 0 (τ, θ))
          (Set.Icc 0 Real.pi) 0 = betaBoostSliceDot d F j (τ, 0) :=
        iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
          ⟨le_rfl, Real.pi_pos.le⟩ j
      _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F j hτ (Or.inl rfl)
  · intro j
    calc
      iteratedDerivWithin j (fun θ : ℝ => betaBoostSliceDot d F 0 (τ, θ))
          (Set.Icc 0 Real.pi) Real.pi = betaBoostSliceDot d F j (τ, Real.pi) :=
        iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
          ⟨Real.pi_pos.le, le_rfl⟩ j
      _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F j hτ (Or.inr rfl)

/-- [T26], Lemma 3.6; the parameter-derivative angle function is upper-flat. -/
theorem isUpperFlat_betaBoostDerivCut (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) : IsUpperFlat (betaBoostDerivCut d τ F) := by
  refine ⟨contDiff_betaBoostDerivCut d F hτ, ?_⟩
  intro θ hθ
  by_cases hIcc : θ ∈ Set.Icc 0 Real.pi
  · by_cases hzero : θ = 0
    · subst θ
      rw [betaBoostDerivCut, zeroExtend_eq_of_mem _ ⟨le_rfl, Real.pi_pos.le⟩]
      exact betaBoostSliceDot_eq_zero_of_endpoint_closed d F 0 hτ (Or.inl rfl)
    · have hpos : 0 < θ := lt_of_le_of_ne hIcc.1 (Ne.symm hzero)
      have hpi : θ = Real.pi := by
        apply le_antisymm hIcc.2
        apply le_of_not_gt
        intro hlt
        exact hθ ⟨hpos, hlt⟩
      subst θ
      rw [betaBoostDerivCut, zeroExtend_eq_of_mem _ ⟨Real.pi_pos.le, le_rfl⟩]
      exact betaBoostSliceDot_eq_zero_of_endpoint_closed d F 0 hτ (Or.inr rfl)
  · exact zeroExtend_eq_zero_of_notMem _ hIcc

/-- [T26], Lemma 3.6; the derivative in the strip parameter of the curve
`τ ↦ β_d(v_τ)F|_{I_+}`, as an element of `C_0^∞(I_+)`. -/
noncomputable def betaBoostDeriv (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) : TestFn :=
  open Classical in
  if hτ : τ ∈ strip (Complex.I * Real.pi) then
    Classical.choose (exists_suppUpper_toAngle_eq_periodize
      (isUpperFlat_betaBoostDerivCut d F hτ))
  else 0

/-- On the closed strip, the angle representative of the parameter derivative is the periodisation
of its zero-extended upper-semicircle formula. -/
theorem toAngle_betaBoostDeriv (d : ℕ) (F : AnalyticTestFn) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    toAngle (betaBoostDeriv d τ F) = periodize (2 * Real.pi) (betaBoostDerivCut d τ F) := by
  rw [betaBoostDeriv, dif_pos hτ]
  exact (Classical.choose_spec
    (exists_suppUpper_toAngle_eq_periodize (isUpperFlat_betaBoostDerivCut d F hτ))).1

/-- [T26], Lemma 3.6; the parameter-derivative test function is supported in the upper
semicircle. -/
theorem suppUpper_betaBoostDeriv (d : ℕ) (τ : ℂ) (F : AnalyticTestFn) :
    SuppUpper (betaBoostDeriv d τ F) := by
  by_cases hτ : τ ∈ strip (Complex.I * Real.pi)
  · rw [betaBoostDeriv, dif_pos hτ]
    exact (Classical.choose_spec
      (exists_suppUpper_toAngle_eq_periodize (isUpperFlat_betaBoostDerivCut d F hτ))).2
  · rw [betaBoostDeriv, dif_neg hτ]
    exact suppUpper_zero

/-- [T26], Lemma 3.6; on the closed upper semicircle, the angle derivatives of the parameter
derivative are the derivatives of its defining slice formula. -/
theorem angleDeriv_betaBoostDeriv_of_mem (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) :
    angleDeriv j (betaBoostDeriv d τ F) θ = betaBoostSliceDot d F j (τ, θ) := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 (2 * Real.pi / 2) →
      betaBoostDerivCut d τ F x = 0 := by
    intro x hx
    refine zeroExtend_eq_zero_of_notMem _ ?_
    intro hmem
    exact hx (by simpa using hmem)
  have hper := iteratedDeriv_periodize_eqOn (T := 2 * Real.pi) Real.two_pi_pos hsupp j
  have hmemIoo : θ ∈ Set.Ioo (-(2 * Real.pi / 2)) (2 * Real.pi) := by
    constructor
    · have := hθ.1
      nlinarith [Real.pi_pos]
    · have := hθ.2
      nlinarith [Real.pi_pos]
  have hcut :=
    iteratedDeriv_zeroExtendIcc Real.pi_pos
      (contDiffOn_betaBoostSliceDot_angle d F hτ)
      (fun n => by
        calc
          iteratedDerivWithin n (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
              (Set.Icc 0 Real.pi) 0 = betaBoostSliceDot d F n (τ, 0) :=
            iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
              ⟨le_rfl, Real.pi_pos.le⟩ n
          _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F n hτ (Or.inl rfl))
      (fun n => by
        calc
          iteratedDerivWithin n (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
              (Set.Icc 0 Real.pi) Real.pi = betaBoostSliceDot d F n (τ, Real.pi) :=
            iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
              ⟨Real.pi_pos.le, le_rfl⟩ n
          _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F n hτ (Or.inr rfl))
      j
  calc
    angleDeriv j (betaBoostDeriv d τ F) θ
        = iteratedDeriv j (periodize (2 * Real.pi) (betaBoostDerivCut d τ F)) θ := by
          rw [angleDeriv, toAngle_betaBoostDeriv d F hτ]
    _ = iteratedDeriv j (betaBoostDerivCut d τ F) θ := hper hmemIoo
    _ = zeroExtendIcc 0 Real.pi
          (iteratedDerivWithin j
            (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t)) (Set.Icc 0 Real.pi)) θ := by
          rw [betaBoostDerivCut, hcut]
    _ = iteratedDerivWithin j
          (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t)) (Set.Icc 0 Real.pi) θ :=
          zeroExtend_eq_of_mem _ hθ
    _ = betaBoostSliceDot d F j (τ, θ) :=
      iteratedDerivWithin_betaBoostSliceDot_angle d F hτ hθ j

/-- [T26], Lemma 3.6; off the closed upper semicircle, within one period, every angle derivative
of the parameter derivative vanishes. -/
theorem angleDeriv_betaBoostDeriv_of_notMem (d : ℕ) (F : AnalyticTestFn) (j : ℕ) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo Real.pi (2 * Real.pi)) :
    angleDeriv j (betaBoostDeriv d τ F) θ = 0 := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc 0 (2 * Real.pi / 2) →
      betaBoostDerivCut d τ F x = 0 := by
    intro x hx
    refine zeroExtend_eq_zero_of_notMem _ ?_
    intro hmem
    exact hx (by simpa using hmem)
  have hper := iteratedDeriv_periodize_eqOn (T := 2 * Real.pi) Real.two_pi_pos hsupp j
  have hmemIoo : θ ∈ Set.Ioo (-(2 * Real.pi / 2)) (2 * Real.pi) := by
    constructor
    · have := hθ.1
      nlinarith [Real.pi_pos]
    · exact hθ.2
  have hcut :=
    iteratedDeriv_zeroExtendIcc Real.pi_pos
      (contDiffOn_betaBoostSliceDot_angle d F hτ)
      (fun n => by
        calc
          iteratedDerivWithin n (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
              (Set.Icc 0 Real.pi) 0 = betaBoostSliceDot d F n (τ, 0) :=
            iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
              ⟨le_rfl, Real.pi_pos.le⟩ n
          _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F n hτ (Or.inl rfl))
      (fun n => by
        calc
          iteratedDerivWithin n (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t))
              (Set.Icc 0 Real.pi) Real.pi = betaBoostSliceDot d F n (τ, Real.pi) :=
            iteratedDerivWithin_betaBoostSliceDot_angle d F hτ
              ⟨Real.pi_pos.le, le_rfl⟩ n
          _ = 0 := betaBoostSliceDot_eq_zero_of_endpoint_closed d F n hτ (Or.inr rfl))
      j
  have hnot : θ ∉ Set.Icc 0 Real.pi := by
    intro hmem
    exact absurd hmem.2 (not_le_of_gt hθ.1)
  calc
    angleDeriv j (betaBoostDeriv d τ F) θ
        = iteratedDeriv j (periodize (2 * Real.pi) (betaBoostDerivCut d τ F)) θ := by
          rw [angleDeriv, toAngle_betaBoostDeriv d F hτ]
    _ = iteratedDeriv j (betaBoostDerivCut d τ F) θ := hper hmemIoo
    _ = zeroExtendIcc 0 Real.pi
          (iteratedDerivWithin j
            (fun t : ℝ => betaBoostSliceDot d F 0 (τ, t)) (Set.Icc 0 Real.pi)) θ := by
          rw [betaBoostDerivCut, hcut]
    _ = 0 := zeroExtend_eq_zero_of_notMem _ hnot

end

end MobiusCPT
