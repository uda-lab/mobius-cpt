import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

namespace MobiusCPT

noncomputable section

open scoped BigOperators

/-- A function continuous on the closed unit disc and holomorphic on the open unit disc
([CRTT25], Appendix A, the space `A(D̄)`). -/
def IsDiscBoundaryClass (F : ℂ → ℂ) : Prop :=
  ContinuousOn F (Metric.closedBall (0 : ℂ) 1) ∧ DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1)

private lemma norm_rotate (psi : ℝ) (z : ℂ) :
    ‖Complex.exp (psi * Complex.I) * z‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

private lemma exists_factor_eq_zero_of_prod_eq_zero {alpha : Type*} {U : Set ℂ}
    (hU : IsPreconnected U) {f : alpha → ℂ → ℂ} {t : Finset alpha}
    (ht : t.Nonempty) (hf : ∀ i ∈ t, AnalyticOnNhd ℂ (f i) U)
    (hprod : ∀ z ∈ U, ∏ i ∈ t, f i z = 0) :
    ∃ i ∈ t, ∀ z ∈ U, f i z = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp at ht
  | @insert i t hit ih =>
      by_cases ht' : t.Nonempty
      · have hiAnalytic : AnalyticOnNhd ℂ (f i) U :=
          hf i (Finset.mem_insert_self i t)
        have htAnalytic : AnalyticOnNhd ℂ (fun z ↦ ∏ j ∈ t, f j z) U :=
          t.analyticOnNhd_fun_prod fun j hj => hf j (Finset.mem_insert_of_mem hj)
        have hmul : ∀ z ∈ U, f i z * (∏ j ∈ t, f j z) = 0 := by
          intro z hz
          simpa [Finset.prod_insert, hit] using hprod z hz
        rcases hiAnalytic.eq_zero_or_eq_zero_of_mul_eq_zero htAnalytic hmul hU with
          hiZero | htZero
        · exact ⟨i, Finset.mem_insert_self i t, hiZero⟩
        · rcases ih ht' (fun j hj => hf j (Finset.mem_insert_of_mem hj)) htZero with
            ⟨j, hjt, hjZero⟩
          exact ⟨j, Finset.mem_insert_of_mem hjt, hjZero⟩
      · have htEmpty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
        refine ⟨i, Finset.mem_insert_self i t, ?_⟩
        intro z hz
        simpa [htEmpty] using hprod z hz

/-- R1(a), the reflection-free arc-vanishing lemma: an `IsDiscBoundaryClass` function that
vanishes on a nonempty open arc of the unit circle (given in angle coordinates through
`Complex.exp (θ * Complex.I)`) vanishes on the whole closed disc. Proved WITHOUT the Schwarz
reflection principle: a maximum-principle / identity-theorem argument over a finite rotated
product. See [CRTT25], Appendix A, the vanishing-arc replacement used in Lemma A.2's proof. -/
theorem IsDiscBoundaryClass.eq_zero_of_eqOn_arc {F : ℂ → ℂ} (hF : IsDiscBoundaryClass F)
    {a b : ℝ} (hab : a < b)
    (hzero : ∀ θ ∈ Set.Ioo a b, F (Complex.exp (θ * Complex.I)) = 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, F z = 0 := by
  classical
  let m : ℝ := (a + b) / 2
  let V : ℝ → Set ℝ := fun psi => Set.Ioo (a - psi) (b - psi)
  have hm : m ∈ Set.Ioo a b := by
    dsimp [m]
    constructor <;> linarith
  have hcover : Set.Icc (-Real.pi) Real.pi ⊆ ⋃ psi : ℝ, V psi := by
    intro phi hphi
    refine Set.mem_iUnion.2 ⟨m - phi, ?_⟩
    dsimp [V]
    constructor <;> linarith [hm.1, hm.2]
  obtain ⟨t, htcover⟩ :=
    isCompact_Icc.elim_finite_subcover V (fun _ => isOpen_Ioo) hcover
  have htNonempty : t.Nonempty := by
    by_contra ht
    have htEmpty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hzeroIcc : (0 : ℝ) ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have := htcover hzeroIcc
    simp [htEmpty] at this

  let rot : ℝ → ℂ → ℂ := fun psi z => Complex.exp (psi * Complex.I) * z
  let G : ℂ → ℂ := fun z => ∏ psi ∈ t, F (rot psi z)
  have hrotClosed (psi : ℝ) :
      Set.MapsTo (rot psi) (Metric.closedBall (0 : ℂ) 1)
        (Metric.closedBall (0 : ℂ) 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz ⊢
    simpa only [rot, norm_rotate] using hz
  have hrotBall (psi : ℝ) :
      Set.MapsTo (rot psi) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    simpa only [rot, norm_rotate] using hz
  have hrotContinuous (psi : ℝ) : Continuous (rot psi) := by
    show Continuous (fun z : ℂ => Complex.exp (psi * Complex.I) * z)
    fun_prop
  have hrotDifferentiable (psi : ℝ) : Differentiable ℂ (rot psi) := by
    show Differentiable ℂ (fun z : ℂ => Complex.exp (psi * Complex.I) * z)
    fun_prop
  have hfactorContinuous : ∀ psi ∈ t,
      ContinuousOn (fun z => F (rot psi z)) (Metric.closedBall (0 : ℂ) 1) := by
    intro psi hpsi
    exact hF.1.comp' (hrotContinuous psi).continuousOn (hrotClosed psi)
  have hfactorDifferentiable : ∀ psi ∈ t,
      DifferentiableOn ℂ (fun z => F (rot psi z)) (Metric.ball (0 : ℂ) 1) := by
    intro psi hpsi
    exact hF.2.fun_comp (hrotDifferentiable psi).differentiableOn (hrotBall psi)
  have hGContinuous : ContinuousOn G (Metric.closedBall (0 : ℂ) 1) := by
    dsimp [G]
    exact continuousOn_finsetProd t hfactorContinuous
  have hGDifferentiable : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1) := by
    dsimp [G]
    exact DifferentiableOn.fun_finsetProd hfactorDifferentiable
  have hfactorAnalytic : ∀ psi ∈ t,
      AnalyticOnNhd ℂ (fun z => F (rot psi z)) (Metric.ball (0 : ℂ) 1) := by
    intro psi hpsi
    exact (hfactorDifferentiable psi hpsi).analyticOnNhd Metric.isOpen_ball
  have hGAnalytic : AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) 1) := by
    dsimp [G]
    exact t.analyticOnNhd_fun_prod hfactorAnalytic

  have hGCircle : ∀ z : ℂ, ‖z‖ = 1 → G z = 0 := by
    intro z hz
    have hzExp : Complex.exp (Complex.arg z * Complex.I) = z := by
      have h := Complex.norm_mul_exp_arg_mul_I z
      rw [hz] at h
      simpa only [Complex.ofReal_one, one_mul] using h
    have hargIcc : Complex.arg z ∈ Set.Icc (-Real.pi) Real.pi :=
      ⟨(Complex.arg_mem_Ioc z).1.le, (Complex.arg_mem_Ioc z).2⟩
    rcases Set.mem_iUnion.1 (htcover hargIcc) with ⟨psi, hpsi⟩
    rcases Set.mem_iUnion.1 hpsi with ⟨hpsiMem, hpsiV⟩
    have htheta : Complex.arg z + psi ∈ Set.Ioo a b := by
      dsimp [V] at hpsiV
      constructor <;> linarith [hpsiV.1, hpsiV.2]
    have hrotation :
        Complex.exp (((Complex.arg z + psi : ℝ) : ℂ) * Complex.I) = rot psi z := by
      dsimp [rot]
      calc
        Complex.exp (((Complex.arg z + psi : ℝ) : ℂ) * Complex.I) =
            Complex.exp (Complex.arg z * Complex.I + psi * Complex.I) := by
              congr 1
              push_cast
              ring
        _ =
            Complex.exp (Complex.arg z * Complex.I) *
              Complex.exp (psi * Complex.I) := by
                rw [Complex.exp_add]
        _ = Complex.exp (psi * Complex.I) * z := by rw [hzExp, mul_comm]
    have hfactor : F (rot psi z) = 0 := by
      rw [← hrotation]
      exact hzero (Complex.arg z + psi) htheta
    dsimp [G]
    exact Finset.prod_eq_zero hpsiMem hfactor

  have hGDiffCont : DiffContOnCl ℂ G (Metric.ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball hGDifferentiable hGContinuous
  have hGClosed : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, G z = 0 := by
    intro z hz
    have hzClosure : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num)]
      exact hz
    have hfrontier : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1), ‖G w‖ ≤ 0 := by
      intro w hw
      rw [frontier_ball (0 : ℂ) (by norm_num)] at hw
      have hwZero := hGCircle w (mem_sphere_zero_iff_norm.mp hw)
      simp [hwZero]
    have hnorm := Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hGDiffCont hfrontier hzClosure
    apply norm_eq_zero.mp
    exact le_antisymm hnorm (norm_nonneg _)

  have hGOpen : ∀ z ∈ Metric.ball (0 : ℂ) 1, G z = 0 :=
    fun z hz => hGClosed z (Metric.ball_subset_closedBall hz)
  obtain ⟨psi0, hpsi0Mem, hpsi0Zero⟩ := exists_factor_eq_zero_of_prod_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected htNonempty hfactorAnalytic (by
      intro z hz
      exact hGOpen z hz)
  have hFOpen : ∀ z ∈ Metric.ball (0 : ℂ) 1, F z = 0 := by
    intro z hz
    have hzInv : rot (-psi0) z ∈ Metric.ball (0 : ℂ) 1 := hrotBall (-psi0) hz
    have h := hpsi0Zero (rot (-psi0) z) hzInv
    have hcancel :
        Complex.exp (psi0 * Complex.I) * Complex.exp ((-psi0) * Complex.I) = 1 := by
      rw [neg_mul, Complex.exp_neg, mul_inv_cancel₀ (Complex.exp_ne_zero _)]
    dsimp [rot] at h
    simp only [Complex.ofReal_neg] at h
    rw [← mul_assoc, hcancel, one_mul] at h
    exact h
  have hEqOpen : Set.EqOn F (fun _ : ℂ => 0) (Metric.ball (0 : ℂ) 1) :=
    fun z hz => hFOpen z hz
  have hEqClosed := hEqOpen.of_subset_closure hF.1 continuousOn_const
    Metric.ball_subset_closedBall (by
      intro z hz
      rw [closure_ball (0 : ℂ) (by norm_num)]
      exact hz)
  exact hEqClosed

/-- R1(b): `IsDiscBoundaryClass` is closed under uniform convergence on the closed disc.
This is the uniform-limit closure used with the vanishing-arc argument in [CRTT25], Appendix A. -/
theorem isDiscBoundaryClass_of_tendstoUniformlyOn {Fseq : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hFseq : ∀ n, IsDiscBoundaryClass (Fseq n))
    (htendsto : TendstoUniformlyOn Fseq F Filter.atTop (Metric.closedBall (0 : ℂ) 1)) :
    IsDiscBoundaryClass F := by
  constructor
  · exact htendsto.continuousOn
      (Filter.Eventually.of_forall (fun n => (hFseq n).1)).frequently
  · exact (htendsto.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun n => (hFseq n).2) Metric.isOpen_ball

end

end MobiusCPT
