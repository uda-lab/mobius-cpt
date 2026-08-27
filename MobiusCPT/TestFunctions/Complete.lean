import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Sequences
import MobiusCPT.TestFunctions.CNorm

/-!
# MobiusCPT.TestFunctions.Complete

Completeness, the Baire property, and barrelledness of the smooth test-function space.

`TestFn` carries the topology induced by the injective linear map `angleDerivsₗ` into the
countable product `ℕ → (ℝ →ᵇ ℂ)`, which is completely metrizable.  So everything here reduces
to `isClosed_range_angleDerivs`: a sequence of test functions whose every angle derivative
converges uniformly has a smooth `2π`-periodic limit, which `exists_toAngle_eq` realises as a
test function again.  `TestFn` is therefore a closed topological embedding into a completely
metrizable space, hence Baire, hence barrelled ([Trèves, §33]).

Barrelledness is what `MobiusCPT.Analysis.SeparateJoint` needs, and through it the
joint-versus-separate continuity adapter of `MobiusCPT.Wightman.Continuity`.
-/

namespace MobiusCPT

open Filter TopologicalSpace
open scoped ContDiff Topology

/-- [T26], §2.2; the family of all angle derivatives separates test functions. -/
theorem angleDerivsₗ_injective : Function.Injective ⇑angleDerivsₗ := by
  intro f h hfh
  apply toAngle_injective
  funext θ
  have hzero := congrFun hfh 0
  change angleDerivB 0 f = angleDerivB 0 h at hzero
  calc
    toAngle f θ = angleDerivB 0 f θ := by
      rw [angleDerivB_apply, angleDeriv, iteratedDeriv_zero]
    _ = angleDerivB 0 h θ := DFunLike.congr_fun hzero θ
    _ = toAngle h θ := by
      rw [angleDerivB_apply, angleDeriv, iteratedDeriv_zero]

/-- [T26], §2.2; the test-function topology is induced by all angle derivatives. -/
theorem isInducing_angleDerivs : Topology.IsInducing ⇑angleDerivsₗ := by
  exact ⟨rfl⟩

/-- [T26], §2.2; uniform limits of every iterated derivative remain smooth, with the
prescribed limiting derivatives. -/
theorem contDiff_of_tendstoUniformly_iteratedDeriv
    {u : ℕ → ℝ → ℂ} {g : ℕ → ℝ → ℂ}
    (hsmooth : ∀ n, ContDiff ℝ ∞ (u n))
    (hconv : ∀ j, TendstoUniformly (fun n ↦ iteratedDeriv j (u n)) (g j) atTop) :
    ContDiff ℝ ∞ (g 0) ∧ ∀ j, iteratedDeriv j (g 0) = g j := by
  have hderiv : ∀ j x, HasDerivAt (g j) (g (j + 1) x) x := by
    intro j x
    apply hasDerivAt_of_tendstoUniformly (hconv (j + 1))
    · apply Eventually.of_forall
      intro n y
      have hdifferentiable : DifferentiableAt ℝ (iteratedDeriv j (u n)) y :=
        ((hsmooth n).differentiable_iteratedDeriv j
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))).differentiableAt
      rw [iteratedDeriv_succ]
      exact hdifferentiable.hasDerivAt
    · intro y
      exact (hconv j).tendsto_at y
  have hderiv_eq : ∀ j, deriv (g j) = g (j + 1) := by
    intro j
    funext x
    exact (hderiv j x).deriv
  have hiterated : ∀ j, iteratedDeriv j (g 0) = g j := by
    intro j
    induction j with
    | zero =>
        exact iteratedDeriv_zero
    | succ j ih =>
        rw [iteratedDeriv_succ, ih, hderiv_eq]
  refine ⟨?_, hiterated⟩
  apply contDiff_of_differentiable_iteratedDeriv (n := (⊤ : ℕ∞))
  intro j _
  rw [hiterated j]
  exact fun x ↦ (hderiv j x).differentiableAt

/-- [T26], §2.2; compatible uniform limits of all angle derivatives again come from a
smooth test function, so the angle-derivative image is closed. -/
theorem isClosed_range_angleDerivs : IsClosed (Set.range ⇑angleDerivsₗ) := by
  let _ : IsCompletelyMetrizableSpace
      (ℕ → BoundedContinuousFunction ℝ ℂ) := inferInstance
  apply IsSeqClosed.isClosed
  intro p F hp hF
  choose f hf using hp
  let g : ℕ → ℝ → ℂ := fun j θ ↦ F j θ
  have hconv :
      ∀ j, TendstoUniformly (fun n ↦ iteratedDeriv j (toAngle (f n))) (g j) atTop := by
    intro j
    have hcomponent :
        Tendsto (fun n ↦ angleDerivB j (f n)) atTop (nhds (F j)) := by
      have hj := (tendsto_pi_nhds.mp hF) j
      apply hj.congr'
      apply Eventually.of_forall
      intro n
      have hn := congrFun (hf n) j
      change angleDerivB j (f n) = p n j at hn
      exact hn.symm
    have huniform :
        TendstoUniformly
          (fun n ↦ (angleDerivB j (f n) : ℝ → ℂ))
          (F j : ℝ → ℂ) atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcomponent
    have hfamily :
        (fun n ↦ (angleDerivB j (f n) : ℝ → ℂ)) =
          fun n ↦ iteratedDeriv j (toAngle (f n)) := by
      funext n θ
      rw [angleDerivB_apply, angleDeriv]
    change TendstoUniformly (fun n ↦ iteratedDeriv j (toAngle (f n)))
      (F j : ℝ → ℂ) atTop
    rw [← hfamily]
    exact huniform
  obtain ⟨hg_smooth, hg_iterated⟩ :=
    contDiff_of_tendstoUniformly_iteratedDeriv
      (u := fun n ↦ toAngle (f n)) (g := g) (fun n ↦ contDiff_toAngle (f n)) hconv
  have hg_periodic : Function.Periodic (g 0) (2 * Real.pi) := by
    intro x
    have hplus := (hconv 0).tendsto_at (x + 2 * Real.pi)
    have hx := (hconv 0).tendsto_at x
    apply tendsto_nhds_unique_of_eventuallyEq hplus hx
    apply Eventually.of_forall
    intro n
    simpa only [iteratedDeriv_zero] using periodic_toAngle (f n) x
  obtain ⟨h, hh⟩ := exists_toAngle_eq hg_smooth hg_periodic
  refine ⟨h, ?_⟩
  change (fun j ↦ angleDerivB j h) = F
  funext j
  apply BoundedContinuousFunction.ext
  intro θ
  calc
    angleDerivB j h θ = iteratedDeriv j (toAngle h) θ := by
      rw [angleDerivB_apply, angleDeriv]
    _ = iteratedDeriv j (g 0) θ := by rw [hh]
    _ = g j θ := congrFun (hg_iterated j) θ
    _ = F j θ := rfl

/-- [T26], §2.2; `C∞(S¹)` is completely metrizable because its derivative image is
closed in a countable product of Banach spaces. -/
theorem isCompletelyMetrizableSpace_testFn : IsCompletelyMetrizableSpace TestFn := by
  have hclosedEmbedding : Topology.IsClosedEmbedding
      (angleDerivsₗ : TestFn → ℕ → BoundedContinuousFunction ℝ ℂ) :=
    ⟨⟨isInducing_angleDerivs, angleDerivsₗ_injective⟩, isClosed_range_angleDerivs⟩
  exact hclosedEmbedding.IsCompletelyMetrizableSpace

/-- [T26], §2.2 and [Trèves, §33]; the Fréchet test-function space is a Baire space. -/
instance testFnBaireSpace : BaireSpace TestFn := by
  let _ : IsCompletelyMetrizableSpace TestFn := isCompletelyMetrizableSpace_testFn
  exact BaireSpace.of_completelyPseudoMetrizable

/-- [T26], §2.2 and [CRTT25], Definition 2.5; the complex test-function space is
barrelled. -/
instance testFnBarrelledSpace : BarrelledSpace ℂ TestFn := by
  infer_instance

/-- [T26], §2.2 and [Trèves, §33]; the underlying real test-function space is barrelled. -/
instance testFnRealBarrelledSpace : BarrelledSpace ℝ TestFn := by
  let _ : ContinuousSMul ℝ TestFn := IsScalarTower.continuousSMul ℂ
  infer_instance

end MobiusCPT
