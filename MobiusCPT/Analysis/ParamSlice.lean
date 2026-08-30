import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Smooth parameter slices

Joint smoothness on a product set controls the iterated derivatives in the second variable.
This file supplies the first-order bridge between joint Fréchet derivatives and derivatives of
a one-dimensional slice, and the compactness argument giving uniformity in the sliced variable.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- The `n`-th derivative of a jointly smooth function in its second variable, taken as an
iterated directional derivative of the joint function. This is the device that lets the slice
derivatives be handled with the joint smoothness of `f`, since mathlib has no lemma relating a
slice's iterated derivative to the joint one. -/
noncomputable def sliceDeriv (S : Set (ℂ × ℝ)) : ℕ → (ℂ × ℝ → ℂ) → (ℂ × ℝ → ℂ)
  | 0, f => f
  | (n + 1), f => fun p => fderivWithin ℝ (sliceDeriv S n f) S p (0, 1)

/-- The zeroth slice derivative is the original function. -/
@[simp] theorem sliceDeriv_zero (S : Set (ℂ × ℝ)) (f : ℂ × ℝ → ℂ) :
    sliceDeriv S 0 f = f := rfl

/-- A successor slice derivative differentiates once more in the second-coordinate direction. -/
theorem sliceDeriv_succ (S : Set (ℂ × ℝ)) (n : ℕ) (f : ℂ × ℝ → ℂ) :
    sliceDeriv S (n + 1) f =
      fun p => fderivWithin ℝ (sliceDeriv S n f) S p (0, 1) := rfl

/-- Every slice derivative of a jointly smooth function is again jointly smooth. -/
theorem contDiffOn_sliceDeriv {S : Set (ℂ × ℝ)} (hS : UniqueDiffOn ℝ S)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f S) (n : ℕ) :
    ContDiffOn ℝ ∞ (sliceDeriv S n f) S := by
  induction n with
  | zero => simpa only [sliceDeriv_zero] using hf
  | succ n ih =>
      rw [sliceDeriv_succ]
      exact ((contDiffOn_infty_iff_fderivWithin hS).mp ih).2.clm_apply contDiffOn_const

/-- Every slice derivative of a jointly smooth function is jointly continuous. -/
theorem continuousOn_sliceDeriv {S : Set (ℂ × ℝ)} (hS : UniqueDiffOn ℝ S)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f S) (n : ℕ) :
    ContinuousOn (sliceDeriv S n f) S :=
  (contDiffOn_sliceDeriv hS hf n).continuousOn

/-- A jointly differentiable function differentiates along its second variable, with the joint
derivative applied to the second coordinate direction. -/
theorem hasDerivWithinAt_slice {s : Set ℂ} {K : Set ℝ} {f : ℂ × ℝ → ℂ} {u : ℂ} {θ : ℝ}
    (hu : u ∈ s) (hf : DifferentiableWithinAt ℝ f (s ×ˢ K) (u, θ)) :
    HasDerivWithinAt (fun t : ℝ => f (u, t))
      (fderivWithin ℝ f (s ×ˢ K) (u, θ) (0, 1)) K θ := by
  have hmaps : MapsTo (fun t : ℝ => (u, t)) K (s ×ˢ K) :=
    fun _ ht => ⟨hu, ht⟩
  have hcomp := hf.hasFDerivWithinAt.comp θ
    (hasFDerivAt_prodMk_right u θ).hasFDerivWithinAt hmaps
  have hd := hcomp.hasDerivWithinAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hd
  exact hd

/-- On a product set, the `n`-th slice derivative of a jointly smooth function computes the
`n`-th derivative of the slice within the second factor. -/
theorem sliceDeriv_eq_iteratedDerivWithin {s : Set ℂ} {K : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hK : UniqueDiffOn ℝ K)
    {f : ℂ × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (s ×ˢ K)) (n : ℕ)
    {u : ℂ} {θ : ℝ} (hu : u ∈ s) (hθ : θ ∈ K) :
    sliceDeriv (s ×ˢ K) n f (u, θ) =
      iteratedDerivWithin n (fun t : ℝ => f (u, t)) K θ := by
  have hprod : UniqueDiffOn ℝ (s ×ˢ K) := hs.prod hK
  induction n generalizing θ with
  | zero => simp only [sliceDeriv_zero, iteratedDerivWithin_zero]
  | succ n ih =>
      rw [sliceDeriv_succ, iteratedDerivWithin_succ]
      have hdiff : DifferentiableOn ℝ (sliceDeriv (s ×ˢ K) n f) (s ×ˢ K) :=
        (contDiffOn_sliceDeriv hprod hf n).differentiableOn (by simp)
      have hslice := hasDerivWithinAt_slice hu (hdiff (u, θ) ⟨hu, hθ⟩)
      calc
        fderivWithin ℝ (sliceDeriv (s ×ˢ K) n f) (s ×ˢ K) (u, θ) (0, 1) =
            derivWithin (fun t : ℝ => sliceDeriv (s ×ˢ K) n f (u, t)) K θ :=
          (hslice.derivWithin (hK θ hθ)).symm
        _ = derivWithin (iteratedDerivWithin n (fun t : ℝ => f (u, t)) K) K θ :=
          derivWithin_congr (fun t ht => ih (θ := t) ht) (ih (θ := θ) hθ)

/-- A function continuous on `s ×ˢ K` with `K` compact is uniformly close, over all of `K`,
to its values at a fixed parameter, for all parameters near that one. -/
theorem eventually_forall_norm_sub_lt {s : Set ℂ} {K : Set ℝ} (hK : IsCompact K)
    {f : ℂ × ℝ → ℂ} (hf : ContinuousOn f (s ×ˢ K)) {u₀ : ℂ} (hu₀ : u₀ ∈ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u in 𝓝[s] u₀, ∀ θ ∈ K, ‖f (u, θ) - f (u₀, θ)‖ < ε := by
  have huncurry : (Function.uncurry fun u : ℂ => fun θ : ℝ => f (u, θ)) = f := by
    funext p
    rfl
  obtain ⟨v, hv, hclose⟩ :
      ∃ v ∈ 𝓝[s] u₀, ∀ u ∈ v, ∀ θ ∈ K, dist (f (u, θ)) (f (u₀, θ)) < ε :=
    hK.mem_uniformity_of_prod (f := fun u θ => f (u, θ))
      (by rw [huncurry]; exact hf) hu₀
      (Metric.dist_mem_uniformity hε)
  filter_upwards [hv] with u hu
  intro θ hθ
  simpa only [dist_eq_norm] using hclose u hu θ hθ

/-- A convex subset of `ℂ` with nonempty interior determines derivatives at each of its points. -/
theorem uniqueDiffOn_of_convex {s : Set ℂ} (hs : Convex ℝ s) (hne : (interior s).Nonempty) :
    UniqueDiffOn ℝ s :=
  fun _ hz => uniqueDiffWithinAt_convex hs hne (subset_closure hz)

end

end MobiusCPT
