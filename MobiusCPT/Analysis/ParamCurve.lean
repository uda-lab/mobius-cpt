import MobiusCPT.Analysis.ParamSlice
import MobiusCPT.Analysis.TestFnCurve

/-!
# A real-parameter joint-smoothness criterion for curves in `C^∞(S¹)`

[CRTT25], Lemma 2.10(i): a curve `u : ℝ → TestFn` whose angle picture is jointly smooth in the
real parameter and the angle, and `2π`-periodic in the angle, is continuous for the Fréchet
topology of `C^∞(S¹)`.  This is the mechanism PR #41's `continuousOn_betaBoost` used for the
complex strip parameter (joint smoothness plus the `ParamSlice` tube lemma), specialised to a
real parameter ranging over all of `ℝ`: there is no boundary, so uniform closeness on one period
suffices, folded back to every angle by periodicity instead of a support argument.

The `ParamSlice` machinery is typed over `ℂ × ℝ`; the real parameter is embedded by its real
part into the first, complex coordinate to reuse it without duplication.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [CRTT25], Lemma 2.10(i); the reusable core. A curve `u : ℝ → TestFn` whose angle picture
`(t, θ) ↦ toAngle (u t) θ` agrees with a jointly smooth, `2π`-periodic-in-`θ` function `g` is
continuous into `C^∞(S¹)`. Boosts and rotations are two instantiations of this single fact. -/
theorem continuous_of_jointlySmooth_periodic
    {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {u : ℝ → TestFn} (hu : ∀ t θ : ℝ, toAngle (u t) θ = g (t, θ)) :
    Continuous u := by
  -- Embed the real parameter into `ℂ` by its real part, to reuse the `ℂ × ℝ`-typed
  -- `ParamSlice` machinery.
  have hg' : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g (p.1.re, p.2)) := by
    have h1 : ContDiff ℝ ∞ (fun p : ℂ × ℝ => p.1.re) :=
      Complex.reCLM.contDiff.comp contDiff_fst
    exact hg.comp (h1.prodMk contDiff_snd)
  set K : Set ℝ := Set.Icc 0 (2 * Real.pi) with hKdef
  have hKcompact : IsCompact K := isCompact_Icc
  have hKuniq : UniqueDiffOn ℝ K := uniqueDiffOn_Icc Real.two_pi_pos
  have huniv : UniqueDiffOn ℝ (Set.univ : Set ℂ) := uniqueDiffOn_univ
  have hS : UniqueDiffOn ℝ ((Set.univ : Set ℂ) ×ˢ K) := huniv.prod hKuniq
  have hgOn : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => g (p.1.re, p.2)) ((Set.univ : Set ℂ) ×ˢ K) :=
    hg'.contDiffOn
  -- The slice derivative of the embedded function agrees with the global angle derivative of
  -- the curve, at every point of `K`.
  have hslice_eq : ∀ (j : ℕ) (z : ℂ) (θ : ℝ), θ ∈ K →
      sliceDeriv ((Set.univ : Set ℂ) ×ˢ K) j (fun p : ℂ × ℝ => g (p.1.re, p.2)) (z, θ) =
        angleDeriv j (u z.re) θ := by
    intro j z θ hθ
    rw [sliceDeriv_eq_iteratedDerivWithin huniv hKuniq hgOn j (mem_univ z) hθ]
    have h2 : (fun t : ℝ => g (z.re, t)) = toAngle (u z.re) := by
      funext t
      exact (hu z.re t).symm
    rw [h2]
    exact iteratedDerivWithin_eq_iteratedDeriv hKuniq
      ((contDiff_toAngle (u z.re)).contDiffAt.of_le (by exact_mod_cast le_top)) hθ
  have hcont_slice : ∀ j : ℕ,
      ContinuousOn
        (sliceDeriv ((Set.univ : Set ℂ) ×ˢ K) j (fun p : ℂ × ℝ => g (p.1.re, p.2)))
        ((Set.univ : Set ℂ) ×ˢ K) :=
    fun j => continuousOn_sliceDeriv hS hgOn j
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt]
  apply tendsto_testFn_of_forall_eventually
  intro N ε hε
  -- Uniform closeness of every angle derivative, on one period `K`, near `t₀`.
  have hslice_close : ∀ j : ℕ,
      ∀ᶠ t in 𝓝 t₀, ∀ θ ∈ K, ‖angleDeriv j (u t) θ - angleDeriv j (u t₀) θ‖ < ε := by
    intro j
    have hraw := eventually_forall_norm_sub_lt hKcompact (hcont_slice j)
      (mem_univ (t₀ : ℂ)) hε
    rw [nhdsWithin_univ] at hraw
    have htendsto : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 t₀) (𝓝 (t₀ : ℂ)) :=
      Complex.continuous_ofReal.tendsto t₀
    filter_upwards [htendsto.eventually hraw] with t ht θ hθ
    have hval := ht θ hθ
    rwa [hslice_eq j (t : ℂ) θ hθ, hslice_eq j (t₀ : ℂ) θ hθ,
      Complex.ofReal_re, Complex.ofReal_re] at hval
  have hfin : ∀ᶠ t in 𝓝 t₀,
      ∀ j ∈ Finset.range (N + 1), ∀ θ ∈ K,
        ‖angleDeriv j (u t) θ - angleDeriv j (u t₀) θ‖ < ε :=
    (Filter.eventually_all_finset _).mpr fun j _ => hslice_close j
  -- Fold an arbitrary angle back into `K` by `2π`-periodicity of the angle derivatives.
  filter_upwards [hfin] with t htfin j hj θ
  have hjmem : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hperFn : Function.Periodic
      (fun φ : ℝ => angleDeriv j (u t) φ - angleDeriv j (u t₀) φ) (2 * Real.pi) := by
    intro φ
    simp only
    rw [periodic_angleDeriv j (u t) φ, periodic_angleDeriv j (u t₀) φ]
  obtain ⟨y, hy, heq⟩ := hperFn.exists_mem_Ico₀ Real.two_pi_pos θ
  rw [heq]
  exact htfin j hjmem y ⟨hy.1, hy.2.le⟩

end

end MobiusCPT
