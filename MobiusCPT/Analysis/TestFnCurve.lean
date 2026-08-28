import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Fintype.BigOperators
import MobiusCPT.TestFunctions.CNorm

/-!
# Curves in the test-function space

Seminorm criteria for convergence and a multilinear product rule for curves in
`C^∞(S¹)`.
-/

namespace MobiusCPT

open scoped Topology

noncomputable section

/-- The `C^N` seminorm is bounded by a common bound on the first `N` angle derivatives.  Because
angle derivatives are `2π`-periodic, checking the bound on one period suffices. -/
theorem cnorm_le_of_forall_angleDeriv {N : ℕ} {f : TestFn} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ≤ N, ∀ θ : ℝ, ‖angleDeriv j f θ‖ ≤ C) :
    (cnorm N f : ℝ) ≤ (N + 1) * C := by
  rw [cnorm_eq]
  have hterm : ∀ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ ≤ C := by
    intro j hj
    refine (BoundedContinuousFunction.norm_le hC).mpr ?_
    intro θ
    rw [angleDerivB_apply]
    exact h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) θ
  calc
    ∑ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ ≤
        ∑ _j ∈ Finset.range (N + 1), C :=
      Finset.sum_le_sum hterm
    _ = (N + 1) * C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- Angle differentiation preserves subtraction of test functions. -/
theorem angleDeriv_sub (j : ℕ) (f g : TestFn) :
    angleDeriv j (f - g) = angleDeriv j f - angleDeriv j g := by
  calc
    angleDeriv j (f - g) = angleDeriv j (f + -g) := by rw [sub_eq_add_neg]
    _ = angleDeriv j f + angleDeriv j (-g) := angleDeriv_add j f (-g)
    _ = angleDeriv j f + angleDeriv j ((-1 : ℂ) • g) := by rw [neg_one_smul]
    _ = angleDeriv j f + (-1 : ℂ) • angleDeriv j g := by rw [angleDeriv_smul]
    _ = angleDeriv j f - angleDeriv j g := by rw [neg_one_smul, sub_eq_add_neg]

/-- Convergence in `C^∞(S¹)` along any filter, expressed through the angle derivatives: it is
enough that for every order the angle derivatives converge uniformly. -/
theorem tendsto_testFn_of_forall_eventually {ι : Type*} {l : Filter ι} {u : ι → TestFn}
    {f : TestFn}
    (h : ∀ (N : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ j ≤ N, ∀ θ : ℝ, ‖angleDeriv j (u i) θ - angleDeriv j f θ‖ < ε) :
    Filter.Tendsto u l (𝓝 f) := by
  rw [withSeminorms_cnorm.tendsto_nhds u f]
  intro N ε hε
  let δ : ℝ := ε / (2 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hfactor : ((N : ℝ) + 1) * δ < ε := by
    have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
    have heq : ((N : ℝ) + 1) * δ = ε / 2 := by
      dsimp [δ]
      field_simp
    rw [heq]
    linarith
  filter_upwards [h N δ hδ] with i hi
  rw [← cnorm_coe]
  refine lt_of_le_of_lt (cnorm_le_of_forall_angleDeriv hδ.le ?_) hfactor
  intro j hj θ
  rw [angleDeriv_sub]
  exact (hi j hj θ).le

/-- [T26], Lemma 3.6; complex differentiability of a curve of test functions, in the honest
locally convex sense: the difference quotients converge in the Fréchet topology of `C^∞(S¹)`.
No norm on `C^∞(S¹)` is used or implied. -/
def HasTestFnDerivAt (a : ℂ → TestFn) (a' : TestFn) (τ : ℂ) : Prop :=
  Filter.Tendsto (fun h : ℂ => h⁻¹ • (a (τ + h) - a τ))
    (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds a')

/-- The increment-at-zero definition of a test-function derivative is equivalent to convergence
of the usual punctured slope at the base point. -/
theorem hasTestFnDerivAt_iff_tendsto_slope {a : ℂ → TestFn} {a' : TestFn} {τ : ℂ} :
    HasTestFnDerivAt a a' τ ↔
      Filter.Tendsto (fun t : ℂ => (t - τ)⁻¹ • (a t - a τ))
        (nhdsWithin τ {τ}ᶜ) (nhds a') := by
  unfold HasTestFnDerivAt
  have hfilter :
      nhdsWithin τ {τ}ᶜ =
        Filter.map (fun h : ℂ => τ + h) (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
    simp
  rw [hfilter, Filter.tendsto_map'_iff]
  simp only [Function.comp_def, add_sub_cancel_left]

/-- A continuous map that is linear in each argument turns differentiable curves of test functions
into a differentiable scalar function, by the product rule.  This is how [T26], Lemma 3.6 crosses
from the test-function curve `τ ↦ β_d(v_τ)F|_{I_+}` to the scalar functions
`G_λ(τ) = λ(φ₁(β(v_τ)F₁)⋯φ_k(β(v_τ)F_k)Ω)`: scalar differentiability of each slot separately would
not suffice, because `M` is multilinear rather than linear. -/
theorem hasDerivAt_of_multilinear {k : ℕ} {M : (Fin k → TestFn) → ℂ}
    (hM : Continuous M)
    (hlin : ∀ (i : Fin k) (f : Fin k → TestFn) (g h : TestFn),
      M (Function.update f i (g + h)) = M (Function.update f i g) + M (Function.update f i h))
    (hsmul : ∀ (i : Fin k) (f : Fin k → TestFn) (c : ℂ) (g : TestFn),
      M (Function.update f i (c • g)) = c * M (Function.update f i g))
    {a : Fin k → ℂ → TestFn} {a' : Fin k → TestFn} {τ : ℂ}
    (hcont : ∀ i, ContinuousAt (a i) τ)
    (hderiv : ∀ i, HasTestFnDerivAt (a i) (a' i) τ) :
    HasDerivAt (fun t : ℂ => M (fun i => a i t))
      (∑ i : Fin k, M (Function.update (fun j => a j τ) i (a' i))) τ := by
  classical
  let b : ℂ → ℕ → (Fin k → TestFn) := fun z m j =>
    if (j : ℕ) < m then a j (τ + z) else a j τ
  have hb_zero (z : ℂ) : b z 0 = fun j => a j τ := by
    funext j
    simp [b]
  have hb_top (z : ℂ) : b z k = fun j => a j (τ + z) := by
    funext j
    simp [b, Fin.isLt]
  have hb_update_new (z : ℂ) (m : ℕ) (hm : m < k) :
      Function.update (b z m) (⟨m, hm⟩ : Fin k) (a ⟨m, hm⟩ (τ + z)) = b z (m + 1) := by
    funext j
    by_cases hji : j = (⟨m, hm⟩ : Fin k)
    · subst j
      simp [b]
    · have hjm : (j : ℕ) ≠ m := by
        intro hjm
        apply hji
        apply Fin.ext
        exact hjm
      by_cases hjlt : (j : ℕ) < m
      · have hjlt' : (j : ℕ) < m + 1 := by omega
        simp [b, hji, hjlt, hjlt']
      · have hjlt' : ¬(j : ℕ) < m + 1 := by omega
        simp [b, hji, hjlt, hjlt']
  have hb_update_old (z : ℂ) (m : ℕ) (hm : m < k) :
      Function.update (b z m) (⟨m, hm⟩ : Fin k) (a ⟨m, hm⟩ τ) = b z m := by
    funext j
    by_cases hji : j = (⟨m, hm⟩ : Fin k)
    · subst j
      simp [b]
    · simp [hji]
  have hstep (z : ℂ) (m : ℕ) (hm : m < k) :
      M (b z (m + 1)) - M (b z m) =
        M (Function.update (b z m) (⟨m, hm⟩ : Fin k)
          (a ⟨m, hm⟩ (τ + z) - a ⟨m, hm⟩ τ)) := by
    have hadd := hlin (⟨m, hm⟩ : Fin k) (b z m)
      (a ⟨m, hm⟩ (τ + z) - a ⟨m, hm⟩ τ) (a ⟨m, hm⟩ τ)
    rw [sub_add_cancel, hb_update_new z m hm, hb_update_old z m hm] at hadd
    calc
      M (b z (m + 1)) - M (b z m) =
          (M (Function.update (b z m) (⟨m, hm⟩ : Fin k)
              (a ⟨m, hm⟩ (τ + z) - a ⟨m, hm⟩ τ)) + M (b z m)) - M (b z m) := by
        rw [hadd]
      _ = M (Function.update (b z m) (⟨m, hm⟩ : Fin k)
          (a ⟨m, hm⟩ (τ + z) - a ⟨m, hm⟩ τ)) := add_sub_cancel_right _ _
  have htel (z : ℂ) :
      M (fun j => a j (τ + z)) - M (fun j => a j τ) =
        ∑ i : Fin k,
          M (Function.update (b z (i : ℕ)) i (a i (τ + z) - a i τ)) := by
    calc
      M (fun j => a j (τ + z)) - M (fun j => a j τ) =
          ∑ m ∈ Finset.range k, (M (b z (m + 1)) - M (b z m)) := by
        rw [← hb_top z, ← hb_zero z]
        exact (Finset.sum_range_sub (fun m => M (b z m)) k).symm
      _ = ∑ i : Fin k,
          M (Function.update (b z (i : ℕ)) i (a i (τ + z) - a i τ)) := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro m hm
        have hmk : m < k := Finset.mem_range.mp hm
        simp only [hmk, dif_pos]
        exact hstep z m hmk
  have hslope (z : ℂ) :
      z⁻¹ • (M (fun j => a j (τ + z)) - M (fun j => a j τ)) =
        ∑ i : Fin k,
          M (Function.update (b z (i : ℕ)) i
            (z⁻¹ • (a i (τ + z) - a i τ))) := by
    rw [htel, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa only [smul_eq_mul] using
      (hsmul i (b z (i : ℕ)) z⁻¹ (a i (τ + z) - a i τ)).symm
  have hadd_zero :
      Filter.Tendsto (fun z : ℂ => τ + z) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds τ) := by
    have hfull : Filter.Tendsto (fun z : ℂ => τ + z) (nhds 0) (nhds (τ + 0)) :=
      tendsto_const_nhds.add Filter.tendsto_id
    simpa using hfull.mono_left nhdsWithin_le_nhds
  have harg (i : Fin k) :
      Filter.Tendsto
        (fun z : ℂ => Function.update (b z (i : ℕ)) i
          (z⁻¹ • (a i (τ + z) - a i τ)))
        (nhdsWithin 0 {(0 : ℂ)}ᶜ)
        (nhds (Function.update (fun j => a j τ) i (a' i))) := by
    rw [tendsto_pi_nhds]
    intro j
    by_cases hji : j = i
    · subst j
      have hi : Filter.Tendsto (fun z : ℂ => z⁻¹ • (a i (τ + z) - a i τ))
          (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (a' i)) := hderiv i
      simpa using hi
    · rw [Function.update_of_ne hji]
      by_cases hjlt : (j : ℕ) < (i : ℕ)
      · have heq : (fun z : ℂ => Function.update (b z (i : ℕ)) i
              (z⁻¹ • (a i (τ + z) - a i τ)) j) = fun z : ℂ => a j (τ + z) := by
          funext z
          rw [Function.update_of_ne hji]
          simp [b, hjlt]
        rw [heq]
        exact (hcont j).tendsto.comp hadd_zero
      · have heq : (fun z : ℂ => Function.update (b z (i : ℕ)) i
              (z⁻¹ • (a i (τ + z) - a i τ)) j) = fun _ : ℂ => a j τ := by
          funext z
          rw [Function.update_of_ne hji]
          simp [b, hjlt]
        rw [heq]
        exact tendsto_const_nhds
  have hterm (i : Fin k) :
      Filter.Tendsto
        (fun z : ℂ => M (Function.update (b z (i : ℕ)) i
          (z⁻¹ • (a i (τ + z) - a i τ))))
        (nhdsWithin 0 {(0 : ℂ)}ᶜ)
        (nhds (M (Function.update (fun j => a j τ) i (a' i)))) :=
    (hM.tendsto (Function.update (fun j => a j τ) i (a' i))).comp (harg i)
  have hsum :
      Filter.Tendsto
        (fun z : ℂ => ∑ i : Fin k,
          M (Function.update (b z (i : ℕ)) i
            (z⁻¹ • (a i (τ + z) - a i τ))))
        (nhdsWithin 0 {(0 : ℂ)}ᶜ)
        (nhds (∑ i : Fin k, M (Function.update (fun j => a j τ) i (a' i)))) := by
    exact tendsto_finsetSum Finset.univ (fun i _hi => hterm i)
  rw [hasDerivAt_iff_tendsto_slope_zero]
  change Filter.Tendsto
    (fun z : ℂ => z⁻¹ • (M (fun j => a j (τ + z)) - M (fun j => a j τ)))
    (nhdsWithin 0 {(0 : ℂ)}ᶜ)
    (nhds (∑ i : Fin k, M (Function.update (fun j => a j τ) i (a' i))))
  rw [show (fun z : ℂ => z⁻¹ • (M (fun j => a j (τ + z)) - M (fun j => a j τ))) =
      (fun z : ℂ => ∑ i : Fin k,
        M (Function.update (b z (i : ℕ)) i
          (z⁻¹ • (a i (τ + z) - a i τ)))) from funext hslope]
  exact hsum

end

end MobiusCPT
