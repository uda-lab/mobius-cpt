import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Order.Filter.Pi
import MobiusCPT.TestFunctions.CNorm

/-!
# Bounds for continuous multilinear functionals on test functions

Joint continuity of a finite multilinear functional on `TestFn` gives a product bound in one
of the defining `C^N` norms.  The proof uses only the locally convex topology and its defining
seminorms; in particular, it does not put a normed-space structure on `TestFn`.
-/

namespace MobiusCPT

open scoped Topology

noncomputable section

/-- [T26], Lemma 3.8; a jointly continuous multilinear functional is bounded by a product of
one common `C^N` norm over all its arguments. -/
theorem cnorm_bound_of_continuous_multilinear {k : ℕ}
    (M : MultilinearMap ℂ (fun _ : Fin k => TestFn) ℂ) (hM : Continuous M) :
    ∃ (N : ℕ) (A : ℝ), 0 < A ∧
      ∀ f : Fin k → TestFn, ‖M f‖ ≤ A * ∏ i, (cnorm N (f i) : ℝ) := by
  classical
  cases k with
  | zero =>
      refine ⟨0, ‖M (0 : Fin 0 → TestFn)‖ + 1, by positivity, ?_⟩
      intro f
      have hf : f = 0 := Subsingleton.elim _ _
      subst f
      simp
  | succ k =>
      have hunit : {f : Fin (k + 1) → TestFn | ‖M f‖ < 1} ∈
          nhds (0 : Fin (k + 1) → TestFn) := by
        apply (isOpen_Iio.preimage (continuous_norm.comp hM)).mem_nhds
        show ‖M (0 : Fin (k + 1) → TestFn)‖ < 1
        rw [M.map_zero]
        exact norm_zero.trans_lt zero_lt_one
      rw [nhds_pi, Filter.mem_pi'] at hunit
      obtain ⟨I, U, hU, hIU⟩ := hunit

      have hballs : ∀ i : Fin (k + 1),
          ∃ s : Finset ℕ, ∃ r : ℝ, 0 < r ∧
            (s.sup cnormSeminorm).ball 0 r ⊆ U i := by
        intro i
        simpa only [Prod.exists] using
          (withSeminorms_cnorm.hasBasis_zero_ball.mem_iff.mp (hU i))
      choose s r hr hsr using hballs

      let N : ℕ := Finset.univ.sup fun i : Fin (k + 1) => (s i).sup id
      let ε : ℝ := Finset.univ.inf' Finset.univ_nonempty r
      have hε : 0 < ε := by
        dsimp [ε]
        exact (Finset.lt_inf'_iff _).2 fun i _ => hr i
      have hε_le (i : Fin (k + 1)) : ε ≤ r i :=
        Finset.inf'_le r (Finset.mem_univ i)
      have hs_le_N (i : Fin (k + 1)) {j : ℕ} (hj : j ∈ s i) : j ≤ N := by
        exact (Finset.le_sup hj).trans
          (Finset.le_sup (f := fun i : Fin (k + 1) => (s i).sup id) (Finset.mem_univ i))

      have hsmall : ∀ f : Fin (k + 1) → TestFn,
          (∀ i, cnormSeminorm N (f i) < ε) → ‖M f‖ < 1 := by
        intro f hf
        apply hIU
        intro i hi
        apply hsr i
        rw [Seminorm.mem_ball_zero]
        apply Seminorm.finset_sup_apply_lt (hr i)
        intro j hj
        have hmono : cnormSeminorm j (f i) ≤ cnormSeminorm N (f i) := by
          simpa only [cnorm_coe] using
            (NNReal.coe_le_coe.mpr (cnorm_mono (hs_le_N i hj) (f i)))
        exact hmono.trans_lt ((hf i).trans_le (hε_le i))

      let A : ℝ := ∏ _i : Fin (k + 1), 2 / ε
      have hA : 0 < A := Finset.prod_pos fun _ _ => div_pos (by norm_num) hε
      refine ⟨N, A, hA, ?_⟩
      intro f
      by_cases hfzero : ∃ i, cnorm N (f i) = 0
      · obtain ⟨i, hi⟩ := hfzero
        have hfi : f i = 0 := (cnorm_eq_zero N (f i)).mp hi
        have hprod : ∏ j, (cnorm N (f j) : ℝ) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp only [hi, NNReal.coe_zero]
        rw [M.map_coord_zero i hfi, norm_zero, hprod, mul_zero]
      · have hq (i : Fin (k + 1)) : 0 < (cnorm N (f i) : ℝ) := by
          apply NNReal.coe_pos.mpr
          exact pos_iff_ne_zero.mpr fun hi => hfzero ⟨i, hi⟩
        let a : Fin (k + 1) → ℝ := fun i => ε / (2 * (cnorm N (f i) : ℝ))
        have ha (i : Fin (k + 1)) : 0 < a i := by
          dsimp [a]
          exact div_pos hε (mul_pos (by norm_num) (hq i))
        let g : Fin (k + 1) → TestFn := fun i => (a i : ℂ) • f i
        have hag (i : Fin (k + 1)) :
            a i * (cnorm N (f i) : ℝ) = ε / 2 := by
          dsimp [a]
          field_simp [(hq i).ne']
        have hgsmall : ‖M g‖ < 1 := by
          apply hsmall g
          intro i
          change (cnorm N ((a i : ℂ) • f i) : ℝ) < ε
          rw [cnorm_smul, NNReal.coe_mul, coe_nnnorm, Complex.norm_real,
            Real.norm_of_nonneg (ha i).le, hag]
          linarith
        have hscale : ‖M g‖ = (∏ i, a i) * ‖M f‖ := by
          have hMg : M g = (∏ i, (a i : ℂ)) • M f := by
            show M (fun i => (a i : ℂ) • f i) = (∏ i, (a i : ℂ)) • M f
            exact M.map_smul_univ (fun i => (a i : ℂ)) f
          rw [hMg, norm_smul, norm_prod]
          congr 1
          apply Finset.prod_congr rfl
          intro i _
          rw [Complex.norm_real, Real.norm_of_nonneg (ha i).le]
        have hpa : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
        have hMf : ‖M f‖ < 1 / ∏ i, a i := by
          rw [lt_div_iff₀ hpa]
          rw [mul_comm, ← hscale]
          exact hgsmall
        have ha_inv (i : Fin (k + 1)) :
            (a i)⁻¹ = (2 / ε) * (cnorm N (f i) : ℝ) := by
          dsimp [a]
          field_simp [hε.ne', (hq i).ne']
        have hfactor : 1 / ∏ i, a i = A * ∏ i, (cnorm N (f i) : ℝ) := by
          rw [one_div, ← Finset.prod_inv_distrib]
          simp_rw [ha_inv]
          rw [Finset.prod_mul_distrib]
        exact hMf.le.trans_eq hfactor

end

end MobiusCPT
