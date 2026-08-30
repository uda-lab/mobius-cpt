import MobiusCPT.Analysis.MultilinearBound
import MobiusCPT.Mobius.BoostGrowth
import MobiusCPT.Mobius.Covariance
import MobiusCPT.Wightman.Continuity

/-!
# MobiusCPT.Wightman.Lemma38

[T26], Lemma 3.8: the real-boundary `C^N` growth estimate. This file discharges the
`lemma_3_8` placeholder in `MobiusCPT.Contract` by telescoping the difference of two
boosted products slot by slot (Block C), bounding each term with the multilinear bound
of `MobiusCPT.Analysis.MultilinearBound` (Block A) and the boost growth bound of
`MobiusCPT.Mobius.BoostGrowth` (Block B).
-/

namespace MobiusCPT

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

noncomputable section

/-! ### The `k`-term telescoping bound for a multilinear map with a `cnorm`-product bound -/

/-- The classical "multilinear ⟹ Lipschitz-type" telescoping bound, specialised to the
`cnorm`-product bound of `cnorm_bound_of_continuous_multilinear`: a `k`-term sum, each term
linear in the difference of exactly one coordinate, rather than the `2^k`-term full expansion of
`MultilinearMap.map_piecewise_add`. -/
theorem MultilinearMap.norm_sub_le_of_cnorm_bound {k : ℕ}
    (M : MultilinearMap ℂ (fun _ : Fin k => TestFn) ℂ) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ h : Fin k → TestFn, ‖M h‖ ≤ A * ∏ i, (cnorm N (h i) : ℝ))
    (b a : Fin k → TestFn) :
    ‖M b - M a‖ ≤
      A * (k : ℝ) * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
        ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
  classical
  -- The mixed tuple that has `b` on indices `< n` and `a` on indices `≥ n`.
  set mix : ℕ → (Fin k → TestFn) := fun n j => if j.val < n then b j else a j with hmix_def
  have hmix_zero : mix 0 = a := by
    funext j
    simp [hmix_def]
  have hmix_k : mix k = b := by
    funext j
    simp [hmix_def, j.isLt]
  -- The one-step difference is a single-coordinate update.
  have hstep : ∀ n : ℕ, (hn : n < k) →
      mix (n + 1) = Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩) := by
    intro n hn
    funext j
    by_cases hji : j = ⟨n, hn⟩
    · subst hji
      simp [hmix_def]
    · have hjn : j.val ≠ n := by
        intro h
        exact hji (Fin.ext h)
      rw [Function.update_of_ne hji]
      simp only [hmix_def]
      rcases lt_or_gt_of_ne hjn with h | h
      · simp [h, h.trans (Nat.lt_succ_self n)]
      · have h' : ¬ j.val < n := by omega
        have h'' : ¬ j.val < n + 1 := by omega
        simp [h', h'']
  have hmix_n : ∀ n : ℕ, (hn : n < k) → mix n ⟨n, hn⟩ = a ⟨n, hn⟩ := by
    intro n hn
    simp [hmix_def]
  have hupdate_self : ∀ n : ℕ, (hn : n < k) →
      Function.update (mix n) ⟨n, hn⟩ (a ⟨n, hn⟩) = mix n := by
    intro n hn
    rw [← hmix_n n hn, Function.update_eq_self]
  -- One step of the telescoping sum.
  have hone_step : ∀ n : ℕ, (hn : n < k) →
      M (mix (n + 1)) - M (mix n) =
        M (Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩ - a ⟨n, hn⟩)) := by
    intro n hn
    have hb_eq : b ⟨n, hn⟩ = a ⟨n, hn⟩ + (b ⟨n, hn⟩ - a ⟨n, hn⟩) := by abel
    rw [hstep n hn, hb_eq, M.map_update_add, hupdate_self n hn]
    abel
  -- Bound of one telescoping term.
  have hterm_bound : ∀ n : ℕ, (hn : n < k) →
      ‖M (Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩ - a ⟨n, hn⟩))‖ ≤
        A * (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
          ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
    intro n hn
    have h1 := hbound (Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩ - a ⟨n, hn⟩))
    have hprod_eq :
        (∏ i, (cnorm N ((Function.update (mix n) ⟨n, hn⟩
            (b ⟨n, hn⟩ - a ⟨n, hn⟩)) i) : ℝ)) =
          (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
            ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (cnorm N (mix n i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨n, hn⟩ : Fin k))]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro i hi
        have hine : i ≠ ⟨n, hn⟩ := (Finset.mem_erase.mp hi).1
        rw [Function.update_of_ne hine]
    have hmono : ∀ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k),
        (cnorm N (mix n i) : ℝ) ≤ 1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ) := by
      intro i _
      simp only [hmix_def]
      split_ifs
      · linarith [NNReal.coe_nonneg (cnorm N (a i))]
      · linarith [NNReal.coe_nonneg (cnorm N (b i))]
    have hnonneg : ∀ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (0:ℝ) ≤ (cnorm N (mix n i) : ℝ) :=
      fun i _ => NNReal.coe_nonneg _
    have herase_le :
        ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (cnorm N (mix n i) : ℝ) ≤
          ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) :=
      Finset.prod_le_prod hnonneg hmono
    have herase_nonneg :
        (0:ℝ) ≤ ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (cnorm N (mix n i) : ℝ) :=
      Finset.prod_nonneg hnonneg
    have hfull_ge :
        ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) ≤
          ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => 1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) (Finset.mem_univ (⟨n, hn⟩ : Fin k))]
      have hone_le : (1:ℝ) ≤ 1 + (cnorm N (b ⟨n, hn⟩) : ℝ) + (cnorm N (a ⟨n, hn⟩) : ℝ) := by
        linarith [NNReal.coe_nonneg (cnorm N (b ⟨n, hn⟩)), NNReal.coe_nonneg (cnorm N (a ⟨n, hn⟩))]
      have hprod_nonneg :
          (0:ℝ) ≤ ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k),
            (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) :=
        Finset.prod_nonneg (fun i _ => by
          linarith [NNReal.coe_nonneg (cnorm N (b i)), NNReal.coe_nonneg (cnorm N (a i))])
      nlinarith [hprod_nonneg]
    have hcnormnn : (0:ℝ) ≤ (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) := NNReal.coe_nonneg _
    calc
      ‖M (Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩ - a ⟨n, hn⟩))‖
          ≤ A * ∏ i, (cnorm N ((Function.update (mix n) ⟨n, hn⟩
              (b ⟨n, hn⟩ - a ⟨n, hn⟩)) i) : ℝ) := h1
      _ = A * ((cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
            ∏ i ∈ Finset.univ.erase (⟨n, hn⟩ : Fin k), (cnorm N (mix n i) : ℝ)) := by
            rw [hprod_eq]
      _ ≤ A * ((cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
            ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ))) := by
            gcongr
            exact herase_le.trans hfull_ge
      _ = A * (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
            ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by ring
  have hsup_ge : ∀ n : ℕ, (hn : n < k) →
      (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) ≤
        ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) := by
    intro n hn
    exact_mod_cast Finset.le_sup (f := fun i => cnorm N (b i - a i))
      (Finset.mem_univ (⟨n, hn⟩ : Fin k))
  have hterm_bound' : ∀ n : ℕ, (hn : n < k) →
      ‖M (mix (n + 1)) - M (mix n)‖ ≤
        A * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
          ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
    intro n hn
    rw [hone_step n hn]
    have hprod_nonneg :
        (0:ℝ) ≤ ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) :=
      Finset.prod_nonneg (fun i _ => by
        linarith [NNReal.coe_nonneg (cnorm N (b i)), NNReal.coe_nonneg (cnorm N (a i))])
    calc
      ‖M (Function.update (mix n) ⟨n, hn⟩ (b ⟨n, hn⟩ - a ⟨n, hn⟩))‖
          ≤ A * (cnorm N (b ⟨n, hn⟩ - a ⟨n, hn⟩) : ℝ) *
              ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) :=
            hterm_bound n hn
      _ ≤ A * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
              ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
            gcongr
            exact hsup_ge n hn
  -- Telescope: `M b - M a = ∑_{n<k} (M (mix (n+1)) - M (mix n))`.
  have htelescope : M b - M a = ∑ n ∈ Finset.range k, (M (mix (n + 1)) - M (mix n)) := by
    have hsum : ∀ m : ℕ, m ≤ k →
        ∑ n ∈ Finset.range m, (M (mix (n + 1)) - M (mix n)) = M (mix m) - M (mix 0) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm
          rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm)]
          abel
    rw [hsum k le_rfl, hmix_k, hmix_zero]
  rw [htelescope]
  have hnn : (0:ℝ) ≤
      A * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
        ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
    apply mul_nonneg (mul_nonneg hA (NNReal.coe_nonneg _))
    exact Finset.prod_nonneg (fun i _ => by
      linarith [NNReal.coe_nonneg (cnorm N (b i)), NNReal.coe_nonneg (cnorm N (a i))])
  calc
    ‖∑ n ∈ Finset.range k, (M (mix (n + 1)) - M (mix n))‖
        ≤ ∑ n ∈ Finset.range k, ‖M (mix (n + 1)) - M (mix n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range k,
          A * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
            ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hterm_bound' n (Finset.mem_range.mp hn)
    _ = (k : ℝ) * (A * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
          ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = A * (k : ℝ) * ((Finset.univ.sup fun i => cnorm N (b i - a i) : NNReal) : ℝ) *
          ∏ i : Fin k, (1 + (cnorm N (b i) : ℝ) + (cnorm N (a i) : ℝ)) := by ring

end

end MobiusCPT
