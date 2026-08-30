import MobiusCPT.Analysis.MultilinearBound
import MobiusCPT.Mobius.BoostGrowth
import MobiusCPT.Mobius.Covariance
import MobiusCPT.Wightman.Bundle
import MobiusCPT.Wightman.Continuity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.MinMax

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

/-- Equal-length lists zip to the tuple obtained by indexing both by their common `Fin` type. -/
theorem List.zip_eq_ofFn_get_of_length_eq {α β : Type*} (xs : List α) (ys : List β)
    (h : ys.length = xs.length) :
    xs.zip ys = List.ofFn fun i : Fin xs.length =>
      (xs.get i, ys.get (Fin.cast h.symm i)) := by
  induction xs generalizing ys with
  | nil =>
      have hys : ys = [] := List.length_eq_zero_iff.mp (by simpa using h)
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          have htail : ys.length = xs.length := Nat.succ.inj h
          simpa [List.ofFn_succ] using
            congrArg (fun zs => (x, y) :: zs) (ih ys htail)

namespace WightmanData
variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
/-- [T26], Lemma 3.8: real boosts obey a uniform exponential `C^N` continuity estimate. -/
theorem lemma_3_8 (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (φs : List 𝓕) (lam : W.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (C : ℝ → ℝ) (k₁ k₂ : ℝ),
      0 < N ∧ 0 < k₁ ∧ 0 < k₂ ∧
        (∀ t : ℝ, 0 < C t) ∧
        (∀ t : ℝ, C t ≤ k₁ * Real.exp (k₂ * |t|)) ∧
        ∀ (t : ℝ) (fs gs : List TestFn),
          fs.length = φs.length → gs.length = φs.length →
            ‖W.toWightmanStruct.compatApply lam
                (W.boost t (W.toWightmanStruct.smearedProduct (φs.zip fs)) -
                  W.boost t (W.toWightmanStruct.smearedProduct (φs.zip gs)))‖ ≤
              C t *
                  ((((fs.zip gs).map
                    (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
                ((List.foldr max 0
                  ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
  classical
  let φFin : Fin φs.length → 𝓕 := φs.get
  let M : MultilinearMap ℂ (fun _ : Fin φs.length => TestFn) ℂ :=
    lam.1.compMultilinearMap
      (W.toWightmanStruct.multiSmearMultilinear φFin W.vac)
  have hM : Continuous M := by
    apply (lam.2 φs.length φFin W.vac).congr
    intro f
    simp only [M, LinearMap.compMultilinearMap_apply,
      WightmanStruct.multiSmearMultilinear_apply]
  obtain ⟨N₀, A, hA, hbound₀⟩ := cnorm_bound_of_continuous_multilinear M hM
  let N : ℕ := N₀ + 1
  have hN : 0 < N := by simp [N]
  have hbound : ∀ f : Fin φs.length → TestFn,
      ‖M f‖ ≤ A * ∏ i, (cnorm N (f i) : ℝ) := by
    intro f
    calc
      ‖M f‖ ≤ A * ∏ i, (cnorm N₀ (f i) : ℝ) := hbound₀ f
      _ ≤ A * ∏ i, (cnorm N (f i) : ℝ) := by
        gcongr with i
        exact_mod_cast cnorm_mono (by simp [N]) (f i)
  choose B rate hB hrate hboost using
    fun i : Fin φs.length => cnorm_boost_le N (W.dim (φFin i))
  let B₀ : ℝ := 1 + ∑ i, B i
  let rate₀ : ℝ := 1 + ∑ i, rate i
  have hB₀ : 0 < B₀ := by
    dsimp [B₀]
    have : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => (hB i).le
    linarith
  have hrate₀ : 0 < rate₀ := by
    dsimp [rate₀]
    have : 0 ≤ ∑ i, rate i := Finset.sum_nonneg fun i _ => (hrate i).le
    linarith
  have hB_le (i : Fin φs.length) : B i ≤ B₀ := by
    have hi : B i ≤ ∑ j, B j :=
      Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
    dsimp [B₀]
    linarith
  have hrate_le (i : Fin φs.length) : rate i ≤ rate₀ := by
    have hi : rate i ≤ ∑ j, rate j :=
      Finset.single_le_sum (fun j _ => (hrate j).le) (Finset.mem_univ i)
    dsimp [rate₀]
    linarith
  let k₁ : ℝ := 1 + A * (φs.length : ℝ) * B₀ ^ (φs.length + 1)
  let k₂ : ℝ := ((φs.length + 1 : ℕ) : ℝ) * rate₀
  let C : ℝ → ℝ := fun t => k₁ * Real.exp (k₂ * |t|)
  have hk₁ : 0 < k₁ := by
    dsimp [k₁]
    have hnonneg : 0 ≤ A * (φs.length : ℝ) * B₀ ^ (φs.length + 1) := by positivity
    linarith
  have hk₂ : 0 < k₂ := by
    dsimp [k₂]
    positivity
  refine ⟨N, C, k₁, k₂, hN, hk₁, hk₂, ?_, ?_, ?_⟩
  · intro t
    exact mul_pos hk₁ (Real.exp_pos _)
  · intro t
    exact le_rfl
  · intro t fs gs hfs hgs
    let fsFin : Fin φs.length → TestFn := fun i => fs.get (Fin.cast hfs.symm i)
    let gsFin : Fin φs.length → TestFn := fun i => gs.get (Fin.cast hgs.symm i)
    let bfs : Fin φs.length → TestFn := fun i =>
      Mob.beta (W.dim (φFin i)) (Mob.boost t) (fsFin i)
    let bgs : Fin φs.length → TestFn := fun i =>
      Mob.beta (W.dim (φFin i)) (Mob.boost t) (gsFin i)
    have hzip_fs : φs.zip fs = List.ofFn fun i : Fin φs.length => (φFin i, fsFin i) := by
      simpa only [φFin, fsFin] using List.zip_eq_ofFn_get_of_length_eq φs fs hfs
    have hzip_gs : φs.zip gs = List.ofFn fun i : Fin φs.length => (φFin i, gsFin i) := by
      simpa only [φFin, gsFin] using List.zip_eq_ofFn_get_of_length_eq φs gs hgs
    have hcov_fs : ∀ p ∈ φs.zip fs, W.IsCovariant p.1 (W.dim p.1) := by
      intro p _
      exact W1.covariant W hW.w1 p.1
    have hcov_gs : ∀ p ∈ φs.zip gs, W.IsCovariant p.1 (W.dim p.1) := by
      intro p _
      exact W1.covariant W hW.w1 p.1
    have hboost_fs :
        W.boost t (W.toWightmanStruct.smearedProduct (φs.zip fs)) =
          W.toWightmanStruct.multiSmear φFin W.vac bfs := by
      calc
        W.boost t (W.toWightmanStruct.smearedProduct (φs.zip fs)) =
            W.toWightmanStruct.smearedProduct
              ((φs.zip fs).map fun p =>
                (p.1, MobiusAction.beta (W.dim p.1)
                  (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) p.2)) :=
          WightmanData.boost_smearedProduct hW.w4 t _ hcov_fs
        _ = W.toWightmanStruct.multiSmear φFin W.vac bfs := by
          rw [hzip_fs, List.map_ofFn]
          rfl
    have hboost_gs :
        W.boost t (W.toWightmanStruct.smearedProduct (φs.zip gs)) =
          W.toWightmanStruct.multiSmear φFin W.vac bgs := by
      calc
        W.boost t (W.toWightmanStruct.smearedProduct (φs.zip gs)) =
            W.toWightmanStruct.smearedProduct
              ((φs.zip gs).map fun p =>
                (p.1, MobiusAction.beta (W.dim p.1)
                  (MobiusAction.boostElt (G := Mob) (TF := TestFn) t) p.2)) :=
          WightmanData.boost_smearedProduct hW.w4 t _ hcov_gs
        _ = W.toWightmanStruct.multiSmear φFin W.vac bgs := by
          rw [hzip_gs, List.map_ofFn]
          rfl
    have hlhs :
        W.toWightmanStruct.compatApply lam
            (W.boost t (W.toWightmanStruct.smearedProduct (φs.zip fs)) -
              W.boost t (W.toWightmanStruct.smearedProduct (φs.zip gs))) =
          M bfs - M bgs := by
      change lam.1 _ = _
      rw [map_sub, hboost_fs, hboost_gs]
      rfl
    have hzip_fg : fs.zip gs = List.ofFn fun i : Fin φs.length => (fsFin i, gsFin i) := by
      have hfg : gs.length = fs.length := hgs.trans hfs.symm
      have hz := List.zip_eq_ofFn_get_of_length_eq fs gs hfg
      simpa only [hfs, fsFin, gsFin, Fin.cast_refl, Fin.cast_cast] using hz
    let listProd : ℝ :=
      ((((fs.zip gs).map
        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ)
    let listMax : NNReal :=
      List.foldr max 0 ((fs.zip gs).map fun p => cnorm N (p.1 - p.2))
    have hprod_eq : listProd =
        ∏ i : Fin φs.length,
          (1 + (cnorm N (fsFin i) : ℝ) + (cnorm N (gsFin i) : ℝ)) := by
      dsimp [listProd]
      rw [hzip_fg, List.map_ofFn, List.prod_ofFn, NNReal.coe_prod]
      simp
    let q : ℝ := B₀ * Real.exp (rate₀ * |t|)
    have hq : 0 < q := mul_pos hB₀ (Real.exp_pos _)
    have hone_q : 1 ≤ q := by
      have he : 1 ≤ Real.exp (rate₀ * |t|) :=
        Real.one_le_exp (mul_nonneg hrate₀.le (abs_nonneg t))
      have hBone : 1 ≤ B₀ := by
        dsimp [B₀]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hB i).le)
      exact one_le_mul_of_one_le_of_one_le hBone he
    have hboost_uniform (i : Fin φs.length) (f : TestFn) :
        (cnorm N (Mob.beta (W.dim (φFin i)) (Mob.boost t) f) : ℝ) ≤
          q * (cnorm N f : ℝ) := by
      calc
        (cnorm N (Mob.beta (W.dim (φFin i)) (Mob.boost t) f) : ℝ) ≤
            B i * Real.exp (rate i * |t|) * (cnorm N f : ℝ) := hboost i t f
        _ ≤ q * (cnorm N f : ℝ) := by
          dsimp [q]
          gcongr
          · exact hB_le i
          · exact hrate_le i
    have hmem_diff (i : Fin φs.length) :
        cnorm N (fsFin i - gsFin i) ∈
          (fs.zip gs).map (fun p => cnorm N (p.1 - p.2)) := by
      rw [hzip_fg, List.map_ofFn]
      simp
    have hdiff_le_max (i : Fin φs.length) :
        cnorm N (fsFin i - gsFin i) ≤ listMax := by
      exact List.le_max_of_le (hmem_diff i) le_rfl
    let qNN : NNReal := ⟨q, hq.le⟩
    have hsupNN :
        Finset.univ.sup (fun i => cnorm N (bfs i - bgs i)) ≤ qNN * listMax := by
      apply Finset.sup_le
      intro i _
      apply NNReal.coe_le_coe.mp
      change (cnorm N (bfs i - bgs i) : ℝ) ≤ q * (listMax : ℝ)
      have hdiff : bfs i - bgs i =
          Mob.beta (W.dim (φFin i)) (Mob.boost t) (fsFin i - gsFin i) := by
        simp only [bfs, bgs, map_sub]
      rw [hdiff]
      exact (hboost_uniform i (fsFin i - gsFin i)).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hdiff_le_max i) hq.le)
    have hsup :
        ((Finset.univ.sup (fun i => cnorm N (bfs i - bgs i)) : NNReal) : ℝ) ≤
          q * (listMax : ℝ) := by
      calc
        ((Finset.univ.sup (fun i => cnorm N (bfs i - bgs i)) : NNReal) : ℝ) ≤
            ((qNN * listMax : NNReal) : ℝ) := NNReal.coe_le_coe.mpr hsupNN
        _ = q * (listMax : ℝ) := by
          rw [NNReal.coe_mul]
          congr 1
    have hfactor (i : Fin φs.length) :
        1 + (cnorm N (bfs i) : ℝ) + (cnorm N (bgs i) : ℝ) ≤
          q * (1 + (cnorm N (fsFin i) : ℝ) + (cnorm N (gsFin i) : ℝ)) := by
      have hf := hboost_uniform i (fsFin i)
      have hg := hboost_uniform i (gsFin i)
      change (cnorm N (bfs i) : ℝ) ≤ _ at hf
      change (cnorm N (bgs i) : ℝ) ≤ _ at hg
      nlinarith [NNReal.coe_nonneg (cnorm N (fsFin i)),
        NNReal.coe_nonneg (cnorm N (gsFin i))]
    have hprod_boost :
        (∏ i : Fin φs.length,
          (1 + (cnorm N (bfs i) : ℝ) + (cnorm N (bgs i) : ℝ))) ≤
            q ^ φs.length * listProd := by
      calc
        (∏ i : Fin φs.length,
            (1 + (cnorm N (bfs i) : ℝ) + (cnorm N (bgs i) : ℝ))) ≤
            ∏ i : Fin φs.length,
              q * (1 + (cnorm N (fsFin i) : ℝ) + (cnorm N (gsFin i) : ℝ)) := by
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            exact hfactor i
        _ = q ^ φs.length * listProd := by
          rw [Finset.prod_mul_distrib, hprod_eq]
          simp
    have hqpow : q ^ (φs.length + 1) =
        B₀ ^ (φs.length + 1) * Real.exp (k₂ * |t|) := by
      dsimp [q, k₂]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hcoef : A * (φs.length : ℝ) * B₀ ^ (φs.length + 1) ≤ k₁ := by
      dsimp [k₁]
      linarith
    have htel := MultilinearMap.norm_sub_le_of_cnorm_bound
      M N A hA.le hbound bfs bgs
    calc
      ‖W.toWightmanStruct.compatApply lam
          (W.boost t (W.toWightmanStruct.smearedProduct (φs.zip fs)) -
            W.boost t (W.toWightmanStruct.smearedProduct (φs.zip gs)))‖ =
          ‖M bfs - M bgs‖ := congrArg norm hlhs
      _ ≤ A * (φs.length : ℝ) *
            ((Finset.univ.sup (fun i => cnorm N (bfs i - bgs i)) : NNReal) : ℝ) *
              ∏ i : Fin φs.length,
                (1 + (cnorm N (bfs i) : ℝ) + (cnorm N (bgs i) : ℝ)) := htel
      _ ≤ A * (φs.length : ℝ) * (q * (listMax : ℝ)) *
            (q ^ φs.length * listProd) := by
          gcongr
      _ = A * (φs.length : ℝ) * q ^ (φs.length + 1) * listProd * (listMax : ℝ) := by
          rw [pow_succ]
          ring
      _ = (A * (φs.length : ℝ) * B₀ ^ (φs.length + 1)) *
            Real.exp (k₂ * |t|) * listProd * (listMax : ℝ) := by
          rw [hqpow]
          ring
      _ ≤ k₁ * Real.exp (k₂ * |t|) * listProd * (listMax : ℝ) := by
          gcongr
      _ = C t * (listProd * (listMax : ℝ)) := by
          dsimp [C]
          ring
      _ = C t *
            ((((fs.zip gs).map
              (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
              ((List.foldr max 0
                ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
          dsimp [listProd, listMax]
          ring

end WightmanData
namespace WightmanBundle
/-- [T26], Lemma 3.8. Issue #10 discharges `MobiusCPT.Contract`'s
`theorem_wanted lemma_3_8`, byte-identical statement text. -/
theorem lemma_3_8 (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (φs : List W.𝓕) (lam : W.data.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (C : ℝ → ℝ) (k₁ k₂ : ℝ),
      0 < N ∧ 0 < k₁ ∧ 0 < k₂ ∧
        (∀ t : ℝ, 0 < C t) ∧
        (∀ t : ℝ, C t ≤ k₁ * Real.exp (k₂ * |t|)) ∧
        ∀ (t : ℝ) (fs gs : List TestFn),
          fs.length = φs.length → gs.length = φs.length →
            ‖W.data.toWightmanStruct.compatApply lam
                (W.data.boost t (W.data.toWightmanStruct.smearedProduct (φs.zip fs)) -
                  W.data.boost t (W.data.toWightmanStruct.smearedProduct (φs.zip gs)))‖ ≤
              C t *
                  ((((fs.zip gs).map
                    (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
                ((List.foldr max 0
                  ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) :=
  WightmanData.lemma_3_8 W.data h φs lam

end WightmanBundle
end

end MobiusCPT
