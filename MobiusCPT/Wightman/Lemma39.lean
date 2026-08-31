import MobiusCPT.Wightman.Lemma39Interior
import MobiusCPT.Wightman.Lemma39DiffContOnCl
import MobiusCPT.Wightman.Lemma39Boundary
import MobiusCPT.Analysis.StripMaxPrinciple
import MobiusCPT.TestFunctions.CNorm

/-!
# [T26], Lemma 3.9: the closed-strip estimate

The two boundary estimates are reconciled to common constants and combined with the
interior growth and regularity statements by the strip maximum principle.
-/

namespace MobiusCPT

noncomputable section

namespace WightmanBundle

private theorem prod_mono_N {M N : ℕ} (hMN : M ≤ N) (l : List (TestFn × TestFn)) :
    (((l.map (fun p => 1 + cnorm M p.1 + cnorm M p.2)).prod : NNReal) : ℝ) ≤
      (((l.map (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      have hheadNN :
          (1 + cnorm M a.1 + cnorm M a.2 : NNReal) ≤
            1 + cnorm N a.1 + cnorm N a.2 :=
        add_le_add (add_le_add le_rfl (cnorm_mono hMN a.1))
          (cnorm_mono hMN a.2)
      have hhead :
          (((1 + cnorm M a.1 + cnorm M a.2 : NNReal) : ℝ)) ≤
            (((1 + cnorm N a.1 + cnorm N a.2 : NNReal) : ℝ)) :=
        NNReal.coe_le_coe.mpr hheadNN
      simpa only [List.map_cons, List.prod_cons, NNReal.coe_mul] using
        mul_le_mul hhead ih (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

private theorem foldr_max_mono_N {M N : ℕ} (hMN : M ≤ N)
    (l : List (TestFn × TestFn)) :
    (List.foldr max 0 (l.map (fun p => cnorm M (p.1 - p.2))) : NNReal) ≤
      (List.foldr max 0 (l.map (fun p => cnorm N (p.1 - p.2))) : NNReal) := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simpa only [List.map_cons, List.foldr_cons] using
        max_le_max (cnorm_mono hMN (a.1 - a.2)) ih

/-- [T26], Lemma 3.9. Issue #11 discharges `MobiusCPT.Contract`'s
`theorem_wanted lemma_3_9`, byte-identical statement text. -/
theorem lemma_3_9 (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (φs : List W.𝓕) (lam : W.data.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (M : ℝ),
      0 < N ∧ 0 < M ∧
        ∀ (Fs Gs : List AnalyticTestFn),
          Fs.length = φs.length → Gs.length = φs.length →
            ∀ τ ∈ strip (Complex.I * Real.pi),
              ‖W.data.toWightmanStruct.compatApply lam
                  (W.data.vtildeMap τ
                      (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
                    W.data.vtildeMap τ
                      (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
                M * Real.exp (τ.re ^ 2) *
                    (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                      (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
                  ((List.foldr max 0
                    (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                      (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
  obtain ⟨N₁, k₁, k₂, hN₁, hk₁, hk₂, hlow⟩ :=
    lemma_3_9_lower_bound W h φs lam
  obtain ⟨N₂, k₁', k₂', hN₂, hk₁', hk₂', hup⟩ :=
    lemma_3_9_upper_bound W h φs lam
  let N'' : ℕ := max N₁ N₂
  let k₁'' : ℝ := max k₁ k₁'
  let k₂'' : ℝ := max k₂ k₂'
  have hN₁N'' : N₁ ≤ N'' := by
    dsimp [N'']
    exact le_max_left N₁ N₂
  have hN₂N'' : N₂ ≤ N'' := by
    dsimp [N'']
    exact le_max_right N₁ N₂
  have hk₁k₁'' : k₁ ≤ k₁'' := by
    dsimp [k₁'']
    exact le_max_left k₁ k₁'
  have hk₁'k₁'' : k₁' ≤ k₁'' := by
    dsimp [k₁'']
    exact le_max_right k₁ k₁'
  have hk₂k₂'' : k₂ ≤ k₂'' := by
    dsimp [k₂'']
    exact le_max_left k₂ k₂'
  have hk₂'k₂'' : k₂' ≤ k₂'' := by
    dsimp [k₂'']
    exact le_max_right k₂ k₂'
  have hN'' : 0 < N'' := hN₁.trans_le hN₁N''
  have hk₁'' : 0 < k₁'' := hk₁.trans_le hk₁k₁''
  have hk₂'' : 0 < k₂'' := hk₂.trans_le hk₂k₂''
  let M : ℝ := Real.exp (Real.pi ^ 2) * k₁'' * Real.exp (k₂'' ^ 2 / 4)
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (mul_pos (Real.exp_pos _) hk₁'') (Real.exp_pos _)
  refine ⟨N'', M, hN'', hM, ?_⟩
  intro Fs Gs hFs hGs
  let X'' : ℝ :=
    (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
      (fun p => 1 + cnorm N'' p.1 + cnorm N'' p.2)).prod : NNReal) : ℝ) *
      ((List.foldr max 0
        (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
          (fun p => cnorm N'' (p.1 - p.2))) : NNReal) : ℝ)
  have hd := WightmanData.lemma_3_9_diffContOnCl (W := W.data)
    h φs lam Fs Gs hFs hGs
  have hgrowth := WightmanData.lemma_3_9_interior_growth (W := W.data)
    h φs lam Fs Gs hFs hGs
  have hX'' : 0 ≤ X'' := by
    dsimp [X'']
    exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hcontrol₁ :
      (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
        (fun p => 1 + cnorm N₁ p.1 + cnorm N₁ p.2)).prod : NNReal) : ℝ) *
        ((List.foldr max 0
          (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => cnorm N₁ (p.1 - p.2))) : NNReal) : ℝ) ≤ X'' := by
    have hprod := prod_mono_N hN₁N''
      ((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper))
    have hmax :
        (((List.foldr max 0
          (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => cnorm N₁ (p.1 - p.2))) : NNReal) : ℝ)) ≤
          (((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N'' (p.1 - p.2))) : NNReal) : ℝ)) :=
      NNReal.coe_le_coe.mpr (foldr_max_mono_N hN₁N''
        ((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)))
    dsimp [X'']
    exact mul_le_mul hprod hmax (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hcontrol₂ :
      (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
        (fun p => 1 + cnorm N₂ p.1 + cnorm N₂ p.2)).prod : NNReal) : ℝ) *
        ((List.foldr max 0
          (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => cnorm N₂ (p.1 - p.2))) : NNReal) : ℝ) ≤ X'' := by
    have hprod := prod_mono_N hN₂N''
      ((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper))
    have hmax :
        (((List.foldr max 0
          (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => cnorm N₂ (p.1 - p.2))) : NNReal) : ℝ)) ≤
          (((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N'' (p.1 - p.2))) : NNReal) : ℝ)) :=
      NNReal.coe_le_coe.mpr (foldr_max_mono_N hN₂N''
        ((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)))
    dsimp [X'']
    exact mul_le_mul hprod hmax (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  have hlow'' : ∀ t : ℝ,
      ‖W.data.toWightmanStruct.compatApply lam
          (W.data.vtildeMap (t : ℂ)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
            W.data.vtildeMap (t : ℂ)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
        k₁'' * Real.exp (k₂'' * |t|) * X'' := by
    intro t
    have hcoef : k₁ * Real.exp (k₂ * |t|) ≤
        k₁'' * Real.exp (k₂'' * |t|) := by
      exact mul_le_mul hk₁k₁''
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hk₂k₂'' (abs_nonneg t)))
        (Real.exp_nonneg _) hk₁''.le
    calc
      ‖W.data.toWightmanStruct.compatApply lam
          (W.data.vtildeMap (t : ℂ)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
            W.data.vtildeMap (t : ℂ)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
          k₁ * Real.exp (k₂ * |t|) *
            (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => 1 + cnorm N₁ p.1 + cnorm N₁ p.2)).prod : NNReal) : ℝ) *
            ((List.foldr max 0
              (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                (fun p => cnorm N₁ (p.1 - p.2))) : NNReal) : ℝ) :=
        hlow Fs Gs hFs hGs t
      _ ≤ (k₁ * Real.exp (k₂ * |t|)) * X'' := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hcontrol₁
          (mul_nonneg hk₁.le (Real.exp_nonneg _))
      _ ≤ (k₁'' * Real.exp (k₂'' * |t|)) * X'' :=
        mul_le_mul_of_nonneg_right hcoef hX''
  have hup'' : ∀ t : ℝ,
      ‖W.data.toWightmanStruct.compatApply lam
          (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
            W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
        k₁'' * Real.exp (k₂'' * |t|) * X'' := by
    intro t
    have hcoef : k₁' * Real.exp (k₂' * |t|) ≤
        k₁'' * Real.exp (k₂'' * |t|) := by
      exact mul_le_mul hk₁'k₁''
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hk₂'k₂'' (abs_nonneg t)))
        (Real.exp_nonneg _) hk₁''.le
    calc
      ‖W.data.toWightmanStruct.compatApply lam
          (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
            W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
              (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
          k₁' * Real.exp (k₂' * |t|) *
            (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => 1 + cnorm N₂ p.1 + cnorm N₂ p.2)).prod : NNReal) : ℝ) *
            ((List.foldr max 0
              (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                (fun p => cnorm N₂ (p.1 - p.2))) : NNReal) : ℝ) :=
        hup Fs Gs hFs hGs t
      _ ≤ (k₁' * Real.exp (k₂' * |t|)) * X'' := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hcontrol₂
          (mul_nonneg hk₁'.le (Real.exp_nonneg _))
      _ ≤ (k₁'' * Real.exp (k₂'' * |t|)) * X'' :=
        mul_le_mul_of_nonneg_right hcoef hX''
  have hstrip := strip_max_principle hd hgrowth hX'' hlow'' hup''
  intro τ hτ
  calc
    ‖W.data.toWightmanStruct.compatApply lam
        (W.data.vtildeMap τ
            (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
          W.data.vtildeMap τ
            (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
        (Real.exp (Real.pi ^ 2) * k₁'' * Real.exp (k₂'' ^ 2 / 4)) *
          Real.exp (τ.re ^ 2) * X'' := hstrip τ hτ
    _ = M * Real.exp (τ.re ^ 2) *
          (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => 1 + cnorm N'' p.1 + cnorm N'' p.2)).prod : NNReal) : ℝ) *
        ((List.foldr max 0
          (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => cnorm N'' (p.1 - p.2))) : NNReal) : ℝ) := by
      dsimp [M, X'']
      ring

end WightmanBundle

end

end MobiusCPT
