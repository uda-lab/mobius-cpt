import MobiusCPT.Wightman.Lemma37
import MobiusCPT.Wightman.VtildeLaws
import MobiusCPT.Wightman.VtildeReal
import MobiusCPT.Wightman.VtildeLinear
import MobiusCPT.Wightman.Lemma38
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.Inv

/-!
# [T26], Lemma 3.9: the two boundary estimates

The lower boundary is Lemma 3.8 after identifying real continued boosts with real boosts.  On
the upper boundary, Lemma 3.7(ii) reverses the field product and applies inversion to its test
functions.  The sign has norm one, while inversion and list reversal preserve the two control
quantities in Lemma 3.8.
-/

namespace MobiusCPT

noncomputable section

namespace WightmanBundle

/-- Reversal commutes with zipping lists of equal length. -/
private theorem reverse_zip_eq {α β : Type*} (l₁ : List α) (l₂ : List β)
    (hlen : l₂.length = l₁.length) :
    (l₁.zip l₂).reverse = l₁.reverse.zip l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil =>
      have hl₂ : l₂ = [] := List.length_eq_zero_iff.mp hlen
      subst l₂
      rfl
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          have htail : l₂.length = l₁.length := Nat.succ.inj hlen
          simp only [List.zip_cons_cons, List.reverse_cons, ih l₂ htail]
          rw [List.zip_append (by simp [htail])]
          rfl

/-- Restricting the right list before zipping is the pair-list shape used by Lemma 3.7. -/
private theorem zip_xRestrictUpper_eq {α : Type*} (l : List α)
    (Fs : List AnalyticTestFn) :
    l.zip (Fs.map xRestrictUpper) =
      (l.zip Fs).map (fun p => (p.1, xRestrictUpper p.2)) := by
  rw [List.zip_map_right]
  rfl

/-- The conformal-dimension sum of a full zip depends only on its field list. -/
private theorem sum_dim_zip_eq {α β : Type*} (dim' : α → ℕ) (l : List α)
    (r : List β) (hlen : l.length ≤ r.length) :
    ((l.zip r).map (fun p => dim' p.1)).sum = (l.map dim').sum := by
  rw [show (l.zip r).map (fun p => dim' p.1) =
      ((l.zip r).map Prod.fst).map dim' by
        rw [List.map_map]
        rfl,
    List.map_fst_zip hlen]

/-- The reversed, inverted pair-list has the zip shape required by Lemma 3.8. -/
private theorem reverse_map_inv_restrict_eq_zip {α : Type*} (l : List α)
    (Fs : List AnalyticTestFn) (hlen : Fs.length = l.length) :
    (l.zip Fs).reverse.map (fun p => (p.1, inv (xRestrictUpper p.2))) =
      l.reverse.zip (((Fs.map xRestrictUpper).reverse).map inv) := by
  rw [reverse_zip_eq l Fs hlen]
  rw [← List.map_reverse, List.map_map, List.zip_map_right]
  rfl

/-- Inversion is complex-linear, hence preserves subtraction. -/
private theorem inv_sub_eq (f g : TestFn) : inv f - inv g = inv (f - g) := by
  calc
    inv f - inv g = inv f + (-1 : ℂ) • inv g := by
      rw [neg_one_smul, sub_eq_add_neg]
    _ = inv f + inv ((-1 : ℂ) • g) := by rw [inv_smul]
    _ = inv (f + (-1 : ℂ) • g) := by rw [inv_add]
    _ = inv (f - g) := by rw [neg_one_smul, sub_eq_add_neg]

/-- Reversal and inversion preserve Lemma 3.8's product control quantity. -/
private theorem prod_inv_reverse_eq (N : ℕ) (fs gs : List TestFn)
    (hlen : gs.length = fs.length) :
    ((((fs.reverse.map inv).zip (gs.reverse.map inv)).map
        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) =
      (((fs.zip gs).map
        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) := by
  have hzip :
      (fs.reverse.map inv).zip (gs.reverse.map inv) =
        (fs.zip gs).reverse.map (Prod.map inv inv) := by
    rw [List.zip_map, ← reverse_zip_eq fs gs hlen]
  have hfun : ∀ p ∈ (fs.zip gs).reverse,
      ((fun p => 1 + cnorm N p.1 + cnorm N p.2) ∘ Prod.map inv inv) p =
        1 + cnorm N p.1 + cnorm N p.2 := by
    intro p _
    show 1 + cnorm N (inv p.1) + cnorm N (inv p.2) = 1 + cnorm N p.1 + cnorm N p.2
    rw [cnorm_inv, cnorm_inv]
  rw [hzip, List.map_map, List.map_congr_left hfun, List.map_reverse, List.prod_reverse]

/-- Reversal and inversion preserve Lemma 3.8's maximum control quantity. -/
private theorem foldr_max_inv_reverse_eq (N : ℕ) (fs gs : List TestFn)
    (hlen : gs.length = fs.length) :
    List.foldr max 0
        (((fs.reverse.map inv).zip (gs.reverse.map inv)).map
          (fun p => cnorm N (p.1 - p.2))) =
      List.foldr max 0
        ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) := by
  have hzip :
      (fs.reverse.map inv).zip (gs.reverse.map inv) =
        (fs.zip gs).reverse.map (Prod.map inv inv) := by
    rw [List.zip_map, ← reverse_zip_eq fs gs hlen]
  have hfun : ∀ p ∈ (fs.zip gs).reverse,
      ((fun p => cnorm N (p.1 - p.2)) ∘ Prod.map inv inv) p = cnorm N (p.1 - p.2) := by
    intro p _
    show cnorm N (inv p.1 - inv p.2) = cnorm N (p.1 - p.2)
    rw [inv_sub_eq, cnorm_inv]
  rw [hzip, List.map_map, List.map_congr_left hfun, List.map_reverse]
  exact List.Perm.foldr_eq (lcomm := max_left_commutative) (List.reverse_perm _) 0

/-- [T26], Lemma 3.9: exponential control on the lower boundary of the strip. -/
theorem lemma_3_9_lower_bound (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (φs : List W.𝓕) (lam : W.data.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (k₁ k₂ : ℝ), 0 < N ∧ 0 < k₁ ∧ 0 < k₂ ∧
      ∀ (Fs Gs : List AnalyticTestFn), Fs.length = φs.length → Gs.length = φs.length →
        ∀ t : ℝ,
          ‖W.data.toWightmanStruct.compatApply lam
              (W.data.vtildeMap (t : ℂ)
                  (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
                W.data.vtildeMap (t : ℂ)
                  (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
            k₁ * Real.exp (k₂ * |t|) *
              (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
              ((List.foldr max 0
                (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                  (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
  obtain ⟨N, C, k₁, k₂, hN, hk₁, hk₂, _hCpos, hCle, hbound⟩ :=
    lemma_3_8 W h φs lam
  refine ⟨N, k₁, k₂, hN, hk₁, hk₂, ?_⟩
  intro Fs Gs hFs hGs t
  have hreal := hbound t (Fs.map xRestrictUpper) (Gs.map xRestrictUpper)
    (by simpa using hFs) (by simpa using hGs)
  have hvF := (vtilde_real W h t
    (W.data.toWightmanStruct.smearedProduct
      (φs.zip (Fs.map xRestrictUpper)))).2
  have hvG := (vtilde_real W h t
    (W.data.toWightmanStruct.smearedProduct
      (φs.zip (Gs.map xRestrictUpper)))).2
  rw [hvF, hvG]
  calc
    ‖W.data.toWightmanStruct.compatApply lam
        (W.data.boost t
            (W.data.toWightmanStruct.smearedProduct
              (φs.zip (Fs.map xRestrictUpper))) -
          W.data.boost t
            (W.data.toWightmanStruct.smearedProduct
              (φs.zip (Gs.map xRestrictUpper))))‖ ≤
        C t *
          (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := hreal
    _ ≤ (k₁ * Real.exp (k₂ * |t|)) *
          (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hCle t)
        (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

/-- [T26], Lemma 3.9: exponential control on the upper boundary of the strip. -/
theorem lemma_3_9_upper_bound (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (φs : List W.𝓕) (lam : W.data.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (k₁ k₂ : ℝ), 0 < N ∧ 0 < k₁ ∧ 0 < k₂ ∧
      ∀ (Fs Gs : List AnalyticTestFn), Fs.length = φs.length → Gs.length = φs.length →
        ∀ t : ℝ,
          ‖W.data.toWightmanStruct.compatApply lam
              (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
                  (W.data.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
                W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi)
                  (W.data.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
            k₁ * Real.exp (k₂ * |t|) *
              (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
              ((List.foldr max 0
                (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                  (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
  obtain ⟨N, C, k₁, k₂, hN, hk₁, hk₂, _hCpos, hCle, hbound⟩ :=
    lemma_3_8 W h φs.reverse lam
  refine ⟨N, k₁, k₂, hN, hk₁, hk₂, ?_⟩
  intro Fs Gs hFs hGs t
  let lF : List (W.𝓕 × AnalyticTestFn) := φs.zip Fs
  let lG : List (W.𝓕 × AnalyticTestFn) := φs.zip Gs
  let ΦF : W.𝓓 := W.data.toWightmanStruct.smearedProduct
    (lF.map (fun p => (p.1, xRestrictUpper p.2)))
  let ΦG : W.𝓓 := W.data.toWightmanStruct.smearedProduct
    (lG.map (fun p => (p.1, xRestrictUpper p.2)))
  let SF : W.𝓓 := W.data.toWightmanStruct.smearedProduct
    (lF.reverse.map (fun p => (p.1, inv (xRestrictUpper p.2))))
  let SG : W.𝓓 := W.data.toWightmanStruct.smearedProduct
    (lG.reverse.map (fun p => (p.1, inv (xRestrictUpper p.2))))
  let k : ℕ := (φs.map W.data.dim).sum

  have hupperF :
      φs.zip (Fs.map xRestrictUpper) =
        lF.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lF] using zip_xRestrictUpper_eq φs Fs
  have hupperG :
      φs.zip (Gs.map xRestrictUpper) =
        lG.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lG] using zip_xRestrictUpper_eq φs Gs
  have hdimF : (lF.map (fun p => W.data.dim p.1)).sum = k := by
    simpa only [lF, k] using
      sum_dim_zip_eq W.data.dim φs Fs hFs.symm.le
  have hdimG : (lG.map (fun p => W.data.dim p.1)).sum = k := by
    simpa only [lG, k] using
      sum_dim_zip_eq W.data.dim φs Gs hGs.symm.le

  have hipi : Complex.I * Real.pi ∈ strip (Complex.I * Real.pi) := by
    rw [mem_strip]
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.ofReal_re, zero_mul, mul_zero, zero_add, add_zero, one_mul]
    exact ⟨min_le_right 0 Real.pi, le_max_right 0 Real.pi⟩
  have hdomF := (lemma_3_7 W h lF (Complex.I * Real.pi) hipi).1
  have hdomG := (lemma_3_7 W h lG (Complex.I * Real.pi) hipi).1
  have hvalF : W.data.vtildeMap (Complex.I * Real.pi) ΦF =
      (-1 : ℂ) ^ k • SF := by
    simpa only [ΦF, SF, hdimF] using lemma_3_7_at_ipi W h lF
  have hvalG : W.data.vtildeMap (Complex.I * Real.pi) ΦG =
      (-1 : ℂ) ^ k • SG := by
    simpa only [ΦG, SG, hdimG] using lemma_3_7_at_ipi W h lG

  have htransF := WightmanData.vtilde_translation W.data h.actsRegularly
    (Complex.I * Real.pi) t ΦF
  have htransG := WightmanData.vtilde_translation W.data h.actsRegularly
    (Complex.I * Real.pi) t ΦG
  have hdomFt : W.data.VtildeDom (Complex.I * Real.pi + (t : ℂ)) ΦF :=
    htransF.2.1.mpr hdomF
  have hdomGt : W.data.VtildeDom (Complex.I * Real.pi + (t : ℂ)) ΦG :=
    htransG.2.1.mpr hdomG
  have hvF : W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦF =
      (-1 : ℂ) ^ k • W.data.boost t SF := by
    calc
      W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦF =
          W.data.vtildeMap (Complex.I * Real.pi + (t : ℂ)) ΦF := by rw [add_comm]
      _ = W.data.boost t (W.data.vtildeMap (Complex.I * Real.pi) ΦF) :=
        htransF.2.2.1 hdomFt hdomF
      _ = W.data.boost t ((-1 : ℂ) ^ k • SF) := by rw [hvalF]
      _ = (-1 : ℂ) ^ k • W.data.boost t SF :=
        (W.data.boost_linear t SF SF).2 ((-1 : ℂ) ^ k)
  have hvG : W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦG =
      (-1 : ℂ) ^ k • W.data.boost t SG := by
    calc
      W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦG =
          W.data.vtildeMap (Complex.I * Real.pi + (t : ℂ)) ΦG := by rw [add_comm]
      _ = W.data.boost t (W.data.vtildeMap (Complex.I * Real.pi) ΦG) :=
        htransG.2.2.1 hdomGt hdomG
      _ = W.data.boost t ((-1 : ℂ) ^ k • SG) := by rw [hvalG]
      _ = (-1 : ℂ) ^ k • W.data.boost t SG :=
        (W.data.boost_linear t SG SG).2 ((-1 : ℂ) ^ k)

  have hcompat (c : ℂ) (v w : W.𝓓) :
      W.data.toWightmanStruct.compatApply lam (c • v - c • w) =
        c * W.data.toWightmanStruct.compatApply lam (v - w) := by
    rw [← smul_sub,
      (W.data.toWightmanStruct.compatApply_linear lam (v - w) (v - w)).2 c,
      smul_eq_mul]
  have hnorm :
      ‖W.data.toWightmanStruct.compatApply lam
          (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦF -
            W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦG)‖ =
        ‖W.data.toWightmanStruct.compatApply lam
          (W.data.boost t SF - W.data.boost t SG)‖ := by
    rw [hvF, hvG, hcompat]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

  have hSF : SF = W.data.toWightmanStruct.smearedProduct
      (φs.reverse.zip (((Fs.map xRestrictUpper).reverse).map inv)) := by
    simpa only [SF, lF] using congrArg W.data.toWightmanStruct.smearedProduct
      (reverse_map_inv_restrict_eq_zip φs Fs hFs)
  have hSG : SG = W.data.toWightmanStruct.smearedProduct
      (φs.reverse.zip (((Gs.map xRestrictUpper).reverse).map inv)) := by
    simpa only [SG, lG] using congrArg W.data.toWightmanStruct.smearedProduct
      (reverse_map_inv_restrict_eq_zip φs Gs hGs)
  have hlenF : (((Fs.map xRestrictUpper).reverse).map inv).length =
      φs.reverse.length := by simp [hFs]
  have hlenG : (((Gs.map xRestrictUpper).reverse).map inv).length =
      φs.reverse.length := by simp [hGs]
  have hreal := hbound t
    (((Fs.map xRestrictUpper).reverse).map inv)
    (((Gs.map xRestrictUpper).reverse).map inv) hlenF hlenG
  rw [← hSF, ← hSG] at hreal
  have hFGlen : (Gs.map xRestrictUpper).length =
      (Fs.map xRestrictUpper).length := by simp [hFs, hGs]
  rw [prod_inv_reverse_eq N (Fs.map xRestrictUpper) (Gs.map xRestrictUpper) hFGlen,
    foldr_max_inv_reverse_eq N (Fs.map xRestrictUpper)
      (Gs.map xRestrictUpper) hFGlen] at hreal

  rw [hupperF, hupperG]
  change ‖W.data.toWightmanStruct.compatApply lam
      (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦF -
        W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦG)‖ ≤ _
  calc
    ‖W.data.toWightmanStruct.compatApply lam
        (W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦF -
          W.data.vtildeMap ((t : ℂ) + Complex.I * Real.pi) ΦG)‖ =
        ‖W.data.toWightmanStruct.compatApply lam
          (W.data.boost t SF - W.data.boost t SG)‖ := hnorm
    _ ≤ C t *
          (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := hreal
    _ ≤ (k₁ * Real.exp (k₂ * |t|)) *
          (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
            (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0
            (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
              (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hCle t)
        (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

end WightmanBundle

end

end MobiusCPT
