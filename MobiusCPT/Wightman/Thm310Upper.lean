import MobiusCPT.Wightman.Thm310LimitCont
import MobiusCPT.Wightman.Lemma37
import MobiusCPT.Wightman.Lemma38
import MobiusCPT.Wightman.VtildeReal

/-!
# [T26], Theorem 3.10: boundary values of the limiting continuation

The limiting family constructed from analytic approximants has the expected boost orbit on the
real boundary and the reversed, inverted product on the upper boundary.  These identifications
turn the limiting family into the continuation required by [T26], Theorem 3.10(ii).
-/

namespace MobiusCPT

open Set Filter

noncomputable section

/-- Inversion is continuous in the smooth test-function topology. -/
theorem continuous_inv : Continuous inv := by
  change Continuous (invₗ : TestFn → TestFn)
  refine WithSeminorms.continuous_of_isBounded withSeminorms_cnorm
    withSeminorms_cnorm invₗ ?_
  apply Seminorm.IsBounded.of_real
  intro N
  refine ⟨{N}, 1, fun f => ?_⟩
  change cnormSeminorm N (inv f) ≤
    1 * (({N} : Finset ℕ).sup cnormSeminorm) f
  simp only [Finset.sup_singleton, one_mul]
  have heq : cnormSeminorm N (inv f) = cnormSeminorm N f := by
    calc
      cnormSeminorm N (inv f) = (cnorm N (inv f) : ℝ) :=
        (cnorm_coe N (inv f)).symm
      _ = (cnorm N f : ℝ) := by rw [cnorm_inv]
      _ = cnormSeminorm N f := cnorm_coe N f
  exact heq.le

namespace WightmanData

-- The carriers are deliberately `Type`, since the real-axis bridge packages them as a bundle.
variable {D Field : Type} [AddCommGroup D] [Module ℂ D]
variable {W : WightmanData Mob TestFn D Field}

/-- Data-level access to the bundle-only real-parameter theorem. -/
private theorem vtilde_real_data (hW : W.IsWightmanCFT) (t : ℝ) (Φ : D) :
    W.VtildeDom (t : ℂ) Φ ∧ W.vtildeMap (t : ℂ) Φ = W.boost t Φ := by
  let WB : WightmanBundle :=
    { 𝓓 := D
      domAddCommGroup := inferInstance
      domModule := inferInstance
      𝓕 := Field
      data := W }
  simpa [WB] using WightmanBundle.vtilde_real WB hW t Φ

private noncomputable def approxValue (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) (i : Fin l.length) : TestFn :=
  xRestrictUpper (approx (l.get i).2 (hl (l.get i) (List.get_mem l i)) n)

private theorem tendsto_approxValue (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (i : Fin l.length) :
    Tendsto (fun n => approxValue l hl n i) atTop (nhds (l.get i).2) := by
  exact tendsto_xRestrictUpper_approx (hl (l.get i) (List.get_mem l i))

private theorem approxList_restrict_eq_ofFn (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) :
    (approxList l hl n).map xRestrictUpper =
      List.ofFn (fun i : Fin l.length => approxValue l hl n i) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [approxList, approxValue]

private theorem zip_fst_snd (l : List (Field × TestFn)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  simpa [List.unzip_eq_map] using List.zip_unzip l

private theorem reverse_zip_eq {α β : Type*} (l₁ : List α) (l₂ : List β)
    (hlen : l₂.length = l₁.length) :
    (l₁.zip l₂).reverse = l₁.reverse.zip l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil =>
      have : l₂ = [] := List.length_eq_zero_iff.mp hlen
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

private theorem reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn] at hi₁ hi₂ ⊢
    congr 1
    apply Fin.ext
    simp only [Fin.rev, List.length_ofFn]
    omega

private theorem zip_map_right_pair {α β γ : Type*} (xs : List α) (ys : List β)
    (f : β → γ) :
    (xs.zip ys).map (fun p => (p.1, f p.2)) = xs.zip (ys.map f) := by
  rw [List.zip_map_right]
  simp [Prod.map, Function.comp]

private theorem reverse_map_inv_restrict_eq_zip {α : Type*} (l : List α)
    (Fs : List AnalyticTestFn) (hlen : Fs.length = l.length) :
    (l.zip Fs).reverse.map (fun p => (p.1, inv (xRestrictUpper p.2))) =
      l.reverse.zip (((Fs.map xRestrictUpper).reverse).map inv) := by
  rw [reverse_zip_eq l Fs hlen]
  rw [← List.map_reverse, List.map_map, List.zip_map_right]
  rfl

private theorem sum_dim_zip_eq {α : Type*} (dim' : Field → ℕ) (l : List Field) (r : List α)
    (hlen : l.length ≤ r.length) :
    ((l.zip r).map (fun p => dim' p.1)).sum = (l.map dim').sum := by
  rw [show (l.zip r).map (fun p => dim' p.1) =
      ((l.zip r).map Prod.fst).map dim' by rw [List.map_map]; rfl,
    List.map_fst_zip hlen]

/-- Lemma 3.8 converts entrywise convergence of a fixed finite list into convergence of its
boosted smeared matrix coefficient. -/
private theorem tendsto_boost_smearedProduct_ofFn (hW : W.IsWightmanCFT)
    (k : ℕ) (φs : List Field) (hk : φs.length = k)
    (lam : W.toWightmanStruct.Compat) (t : ℝ)
    (F : ℕ → Fin k → TestFn) (g : Fin k → TestFn)
    (hF : ∀ i, Tendsto (fun n => F n i) atTop (nhds (g i))) :
    Tendsto (fun n => W.compatApply lam
      (W.boost t (W.smearedProduct (φs.zip (List.ofFn (F n)))))) atTop
      (nhds (W.compatApply lam
        (W.boost t (W.smearedProduct (φs.zip (List.ofFn g)))))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, C, _k₁, _k₂, _hN, _hk₁, _hk₂, hC, _hCle, hbound⟩ :=
    W.lemma_3_8 hW φs lam
  have hcnorm (i : Fin k) :
      Tendsto (fun n => (cnorm N (F n i) : ℝ)) atTop (nhds (cnorm N (g i) : ℝ)) := by
    exact (((withSeminorms_cnorm.continuous_seminorm N).tendsto (g i)).comp (hF i))
  choose A hA using fun i : Fin k => (hcnorm i).bddAbove_range
  have hAbound (i : Fin k) (n : ℕ) :
      (cnorm N (F n i) : ℝ) ≤ A i := hA i (Set.mem_range_self n)
  have hAnonneg (i : Fin k) : 0 ≤ A i :=
    (NNReal.coe_nonneg (cnorm N (F 0 i))).trans (hAbound i 0)
  let B : ℝ := ∏ i : Fin k, (1 + A i + (cnorm N (g i) : ℝ))
  have hB : 0 < B := by
    dsimp [B]
    exact Finset.prod_pos fun i _ => by
      have := NNReal.coe_nonneg (cnorm N (g i))
      linarith [hAnonneg i]
  let δ : ℝ := ε / (C t * B)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hε (mul_pos (hC t) hB)
  have hδ2 : 0 < δ / 2 := by linarith
  have herr (i : Fin k) :
      Tendsto (fun n => (cnorm N (F n i - g i) : ℝ)) atTop (nhds 0) :=
    (tendsto_iff_cnorm (fun n => F n i) (g i)).mp (hF i) N
  choose q hq using fun i : Fin k => eventually_atTop.mp
    ((herr i).eventually (eventually_lt_nhds hδ2))
  let n₀ : ℕ := Finset.univ.sup q
  refine ⟨n₀, fun n hn => ?_⟩
  have hsmall (i : Fin k) :
      (cnorm N (F n i - g i) : ℝ) < δ / 2 :=
    hq i n ((Finset.le_sup (f := q) (Finset.mem_univ i)).trans hn)
  have hzip : (List.ofFn (F n)).zip (List.ofFn g) =
      List.ofFn (fun i : Fin k => (F n i, g i)) := by
    simpa using List.zip_eq_ofFn_get_of_length_eq (List.ofFn (F n)) (List.ofFn g) (by simp)
  have hprod :
      (((((List.ofFn (F n)).zip (List.ofFn g)).map
        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) ≤ B := by
    rw [hzip, List.map_ofFn, List.prod_ofFn, NNReal.coe_prod]
    dsimp [B]
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      exact add_le_add (add_le_add le_rfl (hAbound i n)) le_rfl
  have hmax :
      ((List.foldr max 0 (((List.ofFn (F n)).zip (List.ofFn g)).map
        (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) < δ := by
    rw [hzip, List.map_ofFn]
    have hmaxNN :
        List.foldr max 0 (List.ofFn fun i : Fin k => cnorm N (F n i - g i)) ≤
          (⟨δ / 2, hδ2.le⟩ : NNReal) := by
      apply List.max_le_of_forall_le
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact NNReal.coe_le_coe.mp (le_of_lt (hsmall i))
    exact lt_of_le_of_lt (NNReal.coe_le_coe.mpr hmaxNN) (by
      show (δ / 2 : ℝ) < δ
      linarith)
  have hb := hbound t (List.ofFn (F n)) (List.ofFn g)
    (by simpa [hk]) (by simpa [hk])
  rw [dist_eq_norm]
  calc
    ‖W.compatApply lam (W.boost t (W.smearedProduct (φs.zip (List.ofFn (F n))))) -
        W.compatApply lam (W.boost t (W.smearedProduct (φs.zip (List.ofFn g))))‖ ≤
        C t *
          (((((List.ofFn (F n)).zip (List.ofFn g)).map
            (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0 (((List.ofFn (F n)).zip (List.ofFn g)).map
            (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      simpa [WightmanStruct.compatApply, map_sub] using hb
    _ ≤ C t * B *
          ((List.foldr max 0 (((List.ofFn (F n)).zip (List.ofFn g)).map
            (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      gcongr
      exact (hC t).le
    _ < C t * B * δ := mul_lt_mul_of_pos_left hmax (mul_pos (hC t) hB)
    _ = ε := by
      dsimp [δ]
      field_simp [ne_of_gt (hC t), ne_of_gt hB]

/-! ### The lower boundary -/

theorem tendsto_limG_ofReal (hW : W.IsWightmanCFT) (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (t : ℝ) :
    Tendsto (fun n => limG l hl lam n (t : ℂ)) atTop
      (nhds (W.compatApply lam (W.boost t (W.smearedProduct l)))) := by
  let F : ℕ → Fin l.length → TestFn := fun n i => approxValue l hl n i
  let g : Fin l.length → TestFn := fun i => (l.get i).2
  have hbase := tendsto_boost_smearedProduct_ofFn hW l.length (l.map Prod.fst) (by simp) lam t F g
    (fun i => tendsto_approxValue l hl i)
  have hpoint (n : ℕ) : limG l hl lam n (t : ℂ) =
      W.compatApply lam (W.boost t
        (W.smearedProduct ((l.map Prod.fst).zip (List.ofFn (F n))))) := by
    unfold limG limApproxProduct
    rw [(vtilde_real_data hW t _).2]
    simpa only [F] using congrArg
      (fun fs => W.compatApply lam (W.boost t (W.smearedProduct ((l.map Prod.fst).zip fs))))
      (approxList_restrict_eq_ofFn l hl n)
  have htarget : W.compatApply lam (W.boost t (W.smearedProduct l)) =
      W.compatApply lam (W.boost t
        (W.smearedProduct ((l.map Prod.fst).zip (List.ofFn g)))) := by
    have hg : List.ofFn g = l.map Prod.snd := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        simp [g]
    rw [hg, zip_fst_snd]
  simpa only [hpoint, htarget] using hbase

/-! ### The upper boundary -/

/-- The continuation partner in [T26], Theorem 3.10(ii). -/
noncomputable def upperLimitVector (l : List (Field × TestFn)) : D :=
  (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) •
    W.smearedProduct (l.reverse.map (fun p => (p.1, inv p.2)))

theorem tendsto_limG_ipi_add_ofReal (hW : W.IsWightmanCFT)
    (l : List (Field × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) (t : ℝ) :
    Tendsto (fun n => limG l hl lam n (Complex.I * Real.pi + (t : ℂ))) atTop
      (nhds (W.compatApply lam (W.boost t (upperLimitVector (W := W) l)))) := by
  let φs := (l.map Prod.fst).reverse
  let F : ℕ → Fin l.length → TestFn :=
    fun n i => inv (approxValue l hl n i.rev)
  let g : Fin l.length → TestFn := fun i => inv (l.get i.rev).2
  let S : ℕ → D := fun n => W.smearedProduct (φs.zip (List.ofFn (F n)))
  let S₀ : D := W.smearedProduct (φs.zip (List.ofFn g))
  let c : ℂ := (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum)
  have hF (i : Fin l.length) :
      Tendsto (fun n => F n i) atTop (nhds (g i)) := by
    exact (continuous_inv.tendsto (l.get i.rev).2).comp (tendsto_approxValue l hl i.rev)
  have hbase : Tendsto (fun n => W.compatApply lam (W.boost t (S n))) atTop
      (nhds (W.compatApply lam (W.boost t S₀))) := by
    exact tendsto_boost_smearedProduct_ofFn hW l.length φs (by simp [φs]) lam t F g hF
  let L : ℕ → List (Field × AnalyticTestFn) :=
    fun n => (l.map Prod.fst).zip (approxList l hl n)
  have hrevApprox (n : ℕ) :
      ((approxList l hl n).map xRestrictUpper).reverse.map inv = List.ofFn (F n) := by
    rw [approxList_restrict_eq_ofFn, reverse_ofFn, List.map_ofFn]
    rfl
  have hLn (n : ℕ) :
      (L n).reverse.map (fun p => (p.1, inv (xRestrictUpper p.2))) =
        φs.zip (List.ofFn (F n)) := by
    dsimp only [L, φs]
    rw [reverse_map_inv_restrict_eq_zip _ _ (by simp), hrevApprox]
  have hS₀ : S₀ = W.smearedProduct
      (l.reverse.map (fun p => (p.1, inv p.2))) := by
    have hg : List.ofFn g = (l.map Prod.snd).reverse.map inv := by
      rw [show l.map Prod.snd = List.ofFn (fun i : Fin l.length => (l.get i).2) by
        apply List.ext_getElem <;> simp]
      rw [reverse_ofFn, List.map_ofFn]
      rfl
    dsimp only [S₀, φs]
    rw [hg, ← zip_map_right_pair, ← reverse_zip_eq _ _ (by simp), zip_fst_snd]
  have hshape (n : ℕ) : limApproxProduct (W := W) l hl n =
      W.smearedProduct ((L n).map (fun p => (p.1, xRestrictUpper p.2))) := by
    unfold limApproxProduct
    dsimp only [L]
    rw [List.zip_map_right]
    rfl
  have hdim (n : ℕ) :
      (((L n).map (fun p => W.dim p.1)).sum) =
        (l.map (fun p => W.dim p.1)).sum := by
    dsimp only [L]
    simpa only [List.map_map, Function.comp_def] using
      sum_dim_zip_eq W.dim (l.map Prod.fst) (approxList l hl n) (by simp)
  have hpoint (n : ℕ) :
      limG l hl lam n (Complex.I * Real.pi + (t : ℂ)) =
        c * W.compatApply lam (W.boost t (S n)) := by
    have hdomt : W.VtildeDom (Complex.I * Real.pi + (t : ℂ))
        (limApproxProduct (W := W) l hl n) := by
      rw [hshape]
      exact (W.lemma_3_7 hW (L n) _
        (add_ofReal_mem_strip (Complex.I * Real.pi) t)).1
    have hdom0 : W.VtildeDom (Complex.I * Real.pi)
        (limApproxProduct (W := W) l hl n) := by
      rw [hshape]
      exact (W.lemma_3_7 hW (L n) _ I_mul_pi_mem_strip).1
    have hv : W.vtildeMap (Complex.I * Real.pi + (t : ℂ))
        (limApproxProduct (W := W) l hl n) = c • W.boost t (S n) := by
      calc
        W.vtildeMap (Complex.I * Real.pi + (t : ℂ))
            (limApproxProduct (W := W) l hl n) =
            W.boost t (W.vtildeMap (Complex.I * Real.pi)
              (limApproxProduct (W := W) l hl n)) :=
          (W.vtilde_translation hW.actsRegularly (Complex.I * Real.pi) t _).2.2.1
            hdomt hdom0
        _ = W.boost t (c • S n) := by
          rw [hshape, W.lemma_3_7_at_ipi hW (L n), hdim, hLn]
        _ = c • W.boost t (S n) := (W.boost_linear t (S n) (S n)).2 c
    unfold limG
    rw [hv, (W.toWightmanStruct.compatApply_linear lam
      (W.boost t (S n)) (W.boost t (S n))).2 c, smul_eq_mul]
  have hscaled : Tendsto (fun n => c * W.compatApply lam (W.boost t (S n))) atTop
      (nhds (c * W.compatApply lam (W.boost t S₀))) :=
    tendsto_const_nhds.mul hbase
  have htarget : W.compatApply lam (W.boost t (upperLimitVector (W := W) l)) =
      c * W.compatApply lam (W.boost t S₀) := by
    have heq : upperLimitVector (W := W) l = c • S₀ := by
      rw [hS₀]
      rfl
    rw [heq, (W.boost_linear t S₀ S₀).2 c,
      (W.toWightmanStruct.compatApply_linear lam (W.boost t S₀) (W.boost t S₀)).2 c, smul_eq_mul]
  simpa only [hpoint, htarget] using hscaled

/-! ### Identification and packaging -/

theorem limitG_ofReal (hW : W.IsWightmanCFT) (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (t : ℝ) :
    limitG hW l hl lam (t : ℂ) =
      W.compatApply lam (W.boost t (W.smearedProduct l)) :=
  tendsto_nhds_unique
    (tendsto_limG hW l hl lam (ofReal_mem_strip (Complex.I * Real.pi) t))
    (tendsto_limG_ofReal hW l hl lam t)

theorem limitG_ipi_add_ofReal (hW : W.IsWightmanCFT)
    (l : List (Field × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) (t : ℝ) :
    limitG hW l hl lam (Complex.I * Real.pi + (t : ℂ)) =
      W.compatApply lam (W.boost t (upperLimitVector (W := W) l)) :=
  tendsto_nhds_unique
    (tendsto_limG hW l hl lam (add_ofReal_mem_strip (Complex.I * Real.pi) t))
    (tendsto_limG_ipi_add_ofReal hW l hl lam t)

theorem isBoostContinuation_limitG (hW : W.IsWightmanCFT)
    (l : List (Field × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2) :
    W.IsBoostContinuation (Complex.I * Real.pi) (W.smearedProduct l) (upperLimitVector (W := W) l)
      (fun lam => limitG hW l hl lam) := by
  intro lam
  exact ⟨continuousOn_limitG hW l hl lam, differentiableOn_limitG hW l hl lam,
    limitG_ofReal hW l hl lam, limitG_ipi_add_ofReal hW l hl lam⟩

theorem thm_3_10_ii_core (hW : W.IsWightmanCFT) (l : List (Field × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) :
    W.VtildeDom (Complex.I * Real.pi) (W.smearedProduct l) ∧
      W.vtildeMap (Complex.I * Real.pi) (W.smearedProduct l) = upperLimitVector (W := W) l :=
  W.vtildeDom_and_vtildeMap_eq hW.actsRegularly (isBoostContinuation_limitG hW l hl)

end WightmanData

end

end MobiusCPT
