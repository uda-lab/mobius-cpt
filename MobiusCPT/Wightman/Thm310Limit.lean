import MobiusCPT.Wightman.Lemma37Continuation
import MobiusCPT.Wightman.Lemma39
import MobiusCPT.TestFunctions.AnalyticDensity

/-!
# [T26], Theorem 3.10: the limiting continuation family

This file constructs the analytic-continuation family for arbitrary upper-supported smooth test
functions.  Lemma 3.4 supplies analytic approximants and Lemma 3.9 makes their continued matrix
coefficients uniformly Cauchy on compact subsets of the closed strip.
-/

namespace MobiusCPT

open Set Filter

noncomputable section

namespace WightmanData

-- `𝓓 𝓕 : Type` (not `Type*`): Block U1's Lemma 3.9 input is only proved for `WightmanBundle`,
-- whose carriers are fixed at `Type`, so `lemma_3_9_data` below builds a `WightmanBundle` from
-- the ambient `W` and needs the universes to match exactly.
variable {𝓓 𝓕 : Type} [AddCommGroup 𝓓] [Module ℂ 𝓓]
variable {W : WightmanData Mob TestFn 𝓓 𝓕}

/-! ### The approximating families -/

/-- Apply the upper-support analytic approximation entrywise. -/
noncomputable def approxList (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) : List AnalyticTestFn :=
  l.pmap (fun p hp => approx p.2 hp n) hl

@[simp] theorem approxList_length (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) :
    (approxList l hl n).length = l.length := by
  simp [approxList]

/-- The smeared product formed from the `n`-th analytic approximants. -/
noncomputable def limApproxProduct (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) : 𝓓 :=
  W.smearedProduct
    ((l.map Prod.fst).zip ((approxList l hl n).map xRestrictUpper))

/-- The continued scalar matrix coefficient of the `n`-th approximating product. -/
noncomputable def limG (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat)
    (n : ℕ) (τ : ℂ) : ℂ :=
  W.compatApply lam (W.vtildeMap τ (limApproxProduct (W := W) l hl n))

private theorem zip_map_right_pair {α β γ : Type*} (xs : List α) (ys : List β)
    (f : β → γ) :
    (xs.zip ys).map (fun p => (p.1, f p.2)) = xs.zip (ys.map f) := by
  rw [List.zip_map_right]
  simp [Prod.map, Function.comp]

/-- On the strip, `limG` is the analytic-core complex-boost expression. -/
theorem limG_eq (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (n : ℕ)
    {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    limG l hl lam n τ =
      W.compatApply lam (W.smearedProduct
        (((l.map Prod.fst).zip (approxList l hl n)).map
          (fun p => (p.1, betaBoost (W.dim p.1) τ p.2)))) := by
  unfold limG limApproxProduct
  rw [← zip_map_right_pair]
  exact congrArg (W.compatApply lam)
    (WightmanData.lemma_3_7 hW
      ((l.map Prod.fst).zip (approxList l hl n)) τ hτ).2

/-- Every approximating coefficient is continuous on the closed strip. -/
theorem continuousOn_limG (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (n : ℕ) :
    ContinuousOn (limG l hl lam n) (strip (Complex.I * Real.pi)) := by
  let L := (l.map Prod.fst).zip (approxList l hl n)
  apply (continuousOn_compatApply_smearedProduct_betaBoost
    W.toWightmanStruct lam L).congr
  intro τ hτ
  exact limG_eq hW l hl lam n hτ

/-- Every approximating coefficient is holomorphic in the open strip. -/
theorem differentiableOn_limG (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (n : ℕ) :
    DifferentiableOn ℂ (limG l hl lam n)
      (interior (strip (Complex.I * Real.pi))) := by
  let L := (l.map Prod.fst).zip (approxList l hl n)
  apply (differentiableOn_compatApply_smearedProduct_betaBoost
    W.toWightmanStruct lam L).congr
  intro τ hτ
  exact limG_eq hW l hl lam n (interior_subset hτ)

/-! ### Compact-set and finite-list estimates -/

private theorem exists_exp_re_sq_bound {K : Set ℂ} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ K, Real.exp (τ.re ^ 2) ≤ R := by
  have hc : Continuous (fun τ : ℂ => Real.exp (τ.re ^ 2)) :=
    Real.continuous_exp.comp (Complex.continuous_re.pow 2)
  obtain ⟨R₀, hR₀⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨|R₀| + 1, by positivity, ?_⟩
  intro τ hτ
  have hle : Real.exp (τ.re ^ 2) ≤ R₀ :=
    hR₀ (mem_image_of_mem _ hτ)
  exact hle.trans (by linarith [le_abs_self R₀])

/-- Data-level form of Lemma 3.9.  The published theorem is bundled only for the Contract;
bundling an already supplied `W` is definitionally lossless. -/
private theorem lemma_3_9_data (hW : W.IsWightmanCFT) (φs : List 𝓕)
    (lam : W.toWightmanStruct.Compat) :
    ∃ (N : ℕ) (M : ℝ), 0 < N ∧ 0 < M ∧
      ∀ (Fs Gs : List AnalyticTestFn), Fs.length = φs.length →
        Gs.length = φs.length → ∀ τ ∈ strip (Complex.I * Real.pi),
          ‖W.compatApply lam
              (W.vtildeMap τ (W.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
                W.vtildeMap τ (W.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
            M * Real.exp (τ.re ^ 2) *
                (((((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                  (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
              ((List.foldr max 0
                (((Fs.map xRestrictUpper).zip (Gs.map xRestrictUpper)).map
                  (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
  let WB : WightmanBundle :=
    { 𝓓 := 𝓓
      domAddCommGroup := inferInstance
      domModule := inferInstance
      𝓕 := 𝓕
      data := W }
  simpa [WB] using WightmanBundle.lemma_3_9 WB hW φs lam

private noncomputable def approxValue (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) (i : Fin l.length) : TestFn :=
  xRestrictUpper (approx (l.get i).2 (hl (l.get i) (List.get_mem l i)) n)

private theorem tendsto_approxValue (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (i : Fin l.length) :
    Tendsto (fun n => approxValue l hl n i) atTop (nhds (l.get i).2) := by
  exact tendsto_xRestrictUpper_approx (hl (l.get i) (List.get_mem l i))

private theorem approxList_restrict_eq_ofFn (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (n : ℕ) :
    (approxList l hl n).map xRestrictUpper =
      List.ofFn (fun i : Fin l.length => approxValue l hl n i) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [approxList, approxValue]

private theorem approx_pair_zip_eq_ofFn (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (m n : ℕ) :
    ((approxList l hl m).map xRestrictUpper).zip
        ((approxList l hl n).map xRestrictUpper) =
      List.ofFn (fun i : Fin l.length =>
        (approxValue l hl m i, approxValue l hl n i)) := by
  rw [approxList_restrict_eq_ofFn, approxList_restrict_eq_ofFn]
  simpa using List.zip_eq_ofFn_get_of_length_eq
    (List.ofFn (fun i : Fin l.length => approxValue l hl m i))
    (List.ofFn (fun i : Fin l.length => approxValue l hl n i)) (by simp)

private theorem cnorm_neg (N : ℕ) (f : TestFn) : cnorm N (-f) = cnorm N f := by
  calc
    cnorm N (-f) = cnorm N ((-1 : ℂ) • f) := by simp
    _ = ‖(-1 : ℂ)‖₊ * cnorm N f := cnorm_smul N (-1) f
    _ = cnorm N f := by simp

private theorem tendsto_cnorm_approxValue (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (N : ℕ) (i : Fin l.length) :
    Tendsto (fun n => (cnorm N (approxValue l hl n i) : ℝ)) atTop
      (nhds (cnorm N (l.get i).2 : ℝ)) := by
  have h := ((withSeminorms_cnorm.continuous_seminorm N).tendsto (l.get i).2).comp
    (tendsto_approxValue l hl i)
  simpa only [cnorm_coe, Function.comp_def] using h

/-! ### Uniform Cauchy convergence and the pointwise limit -/

/-- Lemma 3.9 turns the finite family of Lemma 3.4 approximants into a uniformly Cauchy family
on every compact subset of the closed strip. -/
theorem uniformCauchySeqOn_limG (hW : W.IsWightmanCFT)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) {K : Set ℂ}
    (hK : K ⊆ strip (Complex.I * Real.pi)) (hKc : IsCompact K) :
    UniformCauchySeqOn (limG l hl lam) atTop K := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, M, _hN, hM, h39⟩ := lemma_3_9_data hW (l.map Prod.fst) lam
  obtain ⟨R, hR, hRbound⟩ := exists_exp_re_sq_bound hKc
  choose C hC using fun i : Fin l.length =>
    (tendsto_cnorm_approxValue l hl N i).bddAbove_range
  have hCbound (i : Fin l.length) (n : ℕ) :
      (cnorm N (approxValue l hl n i) : ℝ) ≤ C i :=
    hC i (Set.mem_range_self n)
  have hCnonneg (i : Fin l.length) : 0 ≤ C i :=
    (NNReal.coe_nonneg (cnorm N (approxValue l hl 0 i))).trans (hCbound i 0)
  let B : ℝ := ∏ i : Fin l.length, (1 + C i + C i)
  have hB : 0 < B := by
    dsimp [B]
    exact Finset.prod_pos fun i _ => by linarith [hCnonneg i]
  let δ : ℝ := ε / (M * R * B)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have herr (i : Fin l.length) :
      Tendsto (fun n => (cnorm N (approxValue l hl n i - (l.get i).2) : ℝ))
        atTop (nhds 0) :=
    (tendsto_iff_cnorm (fun n => approxValue l hl n i) (l.get i).2).mp
      (tendsto_approxValue l hl i) N
  choose q hq using fun i : Fin l.length => eventually_atTop.mp
    ((herr i).eventually (eventually_lt_nhds (by positivity : 0 < δ / 4)))
  let n₀ : ℕ := Finset.univ.sup q
  refine ⟨n₀, fun m hm n hn τ hτ => ?_⟩
  have hqle (i : Fin l.length) : q i ≤ n₀ := by
    exact Finset.le_sup (f := q) (Finset.mem_univ i)
  have hpair (i : Fin l.length) :
      (cnorm N (approxValue l hl m i - approxValue l hl n i) : ℝ) < δ / 2 := by
    have hm' := hq i m ((hqle i).trans hm)
    have hn' := hq i n ((hqle i).trans hn)
    have hadd := cnorm_add_le N
      (approxValue l hl m i - (l.get i).2)
      ((l.get i).2 - approxValue l hl n i)
    have hneg : cnorm N ((l.get i).2 - approxValue l hl n i) =
        cnorm N (approxValue l hl n i - (l.get i).2) := by
      rw [show (l.get i).2 - approxValue l hl n i =
        -(approxValue l hl n i - (l.get i).2) by abel, cnorm_neg]
    calc
      (cnorm N (approxValue l hl m i - approxValue l hl n i) : ℝ) ≤
          (cnorm N (approxValue l hl m i - (l.get i).2) : ℝ) +
            (cnorm N ((l.get i).2 - approxValue l hl n i) : ℝ) := by
        convert NNReal.coe_le_coe.mpr hadd using 1 <;> simp <;> abel
      _ = (cnorm N (approxValue l hl m i - (l.get i).2) : ℝ) +
            (cnorm N (approxValue l hl n i - (l.get i).2) : ℝ) := by rw [hneg]
      _ < δ / 2 := by linarith
  have hzip := approx_pair_zip_eq_ofFn l hl m n
  have hprod :
      ((((((approxList l hl m).map xRestrictUpper).zip
        ((approxList l hl n).map xRestrictUpper)).map
          (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) ≤ B := by
    rw [hzip, List.map_ofFn, List.prod_ofFn, NNReal.coe_prod]
    dsimp [B]
    apply Finset.prod_le_prod
    · intro i _
      positivity
    · intro i _
      exact add_le_add (add_le_add le_rfl (hCbound i m)) (hCbound i n)
  have hmax :
      ((List.foldr max 0
        ((((approxList l hl m).map xRestrictUpper).zip
          ((approxList l hl n).map xRestrictUpper)).map
            (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) < δ := by
    rw [hzip, List.map_ofFn]
    have hmaxNN :
        List.foldr max 0
            (List.ofFn fun i : Fin l.length =>
              cnorm N (approxValue l hl m i - approxValue l hl n i)) ≤
          (⟨δ / 2, by positivity⟩ : NNReal) := by
      apply List.max_le_of_forall_le
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact NNReal.coe_le_coe.mp (le_of_lt (hpair i))
    exact lt_of_le_of_lt (NNReal.coe_le_coe.mpr hmaxNN) (by
      show (δ / 2 : ℝ) < δ
      linarith)
  have h39mn := h39 (approxList l hl m) (approxList l hl n)
    (by simp) (by simp) τ (hK hτ)
  rw [dist_eq_norm]
  calc
    ‖limG l hl lam m τ - limG l hl lam n τ‖ ≤
        M * Real.exp (τ.re ^ 2) *
          ((((((approxList l hl m).map xRestrictUpper).zip
            ((approxList l hl n).map xRestrictUpper)).map
              (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
          ((List.foldr max 0
            ((((approxList l hl m).map xRestrictUpper).zip
              ((approxList l hl n).map xRestrictUpper)).map
                (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      simpa [limG, limApproxProduct, WightmanStruct.compatApply, map_sub] using h39mn
    _ ≤ M * R * B *
          ((List.foldr max 0
            ((((approxList l hl m).map xRestrictUpper).zip
              ((approxList l hl n).map xRestrictUpper)).map
                (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
      gcongr
      exact hRbound τ hτ
    _ < M * R * B * δ := mul_lt_mul_of_pos_left hmax (by positivity)
    _ = ε := by
      dsimp [δ]
      field_simp [ne_of_gt hM, ne_of_gt hR, ne_of_gt hB]

private theorem cauchySeq_limG (hW : W.IsWightmanCFT)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) {τ : ℂ}
    (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    CauchySeq (fun n => limG l hl lam n τ) := by
  have h := uniformCauchySeqOn_limG hW l hl lam
    (K := {τ}) (Set.singleton_subset_iff.mpr hτ) isCompact_singleton
  exact h.cauchySeq (mem_singleton τ)

/-- Pointwise limit of the analytic approximating family. -/
noncomputable def limitG (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) (τ : ℂ) : ℂ :=
  limUnder atTop (fun n => limG l hl lam n τ)

/-- The approximating coefficients converge pointwise everywhere on the closed strip. -/
theorem tendsto_limG (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat)
    {τ : ℂ} (hτ : τ ∈ strip (Complex.I * Real.pi)) :
    Tendsto (fun n => limG l hl lam n τ) atTop
      (nhds (limitG hW l hl lam τ)) := by
  exact (cauchySeq_limG hW l hl lam hτ).tendsto_limUnder

/-! ### Holomorphy of the limit -/

/-- The approximants converge locally uniformly to `limitG` in the open strip. -/
theorem tendstoLocallyUniformlyOn_limG (hW : W.IsWightmanCFT)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) :
    TendstoLocallyUniformlyOn (limG l hl lam) (limitG hW l hl lam) atTop
      (interior (strip (Complex.I * Real.pi))) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_interior]
  intro K hKU hKc
  have hKC : K ⊆ strip (Complex.I * Real.pi) := hKU.trans interior_subset
  exact (uniformCauchySeqOn_limG hW l hl lam hKC hKc).tendstoUniformlyOn_of_tendsto
    (fun τ hτ => tendsto_limG hW l hl lam (hKC hτ))

/-- The limiting continuation family is holomorphic in the open strip. -/
theorem differentiableOn_limitG (hW : W.IsWightmanCFT)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) :
    DifferentiableOn ℂ (limitG hW l hl lam)
      (interior (strip (Complex.I * Real.pi))) := by
  apply (tendstoLocallyUniformlyOn_limG hW l hl lam).differentiableOn
  · exact Eventually.of_forall fun n => differentiableOn_limG hW l hl lam n
  · exact isOpen_interior

end WightmanData

end

end MobiusCPT
