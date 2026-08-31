import MobiusCPT.Wightman.Lemma37Continuation
import MobiusCPT.Wightman.VtildeLaws
import MobiusCPT.Wightman.Lemma38
import MobiusCPT.Mobius.ComplexBetaCont
import MobiusCPT.TestFunctions.CNorm

/-!
# [T26], Lemma 3.9: the interior growth estimate

This module supplies the exponential growth estimate on the closed strip.  Compactness of the
imaginary-parameter interval gives a uniform `C^N` bound for every complex-boosted test
function.  The real part of the parameter is then separated by the translation law for
`vtildeMap`, and the real-boost estimate of Lemma 3.8 applies.
-/

namespace MobiusCPT

open Set

noncomputable section

namespace WightmanData

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- Zipping after restricting the right list is the list shape used by `lemma_3_7`. -/
private theorem zip_xRestrictUpper_eq (φs : List 𝓕) (Fs : List AnalyticTestFn) :
    φs.zip (Fs.map xRestrictUpper) =
      (φs.zip Fs).map (fun p => (p.1, xRestrictUpper p.2)) := by
  rw [List.zip_map_right]
  rfl

/-- Repackage the pair list produced by `lemma_3_7` as a zip over the original field list. -/
private theorem betaBoost_pairs_eq_zip (dim' : 𝓕 → ℕ) (φs : List 𝓕)
    (Fs : List AnalyticTestFn) (τ : ℂ) (hlen : φs.length ≤ Fs.length) :
    (φs.zip Fs).map (fun p => (p.1, betaBoost (dim' p.1) τ p.2)) =
      φs.zip ((φs.zip Fs).map (fun p => betaBoost (dim' p.1) τ p.2)) := by
  rw [← List.zip_map']
  rw [List.map_fst_zip hlen]

/-- On the compact imaginary-parameter interval, one complex-boosted test function has a
uniform `C^N` bound. -/
private theorem cnorm_betaBoost_uniform_single (d : ℕ) (F : AnalyticTestFn) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      (cnorm N (betaBoost d (Complex.I * s) F) : ℝ) ≤ K := by
  have hmaps : Set.MapsTo (fun s : ℝ => Complex.I * (s : ℂ))
      (Set.Icc (0 : ℝ) Real.pi) (strip (Complex.I * Real.pi)) := by
    intro s hs
    rw [mem_strip]
    simpa [Complex.mul_im, min_eq_left Real.pi_pos.le,
      max_eq_right Real.pi_pos.le] using hs
  have hline : Continuous (fun s : ℝ => Complex.I * (s : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hboost : ContinuousOn (fun s : ℝ => betaBoost d (Complex.I * s) F)
      (Set.Icc (0 : ℝ) Real.pi) :=
    (continuousOn_betaBoost d F).comp hline.continuousOn hmaps
  have hseminorm : ContinuousOn
      (fun s : ℝ => cnormSeminorm N (betaBoost d (Complex.I * s) F))
      (Set.Icc (0 : ℝ) Real.pi) :=
    (withSeminorms_cnorm.continuous_seminorm N).comp_continuousOn hboost
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hseminorm
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro s hs
  rw [cnorm_coe]
  calc
    cnormSeminorm N (betaBoost d (Complex.I * s) F) ≤
        ‖cnormSeminorm N (betaBoost d (Complex.I * s) F)‖ := Real.le_norm_self _
    _ ≤ C := hC s hs
    _ ≤ max C 0 := le_max_left C 0

/-- A finite list of complex-boosted test functions admits one uniform `C^N` bound. -/
private theorem cnorm_betaBoost_uniform_list {𝓕' : Type*} (dim' : 𝓕' → ℕ)
    (l : List (𝓕' × AnalyticTestFn)) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc (0 : ℝ) Real.pi, ∀ p ∈ l,
      (cnorm N (betaBoost (dim' p.1) (Complex.I * s) p.2) : ℝ) ≤ K := by
  induction l with
  | nil =>
      exact ⟨0, le_rfl, by simp⟩
  | cons p rest ih =>
      obtain ⟨Kp, hKp, hp⟩ :=
        cnorm_betaBoost_uniform_single (dim' p.1) p.2 N
      obtain ⟨Kr, hKr, hr⟩ := ih
      refine ⟨max Kp Kr, hKp.trans (le_max_left Kp Kr), ?_⟩
      intro s hs q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hp s hs).trans (le_max_left Kp Kr)
      · exact (hr s hs q hq).trans (le_max_right Kp Kr)

/-- Subadditivity of `cnorm`, in the real-coercion form used below. -/
private theorem cnorm_sub_le (N : ℕ) (a b : TestFn) :
    (cnorm N (a - b) : ℝ) ≤ (cnorm N a : ℝ) + (cnorm N b : ℝ) := by
  have hnegb : cnorm N (-b) = cnorm N b := by
    simpa only [neg_one_smul, nnnorm_neg, nnnorm_one, one_mul] using
      (cnorm_smul N (-1 : ℂ) b)
  calc
    (cnorm N (a - b) : ℝ) = (cnorm N (a + -b) : ℝ) := by rw [sub_eq_add_neg]
    _ ≤ (cnorm N a : ℝ) + (cnorm N (-b) : ℝ) := by
      exact_mod_cast cnorm_add_le N a (-b)
    _ = (cnorm N a : ℝ) + (cnorm N b : ℝ) := by rw [hnegb]

/-- A pointwise `C^N` bound controls the product appearing in `lemma_3_8`. -/
private theorem prod_one_add_cnorm_le (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (fs gs : List TestFn) (hlen : gs.length = fs.length)
    (hfs : ∀ f ∈ fs, (cnorm N f : ℝ) ≤ K)
    (hgs : ∀ g ∈ gs, (cnorm N g : ℝ) ≤ K) :
    ((((fs.zip gs).map (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) ≤
      (1 + 2 * K) ^ fs.length := by
  induction fs generalizing gs with
  | nil =>
      have hgsnil : gs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst gs
      simp
  | cons f fs ih =>
      cases gs with
      | nil => simp at hlen
      | cons g gs =>
          have hlen' : gs.length = fs.length := Nat.succ.inj hlen
          have hfK : (cnorm N f : ℝ) ≤ K := hfs f (by simp)
          have hgK : (cnorm N g : ℝ) ≤ K := hgs g (by simp)
          have hfactor :
              (((1 + cnorm N f + cnorm N g : NNReal) : ℝ)) ≤ 1 + 2 * K := by
            push_cast
            linarith
          have hbase : 0 ≤ 1 + 2 * K := by linarith
          have htail := ih gs hlen'
            (fun q hq => hfs q (List.mem_cons_of_mem f hq))
            (fun q hq => hgs q (List.mem_cons_of_mem g hq))
          calc
            (((((f :: fs).zip (g :: gs)).map
                (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) =
                (((1 + cnorm N f + cnorm N g : NNReal) : ℝ)) *
                  ((((fs.zip gs).map
                    (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) := by
              simp only [List.zip_cons_cons, List.map_cons, List.prod_cons, NNReal.coe_mul]
            _ ≤ (1 + 2 * K) * (1 + 2 * K) ^ fs.length :=
              mul_le_mul hfactor htail (NNReal.coe_nonneg _) hbase
            _ = (1 + 2 * K) ^ (f :: fs).length := by
              rw [List.length_cons, pow_succ]
              ring

/-- A pointwise `C^N` bound controls the folded maximum appearing in `lemma_3_8`. -/
private theorem foldr_max_cnorm_sub_le (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (fs gs : List TestFn)
    (hfs : ∀ f ∈ fs, (cnorm N f : ℝ) ≤ K)
    (hgs : ∀ g ∈ gs, (cnorm N g : ℝ) ≤ K) :
    ((List.foldr max 0
      ((fs.zip gs).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) ≤ 2 * K := by
  induction fs generalizing gs with
  | nil => simp [hK]
  | cons f fs ih =>
      cases gs with
      | nil => simp [hK]
      | cons g gs =>
          have hfK : (cnorm N f : ℝ) ≤ K := hfs f (by simp)
          have hgK : (cnorm N g : ℝ) ≤ K := hgs g (by simp)
          have hhead : (cnorm N (f - g) : ℝ) ≤ 2 * K :=
            (cnorm_sub_le N f g).trans (by linarith)
          have htail := ih gs
            (fun q hq => hfs q (List.mem_cons_of_mem f hq))
            (fun q hq => hgs q (List.mem_cons_of_mem g hq))
          calc
            ((List.foldr max 0
                (((f :: fs).zip (g :: gs)).map
                  (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) =
                max (cnorm N (f - g) : ℝ)
                  ((List.foldr max 0
                    ((fs.zip gs).map
                      (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) := by
              simp only [List.zip_cons_cons, List.map_cons, List.foldr_cons, NNReal.coe_max]
            _ ≤ 2 * K := max_le hhead htail

/-- [T26], Lemma 3.9, interior-growth input: the continued-boost difference grows at most
exponentially in the real part throughout the closed strip. -/
theorem lemma_3_9_interior_growth {W : WightmanData Mob TestFn 𝓓 𝓕}
    (hW : W.IsWightmanCFT) (φs : List 𝓕) (lam : W.toWightmanStruct.Compat)
    (Fs Gs : List AnalyticTestFn) (hFs : Fs.length = φs.length)
    (hGs : Gs.length = φs.length) :
    ∃ A a : ℝ, ∀ τ ∈ strip (Complex.I * Real.pi),
      ‖W.toWightmanStruct.compatApply lam
          (W.vtildeMap τ
              (W.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
            W.vtildeMap τ
              (W.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))‖ ≤
        A * Real.exp (a * |τ.re|) := by
  let lF : List (𝓕 × AnalyticTestFn) := φs.zip Fs
  let lG : List (𝓕 × AnalyticTestFn) := φs.zip Gs
  let ΦF0 : 𝓓 := W.toWightmanStruct.smearedProduct
    (lF.map (fun p => (p.1, xRestrictUpper p.2)))
  let ΦG0 : 𝓓 := W.toWightmanStruct.smearedProduct
    (lG.map (fun p => (p.1, xRestrictUpper p.2)))
  have hupperF :
      φs.zip (Fs.map xRestrictUpper) =
        lF.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lF] using zip_xRestrictUpper_eq φs Fs
  have hupperG :
      φs.zip (Gs.map xRestrictUpper) =
        lG.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lG] using zip_xRestrictUpper_eq φs Gs
  have hlF : lF.length = φs.length := by
    simp [lF, List.length_zip, hFs]
  have hlG : lG.length = φs.length := by
    simp [lG, List.length_zip, hGs]

  obtain ⟨N, C, k₁, k₂, _hN, hk₁, _hk₂, _hCpos, hCle, hbound⟩ :=
    lemma_3_8 W hW φs lam
  obtain ⟨KF, hKF0, hKF⟩ := cnorm_betaBoost_uniform_list W.dim lF N
  obtain ⟨KG, hKG0, hKG⟩ := cnorm_betaBoost_uniform_list W.dim lG N
  let K : ℝ := max KF KG
  have hK : 0 ≤ K := hKF0.trans (le_max_left KF KG)
  let A : ℝ := k₁ * ((1 + 2 * K) ^ φs.length * (2 * K))
  refine ⟨A, k₂, ?_⟩
  intro τ hτ
  rw [hupperF, hupperG]

  have hτim : τ.im ∈ Set.Icc (0 : ℝ) Real.pi := by
    have h := hτ
    rw [mem_strip] at h
    simpa [Complex.mul_im, min_eq_left Real.pi_pos.le,
      max_eq_right Real.pi_pos.le] using h
  let σ : ℂ := Complex.I * (τ.im : ℂ)
  have hσ : σ ∈ strip (Complex.I * Real.pi) := by
    rw [mem_strip]
    simpa [σ, Complex.mul_im, min_eq_left Real.pi_pos.le,
      max_eq_right Real.pi_pos.le] using hτim
  have hτσ : τ = σ + (τ.re : ℂ) := by
    apply Complex.ext
    · simp [σ, Complex.mul_re]
    · simp [σ, Complex.mul_im]

  obtain ⟨hdomF, hvalF⟩ := lemma_3_7 hW lF σ hσ
  obtain ⟨hdomG, hvalG⟩ := lemma_3_7 hW lG σ hσ
  have htransF := vtilde_translation W hW.actsRegularly σ τ.re ΦF0
  have htransG := vtilde_translation W hW.actsRegularly σ τ.re ΦG0
  have hdomτF : W.VtildeDom (σ + (τ.re : ℂ)) ΦF0 := htransF.2.1.mpr hdomF
  have hdomτG : W.VtildeDom (σ + (τ.re : ℂ)) ΦG0 := htransG.2.1.mpr hdomG
  have hvF0 : W.vtildeMap τ ΦF0 = W.boost τ.re (W.vtildeMap σ ΦF0) := by
    calc
      W.vtildeMap τ ΦF0 = W.vtildeMap (σ + (τ.re : ℂ)) ΦF0 :=
        congrArg (fun z => W.vtildeMap z ΦF0) hτσ
      _ = W.boost τ.re (W.vtildeMap σ ΦF0) :=
        htransF.2.2.1 hdomτF hdomF
  have hvG0 : W.vtildeMap τ ΦG0 = W.boost τ.re (W.vtildeMap σ ΦG0) := by
    calc
      W.vtildeMap τ ΦG0 = W.vtildeMap (σ + (τ.re : ℂ)) ΦG0 :=
        congrArg (fun z => W.vtildeMap z ΦG0) hτσ
      _ = W.boost τ.re (W.vtildeMap σ ΦG0) :=
        htransG.2.2.1 hdomτG hdomG

  let fsAt : List TestFn :=
    lF.map (fun p => betaBoost (W.dim p.1) σ p.2)
  let gsAt : List TestFn :=
    lG.map (fun p => betaBoost (W.dim p.1) σ p.2)
  have hpairsF :
      lF.map (fun p => (p.1, betaBoost (W.dim p.1) σ p.2)) = φs.zip fsAt := by
    simpa only [lF, fsAt] using
      betaBoost_pairs_eq_zip W.dim φs Fs σ hFs.symm.le
  have hpairsG :
      lG.map (fun p => (p.1, betaBoost (W.dim p.1) σ p.2)) = φs.zip gsAt := by
    simpa only [lG, gsAt] using
      betaBoost_pairs_eq_zip W.dim φs Gs σ hGs.symm.le
  have hvF : W.vtildeMap τ ΦF0 =
      W.boost τ.re (W.toWightmanStruct.smearedProduct (φs.zip fsAt)) := by
    rw [hvF0, hvalF, hpairsF]
  have hvG : W.vtildeMap τ ΦG0 =
      W.boost τ.re (W.toWightmanStruct.smearedProduct (φs.zip gsAt)) := by
    rw [hvG0, hvalG, hpairsG]
  have hfsAt_len : fsAt.length = φs.length := by
    simpa only [fsAt, List.length_map] using hlF
  have hgsAt_len : gsAt.length = φs.length := by
    simpa only [gsAt, List.length_map] using hlG

  have hfsAt : ∀ f ∈ fsAt, (cnorm N f : ℝ) ≤ K := by
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    exact (hKF τ.im hτim p hp).trans (le_max_left KF KG)
  have hgsAt : ∀ g ∈ gsAt, (cnorm N g : ℝ) ≤ K := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
    exact (hKG τ.im hτim p hp).trans (le_max_right KF KG)
  have hprod :
      ((((fsAt.zip gsAt).map
        (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) ≤
        (1 + 2 * K) ^ φs.length := by
    simpa only [hfsAt_len] using
      prod_one_add_cnorm_le N K hK fsAt gsAt
        (hgsAt_len.trans hfsAt_len.symm) hfsAt hgsAt
  have hmax :
      ((List.foldr max 0
        ((fsAt.zip gsAt).map (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ) ≤
        2 * K :=
    foldr_max_cnorm_sub_le N K hK fsAt gsAt hfsAt hgsAt
  have hreal := hbound τ.re fsAt gsAt hfsAt_len hgsAt_len

  rw [hvF, hvG]
  calc
    ‖W.toWightmanStruct.compatApply lam
        (W.boost τ.re (W.toWightmanStruct.smearedProduct (φs.zip fsAt)) -
          W.boost τ.re (W.toWightmanStruct.smearedProduct (φs.zip gsAt)))‖ ≤
        C τ.re *
          (((((fsAt.zip gsAt).map
              (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
            ((List.foldr max 0
              ((fsAt.zip gsAt).map
                (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ)) := by
      rw [← mul_assoc]; exact hreal
    _ ≤ (k₁ * Real.exp (k₂ * |τ.re|)) *
          (((((fsAt.zip gsAt).map
              (fun p => 1 + cnorm N p.1 + cnorm N p.2)).prod : NNReal) : ℝ) *
            ((List.foldr max 0
              ((fsAt.zip gsAt).map
                (fun p => cnorm N (p.1 - p.2))) : NNReal) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (hCle τ.re)
        (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
    _ ≤ (k₁ * Real.exp (k₂ * |τ.re|)) *
          ((1 + 2 * K) ^ φs.length * (2 * K)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hk₁.le (Real.exp_nonneg _))
      exact mul_le_mul hprod hmax (NNReal.coe_nonneg _)
        (pow_nonneg (by linarith [hK]) _)
    _ = A * Real.exp (k₂ * |τ.re|) := by
      dsimp [A]
      ring

end WightmanData

end

end MobiusCPT
