import MobiusCPT.Wightman.Lemma37Continuation
import MobiusCPT.Wightman.BoostCurve

/-!
# [T26], Lemma 3.9: differentiability and closed-strip continuity

This module supplies the `DiffContOnCl` input for the maximum-principle assembly.  Lemma 3.7
identifies the continued vectors with the complex-boost curves on the whole closed strip, where
Lemma 3.6 already gives continuity and interior holomorphy.
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

/-- The open horizontal strip is the interior of the closed geometric strip. -/
private theorem im_preimage_Ioo_eq_interior_strip :
    Complex.im ⁻¹' Set.Ioo (0 : ℝ) Real.pi =
      interior (strip (Complex.I * Real.pi)) := by
  rw [interior_strip]
  ext z
  simp [Complex.mul_im, min_eq_left Real.pi_pos.le,
    max_eq_right Real.pi_pos.le]

/-- The closure of the open horizontal strip is the closed geometric strip. -/
private theorem closure_im_preimage_Ioo_eq_strip :
    closure (Complex.im ⁻¹' Set.Ioo (0 : ℝ) Real.pi) =
      strip (Complex.I * Real.pi) := by
  rw [Complex.closure_preimage_im, closure_Ioo Real.pi_pos.ne]
  ext z
  simp [mem_strip, Complex.mul_im, min_eq_left Real.pi_pos.le,
    max_eq_right Real.pi_pos.le]

/-- [T26], Lemma 3.9: the continued-boost difference is holomorphic on the open strip and
continuous on its closure. -/
theorem lemma_3_9_diffContOnCl {W : WightmanData Mob TestFn 𝓓 𝓕} (hW : W.IsWightmanCFT)
    (φs : List 𝓕) (lam : W.toWightmanStruct.Compat)
    (Fs Gs : List AnalyticTestFn) (hFs : Fs.length = φs.length)
    (hGs : Gs.length = φs.length) :
    DiffContOnCl ℂ
      (fun τ : ℂ => W.toWightmanStruct.compatApply lam
        (W.vtildeMap τ
            (W.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
          W.vtildeMap τ
            (W.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper)))))
      (Complex.im ⁻¹' Set.Ioo 0 Real.pi) := by
  let lF : List (𝓕 × AnalyticTestFn) := φs.zip Fs
  let lG : List (𝓕 × AnalyticTestFn) := φs.zip Gs
  let H : ℂ → ℂ := fun τ => W.toWightmanStruct.compatApply lam
    (W.vtildeMap τ
        (W.toWightmanStruct.smearedProduct (φs.zip (Fs.map xRestrictUpper))) -
      W.vtildeMap τ
        (W.toWightmanStruct.smearedProduct (φs.zip (Gs.map xRestrictUpper))))
  let gF : ℂ → ℂ := fun τ => W.toWightmanStruct.compatApply lam
    (W.toWightmanStruct.smearedProduct
      (lF.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2))))
  let gG : ℂ → ℂ := fun τ => W.toWightmanStruct.compatApply lam
    (W.toWightmanStruct.smearedProduct
      (lG.map (fun p => (p.1, betaBoost (W.dim p.1) τ p.2))))
  have hupperF :
      φs.zip (Fs.map xRestrictUpper) =
        lF.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lF] using zip_xRestrictUpper_eq φs Fs
  have hupperG :
      φs.zip (Gs.map xRestrictUpper) =
        lG.map (fun p => (p.1, xRestrictUpper p.2)) := by
    simpa only [lG] using zip_xRestrictUpper_eq φs Gs

  have hcontF : ContinuousOn gF (strip (Complex.I * Real.pi)) :=
    continuousOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam lF
  have hcontG : ContinuousOn gG (strip (Complex.I * Real.pi)) :=
    continuousOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam lG
  have hdiffF : DifferentiableOn ℂ gF (interior (strip (Complex.I * Real.pi))) :=
    differentiableOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam lF
  have hdiffG : DifferentiableOn ℂ gG (interior (strip (Complex.I * Real.pi))) :=
    differentiableOn_compatApply_smearedProduct_betaBoost W.toWightmanStruct lam lG
  have hagree : ∀ τ ∈ strip (Complex.I * Real.pi), H τ = gF τ - gG τ := by
    intro τ hτ
    obtain ⟨_, hvalF⟩ := lemma_3_7 hW lF τ hτ
    obtain ⟨_, hvalG⟩ := lemma_3_7 hW lG τ hτ
    simp only [H, hupperF, hupperG, WightmanStruct.compatApply, map_sub,
      hvalF, hvalG, gF, gG]

  have hcontStrip : ContinuousOn H (strip (Complex.I * Real.pi)) :=
    (hcontF.sub hcontG).congr hagree
  have hdiffInterior : DifferentiableOn ℂ H (interior (strip (Complex.I * Real.pi))) :=
    (hdiffF.sub hdiffG).congr
      (fun τ hτ => hagree τ (interior_subset hτ))
  have hdiff : DifferentiableOn ℂ H (Complex.im ⁻¹' Set.Ioo 0 Real.pi) := by
    rw [im_preimage_Ioo_eq_interior_strip]
    exact hdiffInterior
  have hcont : ContinuousOn H (closure (Complex.im ⁻¹' Set.Ioo 0 Real.pi)) := by
    rw [closure_im_preimage_Ioo_eq_strip]
    exact hcontStrip
  change DiffContOnCl ℂ H (Complex.im ⁻¹' Set.Ioo 0 Real.pi)
  exact ⟨hdiff, hcont⟩

end WightmanData

end

end MobiusCPT
