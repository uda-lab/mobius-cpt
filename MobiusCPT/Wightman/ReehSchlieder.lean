import MobiusCPT.TestFunctions.AnalyticDensity
import MobiusCPT.TestFunctions.AnalyticReflect
import MobiusCPT.Wightman.Bundle
import MobiusCPT.Wightman.ReehSchliederLemma
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Reeh--Schlieder density

Block R4 of Issue #13.  The Hahn--Banach argument proves density of the localized
polynomial subspaces, and analytic density of test functions then gives dense analytic cores.
-/

namespace MobiusCPT

open Filter Set
open scoped Topology

noncomputable section

namespace WightmanBundle

private theorem dense_localizedOmega
    (W : WightmanBundle) (P : Submodule ℂ W.𝓓) (Supp : TestFn → Prop)
    (hgen : ∀ l : List (W.𝓕 × TestFn), (∀ p ∈ l, Supp p.2) →
      W.data.smearedProduct l ∈ P)
    (hkill : ∀ lam : W.data.toWightmanStruct.Compat,
      (∀ l : List (W.𝓕 × TestFn), (∀ p ∈ l, Supp p.2) →
        W.data.toWightmanStruct.compatApply lam (W.data.smearedProduct l) = 0) →
      lam = 0) :
    @Dense W.𝓓 W.data.strongTop (P : Set W.𝓓) := by
  letI : TopologicalSpace W.𝓓 := W.data.strongTop
  letI : IsTopologicalAddGroup W.𝓓 :=
    W.data.toWightmanStruct.fStrongTopology_isTopologicalAddGroup
  letI : ContinuousSMul ℂ W.𝓓 :=
    W.data.toWightmanStruct.fStrongTopology_continuousSMul
  letI : ContinuousSMul ℝ W.𝓓 := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℝ W.𝓓 :=
    W.data.toWightmanStruct.fStrongTopology_locallyConvex
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hne
  obtain ⟨x, hx⟩ :=
    SetLike.exists_not_mem_of_ne_top P.topologicalClosure hne rfl
  have hconvex : Convex ℝ (P.topologicalClosure : Set W.𝓓) := by
    simpa only [Submodule.coe_restrictScalars] using
      (P.topologicalClosure.restrictScalars ℝ).convex
  have hclosed : IsClosed (P.topologicalClosure : Set W.𝓓) :=
    P.isClosed_topologicalClosure
  obtain ⟨f, u, hfx, hbu⟩ :=
    geometric_hahn_banach_point_closed (E := W.𝓓) hconvex hclosed hx
  have hfzero : ∀ b ∈ (P.topologicalClosure : Set W.𝓓), f b = 0 := by
    intro b hb
    by_contra hbne
    have hbsmul : ((u - 1) / f b) • b ∈ P.topologicalClosure := by
      rw [← Complex.coe_smul]
      exact P.topologicalClosure.smul_mem (((u - 1) / f b : ℝ) : ℂ) hb
    have hmap : f (((u - 1) / f b) • b) = u - 1 := by
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ (u - 1) hbne
    have hlt := hbu (((u - 1) / f b) • b) hbsmul
    rw [hmap] at hlt
    linarith
  let f' : StrongDual ℂ W.𝓓 := f.extendRCLike
  have hf'zero : ∀ b ∈ (P.topologicalClosure : Set W.𝓓), f' b = 0 := by
    intro b hb
    apply Complex.ext
    · have heq : (f' b).re = f b :=
        StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f b
      rw [heq]
      exact hfzero b hb
    · have hIb : Complex.I • b ∈ P.topologicalClosure :=
        P.topologicalClosure.smul_mem Complex.I hb
      have heq : (f' b).im = -f (Complex.I • b) :=
        StrongDual.im_extendRCLike_apply (𝕜 := ℂ) f b
      rw [heq, hfzero (Complex.I • b) hIb, neg_zero, Complex.zero_im]
  have hfcont :
      @Continuous W.𝓓 ℂ W.data.strongTop inferInstance f'.toLinearMap :=
    f'.continuous
  have hfcompat : W.data.toWightmanStruct.IsCompatible f'.toLinearMap :=
    (W.data.toWightmanStruct.continuous_iff_isCompatible f'.toLinearMap).1 hfcont
  let lam : W.data.toWightmanStruct.Compat := ⟨f'.toLinearMap, hfcompat⟩
  have hlamvanish : ∀ l : List (W.𝓕 × TestFn),
      (∀ p ∈ l, Supp p.2) →
        W.data.toWightmanStruct.compatApply lam (W.data.smearedProduct l) = 0 := by
    intro l hl
    have hP : W.data.smearedProduct l ∈ P := hgen l hl
    have hclosure : W.data.smearedProduct l ∈ P.topologicalClosure :=
      P.le_topologicalClosure hP
    change f' (W.data.smearedProduct l) = 0
    exact hf'zero _ hclosure
  have hlamzero : lam = 0 := hkill lam hlamvanish
  have hlamval : lam.1 = 0 := congrArg Subtype.val hlamzero
  have hf'all : ∀ y : W.𝓓, f' y = 0 := by
    intro y
    have hy := congrArg (fun g : W.𝓓 →ₗ[ℂ] ℂ => g y) hlamval
    simpa [lam] using hy
  have hfall : ∀ y : W.𝓓, f y = 0 := by
    intro y
    calc
      f y = Complex.re (f.extendRCLike (𝕜 := ℂ) y) :=
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f y).symm
      _ = Complex.re (f' y) := rfl
      _ = 0 := by rw [hf'all y]; rfl
  have hu_neg : u < 0 := by
    simpa [hfall 0] using hbu 0 P.topologicalClosure.zero_mem
  have hu_pos : 0 < u := by
    simpa [hfall x] using hfx
  linarith

/-- [CRTT25], Appendix A, Corollary A.3(i): `P(I₊)Ω` is dense in the
`𝓕`-strong topology. -/
theorem reehSchlieder_upper (W : WightmanBundle) (hW : W.data.IsWightmanCFT) :
    @Dense W.𝓓 W.data.strongTop
      (W.data.toWightmanStruct.PUpperOmega : Set W.𝓓) := by
  apply dense_localizedOmega W W.data.toWightmanStruct.PUpperOmega SuppUpper
  · intro l hl
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  · intro lam hlam
    exact eq_zero_of_forall_smearedProduct_suppUpper_eq_zero W.data hW lam hlam

/-- [CRTT25], Appendix A, Corollary A.3(i): `P(I₋)Ω` is dense in the
`𝓕`-strong topology. -/
theorem reehSchlieder_lower (W : WightmanBundle) (hW : W.data.IsWightmanCFT) :
    @Dense W.𝓓 W.data.strongTop
      (W.data.toWightmanStruct.PLowerOmega : Set W.𝓓) := by
  apply dense_localizedOmega W W.data.toWightmanStruct.PLowerOmega SuppLower
  · intro l hl
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  · intro lam hlam
    exact eq_zero_of_forall_smearedProduct_suppLower_eq_zero W.data hW lam hlam

private theorem analyticCore_dense_of
    (W : WightmanBundle) (Supp : TestFn → Prop)
    (restrictX : AnalyticTestFn → TestFn)
    (hdensity : {f : TestFn | Supp f} ⊆
      closure {g : TestFn | ∃ F : AnalyticTestFn, restrictX F = g})
    (hlocalDense : @Dense W.𝓓 W.data.strongTop
      (Submodule.span ℂ { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
        (∀ p ∈ l, Supp p.2) ∧ Φ = W.data.smearedProduct l } : Set W.𝓓)) :
    @Dense W.𝓓 W.data.strongTop
      (Submodule.span ℂ { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
        (∀ p ∈ l, ∃ F : AnalyticTestFn, restrictX F = p.2) ∧
          Φ = W.data.smearedProduct l } : Set W.𝓓) := by
  classical
  letI : TopologicalSpace W.𝓓 := W.data.strongTop
  letI : IsTopologicalAddGroup W.𝓓 :=
    W.data.toWightmanStruct.fStrongTopology_isTopologicalAddGroup
  letI : ContinuousSMul ℂ W.𝓓 :=
    W.data.toWightmanStruct.fStrongTopology_continuousSMul
  let S : Submodule ℂ W.𝓓 := Submodule.span ℂ
    { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
      (∀ p ∈ l, Supp p.2) ∧ Φ = W.data.smearedProduct l }
  let T : Submodule ℂ W.𝓓 := Submodule.span ℂ
    { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
      (∀ p ∈ l, ∃ F : AnalyticTestFn, restrictX F = p.2) ∧
        Φ = W.data.smearedProduct l }
  change Dense (T : Set W.𝓓)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hSclosure : S.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (by
      simpa only [S] using hlocalDense)
  have hST : S ≤ T.topologicalClosure := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨l, hl, rfl⟩
    rw [Submodule.topologicalClosure_coe]
    let k : ℕ := l.length
    let φ : Fin k → W.𝓕 := fun i => (l.get i).1
    let f₀ : Fin k → TestFn := fun i => (l.get i).2
    have hf₀ : ∀ i : Fin k, Supp (f₀ i) := by
      intro i
      exact hl (l.get i) (List.get_mem l i)
    have happrox : ∀ i : Fin k, ∃ u : ℕ → TestFn,
        (∀ n : ℕ, ∃ F : AnalyticTestFn, restrictX F = u n) ∧
          Tendsto u atTop (nhds (f₀ i)) := by
      intro i
      exact mem_closure_iff_seq_limit.mp (hdensity (hf₀ i))
    choose u hu hlim using happrox
    have hpi : Tendsto (fun n : ℕ => fun i => u i n) atTop (nhds f₀) :=
      tendsto_pi_nhds.2 hlim
    have hmulti :=
      (W.data.toWightmanStruct.fStrongTopology_continuous_multiSmear
        k φ W.data.vac).continuousAt.tendsto.comp hpi
    have hPQ : W.data.smearedProductOn (List.ofFn fun i => l.get i) W.data.vac =
        W.data.smearedProduct l := by
      have hget : List.ofFn (fun i => l.get i) = l := List.ofFn_get l
      show W.data.smearedProductOn (List.ofFn fun i => l.get i) W.data.vac =
        W.data.smearedProductOn l W.data.vac
      rw [hget]
    have hlimit : Tendsto
        (fun n : ℕ => W.data.toWightmanStruct.multiSmear φ W.data.vac
          (fun i => u i n)) atTop (nhds (W.data.smearedProduct l)) := by
      rw [← hPQ]
      simpa only [Function.comp_def, WightmanStruct.multiSmear, φ, f₀] using hmulti
    apply mem_closure_of_tendsto hlimit
    filter_upwards with n
    apply Submodule.subset_span
    refine ⟨List.ofFn fun i => (φ i, u i n), ?_, rfl⟩
    exact List.forall_mem_ofFn_iff.mpr (fun i => hu i n)
  have hmono : S.topologicalClosure ≤ T.topologicalClosure.topologicalClosure :=
    Submodule.topologicalClosure_mono hST
  have hclosed : T.topologicalClosure.topologicalClosure = T.topologicalClosure :=
    T.isClosed_topologicalClosure.submodule_topologicalClosure_eq
  rw [hclosed] at hmono
  exact top_unique (by simpa only [hSclosure] using hmono)

/-- The upper analytic smeared-product core is dense in the `𝓕`-strong topology. -/
theorem analyticCore_dense_upper (W : WightmanBundle) (hW : W.data.IsWightmanCFT) :
    @Dense W.𝓓 W.data.strongTop
      (Submodule.span ℂ { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
        (∀ p ∈ l, ∃ F : AnalyticTestFn, xRestrictUpper F = p.2) ∧
          Φ = W.data.smearedProduct l } : Set W.𝓓) := by
  apply analyticCore_dense_of W SuppUpper xRestrictUpper lemma_3_4_density_upper
  exact reehSchlieder_upper W hW

/-- The lower analytic smeared-product core is dense in the `𝓕`-strong topology. -/
theorem analyticCore_dense_lower (W : WightmanBundle) (hW : W.data.IsWightmanCFT) :
    @Dense W.𝓓 W.data.strongTop
      (Submodule.span ℂ { Φ : W.𝓓 | ∃ l : List (W.𝓕 × TestFn),
        (∀ p ∈ l, ∃ F : AnalyticTestFn, xRestrictLower F = p.2) ∧
          Φ = W.data.smearedProduct l } : Set W.𝓓) := by
  apply analyticCore_dense_of W SuppLower xRestrictLower lemma_3_4_density_lower
  exact reehSchlieder_lower W hW

end WightmanBundle

end

end MobiusCPT
