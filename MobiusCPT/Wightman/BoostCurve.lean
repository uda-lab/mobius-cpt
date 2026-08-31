import MobiusCPT.Wightman.Basic
import MobiusCPT.Wightman.Continuity
import MobiusCPT.Analysis.Strip
import MobiusCPT.Analysis.TestFnCurve
import MobiusCPT.Mobius.ComplexBetaCont
import MobiusCPT.Mobius.ComplexBetaDerivFn
import MobiusCPT.Mobius.ComplexBetaHolo

namespace MobiusCPT

open Filter Set

noncomputable section

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- Scalarised consequence of [T26], Lemma 3.6(ii); the scalar functions of [T26], Definition 3.1
built from the complex boost are continuous on the closed strip.  This is the first clause
`IsBoostContinuation` asks of its family. -/
theorem continuousOn_compatApply_multiSmear_betaBoost (W : WightmanStruct TestFn 𝓓 𝓕)
    (lam : W.Compat) {k : ℕ} (φs : Fin k → 𝓕) (F : Fin k → AnalyticTestFn) :
    ContinuousOn
      (fun τ : ℂ => W.compatApply lam
        (W.multiSmear φs W.vac (fun i => betaBoost (W.dim (φs i)) τ (F i))))
      (strip (Complex.I * Real.pi)) := by
  let M : (Fin k → TestFn) → ℂ := fun f =>
    W.compatApply lam (W.multiSmear φs W.vac f)
  have hM : Continuous M := by
    simpa only [M, WightmanStruct.compatApply] using lam.2 k φs W.vac
  have hcurve : ContinuousOn
      (fun τ : ℂ => fun i : Fin k =>
        betaBoost (W.dim (φs i)) τ (F i))
      (strip (Complex.I * Real.pi)) := by
    rw [continuousOn_pi]
    intro i
    exact continuousOn_betaBoost (W.dim (φs i)) (F i)
  simpa only [M, WightmanStruct.compatApply, Function.comp_def] using
    hM.comp_continuousOn hcurve

/-- Scalarised consequence of [T26], Lemma 3.6(ii); the scalar functions of [T26], Definition 3.1
built from the complex boost are holomorphic in the interior of the strip.  The proof uses the
multilinear chain rule for the smeared product. -/
theorem differentiableOn_compatApply_multiSmear_betaBoost (W : WightmanStruct TestFn 𝓓 𝓕)
    (lam : W.Compat) {k : ℕ} (φs : Fin k → 𝓕) (F : Fin k → AnalyticTestFn) :
    DifferentiableOn ℂ
      (fun τ : ℂ => W.compatApply lam
        (W.multiSmear φs W.vac (fun i => betaBoost (W.dim (φs i)) τ (F i))))
      (interior (strip (Complex.I * Real.pi))) := by
  let M : (Fin k → TestFn) → ℂ := fun f =>
    W.compatApply lam (W.multiSmear φs W.vac f)
  have hM : Continuous M := by
    simpa only [M, WightmanStruct.compatApply] using lam.2 k φs W.vac
  have hlin : ∀ (i : Fin k) (f : Fin k → TestFn) (g h : TestFn),
      M (Function.update f i (g + h)) =
        M (Function.update f i g) + M (Function.update f i h) := by
    intro i f g h
    simp only [M, WightmanStruct.compatApply]
    rw [W.multiSmear_update_add φs W.vac f i g h, map_add]
  have hsmul : ∀ (i : Fin k) (f : Fin k → TestFn) (c : ℂ) (g : TestFn),
      M (Function.update f i (c • g)) = c * M (Function.update f i g) := by
    intro i f c g
    simp only [M, WightmanStruct.compatApply]
    rw [W.multiSmear_update_smul φs W.vac f i c g, map_smul, smul_eq_mul]
  intro τ hτ
  have hcont : ∀ i : Fin k, ContinuousAt
      (fun σ : ℂ => betaBoost (W.dim (φs i)) σ (F i)) τ := by
    intro i
    exact (continuousOn_betaBoost (W.dim (φs i)) (F i) τ
      (interior_subset hτ)).continuousAt
      (mem_of_superset (isOpen_interior.mem_nhds hτ) interior_subset)
  have hderiv : ∀ i : Fin k, HasTestFnDerivAt
      (fun σ : ℂ => betaBoost (W.dim (φs i)) σ (F i))
      (betaBoostDeriv (W.dim (φs i)) τ (F i)) τ := by
    intro i
    exact hasTestFnDerivAt_betaBoost (W.dim (φs i)) (F i) hτ
  have hA : HasDerivAt
      (fun t : ℂ => M (fun i : Fin k =>
        betaBoost (W.dim (φs i)) t (F i)))
      (∑ i : Fin k, M (Function.update
        (fun j : Fin k => betaBoost (W.dim (φs j)) τ (F j)) i
        (betaBoostDeriv (W.dim (φs i)) τ (F i)))) τ :=
    hasDerivAt_of_multilinear (M := M) (a := fun i σ =>
      betaBoost (W.dim (φs i)) σ (F i)) (a' := fun i =>
        betaBoostDeriv (W.dim (φs i)) τ (F i)) (τ := τ)
      hM hlin hsmul hcont hderiv
  have hwithin : DifferentiableWithinAt ℂ
      (fun t : ℂ => M (fun i : Fin k =>
        betaBoost (W.dim (φs i)) t (F i)))
      (interior (strip (Complex.I * Real.pi))) τ :=
    hA.differentiableAt.differentiableWithinAt
  simpa only [M, WightmanStruct.compatApply] using hwithin

/-- Scalarised consequence of [T26], Lemma 3.6(ii), in the list shape used by the continuation
contract. -/
theorem continuousOn_compatApply_smearedProduct_betaBoost (W : WightmanStruct TestFn 𝓓 𝓕)
    (lam : W.Compat) (l : List (𝓕 × AnalyticTestFn)) :
    ContinuousOn
      (fun τ : ℂ => W.compatApply lam
        (W.smearedProduct (l.map (fun p =>
          (p.1, betaBoost (W.dim p.1) τ p.2)))))
      (strip (Complex.I * Real.pi)) := by
  let φs : Fin l.length → 𝓕 := fun i => (l.get i).1
  let F : Fin l.length → AnalyticTestFn := fun i => (l.get i).2
  have hlist (τ : ℂ) :
      l.map (fun p : 𝓕 × AnalyticTestFn =>
        (p.1, betaBoost (W.dim p.1) τ p.2)) =
        List.ofFn (fun i : Fin l.length =>
          (φs i, betaBoost (W.dim (φs i)) τ (F i))) := by
    have h := List.ofFn_comp' (List.get l)
      (fun p : 𝓕 × AnalyticTestFn =>
        (p.1, betaBoost (W.dim p.1) τ p.2))
    rw [List.ofFn_get] at h
    simpa [φs, F] using h.symm
  have hfun :
      (fun τ : ℂ => W.compatApply lam
        (W.smearedProduct (l.map (fun p =>
          (p.1, betaBoost (W.dim p.1) τ p.2))))) =
      (fun τ : ℂ => W.compatApply lam
        (W.multiSmear φs W.vac (fun i =>
          betaBoost (W.dim (φs i)) τ (F i)))) := by
    funext τ
    change W.compatApply lam
        (W.smearedProductOn
          (l.map (fun p : 𝓕 × AnalyticTestFn =>
            (p.1, betaBoost (W.dim p.1) τ p.2))) W.vac) =
      W.compatApply lam
        (W.smearedProductOn
          (List.ofFn (fun i : Fin l.length =>
            (φs i, betaBoost (W.dim (φs i)) τ (F i)))) W.vac)
    rw [hlist τ]
  rw [hfun]
  exact continuousOn_compatApply_multiSmear_betaBoost W lam φs F

/-- Scalarised consequence of [T26], Lemma 3.6(ii), in the list shape used by the continuation
contract; the function is holomorphic in the interior of the strip. -/
theorem differentiableOn_compatApply_smearedProduct_betaBoost (W : WightmanStruct TestFn 𝓓 𝓕)
    (lam : W.Compat) (l : List (𝓕 × AnalyticTestFn)) :
    DifferentiableOn ℂ
      (fun τ : ℂ => W.compatApply lam
        (W.smearedProduct (l.map (fun p =>
          (p.1, betaBoost (W.dim p.1) τ p.2)))))
      (interior (strip (Complex.I * Real.pi))) := by
  let φs : Fin l.length → 𝓕 := fun i => (l.get i).1
  let F : Fin l.length → AnalyticTestFn := fun i => (l.get i).2
  have hlist (τ : ℂ) :
      l.map (fun p : 𝓕 × AnalyticTestFn =>
        (p.1, betaBoost (W.dim p.1) τ p.2)) =
        List.ofFn (fun i : Fin l.length =>
          (φs i, betaBoost (W.dim (φs i)) τ (F i))) := by
    have h := List.ofFn_comp' (List.get l)
      (fun p : 𝓕 × AnalyticTestFn =>
        (p.1, betaBoost (W.dim p.1) τ p.2))
    rw [List.ofFn_get] at h
    simpa [φs, F] using h.symm
  have hfun :
      (fun τ : ℂ => W.compatApply lam
        (W.smearedProduct (l.map (fun p =>
          (p.1, betaBoost (W.dim p.1) τ p.2))))) =
      (fun τ : ℂ => W.compatApply lam
        (W.multiSmear φs W.vac (fun i =>
          betaBoost (W.dim (φs i)) τ (F i)))) := by
    funext τ
    change W.compatApply lam
        (W.smearedProductOn
          (l.map (fun p : 𝓕 × AnalyticTestFn =>
            (p.1, betaBoost (W.dim p.1) τ p.2))) W.vac) =
      W.compatApply lam
        (W.smearedProductOn
          (List.ofFn (fun i : Fin l.length =>
            (φs i, betaBoost (W.dim (φs i)) τ (F i)))) W.vac)
    rw [hlist τ]
  rw [hfun]
  exact differentiableOn_compatApply_multiSmear_betaBoost W lam φs F

end
