import MobiusCPT.Wightman.Vtilde
import MobiusCPT.Wightman.Bundle
import MobiusCPT.Mobius.BoostContinuity

namespace MobiusCPT

/-!
# Real parameters for `Ṽ_τ`

[T26], Definition 3.1 states that for a real parameter `t`, the domain of `Ṽ_t` is all of
`𝓓` and `Ṽ_t = V_t`. When `τ = (t : ℂ)`, the closed strip degenerates to the real axis, so
the lower-boundary clause in Definition 3.1 determines the continuation family on the whole
strip. Its `ContinuousOn` requirement is therefore exactly continuity of
`s ↦ λ(V_s Φ)`.

That continuity is not part of the repository's abstract `IsWightmanCFT` interface: (W1)
gives continuity in the vector argument for each fixed group element, but the abstract
`MobiusAction` supplies no parameter continuity. The source obtains the missing fact through
[CRTT25], Lemma 2.10(i), using continuity of `t ↦ β_d(v_t)f` in the test-function topology.
Accordingly, this module names the missing input, proves the real-parameter result from it,
and reduces that input to continuity of the concrete conformal action. No unconditional
theorem `vtilde_real` is claimed here.
-/

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 3.1 and [CRTT25], Lemma 2.10(i); continuity of the boost orbit
under every compatible functional. This is exactly the input Definition 3.1's
real-parameter case needs, and it is a consequence of the source's axioms rather than one
of them. -/
def BoostOrbitContinuous (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  ∀ (lam : W.toWightmanStruct.Compat) (Φ : 𝓓),
    Continuous fun t : ℝ => W.toWightmanStruct.compatApply lam (W.boost t Φ)

/-- [T26], Definition 3.1; the real-parameter case. For real `τ = t` the strip
degenerates to the real axis, the domain is all of `𝓓`, and `Ṽ_t = V_t`. -/
theorem vtilde_real_of_boostOrbitContinuous (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) (hcont : W.BoostOrbitContinuous) :
    ∀ (t : ℝ) (Φ : 𝓓),
      W.VtildeDom (t : ℂ) Φ ∧ W.vtildeMap (t : ℂ) Φ = W.boost t Φ := by
  intro t Φ
  let Gf : W.toWightmanStruct.Compat → ℂ → ℂ := fun lam z =>
    W.toWightmanStruct.compatApply lam (W.boost z.re Φ)
  apply W.vtildeDom_and_vtildeMap_eq h.actsRegularly (Gf := Gf)
  intro lam
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hcont lam Φ).comp Complex.continuous_re).continuousOn
  · rw [interior_strip_ofReal]
    exact differentiableOn_empty
  · intro s
    simp only [Gf, Complex.ofReal_re]
  · intro s
    change W.toWightmanStruct.compatApply lam
        (W.boost (((t : ℂ) + (s : ℂ)).re) Φ) =
      W.toWightmanStruct.compatApply lam (W.boost s (W.boost t Φ))
    simpa only [Complex.add_re, Complex.ofReal_re, W.boost_add] using
      congrArg
        (fun r : ℝ => W.toWightmanStruct.compatApply lam (W.boost r Φ))
        (add_comm t s)

/-- [T26], Definition 3.1; the real-parameter case in its unconditional-looking form is
equivalent to the continuity input, so nothing is hidden: `Ṽ_t = V_t` on all of `𝓓`
forces the boost orbit to be continuous under every compatible functional. -/
theorem boostOrbitContinuous_of_vtilde_real (W : WightmanData G TF 𝓓 𝓕)
    (h : ∀ (t : ℝ) (Φ : 𝓓), W.VtildeDom (t : ℂ) Φ) : W.BoostOrbitContinuous := by
  intro lam Φ
  obtain ⟨Ψ, hΨ⟩ := h 0 Φ
  obtain ⟨Gf, hGf⟩ := hΨ
  have hGfReal : Continuous (Gf lam ∘ fun s : ℝ => (s : ℂ)) :=
    (hGf lam).1.comp_continuous Complex.continuous_ofReal
      (fun s => ofReal_mem_strip ((0 : ℝ) : ℂ) s)
  exact hGfReal.congr fun s => (hGf lam).2.2.1 s

/-- [T26], Definition 2.4; covariance rewritten as
`U(γ) φ(f) Ψ = φ(β_d(γ)f) U(γ) Ψ`. -/
theorem u_smear (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (γ : G) (φ : 𝓕)
    (f : TF) (Ψ : 𝓓) :
    W.U γ (W.smear φ f Ψ) =
      W.smear φ (MobiusAction.beta (W.dim φ) γ f) (W.U γ Ψ) := by
  have hcov := h.2 φ γ f (W.U γ Ψ)
  rw [(W.U_inv_apply γ Ψ).2] at hcov
  exact hcov

/-- [T26], Definition 2.4; covariance moves a Möbius transformation through every
factor of a smeared product while transforming its test function. -/
theorem u_smearedProductOn (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (γ : G)
    (l : List (𝓕 × TF)) (Ψ : 𝓓) :
    W.U γ (W.smearedProductOn l Ψ) =
      W.smearedProductOn
        (l.map fun p => (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) (W.U γ Ψ) := by
  induction l with
  | nil =>
      simp only [WightmanStruct.smearedProductOn_nil, List.map_nil]
  | cons p l ih =>
      simp only [WightmanStruct.smearedProductOn_cons, List.map_cons]
      rw [W.u_smear h, ih]

/-- [T26], Definition 2.4 and axiom (W4); covariance of a vacuum smeared product,
using Möbius invariance of the vacuum. -/
theorem u_smearedProduct (W : WightmanData G TF 𝓓 𝓕) (h : W.IsWightmanCFT)
    (γ : G) (l : List (𝓕 × TF)) :
    W.U γ (W.smearedProduct l) =
      W.smearedProduct
        (l.map fun p => (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) := by
  change W.U γ (W.smearedProductOn l W.vac) =
    W.smearedProductOn
      (l.map fun p => (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) W.vac
  rw [W.u_smearedProductOn h.w1, h.w4.1 γ]

/-- [T26], Definition 3.1 and [CRTT25], Lemma 2.10(i); the reduction. Given (W1)
covariance, (W4) and compatibility, boost-orbit continuity follows from continuity of the
conformal action `t ↦ β_d(v_t) f` on test functions, a statement about the concrete Möbius
action alone. -/
theorem boostOrbitContinuous_of_beta_continuous (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT)
    (hbeta : ∀ (d : ℕ) (f : TF),
      Continuous fun t : ℝ =>
        MobiusAction.beta (G := G) (TF := TF) d
          (MobiusAction.boostElt (G := G) (TF := TF) t) f) :
    W.BoostOrbitContinuous := by
  intro lam Φ
  have hΦ :
      Φ ∈ Submodule.span ℂ
        { Ψ : 𝓓 | ∃ l : List (𝓕 × TF), Ψ = W.smearedProduct l } := by
    rw [← h.w4.2]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun Ψ _ =>
    Continuous fun t : ℝ => W.toWightmanStruct.compatApply lam (W.boost t Ψ)) ?_ ?_ ?_ ?_ hΦ
  · intro Ψ hΨ
    obtain ⟨l, rfl⟩ := hΨ
    let φs : Fin l.length → 𝓕 := fun i => (l.get i).1
    let fs : Fin l.length → TF := fun i => (l.get i).2
    have hargs : Continuous fun t : ℝ => fun i : Fin l.length =>
        MobiusAction.beta (G := G) (TF := TF) (W.dim (φs i))
          (MobiusAction.boostElt (G := G) (TF := TF) t) (fs i) :=
      continuous_pi fun i => hbeta (W.dim (φs i)) (fs i)
    have hmulti := (lam.2 l.length φs W.vac).comp hargs
    have hlist (t : ℝ) :
        l.map (fun p =>
          (p.1, MobiusAction.beta (G := G) (TF := TF) (W.dim p.1)
            (MobiusAction.boostElt (G := G) (TF := TF) t) p.2)) =
          List.ofFn fun i : Fin l.length =>
            (φs i, MobiusAction.beta (G := G) (TF := TF) (W.dim (φs i))
              (MobiusAction.boostElt (G := G) (TF := TF) t) (fs i)) := by
      dsimp [φs, fs]
      simpa only [List.ofFn_get, List.get_eq_getElem] using
        (List.ofFn_comp' (List.get l) (fun p : 𝓕 × TF =>
          (p.1, MobiusAction.beta (G := G) (TF := TF) (W.dim p.1)
            (MobiusAction.boostElt (G := G) (TF := TF) t) p.2))).symm
    apply hmulti.congr
    intro t
    change lam.1
        (W.multiSmear φs W.vac (fun i =>
          MobiusAction.beta (G := G) (TF := TF) (W.dim (φs i))
            (MobiusAction.boostElt (G := G) (TF := TF) t) (fs i))) =
      lam.1 (W.boost t (W.smearedProduct l))
    apply congrArg lam.1
    symm
    change W.U (MobiusAction.boostElt (G := G) (TF := TF) t)
        (W.smearedProduct l) =
      W.multiSmear φs W.vac (fun i =>
        MobiusAction.beta (G := G) (TF := TF) (W.dim (φs i))
          (MobiusAction.boostElt (G := G) (TF := TF) t) (fs i))
    rw [W.u_smearedProduct h]
    change W.smearedProductOn
        (l.map fun p =>
          (p.1, MobiusAction.beta (G := G) (TF := TF) (W.dim p.1)
            (MobiusAction.boostElt (G := G) (TF := TF) t) p.2)) W.vac =
      W.smearedProductOn
        (List.ofFn fun i : Fin l.length =>
          (φs i, MobiusAction.beta (G := G) (TF := TF) (W.dim (φs i))
            (MobiusAction.boostElt (G := G) (TF := TF) t) (fs i))) W.vac
    rw [hlist t]
  · apply (continuous_const : Continuous fun _ : ℝ => (0 : ℂ)).congr
    intro t
    change (0 : ℂ) = lam.1 (W.boost t (0 : 𝓓))
    rw [(W.boost t).map_zero, lam.1.map_zero]
  · intro Ψ₁ Ψ₂ _ _ hΨ₁ hΨ₂
    apply (hΨ₁.add hΨ₂).congr
    intro t
    rw [(W.boost_linear t Ψ₁ Ψ₂).1,
      (W.toWightmanStruct.compatApply_linear lam (W.boost t Ψ₁) (W.boost t Ψ₂)).1]
    rfl
  · intro c Ψ _ hΨ
    apply (hΨ.const_smul c).congr
    intro t
    rw [(W.boost_linear t Ψ Ψ).2 c,
      (W.toWightmanStruct.compatApply_linear lam (W.boost t Ψ) (W.boost t Ψ)).2 c]
    rfl

end WightmanData

namespace WightmanBundle

/-- [T26], Definition 3.1; [CRTT25], Lemma 2.10(i). Issue #38 discharges
`MobiusCPT.Contract`'s `theorem_wanted vtilde_real`, byte-identical statement text: for the
concrete Möbius group and conformal action `WightmanBundle` fixes (`docs/adr/0001-fix-mobius-group-in-bundle.md`),
boost-orbit continuity is unconditional, via `hbeta_mobiusActionMobTestFn`
(`MobiusCPT.Mobius.BoostContinuity`), so the real-parameter case of `Ṽ_τ` holds outright. -/
theorem vtilde_real (W : WightmanBundle) (h : W.data.IsWightmanCFT) :
    ∀ (t : ℝ) (Φ : W.𝓓),
      W.data.VtildeDom (t : ℂ) Φ ∧ W.data.vtildeMap (t : ℂ) Φ = W.data.boost t Φ :=
  WightmanData.vtilde_real_of_boostOrbitContinuous W.data h
    (WightmanData.boostOrbitContinuous_of_beta_continuous W.data h hbeta_mobiusActionMobTestFn)

end WightmanBundle

end MobiusCPT
