import MobiusCPT.Wightman.Mobius

namespace MobiusCPT

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- [T26], Definition 2.4: covariance in the form used to move `U(γ)` to the left of a
smeared field, `U(γ) φ(f) Ψ = φ(β_d(γ) f) U(γ) Ψ`. -/
theorem WightmanData.IsCovariant.smear_comm
    {W : WightmanData G TF 𝓓 𝓕} {φ : 𝓕} {d : ℕ}
    (h : W.IsCovariant φ d) (γ : G) (f : TF) (Ψ : 𝓓) :
    W.U γ (W.smear φ f Ψ) =
      W.smear φ (MobiusAction.beta d γ f) (W.U γ Ψ) := by
  have h' := h γ f (W.U γ Ψ)
  rw [(W.U_inv_apply γ Ψ).2] at h'
  exact h'

/-- [T26], §3: a Möbius element moves through a product of smeared fields, transforming
each test function by `β_{d_j}(γ)`. -/
theorem WightmanData.U_smearedProductOn {W : WightmanData G TF 𝓓 𝓕} (γ : G)
    (l : List (𝓕 × TF)) (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1)) (Φ : 𝓓) :
    W.U γ (W.smearedProductOn l Φ) =
      W.smearedProductOn (l.map fun p =>
        (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) (W.U γ Φ) := by
  revert hcov Φ
  induction l with
  | nil =>
      intro hcov Φ
      rfl
  | cons p l ih =>
      intro hcov Φ
      have hp : W.IsCovariant p.1 (W.dim p.1) := hcov p (by simp)
      have htail : ∀ q ∈ l, W.IsCovariant q.1 (W.dim q.1) := by
        intro q hq
        exact hcov q (by simp [hq])
      simp only [WightmanStruct.smearedProductOn_cons, List.map_cons]
      rw [WightmanData.IsCovariant.smear_comm hp, ih htail Φ]

/-- [T26], §3: with the (W4) vacuum-invariance, `U(γ)` acts on
`φ₁(f₁)⋯φ_k(f_k)Ω` by transforming the test functions. -/
theorem WightmanData.U_smearedProduct {W : WightmanData G TF 𝓓 𝓕} (hW4 : W.W4) (γ : G)
    (l : List (𝓕 × TF)) (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1)) :
    W.U γ (W.smearedProduct l) =
      W.smearedProduct (l.map fun p =>
        (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) := by
  change W.U γ (W.smearedProductOn l W.vac) =
    W.smearedProductOn (l.map fun p =>
      (p.1, MobiusAction.beta (W.dim p.1) γ p.2)) W.vac
  rw [WightmanData.U_smearedProductOn γ l hcov W.vac, hW4.1 γ]

/-- [T26], §3: the covariance rewrite for the boost, `V_t φ₁(f₁)⋯φ_k(f_k)Ω =
`φ₁(β_{d₁}(v_t)f₁)⋯φ_k(β_{d_k}(v_t)f_k)Ω`. -/
theorem WightmanData.boost_smearedProduct {W : WightmanData G TF 𝓓 𝓕} (hW4 : W.W4) (t : ℝ)
    (l : List (𝓕 × TF)) (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1)) :
    W.boost t (W.smearedProduct l) =
      W.smearedProduct
        (l.map fun p =>
          (p.1, MobiusAction.beta (W.dim p.1)
            (MobiusAction.boostElt (G := G) (TF := TF) t) p.2)) := by
  change W.U (MobiusAction.boostElt (G := G) (TF := TF) t) (W.smearedProduct l) = _
  exact WightmanData.U_smearedProduct hW4
    (MobiusAction.boostElt (G := G) (TF := TF) t) l hcov

/-- [T26], §3: the covariance rewrite for a rotation, with `U(r_θ)` acting on a
smeared product by transforming each test function with `β_d(r_θ)`. -/
theorem WightmanData.rotation_smearedProduct {W : WightmanData G TF 𝓓 𝓕} (hW4 : W.W4) (θ : ℝ)
    (l : List (𝓕 × TF)) (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1)) :
    W.U (MobiusAction.rot (G := G) (TF := TF) θ) (W.smearedProduct l) =
      W.smearedProduct
        (l.map fun p =>
          (p.1, MobiusAction.beta (W.dim p.1)
            (MobiusAction.rot (G := G) (TF := TF) θ) p.2)) := by
  exact WightmanData.U_smearedProduct hW4
    (MobiusAction.rot (G := G) (TF := TF) θ) l hcov

end MobiusCPT
