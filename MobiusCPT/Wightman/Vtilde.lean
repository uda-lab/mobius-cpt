import MobiusCPT.Analysis.Strip
import MobiusCPT.Wightman.Axioms

namespace MobiusCPT

/-!
# The partially defined operator `Ṽ_τ`

[T26], Definition 3.1: this module defines the partially defined operator `Ṽ_τ`, its domain
`D(Ṽ_τ)`, and the uniqueness that makes it well defined. The companion vector is **not**
obtained by an unconstrained choice: the definition takes a value only where the continuation
partner is unique. That uniqueness follows from separation of points by `D*_𝓕` (regularity),
which is the source's own justification.
-/

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 3.1; the family `(G_λ)_{λ ∈ D*_𝓕}` continuing the boost orbit of `Φ`
across the strip `𝕊_τ` to the boost orbit of `Ψ` on the upper boundary line `ℝ + τ`. Each
`G_λ` is continuous on the closed strip, holomorphic in its interior, has the boost orbit of `Φ`
as its values on the real boundary line, and has the boost orbit of the SAME `Ψ` — uniform in
`λ`, which is the content of the definition — as its values on `ℝ + τ`. -/
def IsBoostContinuation (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ Ψ : 𝓓)
    (Gf : W.toWightmanStruct.Compat → ℂ → ℂ) : Prop :=
  ∀ lam : W.toWightmanStruct.Compat,
    ContinuousOn (Gf lam) (strip τ) ∧
      DifferentiableOn ℂ (Gf lam) (interior (strip τ)) ∧
      (∀ t : ℝ, Gf lam (t : ℂ) = W.toWightmanStruct.compatApply lam (W.boost t Φ)) ∧
      (∀ t : ℝ, Gf lam (τ + (t : ℂ)) = W.toWightmanStruct.compatApply lam (W.boost t Ψ))

/-- [T26], Definition 3.1; `Ψ` is a continuation partner of `Φ` at `τ`. -/
def VtildeVal (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ Ψ : 𝓓) : Prop :=
  ∃ Gf : W.toWightmanStruct.Compat → ℂ → ℂ, W.IsBoostContinuation τ Φ Ψ Gf

/-- [T26], Definition 3.1; the domain `D(Ṽ_τ)` of the partially defined operator `Ṽ_τ`. -/
def VtildeDom (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ : 𝓓) : Prop :=
  ∃ Ψ : 𝓓, W.VtildeVal τ Φ Ψ

/-- [T26], Definition 3.1; the continuation family is unique. Two families for the same `Φ`
agree on the real boundary line by construction, hence on the whole closed strip. -/
theorem isBoostContinuation_eqOn (W : WightmanData G TF 𝓓 𝓕) {τ : ℂ} {Φ Ψ Ψ' : 𝓓}
    {Gf Gf' : W.toWightmanStruct.Compat → ℂ → ℂ}
    (h : W.IsBoostContinuation τ Φ Ψ Gf) (h' : W.IsBoostContinuation τ Φ Ψ' Gf')
    (lam : W.toWightmanStruct.Compat) :
    Set.EqOn (Gf lam) (Gf' lam) (strip τ) := by
  apply eqOn_closedStrip_of_eqOn_ofReal
      (h lam).1 (h lam).2.1 (h' lam).1 (h' lam).2.1
  intro t
  rw [(h lam).2.2.1 t, (h' lam).2.2.1 t]

/-- [T26], Definition 3.1; the continuation partner is unique. This is where the source's
"`λ(V_t Ψ) = λ(V_t Ψ')` for all compatible `λ` forces `Ψ = Ψ'`" is discharged, and it is
exactly separation of points by `D*_𝓕`, i.e. regularity — nothing stronger. -/
theorem vtildeVal_unique (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ Ψ Ψ' : 𝓓}
    (h : W.VtildeVal τ Φ Ψ) (h' : W.VtildeVal τ Φ Ψ') : Ψ = Ψ' := by
  obtain ⟨Gf, hGf⟩ := h
  obtain ⟨Gf', hGf'⟩ := h'
  apply (W.toWightmanStruct.actsRegularly_iff.mp hreg) Ψ Ψ'
  intro lam
  have hboundary := W.isBoostContinuation_eqOn hGf hGf' lam
    (add_ofReal_mem_closedStrip τ 0)
  rw [(hGf lam).2.2.2 0, (hGf' lam).2.2.2 0] at hboundary
  simpa only [W.boost_zero] using hboundary

/-- [T26], Definition 3.1; on the domain the continuation partner exists and is unique, so
`Ṽ_τ` is a genuine partial function determined by the source conditions. -/
theorem existsUnique_vtildeVal (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ : 𝓓} (h : W.VtildeDom τ Φ) :
    ∃! Ψ : 𝓓, W.VtildeVal τ Φ Ψ := by
  obtain ⟨Ψ, hΨ⟩ := h
  exact ⟨Ψ, hΨ, fun y hy => W.vtildeVal_unique hreg hy hΨ⟩

/-- [T26], Definition 3.1; a total Lean representative of the partially defined `Ṽ_τ`. The
value is read off the `∃!` statement, so it is taken only where the source conditions determine
it uniquely; where they do not — off the domain, or without regularity — it is `0`, and no
lemma below appeals to that value. -/
noncomputable def vtildeMap (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ : 𝓓) : 𝓓 :=
  open Classical in
  if h : ∃! Ψ : 𝓓, W.VtildeVal τ Φ Ψ then h.choose else 0

/-- [T26], Definition 3.1; on the domain, the representative is a continuation partner. -/
theorem vtildeVal_vtildeMap (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ : 𝓓} (h : W.VtildeDom τ Φ) :
    W.VtildeVal τ Φ (W.vtildeMap τ Φ) := by
  have hu := W.existsUnique_vtildeVal hreg h
  rw [vtildeMap, dif_pos hu]
  exact hu.choose_spec.1

/-- [T26], Definition 3.1; any continuation partner IS the value of the representative. -/
theorem vtildeMap_eq (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ Ψ : 𝓓} (h : W.VtildeVal τ Φ Ψ) :
    W.vtildeMap τ Φ = Ψ := by
  have hdom : W.VtildeDom τ Φ := ⟨Ψ, h⟩
  have hu := W.existsUnique_vtildeVal hreg hdom
  rw [vtildeMap, dif_pos hu]
  exact (hu.choose_spec.2 Ψ h).symm

/-- [T26], Definition 3.1; the domain-membership interface later results use: exhibiting one
family `G_λ` together with one companion vector both proves membership in `D(Ṽ_τ)` and pins the
value of `Ṽ_τ`. This is the lemma Lemma 3.7 and Theorem 3.10 invoke. -/
theorem vtildeDom_and_vtildeMap_eq (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ Ψ : 𝓓}
    {Gf : W.toWightmanStruct.Compat → ℂ → ℂ} (h : W.IsBoostContinuation τ Φ Ψ Gf) :
    W.VtildeDom τ Φ ∧ W.vtildeMap τ Φ = Ψ := by
  have hval : W.VtildeVal τ Φ Ψ := ⟨Gf, h⟩
  exact ⟨⟨Ψ, hval⟩, W.vtildeMap_eq hreg hval⟩

/-- [T26], Definition 3.1; membership in `D(Ṽ_τ)` written out. -/
theorem vtildeDom_iff (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ : 𝓓) :
    W.VtildeDom τ Φ ↔
      ∃ (Ψ : 𝓓) (Gf : W.toWightmanStruct.Compat → ℂ → ℂ),
        ∀ lam : W.toWightmanStruct.Compat,
          ContinuousOn (Gf lam) (strip τ) ∧
            DifferentiableOn ℂ (Gf lam) (interior (strip τ)) ∧
            (∀ t : ℝ, Gf lam (t : ℂ) = W.toWightmanStruct.compatApply lam (W.boost t Φ)) ∧
            (∀ t : ℝ,
              Gf lam (τ + (t : ℂ)) = W.toWightmanStruct.compatApply lam (W.boost t Ψ)) :=
  Iff.rfl

/-- [T26], Definition 3.1; the compatible-functional characterization of `Ṽ_τ`, in the exact
form the repository's statement contract pins. Regularity is the precise separation-of-points
hypothesis needed for this equivalence. (The bound family is written `Gf` rather than `G`
because `G` is the Möbius group type variable in this module; the statement is unchanged.) -/
theorem vtilde_spec (W : WightmanData G TF 𝓓 𝓕) :
    W.toWightmanStruct.ActsRegularly →
      ∀ (τ : ℂ) (Φ Ψ : 𝓓),
      (W.VtildeDom τ Φ ∧ W.vtildeMap τ Φ = Ψ) ↔
        ∃ Gf : W.toWightmanStruct.Compat → ℂ → ℂ,
          ∀ lam : W.toWightmanStruct.Compat,
            ContinuousOn (Gf lam) (strip τ) ∧
              DifferentiableOn ℂ (Gf lam) (interior (strip τ)) ∧
              (∀ t : ℝ,
                Gf lam (t : ℂ) = W.toWightmanStruct.compatApply lam (W.boost t Φ)) ∧
              (∀ t : ℝ,
                Gf lam (τ + (t : ℂ)) = W.toWightmanStruct.compatApply lam (W.boost t Ψ)) := by
  intro hreg τ Φ Ψ
  constructor
  · rintro ⟨hdom, rfl⟩
    exact W.vtildeVal_vtildeMap hreg hdom
  · intro hval
    exact ⟨⟨Ψ, hval⟩, W.vtildeMap_eq hreg hval⟩

end WightmanData

end MobiusCPT
