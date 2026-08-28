import MobiusCPT.Wightman.Vtilde
import Mathlib.LinearAlgebra.LinearPMap

/-!
# Linearity of the partially defined operator `Ṽ_τ`

[T26], Definition 3.1: the domain `D(Ṽ_τ)` is a complex subspace and the companion
assignment is linear on that domain. The `LinearPMap` constructed here has exactly the
domain `D(Ṽ_τ)` and exactly the action `Ṽ_τ`; it neither enlarges nor restricts that
partially defined operator.
-/

namespace MobiusCPT

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 3.1; the zero vector continues to the zero vector. -/
theorem isBoostContinuation_zero (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) :
    W.IsBoostContinuation τ 0 0 (fun _ _ => 0) := by
  intro lam
  refine ⟨continuousOn_const, differentiableOn_const (0 : ℂ), ?_, ?_⟩
  · intro t
    simp [WightmanStruct.compatApply]
  · intro t
    simp [WightmanStruct.compatApply]

/-- [T26], Definition 3.1; continuations add. -/
theorem IsBoostContinuation.add {W : WightmanData G TF 𝓓 𝓕} {τ : ℂ}
    {Φ₁ Ψ₁ Φ₂ Ψ₂ : 𝓓}
    {Gf₁ Gf₂ : W.toWightmanStruct.Compat → ℂ → ℂ}
    (h₁ : W.IsBoostContinuation τ Φ₁ Ψ₁ Gf₁)
    (h₂ : W.IsBoostContinuation τ Φ₂ Ψ₂ Gf₂) :
    W.IsBoostContinuation τ (Φ₁ + Φ₂) (Ψ₁ + Ψ₂)
      (fun lam z => Gf₁ lam z + Gf₂ lam z) := by
  intro lam
  refine ⟨(h₁ lam).1.add (h₂ lam).1, (h₁ lam).2.1.add (h₂ lam).2.1, ?_, ?_⟩
  · intro t
    change Gf₁ lam (t : ℂ) + Gf₂ lam (t : ℂ) =
      W.toWightmanStruct.compatApply lam (W.boost t (Φ₁ + Φ₂))
    calc
      Gf₁ lam (t : ℂ) + Gf₂ lam (t : ℂ) =
          W.toWightmanStruct.compatApply lam (W.boost t Φ₁) +
            W.toWightmanStruct.compatApply lam (W.boost t Φ₂) := by
        rw [(h₁ lam).2.2.1 t, (h₂ lam).2.2.1 t]
      _ = W.toWightmanStruct.compatApply lam
          (W.boost t Φ₁ + W.boost t Φ₂) :=
        ((W.toWightmanStruct.compatApply_linear lam (W.boost t Φ₁)
          (W.boost t Φ₂)).1).symm
      _ = W.toWightmanStruct.compatApply lam (W.boost t (Φ₁ + Φ₂)) := by
        rw [(W.boost_linear t Φ₁ Φ₂).1]
  · intro t
    change Gf₁ lam (τ + (t : ℂ)) + Gf₂ lam (τ + (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost t (Ψ₁ + Ψ₂))
    calc
      Gf₁ lam (τ + (t : ℂ)) + Gf₂ lam (τ + (t : ℂ)) =
          W.toWightmanStruct.compatApply lam (W.boost t Ψ₁) +
            W.toWightmanStruct.compatApply lam (W.boost t Ψ₂) := by
        rw [(h₁ lam).2.2.2 t, (h₂ lam).2.2.2 t]
      _ = W.toWightmanStruct.compatApply lam
          (W.boost t Ψ₁ + W.boost t Ψ₂) :=
        ((W.toWightmanStruct.compatApply_linear lam (W.boost t Ψ₁)
          (W.boost t Ψ₂)).1).symm
      _ = W.toWightmanStruct.compatApply lam (W.boost t (Ψ₁ + Ψ₂)) := by
        rw [(W.boost_linear t Ψ₁ Ψ₂).1]

/-- [T26], Definition 3.1; continuations are homogeneous. -/
theorem IsBoostContinuation.smul {W : WightmanData G TF 𝓓 𝓕} {τ : ℂ}
    {Φ Ψ : 𝓓} {Gf : W.toWightmanStruct.Compat → ℂ → ℂ} (c : ℂ)
    (h : W.IsBoostContinuation τ Φ Ψ Gf) :
    W.IsBoostContinuation τ (c • Φ) (c • Ψ) (fun lam z => c * Gf lam z) := by
  intro lam
  refine ⟨(continuousOn_const : ContinuousOn (fun _ : ℂ => c) (strip τ)).mul
      (h lam).1, (h lam).2.1.const_mul c, ?_, ?_⟩
  · intro t
    change c * Gf lam (t : ℂ) =
      W.toWightmanStruct.compatApply lam (W.boost t (c • Φ))
    calc
      c * Gf lam (t : ℂ) =
          c * W.toWightmanStruct.compatApply lam (W.boost t Φ) := by
        rw [(h lam).2.2.1 t]
      _ = c • W.toWightmanStruct.compatApply lam (W.boost t Φ) := by
        rw [smul_eq_mul]
      _ = W.toWightmanStruct.compatApply lam (c • W.boost t Φ) :=
        ((W.toWightmanStruct.compatApply_linear lam (W.boost t Φ)
          (W.boost t Φ)).2 c).symm
      _ = W.toWightmanStruct.compatApply lam (W.boost t (c • Φ)) := by
        rw [(W.boost_linear t Φ Φ).2 c]
  · intro t
    change c * Gf lam (τ + (t : ℂ)) =
      W.toWightmanStruct.compatApply lam (W.boost t (c • Ψ))
    calc
      c * Gf lam (τ + (t : ℂ)) =
          c * W.toWightmanStruct.compatApply lam (W.boost t Ψ) := by
        rw [(h lam).2.2.2 t]
      _ = c • W.toWightmanStruct.compatApply lam (W.boost t Ψ) := by
        rw [smul_eq_mul]
      _ = W.toWightmanStruct.compatApply lam (c • W.boost t Ψ) :=
        ((W.toWightmanStruct.compatApply_linear lam (W.boost t Ψ)
          (W.boost t Ψ)).2 c).symm
      _ = W.toWightmanStruct.compatApply lam (W.boost t (c • Ψ)) := by
        rw [(W.boost_linear t Ψ Ψ).2 c]

/-- [T26], Definition 3.1; `D(Ṽ_τ)` is a complex subspace of `𝓓`. -/
def vtildeDomain (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) : Submodule ℂ 𝓓 where
  carrier := {Φ : 𝓓 | W.VtildeDom τ Φ}
  zero_mem' := by
    refine ⟨0, ?_⟩
    exact ⟨fun _ _ => 0, isBoostContinuation_zero W τ⟩
  add_mem' := by
    intro Φ₁ Φ₂ h₁ h₂
    rcases h₁ with ⟨Ψ₁, Gf₁, h₁⟩
    rcases h₂ with ⟨Ψ₂, Gf₂, h₂⟩
    refine ⟨Ψ₁ + Ψ₂, ?_⟩
    exact ⟨fun lam z => Gf₁ lam z + Gf₂ lam z, h₁.add h₂⟩
  smul_mem' := by
    intro c Φ hΦ
    rcases hΦ with ⟨Ψ, Gf, hGf⟩
    refine ⟨c • Ψ, ?_⟩
    exact ⟨fun lam z => c * Gf lam z, hGf.smul c⟩

/-- [T26], Definition 3.1; membership in the subspace is membership in the domain. -/
theorem mem_vtildeDomain (W : WightmanData G TF 𝓓 𝓕) (τ : ℂ) (Φ : 𝓓) :
    Φ ∈ W.vtildeDomain τ ↔ W.VtildeDom τ Φ := by
  rfl

/-- [T26], Definition 3.1; `Ṽ_τ` is additive on its domain. -/
theorem vtildeMap_add (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} {Φ₁ Φ₂ : 𝓓}
    (h₁ : W.VtildeDom τ Φ₁) (h₂ : W.VtildeDom τ Φ₂) :
    W.vtildeMap τ (Φ₁ + Φ₂) = W.vtildeMap τ Φ₁ + W.vtildeMap τ Φ₂ := by
  apply W.vtildeMap_eq hreg
  obtain ⟨Gf₁, hGf₁⟩ := W.vtildeVal_vtildeMap hreg h₁
  obtain ⟨Gf₂, hGf₂⟩ := W.vtildeVal_vtildeMap hreg h₂
  exact ⟨fun lam z => Gf₁ lam z + Gf₂ lam z, hGf₁.add hGf₂⟩

/-- [T26], Definition 3.1; `Ṽ_τ` is homogeneous on its domain. -/
theorem vtildeMap_smul (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) {τ : ℂ} (c : ℂ) {Φ : 𝓓}
    (h : W.VtildeDom τ Φ) :
    W.vtildeMap τ (c • Φ) = c • W.vtildeMap τ Φ := by
  apply W.vtildeMap_eq hreg
  obtain ⟨Gf, hGf⟩ := W.vtildeVal_vtildeMap hreg h
  exact ⟨fun lam z => c * Gf lam z, hGf.smul c⟩

/-- [T26], Definition 3.1; `Ṽ_τ 0 = 0`. -/
theorem vtildeMap_zero (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) (τ : ℂ) :
    W.vtildeMap τ 0 = 0 := by
  apply W.vtildeMap_eq hreg
  exact ⟨fun _ _ => 0, isBoostContinuation_zero W τ⟩

/-- [T26], Definition 3.1; the partially defined operator `Ṽ_τ` as a mathlib `LinearPMap`,
with domain exactly `D(Ṽ_τ)` and action exactly `Ṽ_τ`. Regularity is needed because without
separation of points the companion vector is not determined, so there is no operator to package. -/
noncomputable def vtildePMap (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) (τ : ℂ) : 𝓓 →ₗ.[ℂ] 𝓓 where
  domain := W.vtildeDomain τ
  toFun :=
    { toFun := fun Φ => W.vtildeMap τ (Φ : 𝓓)
      map_add' := by
        intro Φ₁ Φ₂
        change W.vtildeMap τ ((Φ₁ : 𝓓) + (Φ₂ : 𝓓)) =
          W.vtildeMap τ (Φ₁ : 𝓓) + W.vtildeMap τ (Φ₂ : 𝓓)
        apply W.vtildeMap_add hreg
        · exact (mem_vtildeDomain W τ (Φ₁ : 𝓓)).mp Φ₁.property
        · exact (mem_vtildeDomain W τ (Φ₂ : 𝓓)).mp Φ₂.property
      map_smul' := by
        intro c Φ
        change W.vtildeMap τ (c • (Φ : 𝓓)) =
          RingHom.id ℂ c • W.vtildeMap τ (Φ : 𝓓)
        simpa only [RingHom.id_apply] using
          W.vtildeMap_smul hreg c
            ((mem_vtildeDomain W τ (Φ : 𝓓)).mp Φ.property) }

/-- [T26], Definition 3.1; the packaged operator has exactly the intended domain. -/
theorem vtildePMap_domain (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) (τ : ℂ) :
    (W.vtildePMap hreg τ).domain = W.vtildeDomain τ := rfl

/-- [T26], Definition 3.1; the packaged operator has exactly the intended action. -/
theorem vtildePMap_apply (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) (τ : ℂ) (Φ : W.vtildeDomain τ) :
    W.vtildePMap hreg τ Φ = W.vtildeMap τ (Φ : 𝓓) := rfl

/-- [T26], Definition 3.1; membership in the packaged operator's domain is exactly membership
in `D(Ṽ_τ)`. -/
theorem mem_vtildePMap_domain (W : WightmanData G TF 𝓓 𝓕)
    (hreg : W.toWightmanStruct.ActsRegularly) (τ : ℂ) (Φ : 𝓓) :
    Φ ∈ (W.vtildePMap hreg τ).domain ↔ W.VtildeDom τ Φ := by
  rw [vtildePMap_domain W hreg τ]
  exact mem_vtildeDomain W τ Φ

end WightmanData

end MobiusCPT
