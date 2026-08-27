import MobiusCPT.Wightman.TestFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace MobiusCPT

variable {TF 𝓓 𝓕 : Type*}
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF] [TestFunctions TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- [T26], Definition 2.5: the data of a Möbius-covariant Wightman CFT, minus the
Möbius representation and axioms (W1)–(W4), which are added in a later module. -/
structure WightmanStruct (TF : Type*) [AddCommGroup TF] [Module ℂ TF]
    [TopologicalSpace TF] [TestFunctions TF] (𝓓 : Type*) [AddCommGroup 𝓓]
    [Module ℂ 𝓓] (𝓕 : Type*) where
  /-- [T26], Definition 2.5 (W1): the conformal dimension, represented by naturals. -/
  dim : 𝓕 → ℕ
  /-- [T26], Definition 2.5: the smeared field, linear in the test function. -/
  smear : 𝓕 → TF →ₗ[ℂ] (𝓓 →ₗ[ℂ] 𝓓)
  /-- [T26], Definition 2.5: the vacuum vector `Ω`. -/
  vac : 𝓓

namespace WightmanStruct

/-- [T26], §2: the smeared field is linear in the domain vector. -/
theorem smear_linear
    (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (φ : 𝓕) (f : TF) (Φ Ψ : 𝓓),
      (W.smear φ f (Φ + Ψ) = W.smear φ f Φ + W.smear φ f Ψ) ∧
        (∀ c : ℂ, W.smear φ f (c • Φ) = c • W.smear φ f Φ) := by
  intro φ f Φ Ψ
  exact ⟨(W.smear φ f).map_add Φ Ψ, fun c => (W.smear φ f).map_smul c Φ⟩

/-- [T26], §2: the smeared field is linear in the test function. -/
theorem smear_addLinear
    (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (φ : 𝓕) (f g : TF) (Φ : 𝓓),
      (W.smear φ (f + g) Φ = W.smear φ f Φ + W.smear φ g Φ) ∧
        (∀ c : ℂ, W.smear φ (c • f) Φ = c • W.smear φ f Φ) := by
  intro φ f g Φ
  constructor
  · simp
  · intro c
    simp

/-- [T26], §2: the left-to-right product `φ₁(f₁)⋯φ_k(f_k)` acting on `Φ`. -/
def smearedProductOn (W : WightmanStruct TF 𝓓 𝓕)
    (l : List (𝓕 × TF)) (Φ : 𝓓) : 𝓓 :=
  l.foldr (fun p acc => W.smear p.1 p.2 acc) Φ

/-- [T26], §2: the left-to-right product `φ₁(f₁)⋯φ_k(f_k)Ω`. -/
def smearedProduct (W : WightmanStruct TF 𝓓 𝓕)
    (l : List (𝓕 × TF)) : 𝓓 :=
  W.smearedProductOn l W.vac

/-- [T26], §2: the empty product acting on a domain vector is that vector. -/
theorem smearedProductOn_nil (W : WightmanStruct TF 𝓓 𝓕)
    (Φ : 𝓓) : W.smearedProductOn [] Φ = Φ := rfl

/-- [T26], §2: a cons product acts on the product to its right. -/
theorem smearedProductOn_cons (W : WightmanStruct TF 𝓓 𝓕)
    (p : 𝓕 × TF) (l : List (𝓕 × TF)) (Φ : 𝓓) :
    W.smearedProductOn (p :: l) Φ = W.smear p.1 p.2 (W.smearedProductOn l Φ) := rfl

/-- [T26], §2: the empty smeared product is the vacuum. -/
theorem smearedProduct_nil (W : WightmanStruct TF 𝓓 𝓕) :
    W.smearedProduct [] = W.vac := rfl

/-- [T26], §2: cons acts on the product to its right. -/
theorem smearedProduct_cons (W : WightmanStruct TF 𝓓 𝓕)
    (p : 𝓕 × TF) (l : List (𝓕 × TF)) :
    W.smearedProduct (p :: l) = W.smear p.1 p.2 (W.smearedProduct l) := rfl

/-- [T26], §2: a smeared product is linear in the domain vector. -/
theorem smearedProductOn_linear (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (l : List (𝓕 × TF)) (Φ Ψ : 𝓓),
      (W.smearedProductOn l (Φ + Ψ) =
          W.smearedProductOn l Φ + W.smearedProductOn l Ψ) ∧
        (∀ c : ℂ, W.smearedProductOn l (c • Φ) = c • W.smearedProductOn l Φ) := by
  intro l
  induction l with
  | nil =>
      intro Φ Ψ
      simp [smearedProductOn]
  | cons p l ih =>
      intro Φ Ψ
      constructor
      · change W.smear p.1 p.2 (W.smearedProductOn l (Φ + Ψ)) =
          W.smear p.1 p.2 (W.smearedProductOn l Φ) +
            W.smear p.1 p.2 (W.smearedProductOn l Ψ)
        rw [(ih Φ Ψ).1, (W.smear p.1 p.2).map_add]
      · intro c
        change W.smear p.1 p.2 (W.smearedProductOn l (c • Φ)) =
          c • W.smear p.1 p.2 (W.smearedProductOn l Φ)
        rw [(ih Φ Ψ).2 c, (W.smear p.1 p.2).map_smul]

/-- [T26], Definition 2.4: the multilinear map
`S_{φ₁,…,φ_k,Φ}(f₁,…,f_k) = φ₁(f₁)⋯φ_k(f_k)Φ`. -/
def multiSmear (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin k → 𝓕) (Φ : 𝓓) (f : Fin k → TF) : 𝓓 :=
  W.smearedProductOn (List.ofFn fun i => (φs i, f i)) Φ

/-- [T26], Definition 2.4: a functional is compatible when every composition with
`multiSmear` is jointly continuous in the product topology. -/
def IsCompatible (W : WightmanStruct TF 𝓓 𝓕) (lam : 𝓓 →ₗ[ℂ] ℂ) : Prop :=
  ∀ (k : ℕ) (φs : Fin k → 𝓕) (Φ : 𝓓),
    Continuous fun f : Fin k → TF => lam (W.multiSmear φs Φ f)

/-- [T26], Definition 2.4: the space `D*_𝓕` of compatible functionals. -/
def Compat (W : WightmanStruct TF 𝓓 𝓕) : Type _ :=
  { lam : 𝓓 →ₗ[ℂ] ℂ // W.IsCompatible lam }

/-- [T26], Definition 2.4: evaluation of a compatible functional. -/
def compatApply (W : WightmanStruct TF 𝓓 𝓕)
    (lam : W.Compat) (Φ : 𝓓) : ℂ := lam.1 Φ

/-- [T26], §2: compatibility is closed under the complex-linear operations on functionals. -/
def compatSubmodule (W : WightmanStruct TF 𝓓 𝓕) :
    Submodule ℂ (𝓓 →ₗ[ℂ] ℂ) where
  carrier := {lam | W.IsCompatible lam}
  zero_mem' := by
    intro k φs Φ
    simpa [IsCompatible] using
      (continuous_const : Continuous (fun _ : Fin k → TF => (0 : ℂ)))
  add_mem' := by
    intro f g hf hg k φs Φ
    show Continuous (fun x : Fin k → TF =>
      f (W.multiSmear φs Φ x) + g (W.multiSmear φs Φ x))
    exact (hf k φs Φ).add (hg k φs Φ)
  smul_mem' := by
    intro c f hf k φs Φ
    show Continuous (fun x : Fin k → TF => c * f (W.multiSmear φs Φ x))
    exact (continuous_const : Continuous (fun _ : Fin k → TF => c)).mul (hf k φs Φ)

/-- [T26], Definition 2.4: compatible functionals inherit an additive group structure. -/
instance compatAddCommGroup (W : WightmanStruct TF 𝓓 𝓕) : AddCommGroup W.Compat := by
  change AddCommGroup {lam : 𝓓 →ₗ[ℂ] ℂ // lam ∈ W.compatSubmodule}
  infer_instance

/-- [T26], Definition 2.4: compatible functionals form a complex module. -/
instance compatModule (W : WightmanStruct TF 𝓓 𝓕) : Module ℂ W.Compat := by
  change Module ℂ {lam : 𝓓 →ₗ[ℂ] ℂ // lam ∈ W.compatSubmodule}
  infer_instance

/-- [T26], §2: evaluation by a compatible functional is linear on `𝓓`. -/
theorem compatApply_linear (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (lam : W.Compat) (Φ Ψ : 𝓓),
      (W.compatApply lam (Φ + Ψ) = W.compatApply lam Φ + W.compatApply lam Ψ) ∧
        (∀ c : ℂ, W.compatApply lam (c • Φ) = c • W.compatApply lam Φ) := by
  intro lam Φ Ψ
  exact ⟨lam.1.map_add Φ Ψ, fun c => lam.1.map_smul c Φ⟩

/-- [T26], Definition 2.4: `𝓕` acts regularly when compatible functionals detect
every non-zero domain vector. -/
def ActsRegularly (W : WightmanStruct TF 𝓓 𝓕) : Prop :=
  ∀ Φ : 𝓓, Φ ≠ 0 → ∃ lam : W.Compat, W.compatApply lam Φ ≠ 0

/-- [T26], Definition 2.4: regularity is equivalent to separation of domain vectors. -/
theorem actsRegularly_iff (W : WightmanStruct TF 𝓓 𝓕) :
    W.ActsRegularly ↔
      ∀ Φ Ψ : 𝓓,
        (∀ lam : W.Compat, W.compatApply lam Φ = W.compatApply lam Ψ) → Φ = Ψ := by
  classical
  constructor
  · intro h Φ Ψ hΦΨ
    have hsub : Φ - Ψ = 0 := by
      by_contra hne
      obtain ⟨lam, hlam⟩ := h (Φ - Ψ) hne
      apply hlam
      change lam.1 (Φ - Ψ) = 0
      have hEq : lam.1 Φ = lam.1 Ψ := hΦΨ lam
      rw [map_sub, hEq, sub_self]
    exact sub_eq_zero.mp hsub
  · intro h Φ hΦ
    by_contra hnone
    apply hΦ
    apply h Φ 0
    intro lam
    change lam.1 Φ = lam.1 0
    rw [map_zero]
    by_contra hlam
    exact hnone ⟨lam, hlam⟩

/-- [T26], Definition 2.4 and Theorem 3.10: the localized subspace `P(I_+)Ω`. -/
def PUpperOmega (W : WightmanStruct TF 𝓓 𝓕) : Submodule ℂ 𝓓 :=
  Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
    (∀ p ∈ l, TestFunctions.SuppUpper p.2) ∧ Φ = W.smearedProduct l }

/-- [T26], Definition 2.4 and Theorem 3.10: membership in `P(I_+)Ω`. -/
def MemPUpperOmega (W : WightmanStruct TF 𝓓 𝓕) (Φ : 𝓓) : Prop :=
  Φ ∈ W.PUpperOmega

/-- [T26], Definition 2.4 and Theorem 3.10: the localized subspace `P(I_-)Ω`. -/
def PLowerOmega (W : WightmanStruct TF 𝓓 𝓕) : Submodule ℂ 𝓓 :=
  Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
    (∀ p ∈ l, TestFunctions.SuppLower p.2) ∧ Φ = W.smearedProduct l }

/-- [T26], Definition 2.4 and Theorem 3.10: membership in `P(I_-)Ω`. -/
def MemPLowerOmega (W : WightmanStruct TF 𝓓 𝓕) (Φ : 𝓓) : Prop :=
  Φ ∈ W.PLowerOmega

/-- [T26], Definition 2.4 and Theorem 3.10: upper membership is exactly a finite
complex-linear combination of upper-supported smeared products. -/
theorem memPUpperOmega_iff (W : WightmanStruct TF 𝓓 𝓕) (Φ : 𝓓) :
    W.MemPUpperOmega Φ ↔
      ∃ (n : ℕ) (c : Fin n → ℂ) (ls : Fin n → List (𝓕 × TF)),
        (∀ i, ∀ p ∈ ls i, TestFunctions.SuppUpper p.2) ∧
          Φ = ∑ i, c i • W.smearedProduct (ls i) := by
  constructor
  · intro h
    change Φ ∈ Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
      (∀ p ∈ l, TestFunctions.SuppUpper p.2) ∧ Φ = W.smearedProduct l } at h
    rcases (Submodule.mem_span_set'.mp h) with ⟨n, c, g, hsum⟩
    let ls : Fin n → List (𝓕 × TF) := fun i => (g i).property.choose
    have hls_spec : ∀ i,
        (∀ p ∈ ls i, TestFunctions.SuppUpper p.2) ∧
          (g i : 𝓓) = W.smearedProduct (ls i) := by
      intro i
      dsimp [ls]
      exact (g i).property.choose_spec
    refine ⟨n, c, ls, ?_, ?_⟩
    · intro i p hp
      exact (hls_spec i).1 p hp
    · calc
        Φ = ∑ i, c i • (g i : 𝓓) := hsum.symm
        _ = ∑ i, c i • W.smearedProduct (ls i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun x : 𝓓 => c i • x) (hls_spec i).2
  · rintro ⟨n, c, ls, hls, rfl⟩
    change (∑ i, c i • W.smearedProduct (ls i)) ∈
      Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
        (∀ p ∈ l, TestFunctions.SuppUpper p.2) ∧ Φ = W.smearedProduct l }
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ls i, hls i, rfl⟩))

/-- [T26], Definition 2.4 and Theorem 3.10: lower membership is exactly a finite
complex-linear combination of lower-supported smeared products. -/
theorem memPLowerOmega_iff (W : WightmanStruct TF 𝓓 𝓕) (Φ : 𝓓) :
    W.MemPLowerOmega Φ ↔
      ∃ (n : ℕ) (c : Fin n → ℂ) (ls : Fin n → List (𝓕 × TF)),
        (∀ i, ∀ p ∈ ls i, TestFunctions.SuppLower p.2) ∧
          Φ = ∑ i, c i • W.smearedProduct (ls i) := by
  constructor
  · intro h
    change Φ ∈ Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
      (∀ p ∈ l, TestFunctions.SuppLower p.2) ∧ Φ = W.smearedProduct l } at h
    rcases (Submodule.mem_span_set'.mp h) with ⟨n, c, g, hsum⟩
    let ls : Fin n → List (𝓕 × TF) := fun i => (g i).property.choose
    have hls_spec : ∀ i,
        (∀ p ∈ ls i, TestFunctions.SuppLower p.2) ∧
          (g i : 𝓓) = W.smearedProduct (ls i) := by
      intro i
      dsimp [ls]
      exact (g i).property.choose_spec
    refine ⟨n, c, ls, ?_, ?_⟩
    · intro i p hp
      exact (hls_spec i).1 p hp
    · calc
        Φ = ∑ i, c i • (g i : 𝓓) := hsum.symm
        _ = ∑ i, c i • W.smearedProduct (ls i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun x : 𝓓 => c i • x) (hls_spec i).2
  · rintro ⟨n, c, ls, hls, rfl⟩
    change (∑ i, c i • W.smearedProduct (ls i)) ∈
      Submodule.span ℂ { Φ | ∃ l : List (𝓕 × TF),
        (∀ p ∈ l, TestFunctions.SuppLower p.2) ∧ Φ = W.smearedProduct l }
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨ls i, hls i, rfl⟩))

/-- [T26], Definition 2.4: the upper localized subspace is closed under addition. -/
theorem memPUpperOmega_add (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (Φ Ψ : 𝓓), W.MemPUpperOmega Φ → W.MemPUpperOmega Ψ →
      W.MemPUpperOmega (Φ + Ψ) := by
  intro Φ Ψ hΦ hΨ
  exact W.PUpperOmega.add_mem hΦ hΨ

/-- [T26], Definition 2.4: the upper localized subspace is closed under complex scalars. -/
theorem memPUpperOmega_smul (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (c : ℂ) (Φ : 𝓓), W.MemPUpperOmega Φ → W.MemPUpperOmega (c • Φ) := by
  intro c Φ hΦ
  exact W.PUpperOmega.smul_mem c hΦ

/-- [T26], Definition 2.4: the lower localized subspace is closed under addition. -/
theorem memPLowerOmega_add (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (Φ Ψ : 𝓓), W.MemPLowerOmega Φ → W.MemPLowerOmega Ψ →
      W.MemPLowerOmega (Φ + Ψ) := by
  intro Φ Ψ hΦ hΨ
  exact W.PLowerOmega.add_mem hΦ hΨ

/-- [T26], Definition 2.4: the lower localized subspace is closed under complex scalars. -/
theorem memPLowerOmega_smul (W : WightmanStruct TF 𝓓 𝓕) :
    ∀ (c : ℂ) (Φ : 𝓓), W.MemPLowerOmega Φ → W.MemPLowerOmega (c • Φ) := by
  intro c Φ hΦ
  exact W.PLowerOmega.smul_mem c hΦ

/-- [T26], §2 and Theorem 3.10: the empty product puts the vacuum in `P(I_+)Ω`. -/
theorem memPUpperOmega_vac (W : WightmanStruct TF 𝓓 𝓕) :
    W.MemPUpperOmega W.vac := by
  change W.vac ∈ W.PUpperOmega
  apply Submodule.subset_span
  exact ⟨[], by simp, rfl⟩

/-- [T26], §2 and Theorem 3.10: the empty product puts the vacuum in `P(I_-)Ω`. -/
theorem memPLowerOmega_vac (W : WightmanStruct TF 𝓓 𝓕) :
    W.MemPLowerOmega W.vac := by
  change W.vac ∈ W.PLowerOmega
  apply Submodule.subset_span
  exact ⟨[], by simp, rfl⟩

end WightmanStruct

end MobiusCPT
