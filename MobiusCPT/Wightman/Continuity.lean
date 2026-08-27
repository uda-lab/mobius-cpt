import MobiusCPT.Wightman.Basic
import MobiusCPT.TestFunctions.Complete
import MobiusCPT.TestFunctions.WightmanInstance
import MobiusCPT.Analysis.SeparateJoint

/-!
# MobiusCPT.Wightman.Continuity

The joint-versus-separate continuity adapter of [T26], Definition 2.4 and [CRTT25],
Definition 2.5.

[T26] defines compatibility of `λ ∈ 𝓓*` by **joint** continuity of
`(f₁,…,f_k) ↦ λ(φ₁(f₁)⋯φ_k(f_k)Φ)`; [CRTT25] uses **separate** continuity and records that
the two agree because `C^∞(S¹)` is Fréchet ([Trèves, Cor. 34.2]).  `WightmanStruct.IsCompatible`
is the [T26] reading and `WightmanStruct.IsCompatibleSep` is the [CRTT25] one.

Joint ⟹ separate holds over any `TestFunctions` interface.  The converse is the content of
this file and is proved over the concrete `TestFn`, where
`MobiusCPT.MultilinearMap.continuous_of_continuous_update` applies because
`MobiusCPT.TestFunctions.Complete` makes `TestFn` barrelled and
`MobiusCPT.TestFunctions.CNorm` makes it first countable.  The consequence that matters
downstream is `actsRegularly_iff_actsRegularlySep`: the regularity hypothesis this development
assumes is exactly the source's, not a strictly stronger one.
-/

namespace MobiusCPT

variable {TF 𝓓 𝓕 : Type*}
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF] [TestFunctions TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanStruct

/-- [T26], Definition 2.4: a nonempty `multiSmear` splits into its first field and tail. -/
theorem multiSmear_succ (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin (k + 1) → 𝓕) (Φ : 𝓓) (f : Fin (k + 1) → TF) :
    W.multiSmear φs Φ f =
      W.smear (φs 0) (f 0) (W.multiSmear (Fin.tail φs) Φ (Fin.tail f)) := by
  unfold multiSmear
  rw [List.ofFn_succ, smearedProductOn_cons]
  rfl

/-- [T26], Definition 2.4: `multiSmear` is additive in each test-function slot. -/
theorem multiSmear_update_add (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin k → 𝓕) (Φ : 𝓓) (f : Fin k → TF) (i : Fin k) (x y : TF) :
    W.multiSmear φs Φ (Function.update f i (x + y)) =
      W.multiSmear φs Φ (Function.update f i x) +
        W.multiSmear φs Φ (Function.update f i y) := by
  induction k with
  | zero =>
      exact Fin.elim0 i
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [multiSmear_succ, multiSmear_succ, multiSmear_succ]
        simp only [Function.update_self, Fin.tail_update_zero]
        rw [(W.smear (φs 0)).map_add]
        rfl
      · rw [multiSmear_succ, multiSmear_succ, multiSmear_succ]
        simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)),
          Fin.tail_update_succ]
        rw [ih (φs := Fin.tail φs) (f := Fin.tail f) (i := j)]
        exact (W.smear (φs 0) (f 0)).map_add _ _

/-- [T26], Definition 2.4: `multiSmear` is homogeneous in each test-function slot. -/
theorem multiSmear_update_smul (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin k → 𝓕) (Φ : 𝓓) (f : Fin k → TF) (i : Fin k) (c : ℂ) (x : TF) :
    W.multiSmear φs Φ (Function.update f i (c • x)) =
      c • W.multiSmear φs Φ (Function.update f i x) := by
  induction k with
  | zero =>
      exact Fin.elim0 i
  | succ k ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [multiSmear_succ, multiSmear_succ]
        simp only [Function.update_self, Fin.tail_update_zero]
        rw [(W.smear (φs 0)).map_smul]
        rfl
      · rw [multiSmear_succ, multiSmear_succ]
        simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j)),
          Fin.tail_update_succ]
        rw [ih (φs := Fin.tail φs) (f := Fin.tail f) (i := j)]
        exact (W.smear (φs 0) (f 0)).map_smul c _

/-- [T26], Definition 2.4: the smeared product bundled as a multilinear map in its
test functions. -/
def multiSmearMultilinear (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin k → 𝓕) (Φ : 𝓓) :
    MultilinearMap ℂ (fun _ : Fin k => TF) 𝓓 :=
  MultilinearMap.mk' (W.multiSmear φs Φ)
    (fun f i x y => W.multiSmear_update_add φs Φ f i x y)
    (fun f i c x => W.multiSmear_update_smul φs Φ f i c x)

/-- [T26], Definition 2.4: the bundled multilinear map evaluates to `multiSmear`. -/
@[simp] theorem multiSmearMultilinear_apply (W : WightmanStruct TF 𝓓 𝓕) {k : ℕ}
    (φs : Fin k → 𝓕) (Φ : 𝓓) (f : Fin k → TF) :
    W.multiSmearMultilinear φs Φ f = W.multiSmear φs Φ f := rfl

/-- [CRTT25], Definition 2.5: compatibility with separate continuity in each test
function. -/
def IsCompatibleSep (W : WightmanStruct TF 𝓓 𝓕) (lam : 𝓓 →ₗ[ℂ] ℂ) : Prop :=
  ∀ (k : ℕ) (φs : Fin k → 𝓕) (Φ : 𝓓) (i : Fin k) (g : Fin k → TF),
    Continuous fun x : TF => lam (W.multiSmear φs Φ (Function.update g i x))

/-- [T26], Definition 2.4 and [CRTT25], Definition 2.5: joint continuity implies
separate continuity over any test-function interface. -/
theorem isCompatibleSep_of_isCompatible (W : WightmanStruct TF 𝓓 𝓕)
    (lam : 𝓓 →ₗ[ℂ] ℂ) (h : W.IsCompatible lam) : W.IsCompatibleSep lam := by
  intro k φs Φ i g
  have hupdate : Continuous (fun x : TF => Function.update g i x) :=
    (continuous_const : Continuous (fun _ : TF => g)).update i continuous_id
  exact (h k φs Φ).comp hupdate

/-- [Trèves, Corollary 34.2] via
`MobiusCPT.MultilinearMap.continuous_of_continuous_update`: over the Fréchet space
`C^∞(S¹)`, separate continuity implies joint continuity, so the [CRTT25] reading of
`D*_𝓕` implies the [T26] reading. -/
theorem isCompatible_of_isCompatibleSep {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) (lam : 𝓓 →ₗ[ℂ] ℂ)
    (h : W.IsCompatibleSep lam) : W.IsCompatible lam := by
  intro k φs Φ
  let M : MultilinearMap ℂ (fun _ : Fin k => TestFn) ℂ :=
    lam.compMultilinearMap (W.multiSmearMultilinear φs Φ)
  have hM : Continuous M :=
    MobiusCPT.MultilinearMap.continuous_of_continuous_update M (by
      intro i g
      simpa only [M, LinearMap.compMultilinearMap_apply,
        multiSmearMultilinear_apply] using h k φs Φ i g)
  exact hM.congr fun f => rfl

/-- [T26], Definition 2.4 and [CRTT25], Definition 2.5 define the same `D*_𝓕`. -/
theorem isCompatible_iff_isCompatibleSep {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) (lam : 𝓓 →ₗ[ℂ] ℂ) :
    W.IsCompatible lam ↔ W.IsCompatibleSep lam :=
  ⟨W.isCompatibleSep_of_isCompatible lam, W.isCompatible_of_isCompatibleSep lam⟩

/-- [T26], Definition 2.4 and [CRTT25], Definition 2.5 give the same set of
compatible functionals. -/
theorem setOf_isCompatible_eq {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) :
    {lam : 𝓓 →ₗ[ℂ] ℂ | W.IsCompatible lam} = {lam | W.IsCompatibleSep lam} := by
  apply Set.ext
  intro lam
  exact W.isCompatible_iff_isCompatibleSep lam

/-- [CRTT25], Definition 2.5: regularity stated with the separate-continuity
`D*_𝓕`. -/
def ActsRegularlySep (W : WightmanStruct TF 𝓓 𝓕) : Prop :=
  ∀ Φ : 𝓓, Φ ≠ 0 → ∃ lam : 𝓓 →ₗ[ℂ] ℂ, W.IsCompatibleSep lam ∧ lam Φ ≠ 0

/-- [T26], Definition 2.4 and [CRTT25], Definition 2.5 impose the same regularity
hypothesis, so downstream theorems assuming `ActsRegularly` have the source hypothesis. -/
theorem actsRegularly_iff_actsRegularlySep {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) :
    W.ActsRegularly ↔ W.ActsRegularlySep := by
  constructor
  · intro h Φ hΦ
    obtain ⟨lam, hlam⟩ := h Φ hΦ
    refine ⟨lam.1, (W.isCompatible_iff_isCompatibleSep lam.1).mp lam.2, ?_⟩
    change lam.1 Φ ≠ 0 at hlam
    exact hlam
  · intro h Φ hΦ
    obtain ⟨lam, hsep, hlam⟩ := h Φ hΦ
    refine ⟨⟨lam, (W.isCompatible_iff_isCompatibleSep lam).mpr hsep⟩, ?_⟩
    change lam Φ ≠ 0
    exact hlam

/-- [CRTT25], Definition 2.5: the separate-continuity form of the
separation-of-points characterisation. -/
theorem actsRegularlySep_iff {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) :
    W.ActsRegularlySep ↔
      ∀ Φ Ψ : 𝓓,
        (∀ lam : 𝓓 →ₗ[ℂ] ℂ,
          W.IsCompatibleSep lam → lam Φ = lam Ψ) → Φ = Ψ := by
  constructor
  · intro h Φ Ψ hΦΨ
    have hsub : Φ - Ψ = 0 := by
      by_contra hne
      obtain ⟨lam, hsep, hlam⟩ := h (Φ - Ψ) hne
      apply hlam
      rw [map_sub, hΦΨ lam hsep, sub_self]
    exact sub_eq_zero.mp hsub
  · intro h Φ hΦ
    by_contra hnone
    apply hΦ
    apply h Φ 0
    intro lam hsep
    rw [map_zero]
    by_contra hlam
    exact hnone ⟨lam, hsep, hlam⟩

end WightmanStruct

end MobiusCPT
