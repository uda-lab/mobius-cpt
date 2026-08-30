import MobiusCPT.Wightman.Basic

/-!
# Passing (W2) locality through a test-function limit

[T26]'s proof of Lemma 3.7(ii) needs (W2) between an operator smeared with a fixed test
function `f` and one smeared with a test function on the *opposite* semicircle that only
touches `f`'s support at the shared endpoints `±1` — a case (W2) does not cover directly,
since `W2` is stated for genuinely disjoint supports (`TestFunctions.DisjointSupp`), and
`SuppUpper f ∧ SuppLower g` does **not** imply `DisjointSupport f g` under this repository's
open-semicircle convention (`MobiusCPT.TestFunctions.Support`).

The route, from the owner's second proof-engineering bridge (Issue #9, 2026-08-28): approximate
the endpoint-touching test function by a sequence `g_m` compactly supported strictly inside the
open semicircle (so `DisjointSupp f (g_m)` genuinely holds), apply (W2) at each `g_m`, and pass
to the limit *scalarly* through every compatible functional — never assuming a direct vector
limit in `𝓓`, which the abstract interface does not supply. Regularity then upgrades the
resulting scalar identity, which holds for every compatible functional, to the vector identity.

This module proves the general limit-passing lemma; it takes the approximating sequence `g_m`
and its two per-step hypotheses (disjoint support at each `m`, convergence to `g` in the ambient
test-function topology) as given, and does not itself construct such a sequence — that
construction is [T26]'s endpoint cutoff, a separate piece.
-/

namespace MobiusCPT

namespace WightmanStruct

open Filter

variable {TF 𝓓 𝓕 : Type*} [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- Continuity, in the second test-function slot alone, of the scalar two-field smeared product
`g' ↦ λ(φ₁(f) φ₂(g') Ψ)`, for a compatible `λ`. This is the `k = 2` joint-continuity clause of
`IsCompatible`, restricted along the continuous coordinate embedding that holds the first slot
fixed at `f`. -/
theorem continuous_compatApply_smear_smear_snd (W : WightmanStruct TF 𝓓 𝓕)
    (lam : W.Compat) (φ₁ φ₂ : 𝓕) (f : TF) (Ψ : 𝓓) :
    Continuous fun g' : TF =>
      lam.1 (W.smear φ₁ f (W.smear φ₂ g' Ψ)) := by
  have hjoint : Continuous fun x : Fin 2 → TF =>
      lam.1 (W.multiSmear ![φ₁, φ₂] Ψ x) := lam.2 2 ![φ₁, φ₂] Ψ
  have hemb : Continuous fun g' : TF => (![f, g'] : Fin 2 → TF) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using continuous_const
    · simpa using continuous_id'
  have hcomp := hjoint.comp hemb
  refine hcomp.congr fun g' => ?_
  simp only [Function.comp_apply, multiSmear, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    W.smearedProductOn_cons, W.smearedProductOn_nil]

/-- Continuity, in the first test-function slot alone, of the scalar two-field smeared product
`g' ↦ λ(φ₂(g') φ₁(f) Ψ)`, the mirror of `continuous_compatApply_smear_smear_snd` with the two
fields in the opposite order. -/
theorem continuous_compatApply_smear_smear_fst (W : WightmanStruct TF 𝓓 𝓕)
    (lam : W.Compat) (φ₁ φ₂ : 𝓕) (f : TF) (Ψ : 𝓓) :
    Continuous fun g' : TF =>
      lam.1 (W.smear φ₂ g' (W.smear φ₁ f Ψ)) := by
  have hjoint : Continuous fun x : Fin 2 → TF =>
      lam.1 (W.multiSmear ![φ₂, φ₁] Ψ x) := lam.2 2 ![φ₂, φ₁] Ψ
  have hemb : Continuous fun g' : TF => (![g', f] : Fin 2 → TF) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using continuous_id'
    · simpa using continuous_const
  have hcomp := hjoint.comp hemb
  refine hcomp.congr fun g' => ?_
  simp only [Function.comp_apply, multiSmear, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one,
    W.smearedProductOn_cons, W.smearedProductOn_nil]

/-- **The (W2)-through-a-limit bridge, scalar form.** If a sequence `g_m` of test functions has
disjoint support from `f` at every finite stage and converges to `g` in the ambient test-function
topology, then the two orders of smearing by `f` and by `g` agree once composed with any
compatible functional — even though `f` and `g` themselves need not have disjoint support. -/
theorem compatApply_smear_comm_of_tendsto (W : WightmanStruct TF 𝓓 𝓕) (hW2 : W.W2)
    (φ₁ φ₂ : 𝓕) (f : TF) {g : ℕ → TF} {gLim : TF} (hg : Tendsto g atTop (nhds gLim))
    (hdisj : ∀ m, TestFunctions.DisjointSupp f (g m)) (Ψ : 𝓓) (lam : W.Compat) :
    lam.1 (W.smear φ₁ f (W.smear φ₂ gLim Ψ)) =
      lam.1 (W.smear φ₂ gLim (W.smear φ₁ f Ψ)) := by
  have hL : Tendsto (fun m => lam.1 (W.smear φ₁ f (W.smear φ₂ (g m) Ψ))) atTop
      (nhds (lam.1 (W.smear φ₁ f (W.smear φ₂ gLim Ψ)))) :=
    ((W.continuous_compatApply_smear_smear_snd lam φ₁ φ₂ f Ψ).continuousAt).tendsto.comp hg
  have hR : Tendsto (fun m => lam.1 (W.smear φ₂ (g m) (W.smear φ₁ f Ψ))) atTop
      (nhds (lam.1 (W.smear φ₂ gLim (W.smear φ₁ f Ψ)))) :=
    ((W.continuous_compatApply_smear_smear_fst lam φ₁ φ₂ f Ψ).continuousAt).tendsto.comp hg
  have hEq : ∀ m, lam.1 (W.smear φ₁ f (W.smear φ₂ (g m) Ψ)) =
      lam.1 (W.smear φ₂ (g m) (W.smear φ₁ f Ψ)) :=
    fun m => congrArg lam.1 (hW2 φ₁ φ₂ f (g m) (hdisj m) Ψ)
  exact tendsto_nhds_unique (Tendsto.congr hEq hL) hR

/-- **The (W2)-through-a-limit bridge, vector form.** Under regularity, the scalar identity
above — holding for every compatible functional — upgrades to the vector identity in `𝓓`. -/
theorem smear_comm_of_tendsto (W : WightmanStruct TF 𝓓 𝓕) (hW2 : W.W2) (hreg : W.ActsRegularly)
    (φ₁ φ₂ : 𝓕) (f : TF) {g : ℕ → TF} {gLim : TF} (hg : Tendsto g atTop (nhds gLim))
    (hdisj : ∀ m, TestFunctions.DisjointSupp f (g m)) (Ψ : 𝓓) :
    W.smear φ₁ f (W.smear φ₂ gLim Ψ) = W.smear φ₂ gLim (W.smear φ₁ f Ψ) := by
  apply (W.actsRegularly_iff.mp hreg) _ _
  intro lam
  exact W.compatApply_smear_comm_of_tendsto hW2 φ₁ φ₂ f hg hdisj Ψ lam

end WightmanStruct

end MobiusCPT
