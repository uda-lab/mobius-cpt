import MobiusCPT.TestFunctions.Analytic
import MobiusCPT.TestFunctions.EndpointCutoff
import MobiusCPT.TestFunctions.FourierCauchy
import MobiusCPT.Wightman.Compat
import MobiusCPT.Wightman.LocalityLimit
import MobiusCPT.Wightman.W3Bridge

namespace MobiusCPT

namespace WightmanStruct

/-!
The endpoint cutoff is used only to supply the hypotheses of the abstract locality-through-a-
limit lemma.  In particular, the support assumptions below are the concrete `TestFn` support
predicates, while `smear_comm_of_tendsto` remains generic in the test-function interface.
-/

/-- Concrete in `TestFn`, not generic over the abstract `TestFunctions` class: the
cutoff-sequence existence lemmas this proof needs (`exists_tendsto_of_suppLower`,
`MobiusCPT/TestFunctions/EndpointCutoff.lean`) are proved only for the concrete `TestFn`, not
for an arbitrary type satisfying the abstract `TestFunctions` interface — so this statement
cannot be stated generically over `TF` the way `LocalityLimit.lean`'s lemmas are. Keep `𝓓`,
`𝓕` generic (as `LocalityLimit.smear_comm_of_tendsto` does), fix the test-function type to
`TestFn`. -/
theorem smear_comm_smearedProductOn_of_suppLower_of_forall_suppUpper
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) (hW2 : W.W2) (hreg : W.ActsRegularly)
    (φ : 𝓕) {h : TestFn} (hh : SuppLower h)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2) (Ψ : 𝓓) :
    W.smear φ h (W.smearedProductOn l Ψ) = W.smearedProductOn l (W.smear φ h Ψ) := by
  induction l with
  | nil =>
      simp only [W.smearedProductOn_nil]
  | cons p rest ih =>
      have hp : SuppUpper p.2 := hl p (by simp)
      have hrest : ∀ q ∈ rest, SuppUpper q.2 := by
        intro q hq
        exact hl q (by simp [hq])
      have hIH := ih hrest
      obtain ⟨hSeq, hSeqSupp, hSeqLimit⟩ := exists_tendsto_of_suppLower hh
      have hdisj : ∀ m, TestFunctions.DisjointSupp p.2 (hSeq m) := by
        intro m
        -- The concrete Wightman instance defines `DisjointSupp` to be `DisjointSupport`.
        change DisjointSupport p.2 (hSeq m)
        exact disjointSupport_of_suppUpper_of_tsupport_subset_lowerArc hp (hSeqSupp m)
      have hcomm := W.smear_comm_of_tendsto hW2 hreg p.1 φ p.2 hSeqLimit hdisj
        (W.smearedProductOn rest Ψ)
      simp only [W.smearedProductOn_cons]
      rw [← hIH]
      exact hcomm.symm

end WightmanStruct

namespace WightmanData

/-! `smearedProductOn` is linear in its vacuum/domain-vector argument.  Naming this projection
keeps the sign manipulation in the reverse-list induction readable. -/
private theorem smearedProductOn_smul
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanStruct TestFn 𝓓 𝓕) (l : List (𝓕 × TestFn)) (c : ℂ) (Ψ : 𝓓) :
    W.smearedProductOn l (c • Ψ) = c • W.smearedProductOn l Ψ := by
  exact (W.smearedProductOn_linear l Ψ Ψ).2 c

/-! The vacuum-annihilation bridge applied to the sum of the two endpoint restrictions gives the
sign change.  This is a vector identity, so the additivity used here is in the test-function
slot of `smear`, not the linearity in the vector slot. -/
private theorem smear_inv_xRestrictLower_vac_eq_neg
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (φ : 𝓕) (F : AnalyticTestFn) :
    W.toWightmanStruct.smear φ (inv (xRestrictLower F)) W.toWightmanStruct.vac =
      -W.toWightmanStruct.smear φ (inv (xRestrictUpper F)) W.toWightmanStruct.vac := by
  have hzero := w3_vacuum_annihilation W hW φ F
  change W.toWightmanStruct.smear φ (inv (xRestrictS1 F)) W.toWightmanStruct.vac = 0 at hzero
  rw [xRestrict_split F, inv_add] at hzero
  rw [(W.toWightmanStruct.smear_addLinear φ
    (inv (xRestrictUpper F)) (inv (xRestrictLower F)) W.toWightmanStruct.vac).1] at hzero
  exact eq_neg_of_add_eq_zero_right hzero

theorem smearedProduct_invLower_eq_smearedProduct_invUpper_reverse
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (l : List (𝓕 × AnalyticTestFn)) :
    W.toWightmanStruct.smearedProduct
        (l.map (fun p => (p.1, inv (xRestrictLower p.2)))) =
      (-1 : ℂ) ^ l.length •
        W.toWightmanStruct.smearedProduct
          (l.reverse.map (fun p => (p.1, inv (xRestrictUpper p.2)))) := by
  induction l using List.reverseRecOn with
  | nil =>
      simp only [List.map_nil, List.reverse_nil, List.length_nil, pow_zero, one_smul,
        WightmanStruct.smearedProduct]
  | append_singleton init p ih =>
      rcases p with ⟨φ, F⟩
      have hupper : SuppLower (inv (xRestrictUpper F)) :=
        (inv_supp (xRestrictUpper F)).mp (xRestrictUpper_supp F)
      have hinit :
          ∀ q ∈ init.map (fun p : 𝓕 × AnalyticTestFn =>
            (p.1, inv (xRestrictLower p.2))), SuppUpper q.2 := by
        intro q hq
        obtain ⟨r, _, rfl⟩ := List.mem_map.1 hq
        exact (inv_supp' (xRestrictLower r.2)).mp (xRestrictLower_supp r.2)
      have hcomm :=
        WightmanStruct.smear_comm_smearedProductOn_of_suppLower_of_forall_suppUpper
          W.toWightmanStruct hW.2.2.1 hW.1 φ hupper
          (init.map (fun p : 𝓕 × AnalyticTestFn =>
            (p.1, inv (xRestrictLower p.2)))) hinit W.toWightmanStruct.vac
      have hIH :
          W.toWightmanStruct.smearedProductOn
              (init.map (fun p : 𝓕 × AnalyticTestFn =>
                (p.1, inv (xRestrictLower p.2)))) W.toWightmanStruct.vac =
            (-1 : ℂ) ^ init.length •
              W.toWightmanStruct.smearedProductOn
                (init.reverse.map (fun p : 𝓕 × AnalyticTestFn =>
                  (p.1, inv (xRestrictUpper p.2)))) W.toWightmanStruct.vac := by
        simpa only [WightmanStruct.smearedProduct] using ih
      have hvac := smear_inv_xRestrictLower_vac_eq_neg W hW φ F
      -- `smearedProductOn` is a foldr: after appending `(φ,F)`, that entry is the
      -- operator immediately next to the vacuum.  Reversing the list puts its upper
      -- counterpart at the front, as required by the target convention.
      simp only [WightmanStruct.smearedProduct, List.map_append, List.map_cons, List.map_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append,
        WightmanStruct.smearedProductOn_append, WightmanStruct.smearedProductOn_cons,
        WightmanStruct.smearedProductOn_nil, List.length_append, List.length_cons,
        List.length_nil]
      calc
        W.toWightmanStruct.smearedProductOn
              (init.map (fun p : 𝓕 × AnalyticTestFn =>
                (p.1, inv (xRestrictLower p.2))))
              (W.toWightmanStruct.smear φ (inv (xRestrictLower F))
                W.toWightmanStruct.vac) =
            W.toWightmanStruct.smearedProductOn
              (init.map (fun p : 𝓕 × AnalyticTestFn =>
                (p.1, inv (xRestrictLower p.2))))
              (-W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                W.toWightmanStruct.vac) := by rw [hvac]
        _ = (-1 : ℂ) •
              W.toWightmanStruct.smearedProductOn
                (init.map (fun p : 𝓕 × AnalyticTestFn =>
                  (p.1, inv (xRestrictLower p.2))))
                (W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                  W.toWightmanStruct.vac) := by
          rw [← neg_one_smul ℂ]
          exact smearedProductOn_smul W.toWightmanStruct _ (-1 : ℂ) _
        _ = (-1 : ℂ) •
              W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                (W.toWightmanStruct.smearedProductOn
                  (init.map (fun p : 𝓕 × AnalyticTestFn =>
                    (p.1, inv (xRestrictLower p.2)))) W.toWightmanStruct.vac) := by
          rw [hcomm]
        _ = (-1 : ℂ) •
              W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                ((-1 : ℂ) ^ init.length •
                  W.toWightmanStruct.smearedProductOn
                    (init.reverse.map (fun p : 𝓕 × AnalyticTestFn =>
                      (p.1, inv (xRestrictUpper p.2)))) W.toWightmanStruct.vac) := by
          rw [hIH]
        _ = (-1 : ℂ) •
              ((-1 : ℂ) ^ init.length •
                W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                  (W.toWightmanStruct.smearedProductOn
                    (init.reverse.map (fun p : 𝓕 × AnalyticTestFn =>
                      (p.1, inv (xRestrictUpper p.2)))) W.toWightmanStruct.vac)) := by
          rw [(W.toWightmanStruct.smear φ (inv (xRestrictUpper F))).map_smul]
        _ = (-1 : ℂ) ^ (init.length + 1) •
              W.toWightmanStruct.smear φ (inv (xRestrictUpper F))
                (W.toWightmanStruct.smearedProductOn
                  (init.reverse.map (fun p : 𝓕 × AnalyticTestFn =>
                    (p.1, inv (xRestrictUpper p.2)))) W.toWightmanStruct.vac) := by
          simp [smul_smul, pow_succ, mul_comm]

end WightmanData

end MobiusCPT
