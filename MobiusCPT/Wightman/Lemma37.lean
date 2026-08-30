import MobiusCPT.Wightman.Lemma37Continuation
import MobiusCPT.Wightman.SignReversal
import MobiusCPT.Mobius.ComplexBetaLaws

/-!
# [T26], Lemma 3.7(ii): the sign at `τ = iπ`

Final assembly of Issue #9's remaining contract placeholder, `lemma_3_7_at_ipi`, from the three
pieces already landed: Lemma 3.7(i) (`Wightman.Lemma37Continuation`), the conformal-factor sign
`betaBoost_I_mul_pi` (`Mobius.ComplexBetaLaws`), and the combinatorial sign-reversal identity
(`Wightman.SignReversal`).
-/

namespace MobiusCPT

namespace WightmanData

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- A list-indexed sum of `n_j + 1` is the sum of the `n_j` plus the list's length. -/
private theorem sum_map_add_one_eq (l : List (𝓕 × AnalyticTestFn)) (dim' : 𝓕 → ℕ) :
    (l.map (fun p => dim' p.1 + 1)).sum = (l.map (fun p => dim' p.1)).sum + l.length := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring

/-- Pulling the per-field conformal sign `(-1)^{dim p.1 + 1}` out of `betaBoost` termwise, a
scaled smeared product is the total sign times the unscaled smeared product. -/
private theorem smearedProduct_map_pow_neg_one_smul
    (W : WightmanData Mob TestFn 𝓓 𝓕) (l : List (𝓕 × AnalyticTestFn)) (dim' : 𝓕 → ℕ) :
    W.toWightmanStruct.smearedProduct
        (l.map (fun p => (p.1, (-1 : ℂ) ^ (dim' p.1 + 1) • inv (xRestrictLower p.2)))) =
      (-1 : ℂ) ^ ((l.map (fun p => dim' p.1 + 1)).sum) •
        W.toWightmanStruct.smearedProduct
          (l.map (fun p => (p.1, inv (xRestrictLower p.2)))) := by
  induction l with
  | nil => simp [WightmanStruct.smearedProduct]
  | cons p rest ih =>
      simp only [List.map_cons, WightmanStruct.smearedProduct_cons, List.sum_cons]
      rw [(W.toWightmanStruct.smear_addLinear p.1 (inv (xRestrictLower p.2))
            (inv (xRestrictLower p.2))
            (W.toWightmanStruct.smearedProduct
              (rest.map (fun p =>
                (p.1, (-1 : ℂ) ^ (dim' p.1 + 1) • inv (xRestrictLower p.2)))))).2
          ((-1 : ℂ) ^ (dim' p.1 + 1)),
        ih,
        (W.toWightmanStruct.smear_linear p.1 (inv (xRestrictLower p.2))
            (W.toWightmanStruct.smearedProduct
              (rest.map (fun p => (p.1, inv (xRestrictLower p.2)))))
            (W.toWightmanStruct.smearedProduct
              (rest.map (fun p => (p.1, inv (xRestrictLower p.2)))))).2
          ((-1 : ℂ) ^ (rest.map (fun p => dim' p.1 + 1)).sum),
        smul_smul, ← pow_add]

/-- [T26], Lemma 3.7(ii); the analytic-core vector at `τ = iπ` maps to the reversed product with
the conformal-dimension sign. -/
theorem lemma_3_7_at_ipi (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (l : List (𝓕 × AnalyticTestFn)) :
    W.vtildeMap (Complex.I * Real.pi)
        (W.toWightmanStruct.smearedProduct (l.map (fun p => (p.1, xRestrictUpper p.2)))) =
      (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) •
        W.toWightmanStruct.smearedProduct
          (l.reverse.map (fun p => (p.1, inv (xRestrictUpper p.2)))) := by
  have h37i := lemma_3_7 hW l (Complex.I * Real.pi) I_mul_pi_mem_strip
  rw [h37i.2]
  have hlist :
      l.map (fun p => (p.1, betaBoost (W.dim p.1) (Complex.I * Real.pi) p.2)) =
        l.map (fun p => (p.1, (-1 : ℂ) ^ (W.dim p.1 + 1) • inv (xRestrictLower p.2))) := by
    apply List.map_congr_left
    intro p _
    rw [betaBoost_I_mul_pi]
  rw [hlist, smearedProduct_map_pow_neg_one_smul W l W.dim,
    smearedProduct_invLower_eq_smearedProduct_invUpper_reverse W hW l, smul_smul,
    sum_map_add_one_eq l W.dim]
  congr 1
  rw [pow_add]
  have hsq : ((-1 : ℂ) ^ l.length) * (-1 : ℂ) ^ l.length = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) * (-1 : ℂ) ^ l.length *
        (-1 : ℂ) ^ l.length =
      (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) *
        ((-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length) := by ring
    _ = (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) := by rw [hsq, mul_one]

end WightmanData

namespace WightmanBundle

/-- [T26], Lemma 3.7(ii). Issue #9 discharges `MobiusCPT.Contract`'s
`theorem_wanted lemma_3_7_at_ipi`, byte-identical statement text. -/
theorem lemma_3_7_at_ipi (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (l : List (W.𝓕 × AnalyticTestFn)) :
    W.data.vtildeMap (Complex.I * Real.pi)
        (W.data.toWightmanStruct.smearedProduct
          (l.map (fun p => (p.1, xRestrictUpper p.2)))) =
      (-1 : ℂ) ^ ((l.map (fun p => W.data.dim p.1)).sum) •
        W.data.toWightmanStruct.smearedProduct
          (l.reverse.map (fun p => (p.1, inv (xRestrictUpper p.2)))) :=
  WightmanData.lemma_3_7_at_ipi W.data h l

end WightmanBundle

end MobiusCPT
