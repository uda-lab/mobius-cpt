import MobiusCPT.Wightman.Thm310Limit

/-!
# [T26], Theorem 3.10: continuity of the limiting continuation family

The limiting continuation family is continuous on the closed strip.  The proof uses uniform
convergence on compact intersections of the strip with closed balls.
-/

namespace MobiusCPT

open Set Filter
open scoped Topology Uniformity

noncomputable section

namespace WightmanData

variable {𝓓 𝓕 : Type} [AddCommGroup 𝓓] [Module ℂ 𝓓]
variable {W : WightmanData Mob TestFn 𝓓 𝓕}

private theorem isClosed_strip (τ : ℂ) : IsClosed (strip τ) := by
  change IsClosed
    ({z : ℂ | min 0 τ.im ≤ z.im} ∩ {z : ℂ | z.im ≤ max 0 τ.im})
  exact (isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)

/-- The approximants converge locally uniformly on the closed strip. -/
theorem tendstoLocallyUniformlyOn_limG_strip (hW : W.IsWightmanCFT)
    (l : List (𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2)
    (lam : W.toWightmanStruct.Compat) :
    TendstoLocallyUniformlyOn (limG l hl lam) (limitG hW l hl lam) atTop
      (strip (Complex.I * Real.pi)) := by
  intro u hu x hx
  let K : Set ℂ :=
    strip (Complex.I * Real.pi) ∩ Metric.closedBall x 1
  have hK_nhds : K ∈ 𝓝[strip (Complex.I * Real.pi)] x := by
    dsimp [K]
    exact Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x zero_lt_one))
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall x (1 : ℝ)).inter_left
      (isClosed_strip (Complex.I * Real.pi))
  have hK_subset : K ⊆ strip (Complex.I * Real.pi) := by
    dsimp [K]
    exact Set.inter_subset_left
  have h_uniform :
      TendstoUniformlyOn (limG l hl lam) (limitG hW l hl lam) atTop K :=
    (uniformCauchySeqOn_limG hW l hl lam hK_subset hK_compact).tendstoUniformlyOn_of_tendsto
      (fun y hy => tendsto_limG hW l hl lam (hK_subset hy))
  exact ⟨K, hK_nhds, h_uniform u hu⟩

/-- The limiting continuation family is continuous on the closed strip. -/
theorem continuousOn_limitG (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppUpper p.2) (lam : W.toWightmanStruct.Compat) :
    ContinuousOn (limitG hW l hl lam) (strip (Complex.I * Real.pi)) := by
  apply (tendstoLocallyUniformlyOn_limG_strip hW l hl lam).continuousOn
  exact (Filter.Eventually.of_forall fun n =>
    continuousOn_limG hW l hl lam n).frequently

end WightmanData

end

end MobiusCPT
