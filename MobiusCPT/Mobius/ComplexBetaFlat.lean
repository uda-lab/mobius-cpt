import MobiusCPT.Analysis.FlatCalculus
import MobiusCPT.Analysis.ParamSlice
import MobiusCPT.Mobius.ComplexBetaCore

/-!
# Endpoint flatness of the divided inverted function

The removable-singularity quotient `AnalyticTestFn.invQuot` inherits the endpoint flatness of an
analytic test function after localising the closed unit disc away from the origin.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- The part of the closed unit disc near a boundary point, used to localise the flatness
argument away from the origin where the divided inverted function is defined by continuation. -/
def discNear (c : ℂ) : Set ℂ :=
  Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall c (1 / 2)

/-- The localised disc is convex with nonempty interior, so it determines derivatives. -/
theorem uniqueDiffOn_discNear {c : ℂ} (hc : ‖c‖ = 1) : UniqueDiffOn ℝ (discNear c) := by
  apply uniqueDiffOn_of_convex
  · change Convex ℝ (Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall c (1 / 2))
    exact (convex_closedBall (0 : ℂ) 1).inter (convex_closedBall c (1 / 2))
  · let p : ℂ := (3 / 4 : ℂ) * c
    have hp : p ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.ball c (1 / 2) := by
      constructor
      · dsimp [p]
        rw [Metric.mem_ball, dist_zero_right, norm_mul, hc]
        norm_num
      · dsimp [p]
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : (3 / 4 : ℂ) * c - c = (-1 / 4 : ℂ) * c := by
          ring
        rw [hsub, norm_mul, hc]
        norm_num
    have hopen : IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball c (1 / 2)) :=
      Metric.isOpen_ball.inter Metric.isOpen_ball
    have hsubset : Metric.ball (0 : ℂ) 1 ∩ Metric.ball c (1 / 2) ⊆ discNear c := by
      intro w hw
      exact ⟨Metric.mem_closedBall.2 (Metric.mem_ball.1 hw.1).le,
        Metric.mem_closedBall.2 (Metric.mem_ball.1 hw.2).le⟩
    refine ⟨p, ?_⟩
    exact (interior_maximal hsubset hopen) hp

/-- The localised disc misses the origin. -/
theorem zero_notMem_discNear {c : ℂ} (hc : ‖c‖ = 1) : (0 : ℂ) ∉ discNear c := by
  intro hzero
  have hle : dist (0 : ℂ) c ≤ (1 / 2 : ℝ) := Metric.mem_closedBall.mp hzero.2
  have hbad : (1 : ℝ) ≤ 1 / 2 := by
    simpa [dist_eq_norm, hc] using hle
  norm_num at hbad

/-- Near a boundary point the localised disc is the closed disc. -/
theorem discNear_eventuallyEq {c : ℂ} (hc : ‖c‖ = 1) :
    discNear c =ᶠ[nhds c] Metric.closedBall (0 : ℂ) 1 := by
  apply Filter.eventuallyEq_of_mem
    (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 2))
  intro w hw
  apply propext
  change (w ∈ Metric.closedBall (0 : ℂ) 1 ∩ Metric.closedBall c (1 / 2)) ↔
    w ∈ Metric.closedBall (0 : ℂ) 1
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, Metric.mem_closedBall.2 (Metric.mem_ball.1 hw).le⟩

/-- Inversion maps the localised disc into the exterior domain. -/
theorem mapsTo_inv_discNear {c : ℂ} (hc : ‖c‖ = 1) :
    Set.MapsTo (fun w : ℂ => w⁻¹) (discNear c) Oexterior := by
  intro w hw
  have hw0 : w ≠ 0 := by
    intro hw0
    apply zero_notMem_discNear hc
    simpa [hw0] using hw
  have hnorm : ‖w‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw.1
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  change (1 : ℝ) ≤ ‖w⁻¹‖
  rw [norm_inv]
  exact (one_le_inv₀ hpos).2 hnorm

/-- [T26], Definitions 3.2 and 3.5; the divided inverted function inherits the infinite-order
vanishing of `F` at a boundary point fixed by inversion.  This is what makes the complex boost
endpoint-flat, hence an element of `C_0^∞(I_+)`: the boost fixes `±1`, and `F` is flat there. -/
theorem AnalyticTestFn.iteratedFDerivWithin_invQuot_eq_zero (F : AnalyticTestFn) {c : ℂ}
    (hc : ‖c‖ = 1) (hcinv : c⁻¹ = c)
    (hflat : ∀ n : ℕ, iteratedFDerivWithin ℝ n F.toFun Oexterior c = 0) (n : ℕ) :
    iteratedFDerivWithin ℝ n F.invQuot (Metric.closedBall (0 : ℂ) 1) c = 0 := by
  let s : Set ℂ := discNear c
  have hs : UniqueDiffOn ℝ s := by
    dsimp [s]
    exact uniqueDiffOn_discNear hc
  have hzero : (0 : ℂ) ∉ s := by
    dsimp [s]
    exact zero_notMem_discNear hc
  have hcx : c ∈ s := by
    dsimp [s, discNear]
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hc.le
    · rw [Metric.mem_closedBall, dist_self]
      norm_num
  have hmaps : Set.MapsTo (fun w : ℂ => w⁻¹) s Oexterior := by
    dsimp [s]
    exact mapsTo_inv_discNear hc
  have hinv : ContDiffOn ℝ ∞ (fun w : ℂ => w⁻¹) s := by
    apply (contDiffOn_inv (𝕜 := ℝ) (𝕜' := ℂ)).mono
    intro w hw
    change w ≠ 0
    intro hw0
    apply hzero
    simpa [hw0] using hw
  have hcomp : ContDiffOn ℝ ∞ (F.toFun ∘ (fun w : ℂ => w⁻¹)) s :=
    F.contDiffOn.comp hinv hmaps
  have hcompflat : ∀ i : ℕ,
      iteratedFDerivWithin ℝ i (F.toFun ∘ (fun w : ℂ => w⁻¹)) s c = 0 := by
    intro i
    apply iteratedFDerivWithin_comp_eq_zero_of_flat
      (g := F.toFun) (f := fun w : ℂ => w⁻¹) (s := s) (t := Oexterior) (x := c)
      F.contDiffOn hinv uniqueDiffOn_Oexterior hs hmaps hcx
    intro j
    rw [hcinv]
    exact hflat j
  have hmulflat :
      iteratedFDerivWithin ℝ n (fun w : ℂ => w⁻¹ * F.toFun w⁻¹) s c = 0 := by
    have h := iteratedFDerivWithin_mul_eq_zero_of_flat
      (a := fun w : ℂ => w⁻¹) (h := F.toFun ∘ (fun w : ℂ => w⁻¹))
      hinv hcomp hs hcx hcompflat n
    simpa only [Function.comp_apply] using h
  have hquot_eq : EqOn F.invQuot (fun w : ℂ => w⁻¹ * F.toFun w⁻¹) s := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hw0
      apply hzero
      simpa [hw0] using hw
    calc
      F.invQuot w = F.toFun w⁻¹ / w := F.invQuot_apply hw0
      _ = F.toFun w⁻¹ * w⁻¹ := by rw [div_eq_mul_inv]
      _ = w⁻¹ * F.toFun w⁻¹ := mul_comm _ _
  have hwithin :
      iteratedFDerivWithin ℝ n F.invQuot s c = 0 := by
    calc
      iteratedFDerivWithin ℝ n F.invQuot s c =
          iteratedFDerivWithin ℝ n (fun w : ℂ => w⁻¹ * F.toFun w⁻¹) s c :=
        iteratedFDerivWithin_congr hquot_eq hcx n
      _ = 0 := hmulflat
  have hset :
      iteratedFDerivWithin ℝ n F.invQuot s c =
        iteratedFDerivWithin ℝ n F.invQuot (Metric.closedBall (0 : ℂ) 1) c := by
    apply iteratedFDerivWithin_congr_set
    simpa [s] using discNear_eventuallyEq hc
  calc
    iteratedFDerivWithin ℝ n F.invQuot (Metric.closedBall (0 : ℂ) 1) c =
        iteratedFDerivWithin ℝ n F.invQuot s c := hset.symm
    _ = 0 := hwithin

/-- [T26], Definition 3.2; the divided inverted function is flat at the endpoint `1`. -/
theorem AnalyticTestFn.iteratedFDerivWithin_invQuot_one (F : AnalyticTestFn) (n : ℕ) :
    iteratedFDerivWithin ℝ n F.invQuot (Metric.closedBall (0 : ℂ) 1) 1 = 0 := by
  exact F.iteratedFDerivWithin_invQuot_eq_zero (c := (1 : ℂ))
    (by norm_num) (by norm_num) F.flat_one n

/-- [T26], Definition 3.2; the divided inverted function is flat at the endpoint `-1`. -/
theorem AnalyticTestFn.iteratedFDerivWithin_invQuot_neg_one (F : AnalyticTestFn) (n : ℕ) :
    iteratedFDerivWithin ℝ n F.invQuot (Metric.closedBall (0 : ℂ) 1) (-1) = 0 := by
  exact F.iteratedFDerivWithin_invQuot_eq_zero (c := (-1 : ℂ))
    (by norm_num) (by norm_num) F.flat_neg_one n

/-- [T26], Definition 3.2; `F` vanishes at the endpoint `1`. -/
theorem AnalyticTestFn.toFun_one (F : AnalyticTestFn) : F.toFun 1 = 0 := by
  have hnorm : ‖iteratedFDerivWithin ℝ 0 F.toFun Oexterior 1‖ = 0 := by
    rw [F.flat_one 0]
    simp
  rw [norm_iteratedFDerivWithin_zero] at hnorm
  exact norm_eq_zero.mp hnorm

/-- [T26], Definition 3.2; `F` vanishes at the endpoint `-1`. -/
theorem AnalyticTestFn.toFun_neg_one (F : AnalyticTestFn) : F.toFun (-1) = 0 := by
  have hnorm : ‖iteratedFDerivWithin ℝ 0 F.toFun Oexterior (-1)‖ = 0 := by
    rw [F.flat_neg_one 0]
    simp
  rw [norm_iteratedFDerivWithin_zero] at hnorm
  exact norm_eq_zero.mp hnorm

/-- [T26], Definition 3.2; the divided inverted function vanishes at the endpoint `1`. -/
theorem AnalyticTestFn.invQuot_one (F : AnalyticTestFn) : F.invQuot 1 = 0 := by
  rw [F.invQuot_apply (w := (1 : ℂ)) (by norm_num)]
  simp [F.toFun_one]

/-- [T26], Definition 3.2; the divided inverted function vanishes at the endpoint `-1`. -/
theorem AnalyticTestFn.invQuot_neg_one (F : AnalyticTestFn) : F.invQuot (-1) = 0 := by
  rw [F.invQuot_apply (w := (-1 : ℂ)) (by norm_num)]
  simp [F.toFun_neg_one]

end

end MobiusCPT
