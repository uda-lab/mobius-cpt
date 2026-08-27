import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Seminorm
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

/-!
# Separate and joint continuity of multilinear maps

This file proves the barrelled-space theorem that a separately continuous multilinear map on a
finite power of a first-countable topological vector space is jointly continuous.  It reconciles
the continuity conventions used downstream: [T26, Definition 2.4] asks for joint continuity,
whereas [CRTT25, Definition 2.5] asks for separate continuity.  They agree for `C^∞(S¹)` because
that space is Fréchet, hence barrelled and first-countable.
-/

noncomputable section

open Filter Set Topology

namespace MobiusCPT

/-- A pointwise bounded family of continuous linear functionals on a barrelled space is
equicontinuous at zero, in the explicit form needed below. -/
theorem exists_nhds_zero_forall_norm_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [BarrelledSpace ℂ E] {iota : Sort*} (u : iota → E →ₗ[ℂ] ℂ)
    (hu : ∀ i, Continuous (u i))
    (hb : ∀ x : E, BddAbove (Set.range fun i ↦ ‖u i x‖)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ V ∈ nhds (0 : E), ∀ x ∈ V, ∀ i, ‖u i x‖ ≤ epsilon := by
  let p : iota → Seminorm ℂ E := fun i ↦ (normSeminorm ℂ ℂ).comp (u i)
  have hp_continuous : ∀ i, Continuous (p i) := by
    intro i
    exact continuous_norm.comp (hu i)
  have hp_bounded : BddAbove (Set.range p) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    simpa only [p, Seminorm.comp_apply, coe_normSeminorm] using hb x
  let q : Seminorm ℂ E := ⨆ i, p i
  have hq_continuous : Continuous q := by
    rw [show (q : E → ℝ) = ⨆ i, (p i : E → ℝ) from Seminorm.coe_iSup_eq hp_bounded]
    exact Seminorm.continuous_iSup p hp_continuous hp_bounded
  refine ⟨q ⁻¹' Set.Iio epsilon, ?_, ?_⟩
  · apply (isOpen_Iio.preimage hq_continuous).mem_nhds
    change q (0 : E) < epsilon
    rw [map_zero]
    exact hepsilon
  · intro x hx i
    calc
      ‖u i x‖ = p i x := by
        simp only [p, Seminorm.comp_apply, coe_normSeminorm]
      _ ≤ q x := by
        change p i x ≤ (⨆ i, p i) x
        exact (le_ciSup hp_bounded i) x
      _ ≤ epsilon := le_of_lt hx

/-- A separately continuous complex multilinear map on a barrelled, first-countable topological
vector space is jointly continuous.

This is the classical theorem of [Trèves, *Topological Vector Spaces, Distributions and Kernels*,
Theorem 34.1]. -/
theorem MultilinearMap.continuous_of_continuous_update {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [BarrelledSpace ℂ E]
    [FirstCountableTopology E] {k : ℕ}
    (M : MultilinearMap ℂ (fun _ : Fin k => E) ℂ)
    (hsep : ∀ (i : Fin k) (g : Fin k → E),
      Continuous fun x : E => M (Function.update g i x)) :
    Continuous M := by
  induction k with
  | zero =>
      exact continuous_of_const fun f g ↦ congrArg (fun h ↦ M h) (Subsingleton.elim f g)
  | succ k ih =>
      apply continuous_iff_seqContinuous.mpr
      intro a b hab
      have htail : Tendsto (fun n ↦ Fin.tail (a n)) atTop (nhds (Fin.tail b)) := by
        rw [tendsto_pi_nhds]
        intro i
        exact tendsto_pi_nhds.mp hab i.succ
      have hzero' : Tendsto (fun n ↦ a n 0 - b 0) atTop
          (nhds (b 0 - b 0)) :=
        (tendsto_pi_nhds.mp hab 0).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => b 0) atTop (nhds (b 0)))
      have hzero : Tendsto (fun n ↦ a n 0 - b 0) atTop (nhds (0 : E)) := by
        simpa only [sub_self] using hzero'
      have hcurried_separate (x : E) :
          ∀ (i : Fin k) (g : Fin k → E),
            Continuous fun y : E => M.curryLeft x (Function.update g i y) := by
        intro i g
        simpa only [MultilinearMap.curryLeft_apply, Fin.cons_update] using
          hsep i.succ (Fin.cons x g)
      have hcurried_continuous (x : E) : Continuous (M.curryLeft x) :=
        ih (M.curryLeft x) (hcurried_separate x)
      let u : ℕ → E →ₗ[ℂ] ℂ := fun n ↦
        { toFun := fun x ↦ M (Fin.cons x (Fin.tail (a n)))
          map_add' := fun x y ↦ by
            change M.curryLeft (x + y) (Fin.tail (a n)) =
              M.curryLeft x (Fin.tail (a n)) + M.curryLeft y (Fin.tail (a n))
            rw [map_add]
            rfl
          map_smul' := fun c x ↦ by
            change M.curryLeft (c • x) (Fin.tail (a n)) =
              c • M.curryLeft x (Fin.tail (a n))
            rw [map_smul]
            rfl }
      have hu_continuous : ∀ n, Continuous (u n) := by
        intro n
        change Continuous fun x : E => M (Fin.cons x (Fin.tail (a n)))
        simpa only [Fin.update_cons_zero] using
          hsep (0 : Fin (k + 1)) (Fin.cons (0 : E) (Fin.tail (a n)))
      have hu_tendsto (x : E) :
          Tendsto (fun n ↦ u n x) atTop (nhds (M.curryLeft x (Fin.tail b))) := by
        change Tendsto (fun n ↦ M.curryLeft x (Fin.tail (a n))) atTop
          (nhds (M.curryLeft x (Fin.tail b)))
        exact ((hcurried_continuous x).tendsto (Fin.tail b)).comp htail
      have hu_bounded : ∀ x : E, BddAbove (Set.range fun n ↦ ‖u n x‖) := by
        intro x
        exact (Filter.Tendsto.norm (hu_tendsto x)).bddAbove_range
      have hfirst :
          Tendsto (fun n ↦ M (Fin.cons (a n 0 - b 0) (Fin.tail (a n)))) atTop
            (nhds (0 : ℂ)) := by
        change Tendsto (fun n ↦ u n (a n 0 - b 0)) atTop (nhds (0 : ℂ))
        refine NormedAddGroup.tendsto_nhds_zero.mpr ?_
        intro epsilon hepsilon
        obtain ⟨V, hV, hbound⟩ := exists_nhds_zero_forall_norm_le u hu_continuous
          hu_bounded (half_pos hepsilon)
        have heventually : ∀ᶠ n in atTop, a n 0 - b 0 ∈ V := hzero.eventually hV
        filter_upwards [heventually] with n hn
        exact (hbound (a n 0 - b 0) hn n).trans_lt (half_lt_self hepsilon)
      have hsecond :
          Tendsto
            (fun n ↦ M.curryLeft (b 0) (Fin.tail (a n)) -
              M.curryLeft (b 0) (Fin.tail b))
            atTop (nhds (0 : ℂ)) := by
        have h := ((hcurried_continuous (b 0)).tendsto (Fin.tail b)).comp htail
        have h' :
            Tendsto
              (fun n ↦ M.curryLeft (b 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b))
              atTop
              (nhds
                (M.curryLeft (b 0) (Fin.tail b) -
                  M.curryLeft (b 0) (Fin.tail b))) := by
          simpa only [Function.comp_apply] using h.sub
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => M.curryLeft (b 0) (Fin.tail b)) atTop
                (nhds (M.curryLeft (b 0) (Fin.tail b))))
        simpa only [sub_self] using h'
      have hsplit (n : ℕ) :
          M (a n) - M b =
            M (Fin.cons (a n 0 - b 0) (Fin.tail (a n))) +
              (M.curryLeft (b 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b)) := by
        calc
          M (a n) - M b =
              M.curryLeft (a n 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b) := by
            rw [MultilinearMap.curryLeft_apply, MultilinearMap.curryLeft_apply,
              Fin.cons_self_tail, Fin.cons_self_tail]
          _ = (M.curryLeft (a n 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail (a n))) +
              (M.curryLeft (b 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b)) := by
            abel
          _ = M (Fin.cons (a n 0 - b 0) (Fin.tail (a n))) +
              (M.curryLeft (b 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b)) := by
            rw [← sub_apply, ← map_sub, MultilinearMap.curryLeft_apply]
      have hdifference : Tendsto (fun n ↦ M (a n) - M b) atTop (nhds (0 : ℂ)) := by
        rw [show (fun n ↦ M (a n) - M b) =
            fun n ↦ M (Fin.cons (a n 0 - b 0) (Fin.tail (a n))) +
              (M.curryLeft (b 0) (Fin.tail (a n)) -
                M.curryLeft (b 0) (Fin.tail b)) from funext hsplit]
        simpa only [zero_add] using hfirst.add hsecond
      change Tendsto (fun n ↦ M (a n)) atTop (nhds (M b))
      exact tendsto_sub_nhds_zero_iff.mp hdifference

/-- An unbundled separately continuous multilinear function is jointly continuous. -/
theorem continuous_of_separately_continuous_multilinear {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [BarrelledSpace ℂ E]
    [FirstCountableTopology E] {k : ℕ} {M : (Fin k → E) → ℂ}
    (hadd : ∀ (i : Fin k) (g : Fin k → E) (x y : E),
      M (Function.update g i (x + y)) =
        M (Function.update g i x) + M (Function.update g i y))
    (hsmul : ∀ (i : Fin k) (g : Fin k → E) (c : ℂ) (x : E),
      M (Function.update g i (c • x)) = c * M (Function.update g i x))
    (hsep : ∀ (i : Fin k) (g : Fin k → E),
      Continuous fun x : E => M (Function.update g i x)) :
    Continuous M := by
  let M' : MultilinearMap ℂ (fun _ : Fin k => E) ℂ :=
    { toFun := M
      map_update_add' := by
        intro inst g i x y
        cases Subsingleton.elim inst (instDecidableEqFin k)
        exact hadd i g x y
      map_update_smul' := by
        intro inst g i c x
        cases Subsingleton.elim inst (instDecidableEqFin k)
        simpa only [smul_eq_mul] using hsmul i g c x }
  have hM' : Continuous M' :=
    MultilinearMap.continuous_of_continuous_update M' (by
      intro i g
      exact hsep i g)
  exact hM'

end MobiusCPT
