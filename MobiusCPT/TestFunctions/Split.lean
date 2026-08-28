import MobiusCPT.TestFunctions.Support

/-!
# MobiusCPT.TestFunctions.Split

Named upper- and lower-semicircle pieces for endpoint-flat test functions.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Topology

noncomputable section

/-- [T26], §3; vanishing to all orders at the two endpoints `±1` of the semicircles. -/
structure IsEndpointFlat (f : TestFn) : Prop where
  zero : ∀ j : ℕ, iteratedDeriv j (toAngle f) 0 = 0
  pi : ∀ j : ℕ, iteratedDeriv j (toAngle f) Real.pi = 0

/-- [T26], §3; upper-supported functions are endpoint-flat. -/
theorem IsEndpointFlat.of_suppUpper {f : TestFn} (h : SuppUpper f) : IsEndpointFlat f := by
  exact ⟨fun j => (iteratedDeriv_toAngle_eq_zero_of_suppUpper h j).1,
    fun j => (iteratedDeriv_toAngle_eq_zero_of_suppUpper h j).2⟩

/-- [T26], §3; lower-supported functions are endpoint-flat. -/
theorem IsEndpointFlat.of_suppLower {f : TestFn} (h : SuppLower f) : IsEndpointFlat f := by
  exact ⟨fun j => (iteratedDeriv_toAngle_eq_zero_of_suppLower h j).1,
    fun j => (iteratedDeriv_toAngle_eq_zero_of_suppLower h j).2⟩

/-- Iterated derivatives of a periodic smooth angle function have the same period. -/
private theorem periodic_iteratedDeriv_split {g : ℝ → ℂ} {T : ℝ}
    (hper : Function.Periodic g T) (j : ℕ) :
    Function.Periodic (iteratedDeriv j g) T := by
  have deriv_periodic : ∀ {q : ℝ → ℂ}, Function.Periodic q T →
      Function.Periodic (deriv q) T := by
    intro q hq x
    have hfun : (fun y : ℝ => q (y + T)) = q := hq.funext
    have hderiv := congrArg (deriv : (ℝ → ℂ) → (ℝ → ℂ)) hfun
    have hx := congrFun hderiv x
    simpa only [deriv_comp_add_const] using hx
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hper
  | succ j ih => simpa only [iteratedDeriv_succ] using deriv_periodic ih

/-- A pair of periodic angle functions agreeing on one half-open period agrees everywhere. -/
private theorem periodic_eq_of_eq_on_Ico_split {q r : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
    (hq : Function.Periodic q T) (hr : Function.Periodic r T)
    (hqr : ∀ x ∈ Set.Ico 0 T, q x = r x) : q = r := by
  funext x
  let k : ℤ := ⌊x / T⌋
  let y : ℝ := x - (k : ℝ) * T
  have hy0 : 0 ≤ y := by
    dsimp [y, k]
    exact Int.sub_floor_div_mul_nonneg x hT
  have hyT : y < T := by
    dsimp [y, k]
    exact Int.sub_floor_div_mul_lt x hT
  have hy : y ∈ Set.Ico 0 T := ⟨hy0, hyT⟩
  have hxy : x = y + (k : ℝ) * T := by
    dsimp [y]
    ring
  have hqk := hq.int_mul k y
  have hrk := hr.int_mul k y
  calc
    q x = q y := by rw [hxy]; exact hqk
    _ = r y := hqr y hy
    _ = r x := by rw [hxy, hrk]

/-- [T26], §3; endpoint flatness gives zero angle derivatives at the endpoint at angle `2π`. -/
theorem IsEndpointFlat.two_pi {f : TestFn} (h : IsEndpointFlat f) (j : ℕ) :
    iteratedDeriv j (toAngle f) (2 * Real.pi) = 0 := by
  have hper := periodic_iteratedDeriv_split (periodic_toAngle f) j
  calc
    iteratedDeriv j (toAngle f) (2 * Real.pi) = iteratedDeriv j (toAngle f) 0 := by
      simpa using hper 0
    _ = 0 := h.zero j

/-- [T26], §3; an endpoint-flat test function yields an upper-flat cut-off angle function. -/
theorem IsEndpointFlat.isUpperFlat_cutIcc {f : TestFn} (h : IsEndpointFlat f) :
    IsUpperFlat (cutIcc 0 Real.pi (toAngle f)) := by
  refine ⟨contDiff_cutIcc Real.pi_pos.le (contDiff_toAngle f) h.zero h.pi, ?_⟩
  intro θ hθ
  by_cases hθIcc : θ ∈ Set.Icc 0 Real.pi
  · by_cases hθ0 : θ = 0
    · subst θ
      rw [cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, Real.pi_pos.le⟩]
      simpa only [iteratedDeriv_zero] using h.zero 0
    · by_cases hθpi : θ = Real.pi
      · subst θ
        rw [cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩]
        simpa only [iteratedDeriv_zero] using h.pi 0
      · exact False.elim (hθ ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθ0),
          lt_of_le_of_ne hθIcc.2 hθpi⟩)
  · exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc

/-- [T26], §3; an endpoint-flat test function yields a lower-flat cut-off angle function. -/
theorem IsEndpointFlat.isLowerFlat_cutIcc {f : TestFn} (h : IsEndpointFlat f) :
    IsLowerFlat (cutIcc Real.pi (2 * Real.pi) (toAngle f)) := by
  refine ⟨contDiff_cutIcc (by linarith [Real.pi_pos]) (contDiff_toAngle f) h.pi h.two_pi, ?_⟩
  intro θ hθ
  by_cases hθIcc : θ ∈ Set.Icc Real.pi (2 * Real.pi)
  · by_cases hθpi : θ = Real.pi
    · subst θ
      rw [cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by linarith [Real.pi_pos]⟩]
      simpa only [iteratedDeriv_zero] using h.pi 0
    · by_cases hθT : θ = 2 * Real.pi
      · subst θ
        rw [cutIcc_eq_of_mem (toAngle f) ⟨by linarith [Real.pi_pos], le_rfl⟩]
        simpa only [iteratedDeriv_zero] using h.two_pi 0
      · exact False.elim (hθ ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθpi),
          lt_of_le_of_ne hθIcc.2 hθT⟩)
  · exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc

/-- [T26], Definition 3.2; the named upper piece of an endpoint-flat test function. -/
noncomputable def splitUpper (f : TestFn) (h : IsEndpointFlat f) : TestFn :=
  Classical.choose (exists_suppUpper_toAngle_eq_periodize h.isUpperFlat_cutIcc)

/-- [T26], Definition 3.2; the named lower piece of an endpoint-flat test function. -/
noncomputable def splitLower (f : TestFn) (h : IsEndpointFlat f) : TestFn :=
  Classical.choose (exists_suppLower_toAngle_eq_periodize h.isLowerFlat_cutIcc)

/-- [T26], Definition 3.2; the angle description of the named upper piece. -/
theorem toAngle_splitUpper (f : TestFn) (h : IsEndpointFlat f) :
    toAngle (splitUpper f h) = periodize (2 * Real.pi) (cutIcc 0 Real.pi (toAngle f)) := by
  exact (Classical.choose_spec (exists_suppUpper_toAngle_eq_periodize h.isUpperFlat_cutIcc)).1

/-- [T26], Definition 3.2; the angle description of the named lower piece. -/
theorem toAngle_splitLower (f : TestFn) (h : IsEndpointFlat f) :
    toAngle (splitLower f h) =
      periodize (2 * Real.pi) (cutIcc Real.pi (2 * Real.pi) (toAngle f)) := by
  exact (Classical.choose_spec (exists_suppLower_toAngle_eq_periodize h.isLowerFlat_cutIcc)).1

/-- [T26], Definition 3.2; the named upper piece has upper semicircle support. -/
theorem suppUpper_splitUpper (f : TestFn) (h : IsEndpointFlat f) :
    SuppUpper (splitUpper f h) := by
  exact (Classical.choose_spec (exists_suppUpper_toAngle_eq_periodize h.isUpperFlat_cutIcc)).2

/-- [T26], Definition 3.2; the named lower piece has lower semicircle support. -/
theorem suppLower_splitLower (f : TestFn) (h : IsEndpointFlat f) :
    SuppLower (splitLower f h) := by
  exact (Classical.choose_spec (exists_suppLower_toAngle_eq_periodize h.isLowerFlat_cutIcc)).2

/-- [T26], Definition 3.2; on the closed upper semicircle the upper piece is unchanged. -/
theorem toAngle_splitUpper_of_mem {f : TestFn} (h : IsEndpointFlat f) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    toAngle (splitUpper f h) θ = toAngle f θ := by
  rw [toAngle_splitUpper, periodize_eq_self Real.two_pi_pos]
  · exact cutIcc_eq_of_mem (toAngle f) hθ
  · exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

/-- [T26], Definition 3.2; the upper piece of an upper-supported function is the function itself. -/
theorem splitUpper_of_suppUpper {f : TestFn} (hf : SuppUpper f) :
    splitUpper f (IsEndpointFlat.of_suppUpper hf) = f := by
  let h : IsEndpointFlat f := IsEndpointFlat.of_suppUpper hf
  apply toAngle_injective
  apply periodic_eq_of_eq_on_Ico_split Real.two_pi_pos
    (periodic_toAngle (splitUpper f h)) (periodic_toAngle f)
  intro θ hθ
  by_cases hθle : θ ≤ Real.pi
  · by_cases hθpi : θ = Real.pi
    · subst θ
      rw [toAngle_splitUpper, periodize_eq_self Real.two_pi_pos]
      · rw [cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩]
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · exact toAngle_splitUpper_of_mem h ⟨hθ.1, hθle⟩
  · have hθgt : Real.pi < θ := lt_of_not_ge hθle
    have hzero : toAngle f θ = 0 :=
      (suppUpper_iff_angle f).1 hf θ ⟨hθgt, hθ.2⟩
    rw [toAngle_splitUpper, periodize_eq_self Real.two_pi_pos]
    · rw [cutIcc_eq_zero_of_notMem (toAngle f) (by
        intro hmem
        exact not_le_of_gt hθgt hmem.2)]
      exact hzero.symm
    · exact hθ

/-- [T26], Definition 3.2; the lower piece of a lower-supported function is the function itself. -/
theorem splitLower_of_suppLower {f : TestFn} (hf : SuppLower f) :
    splitLower f (IsEndpointFlat.of_suppLower hf) = f := by
  let h : IsEndpointFlat f := IsEndpointFlat.of_suppLower hf
  apply toAngle_injective
  apply periodic_eq_of_eq_on_Ico_split Real.two_pi_pos
    (periodic_toAngle (splitLower f h)) (periodic_toAngle f)
  intro θ hθ
  by_cases hθ0 : θ = 0
  · subst θ
    have hzero : toAngle f 0 = 0 := by
      simpa only [iteratedDeriv_zero] using h.zero 0
    rw [toAngle_splitLower, periodize_eq_self Real.two_pi_pos]
    · rw [cutIcc_eq_zero_of_notMem (toAngle f) (by
        intro hmem
        exact not_le_of_gt Real.pi_pos hmem.1)]
      exact hzero.symm
    · exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  · by_cases hθle : θ ≤ Real.pi
    · by_cases hθpi : θ = Real.pi
      · subst θ
        rw [toAngle_splitLower, periodize_eq_self Real.two_pi_pos]
        · rw [cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by linarith [Real.pi_pos]⟩]
        · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
        have hθlt : θ < Real.pi := lt_of_le_of_ne hθle hθpi
        have hzero : toAngle f θ = 0 := (suppLower_iff_angle f).1 hf θ ⟨hθpos, hθlt⟩
        rw [toAngle_splitLower, periodize_eq_self Real.two_pi_pos]
        · rw [cutIcc_eq_zero_of_notMem (toAngle f) (by
            intro hmem
            exact not_le_of_gt hθlt hmem.1)]
          exact hzero.symm
        · exact hθ
    · have hθgt : Real.pi < θ := lt_of_not_ge hθle
      rw [toAngle_splitLower, periodize_eq_self Real.two_pi_pos]
      · exact cutIcc_eq_of_mem (toAngle f) ⟨hθgt.le, hθ.2.le⟩
      · exact hθ

/-- [T26], Definition 3.2; endpoint-flatness decomposes a test function into named pieces. -/
theorem splitUpper_add_splitLower (f : TestFn) (h : IsEndpointFlat f) :
    splitUpper f h + splitLower f h = f := by
  apply toAngle_injective
  rw [toAngle_add, toAngle_splitUpper, toAngle_splitLower]
  symm
  apply periodic_eq_of_eq_on_Ico_split Real.two_pi_pos (periodic_toAngle f)
    ((periodic_periodize (2 * Real.pi) Real.two_pi_pos
      (cutIcc 0 Real.pi (toAngle f))).add
      (periodic_periodize (2 * Real.pi) Real.two_pi_pos
        (cutIcc Real.pi (2 * Real.pi) (toAngle f))))
  intro θ hθ
  rw [Pi.add_apply, periodize_eq_self Real.two_pi_pos hθ,
    periodize_eq_self Real.two_pi_pos hθ]
  by_cases hθpi : θ = Real.pi
  · subst θ
    rw [cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩,
      cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by linarith [Real.pi_pos]⟩]
    -- Both closed cuts retain the value at `π`; endpoint flatness makes that common
    -- value zero, so the two retained values add to the original value.
    have hzero : toAngle f Real.pi = 0 := by
      simpa only [iteratedDeriv_zero] using h.pi 0
    simp only [hzero, add_zero]
  · by_cases hθlt : θ < Real.pi
    · rw [cutIcc_eq_of_mem (toAngle f) ⟨hθ.1, hθlt.le⟩,
        cutIcc_eq_zero_of_notMem (toAngle f) (by
          intro hmem
          exact not_le_of_gt hθlt hmem.1)]
      exact (add_zero _).symm
    · have hθgt : Real.pi < θ := lt_of_le_of_ne (le_of_not_gt hθlt) (Ne.symm hθpi)
      rw [cutIcc_eq_zero_of_notMem (toAngle f) (by
          intro hmem
          exact not_le_of_gt hθgt hmem.2),
        cutIcc_eq_of_mem (toAngle f) ⟨hθgt.le, hθ.2.le⟩]
      exact (zero_add _).symm

end

end MobiusCPT
