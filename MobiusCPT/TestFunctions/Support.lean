import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Algebra.Support
import MobiusCPT.Analysis.FlatGluing
import MobiusCPT.TestFunctions.Basic

/-!
# MobiusCPT.TestFunctions.Support

The semicircle support predicates for smooth test functions on the circle.  The open arcs are
used for the vanishing condition, while topological support is compared with their closures.
-/

namespace MobiusCPT

open Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

/-- [T26], §3; the open upper semicircle `I₊ = {z ∈ S¹ : Im z > 0}`. -/
def upperArc : Set Circle := {z | 0 < (z : ℂ).im}

/-- [T26], §3; the open lower semicircle `I₋ = {z ∈ S¹ : Im z < 0}`. -/
def lowerArc : Set Circle := {z | (z : ℂ).im < 0}

/-- [T26], §3; the upper semicircle is open in the circle. -/
theorem isOpen_upperArc : IsOpen upperArc := by
  change IsOpen {z : Circle | 0 < (z : ℂ).im}
  exact isOpen_lt (continuous_const : Continuous (fun _ : Circle => (0 : ℝ)))
    (Complex.continuous_im.comp
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))))

/-- [T26], §3; the lower semicircle is open in the circle. -/
theorem isOpen_lowerArc : IsOpen lowerArc := by
  change IsOpen {z : Circle | (z : ℂ).im < 0}
  exact isOpen_lt
    (Complex.continuous_im.comp
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))))
    (continuous_const : Continuous (fun _ : Circle => (0 : ℝ)))

/-- The imaginary part of a circle exponential is the sine of its angle. -/
private theorem circleExp_im (θ : ℝ) : (Circle.exp θ : ℂ).im = Real.sin θ := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

/-- [T26], §3; a real angle lies in the upper semicircle exactly when one of its representatives
lies in the open interval `(0, π)`. -/
theorem mem_upperArc_circleExp {θ : ℝ} :
    Circle.exp θ ∈ upperArc ↔
      ∃ k : ℤ, θ - 2 * Real.pi * (k : ℝ) ∈ Set.Ioo 0 Real.pi := by
  let T : ℝ := 2 * Real.pi
  constructor
  · intro hθ
    have hsinθ : 0 < Real.sin θ := by
      rw [← circleExp_im θ]
      exact hθ
    let k : ℤ := ⌊θ / T⌋
    let x : ℝ := θ - (k : ℝ) * T
    have hx0 : 0 ≤ x := by
      dsimp [x, k, T]
      exact Int.sub_floor_div_mul_nonneg θ Real.two_pi_pos
    have hxT : x < T := by
      dsimp [x, k, T]
      exact Int.sub_floor_div_mul_lt θ Real.two_pi_pos
    have hsinx : 0 < Real.sin x := by
      have hperiod : Real.sin (θ - (k : ℝ) * T) = Real.sin θ := by
        simpa [T, mul_comm] using Real.sin_sub_int_mul_two_pi θ k
      rw [show x = θ - (k : ℝ) * T by rfl, hperiod]
      exact hsinθ
    have hxpos : 0 < x := by
      have hxne : x ≠ 0 := by
        intro hxzero
        rw [hxzero] at hsinx
        simp at hsinx
      exact lt_of_le_of_ne hx0 (Ne.symm hxne)
    have hxpi : x < Real.pi := by
      by_contra hxnot
      have hpile : Real.pi ≤ x := le_of_not_gt hxnot
      by_cases hx_eq : x = Real.pi
      · rw [hx_eq] at hsinx
        simp at hsinx
      · have hxgt : Real.pi < x := lt_of_le_of_ne hpile (Ne.symm hx_eq)
        have hsubneg : x - T < 0 := by
          dsimp [T] at hxT ⊢
          linarith
        have hsublower : -Real.pi < x - T := by
          dsimp [T]
          linarith
        have hsinneg : Real.sin (x - T) < 0 := by
          simpa [T] using
            (Real.sin_neg_of_neg_of_neg_pi_lt hsubneg hsublower)
        have hperiod : Real.sin (x - T) = Real.sin x := by
          simp [T, Real.sin_sub_two_pi]
        linarith
    refine ⟨k, ?_⟩
    simpa [x, T, mul_comm] using (show x ∈ Set.Ioo 0 Real.pi from ⟨hxpos, hxpi⟩)
  · rintro ⟨k, hk⟩
    have hsin_eq : Real.sin (θ - 2 * Real.pi * (k : ℝ)) = Real.sin θ := by
      simpa [mul_comm] using Real.sin_sub_int_mul_two_pi θ k
    have hsinθ : 0 < Real.sin θ := by
      rw [← hsin_eq]
      exact Real.sin_pos_of_mem_Ioo hk
    change 0 < (Circle.exp θ : ℂ).im
    rw [circleExp_im]
    exact hsinθ

/-- [T26], §3; a real angle lies in the lower semicircle exactly when one of its representatives
lies in the open interval `(π, 2π)`. -/
theorem mem_lowerArc_circleExp {θ : ℝ} :
    Circle.exp θ ∈ lowerArc ↔
      ∃ k : ℤ, θ - 2 * Real.pi * (k : ℝ) ∈ Set.Ioo Real.pi (2 * Real.pi) := by
  let T : ℝ := 2 * Real.pi
  constructor
  · intro hθ
    have hsinθ : Real.sin θ < 0 := by
      rw [← circleExp_im θ]
      exact hθ
    let k : ℤ := ⌊θ / T⌋
    let x : ℝ := θ - (k : ℝ) * T
    have hx0 : 0 ≤ x := by
      dsimp [x, k, T]
      exact Int.sub_floor_div_mul_nonneg θ Real.two_pi_pos
    have hxT : x < T := by
      dsimp [x, k, T]
      exact Int.sub_floor_div_mul_lt θ Real.two_pi_pos
    have hsinx : Real.sin x < 0 := by
      have hperiod : Real.sin (θ - (k : ℝ) * T) = Real.sin θ := by
        simpa [T, mul_comm] using Real.sin_sub_int_mul_two_pi θ k
      rw [show x = θ - (k : ℝ) * T by rfl, hperiod]
      exact hsinθ
    have hxpi : Real.pi < x := by
      by_contra hxnot
      have hxle : x ≤ Real.pi := le_of_not_gt hxnot
      have hsin_nonneg : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxle
      linarith
    refine ⟨k, ?_⟩
    simpa [x, T, mul_comm] using (show x ∈ Set.Ioo Real.pi (2 * Real.pi) from ⟨hxpi, hxT⟩)
  · rintro ⟨k, hk⟩
    have hsin_eq : Real.sin (θ - 2 * Real.pi * (k : ℝ)) = Real.sin θ := by
      simpa [mul_comm] using Real.sin_sub_int_mul_two_pi θ k
    have hsinθ : Real.sin θ < 0 := by
      rw [← hsin_eq]
      have hsubneg : θ - 2 * Real.pi * (k : ℝ) - 2 * Real.pi < 0 := by
        linarith [hk.2]
      have hsublower : -Real.pi < θ - 2 * Real.pi * (k : ℝ) - 2 * Real.pi := by
        linarith [hk.1]
      have hsinxsub :
          Real.sin (θ - 2 * Real.pi * (k : ℝ) - 2 * Real.pi) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt hsubneg hsublower
      have hsinxperiod :
          Real.sin (θ - 2 * Real.pi * (k : ℝ) - 2 * Real.pi) =
            Real.sin (θ - 2 * Real.pi * (k : ℝ)) := by
        simp
      linarith
    change (Circle.exp θ : ℂ).im < 0
    rw [circleExp_im]
    exact hsinθ

/-- [T26], §3; the upper support predicate means vanishing on the opposite open semicircle. -/
def SuppUpper (f : TestFn) : Prop := ∀ z ∈ lowerArc, f z = 0

/-- [T26], §3; the lower support predicate means vanishing on the opposite open semicircle. -/
def SuppLower (f : TestFn) : Prop := ∀ z ∈ upperArc, f z = 0

/-- [T26], §3; the upper support predicate in the angle picture. -/
theorem suppUpper_iff_angle (f : TestFn) :
    SuppUpper f ↔ ∀ θ ∈ Set.Ioo Real.pi (2 * Real.pi), toAngle f θ = 0 := by
  constructor
  · intro hf θ hθ
    have hz : Circle.exp θ ∈ lowerArc :=
      (mem_lowerArc_circleExp).2 ⟨0, by simpa using hθ⟩
    have hzzero := hf (Circle.exp θ) hz
    simpa [toAngle] using hzzero
  · intro hf z hz
    obtain ⟨θ, hθz⟩ := Circle.exp_surjective z
    have hz' : Circle.exp θ ∈ lowerArc := by simpa [hθz] using hz
    obtain ⟨k, hk⟩ := (mem_lowerArc_circleExp).1 hz'
    have hzero := hf (θ - 2 * Real.pi * (k : ℝ)) hk
    have hexp : Circle.exp (θ - 2 * Real.pi * (k : ℝ)) = z := by
      calc
        Circle.exp (θ - 2 * Real.pi * (k : ℝ)) = Circle.exp θ := by
          apply Circle.exp_eq_exp.mpr
          refine ⟨-k, ?_⟩
          rw [Int.cast_neg]
          ring
        _ = z := hθz
    change f z = 0
    change f (Circle.exp (θ - 2 * Real.pi * (k : ℝ))) = 0 at hzero
    rw [hexp] at hzero
    exact hzero

/-- [T26], §3; the lower support predicate in the angle picture. -/
theorem suppLower_iff_angle (f : TestFn) :
    SuppLower f ↔ ∀ θ ∈ Set.Ioo 0 Real.pi, toAngle f θ = 0 := by
  constructor
  · intro hf θ hθ
    have hz : Circle.exp θ ∈ upperArc :=
      (mem_upperArc_circleExp).2 ⟨0, by simpa using hθ⟩
    have hzzero := hf (Circle.exp θ) hz
    simpa [toAngle] using hzzero
  · intro hf z hz
    obtain ⟨θ, hθz⟩ := Circle.exp_surjective z
    have hz' : Circle.exp θ ∈ upperArc := by simpa [hθz] using hz
    obtain ⟨k, hk⟩ := (mem_upperArc_circleExp).1 hz'
    have hzero := hf (θ - 2 * Real.pi * (k : ℝ)) hk
    have hexp : Circle.exp (θ - 2 * Real.pi * (k : ℝ)) = z := by
      calc
        Circle.exp (θ - 2 * Real.pi * (k : ℝ)) = Circle.exp θ := by
          apply Circle.exp_eq_exp.mpr
          refine ⟨-k, ?_⟩
          rw [Int.cast_neg]
          ring
        _ = z := hθz
    change f z = 0
    change f (Circle.exp (θ - 2 * Real.pi * (k : ℝ))) = 0 at hzero
    rw [hexp] at hzero
    exact hzero

/-- [T26], §3; the upper support predicate is closed under zero. -/
theorem suppUpper_zero : SuppUpper (0 : TestFn) := by
  intro z hz
  simp

/-- [T26], §3; the upper support predicate is closed under addition. -/
theorem suppUpper_add {f g : TestFn} (hf : SuppUpper f) (hg : SuppUpper g) :
    SuppUpper (f + g) := by
  intro z hz
  simp [hf z hz, hg z hz]

/-- [T26], §3; the upper support predicate is closed under complex scalar multiplication. -/
theorem suppUpper_smul (c : ℂ) {f : TestFn} (hf : SuppUpper f) : SuppUpper (c • f) := by
  intro z hz
  simp [hf z hz]

/-- [T26], §3; the upper support predicate is closed under negation. -/
theorem suppUpper_neg {f : TestFn} (hf : SuppUpper f) : SuppUpper (-f) := by
  intro z hz
  simp [hf z hz]

/-- [T26], §3; the upper support predicate is closed under subtraction. -/
theorem suppUpper_sub {f g : TestFn} (hf : SuppUpper f) (hg : SuppUpper g) :
    SuppUpper (f - g) := by
  intro z hz
  simp [hf z hz, hg z hz]

/-- [T26], §3; the lower support predicate is closed under zero. -/
theorem suppLower_zero : SuppLower (0 : TestFn) := by
  intro z hz
  simp

/-- [T26], §3; the lower support predicate is closed under addition. -/
theorem suppLower_add {f g : TestFn} (hf : SuppLower f) (hg : SuppLower g) :
    SuppLower (f + g) := by
  intro z hz
  simp [hf z hz, hg z hz]

/-- [T26], §3; the lower support predicate is closed under complex scalar multiplication. -/
theorem suppLower_smul (c : ℂ) {f : TestFn} (hf : SuppLower f) : SuppLower (c • f) := by
  intro z hz
  simp [hf z hz]

/-- [T26], §3; the lower support predicate is closed under negation. -/
theorem suppLower_neg {f : TestFn} (hf : SuppLower f) : SuppLower (-f) := by
  intro z hz
  simp [hf z hz]

/-- [T26], §3; the lower support predicate is closed under subtraction. -/
theorem suppLower_sub {f g : TestFn} (hf : SuppLower f) (hg : SuppLower g) :
    SuppLower (f - g) := by
  intro z hz
  simp [hf z hz, hg z hz]

/-- A smooth function which vanishes on an open set has all iterated derivatives zero on its
closure. -/
private theorem iteratedDeriv_eq_zero_on_closure {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    {s : Set ℝ} (hs : IsOpen s) (hzero : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) s) (j : ℕ) :
    closure s ⊆ {x : ℝ | iteratedDeriv j g x = 0} := by
  have hderiv : Set.EqOn (iteratedDeriv j g) (fun _ : ℝ => (0 : ℂ)) s := by
    intro x hx
    have hx' := hzero.iteratedDeriv_of_isOpen hs j hx
    simpa using hx'
  have hclosed : IsClosed {x : ℝ | iteratedDeriv j g x = 0} :=
    isClosed_eq (hg.continuous_iteratedDeriv j (by exact_mod_cast le_top)) continuous_const
  exact closure_minimal hderiv hclosed

/-- Iterated derivatives of a periodic smooth function inherit the same period. -/
private theorem periodic_iteratedDeriv {g : ℝ → ℂ} {T : ℝ}
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

/-- A pair of periodic functions agreeing on one half-open period interval agree everywhere. -/
private theorem periodic_eq_of_eq_on_Ico {q r : ℝ → ℂ} {T : ℝ} (hT : 0 < T)
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

/-- [T26], §3; an upper-supported function has zero angle derivatives at both endpoints. -/
theorem iteratedDeriv_toAngle_eq_zero_of_suppUpper {f : TestFn} (h : SuppUpper f) (j : ℕ) :
    iteratedDeriv j (toAngle f) 0 = 0 ∧ iteratedDeriv j (toAngle f) Real.pi = 0 := by
  have hzero_on : Set.EqOn (iteratedDeriv j (toAngle f))
      (fun _ : ℝ => (0 : ℂ)) (Set.Ioo Real.pi (2 * Real.pi)) := by
    intro θ hθ
    have hderiv := (show Set.EqOn (toAngle f) (fun _ : ℝ => (0 : ℂ))
        (Set.Ioo Real.pi (2 * Real.pi)) from fun x hx =>
          (suppUpper_iff_angle f).1 h x hx).iteratedDeriv_of_isOpen isOpen_Ioo j hθ
    simpa using hderiv
  have hclosed : IsClosed {x : ℝ | iteratedDeriv j (toAngle f) x = 0} :=
    isClosed_eq ((contDiff_toAngle f).continuous_iteratedDeriv j (by exact_mod_cast le_top)) continuous_const
  have hclosure : closure (Set.Ioo Real.pi (2 * Real.pi)) ⊆
      {x : ℝ | iteratedDeriv j (toAngle f) x = 0} :=
    closure_minimal hzero_on hclosed
  have hpi : iteratedDeriv j (toAngle f) Real.pi = 0 := by
    apply hclosure
    rw [closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have htwo : iteratedDeriv j (toAngle f) (2 * Real.pi) = 0 := by
    apply hclosure
    rw [closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hper := periodic_iteratedDeriv (periodic_toAngle f) j
  have hzero_at_zero : iteratedDeriv j (toAngle f) 0 = 0 := by
    calc
      iteratedDeriv j (toAngle f) 0 = iteratedDeriv j (toAngle f) (2 * Real.pi) := by
        simpa using (hper 0).symm
      _ = 0 := htwo
  exact ⟨hzero_at_zero, hpi⟩

/-- [T26], §3; a lower-supported function has zero angle derivatives at both endpoints. -/
theorem iteratedDeriv_toAngle_eq_zero_of_suppLower {f : TestFn} (h : SuppLower f) (j : ℕ) :
    iteratedDeriv j (toAngle f) 0 = 0 ∧ iteratedDeriv j (toAngle f) Real.pi = 0 := by
  have hzero : Set.EqOn (iteratedDeriv j (toAngle f)) (fun _ : ℝ => (0 : ℂ))
      (Set.Ioo 0 Real.pi) := by
    have hbase : Set.EqOn (toAngle f) (fun _ : ℝ => (0 : ℂ)) (Set.Ioo 0 Real.pi) :=
      fun x hx => (suppLower_iff_angle f).1 h x hx
    intro θ hθ
    have hderiv := hbase.iteratedDeriv_of_isOpen isOpen_Ioo j hθ
    simpa using hderiv
  have hclosed : IsClosed {x : ℝ | iteratedDeriv j (toAngle f) x = 0} :=
    isClosed_eq ((contDiff_toAngle f).continuous_iteratedDeriv j (by exact_mod_cast le_top)) continuous_const
  have hclosure : closure (Set.Ioo 0 Real.pi) ⊆
      {x : ℝ | iteratedDeriv j (toAngle f) x = 0} :=
    closure_minimal hzero hclosed
  have hzero0 : iteratedDeriv j (toAngle f) 0 = 0 := by
    apply hclosure
    rw [closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hpi : iteratedDeriv j (toAngle f) Real.pi = 0 := by
    apply hclosure
    rw [closure_Ioo (by linarith [Real.pi_pos])]
    exact ⟨by linarith [Real.pi_pos], le_rfl⟩
  exact ⟨hzero0, hpi⟩

/-- [T26], §3; a smooth function vanishing outside `(0, π)` is flat at `0` and `π`. -/
structure IsUpperFlat (g : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ g
  zero_outside : ∀ θ ∉ Set.Ioo 0 Real.pi, g θ = 0

namespace IsUpperFlat

/-- [T26], §3; upper-flat functions have zero iterated derivatives at both endpoints. -/
theorem iteratedDeriv_zero {g : ℝ → ℂ} (h : IsUpperFlat g) (j : ℕ) :
    iteratedDeriv j g 0 = 0 ∧ iteratedDeriv j g Real.pi = 0 := by
  have hleft : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0) := by
    intro x hx
    apply h.zero_outside x
    intro hx'
    exact (not_lt_of_ge hx'.1.le) hx
  have hright : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Ioi Real.pi) := by
    intro x hx
    apply h.zero_outside x
    intro hx'
    exact (not_lt_of_ge hx.le) hx'.2
  have hleft' := iteratedDeriv_eq_zero_on_closure h.contDiff isOpen_Iio hleft j
  have hright' := iteratedDeriv_eq_zero_on_closure h.contDiff isOpen_Ioi hright j
  have h0 : iteratedDeriv j g 0 = 0 := by
    apply hleft'
    rw [closure_Iio]
    simp
  have hpi : iteratedDeriv j g Real.pi = 0 := by
    apply hright'
    rw [closure_Ioi]
    simp
  exact ⟨h0, hpi⟩

end IsUpperFlat

/-- [T26], §3; the zero-extension picture of `C_0^∞(I₊)`. -/
theorem suppUpper_iff_zeroExtension (f : TestFn) :
    SuppUpper f ↔
      ∃ g : ℝ → ℂ, IsUpperFlat g ∧ toAngle f = periodize (2 * Real.pi) g := by
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by
    dsimp [T]
    exact Real.two_pi_pos
  constructor
  · intro h
    let g : ℝ → ℂ := cutIcc 0 Real.pi (toAngle f)
    have hflat := fun j => iteratedDeriv_toAngle_eq_zero_of_suppUpper h j
    have hcont : ContDiff ℝ ∞ g := by
      dsimp [g]
      exact contDiff_cutIcc Real.pi_pos.le (contDiff_toAngle f)
        (fun j => (hflat j).1) (fun j => (hflat j).2)
    have hangle0 : toAngle f 0 = 0 := by
      simpa only [iteratedDeriv_zero] using (hflat 0).1
    have hanglepi : toAngle f Real.pi = 0 := by
      simpa only [iteratedDeriv_zero] using (hflat 0).2
    have hg : IsUpperFlat g := by
      refine ⟨hcont, ?_⟩
      intro θ hθ
      by_cases hθIcc : θ ∈ Set.Icc 0 Real.pi
      · by_cases hθ0 : θ ≤ 0
        · have hθeq : θ = 0 := le_antisymm hθ0 hθIcc.1
          subst θ
          change cutIcc 0 Real.pi (toAngle f) 0 = 0
          rw [cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, Real.pi_pos.le⟩]
          exact hangle0
        · have hθpi : Real.pi ≤ θ := by
            apply le_of_not_gt
            intro hθlt
            exact hθ ⟨lt_of_not_ge hθ0, hθlt⟩
          have hθeq : θ = Real.pi := le_antisymm hθIcc.2 hθpi
          subst θ
          change cutIcc 0 Real.pi (toAngle f) Real.pi = 0
          rw [cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩]
          exact hanglepi
      · change cutIcc 0 Real.pi (toAngle f) θ = 0
        exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc
    have hlocal : ∀ x ∈ Set.Ico 0 T, toAngle f x = periodize T g x := by
      intro x hx
      rw [periodize_eq_self hT hx]
      by_cases hxi : x ∈ Set.Icc 0 Real.pi
      · change toAngle f x = cutIcc 0 Real.pi (toAngle f) x
        exact (cutIcc_eq_of_mem (toAngle f) hxi).symm
      · have hxpi : Real.pi < x := by
          apply lt_of_not_ge
          intro hxle
          exact hxi ⟨hx.1, hxle⟩
        have hzero := (suppUpper_iff_angle f).1 h x ⟨hxpi, hx.2⟩
        change toAngle f x = cutIcc 0 Real.pi (toAngle f) x
        rw [cutIcc_eq_zero_of_notMem (toAngle f) hxi]
        exact hzero
    have heq : toAngle f = periodize T g :=
      periodic_eq_of_eq_on_Ico hT (periodic_toAngle f) (periodic_periodize T hT g) hlocal
    refine ⟨g, hg, ?_⟩
    simpa [T] using heq
  · rintro ⟨g, hg, hfg⟩
    apply (suppUpper_iff_angle f).2
    intro θ hθ
    have hθco : θ ∈ Set.Ico 0 T := by
      constructor
      · exact (le_of_lt Real.pi_pos).trans hθ.1.le
      · simpa [T] using hθ.2
    calc
      toAngle f θ = periodize T g θ := congrFun hfg θ
      _ = g θ := periodize_eq_self hT hθco
      _ = 0 := hg.zero_outside θ (by
        intro hθ'
        exact (not_lt_of_ge (le_of_lt hθ.1)) hθ'.2)

/-- [T26], §3; a smooth function vanishing outside `(π, 2π)` is flat at its endpoints. -/
structure IsLowerFlat (g : ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ g
  zero_outside : ∀ θ ∉ Set.Ioo Real.pi (2 * Real.pi), g θ = 0

namespace IsLowerFlat

/-- [T26], §3; lower-flat functions have zero iterated derivatives at both endpoints. -/
theorem iteratedDeriv_zero {g : ℝ → ℂ} (h : IsLowerFlat g) (j : ℕ) :
    iteratedDeriv j g Real.pi = 0 ∧ iteratedDeriv j g (2 * Real.pi) = 0 := by
  have hleft : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Iio Real.pi) := by
    intro x hx
    apply h.zero_outside x
    intro hx'
    exact (not_lt_of_ge hx'.1.le) hx
  have hright : Set.EqOn g (fun _ : ℝ => (0 : ℂ)) (Set.Ioi (2 * Real.pi)) := by
    intro x hx
    apply h.zero_outside x
    intro hx'
    exact (not_lt_of_ge hx.le) hx'.2
  have hleft' := iteratedDeriv_eq_zero_on_closure h.contDiff isOpen_Iio hleft j
  have hright' := iteratedDeriv_eq_zero_on_closure h.contDiff isOpen_Ioi hright j
  have hpi : iteratedDeriv j g Real.pi = 0 := by
    apply hleft'
    rw [closure_Iio]
    simp
  have htwo : iteratedDeriv j g (2 * Real.pi) = 0 := by
    apply hright'
    rw [closure_Ioi]
    simp
  exact ⟨hpi, htwo⟩

end IsLowerFlat

/-- [T26], §3; the zero-extension picture of `C_0^∞(I₋)`. -/
theorem suppLower_iff_zeroExtension (f : TestFn) :
    SuppLower f ↔
      ∃ g : ℝ → ℂ, IsLowerFlat g ∧ toAngle f = periodize (2 * Real.pi) g := by
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by
    dsimp [T]
    exact Real.two_pi_pos
  constructor
  · intro h
    let g : ℝ → ℂ := cutIcc Real.pi T (toAngle f)
    have hflat0 := fun j => iteratedDeriv_toAngle_eq_zero_of_suppLower h j
    have hperiodic := fun j => periodic_iteratedDeriv (periodic_toAngle f) j
    have hflatT : ∀ j : ℕ, iteratedDeriv j (toAngle f) T = 0 := by
      intro j
      calc
        iteratedDeriv j (toAngle f) T = iteratedDeriv j (toAngle f) 0 := by
          simpa using hperiodic j 0
        _ = 0 := (hflat0 j).1
    have hcont : ContDiff ℝ ∞ g := by
      dsimp [g]
      exact contDiff_cutIcc (by
        dsimp [T]
        linarith [Real.pi_pos]) (contDiff_toAngle f)
        (fun j => (hflat0 j).2) hflatT
    have hangle0 : toAngle f 0 = 0 := by
      simpa only [iteratedDeriv_zero] using (hflat0 0).1
    have hanglepi : toAngle f Real.pi = 0 := by
      simpa only [iteratedDeriv_zero] using (hflat0 0).2
    have hg : IsLowerFlat g := by
      refine ⟨hcont, ?_⟩
      intro θ hθ
      by_cases hθIcc : θ ∈ Set.Icc Real.pi T
      · by_cases hθeq : θ = Real.pi
        · subst θ
          change cutIcc Real.pi T (toAngle f) Real.pi = 0
          rw [cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by
            dsimp [T]
            linarith [Real.pi_pos]⟩]
          exact hanglepi
        · have hθgt : Real.pi < θ := lt_of_le_of_ne hθIcc.1 (Ne.symm hθeq)
          have hθT : T ≤ θ := by
            apply le_of_not_gt
            intro hθlt
            exact hθ ⟨hθgt, hθlt⟩
          have hθeqT : θ = T := le_antisymm hθIcc.2 hθT
          subst θ
          change cutIcc Real.pi T (toAngle f) T = 0
          rw [cutIcc_eq_of_mem (toAngle f) ⟨by
            dsimp [T]
            linarith [Real.pi_pos], le_rfl⟩]
          simpa only [iteratedDeriv_zero] using hflatT 0
      · change cutIcc Real.pi T (toAngle f) θ = 0
        exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc
    have hlocal : ∀ x ∈ Set.Ico 0 T, toAngle f x = periodize T g x := by
      intro x hx
      rw [periodize_eq_self hT hx]
      by_cases hxi : x ∈ Set.Icc Real.pi T
      · change toAngle f x = cutIcc Real.pi T (toAngle f) x
        exact (cutIcc_eq_of_mem (toAngle f) hxi).symm
      · have hxpi : x < Real.pi := by
          apply lt_of_not_ge
          intro hxle
          exact hxi ⟨hxle, hx.2.le⟩
        have hzero : toAngle f x = 0 := by
          by_cases hxzero : x = 0
          · subst x
            exact hangle0
          · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
            exact (suppLower_iff_angle f).1 h x ⟨hxpos, hxpi⟩
        change toAngle f x = cutIcc Real.pi T (toAngle f) x
        rw [cutIcc_eq_zero_of_notMem (toAngle f) hxi]
        exact hzero
    have heq : toAngle f = periodize T g :=
      periodic_eq_of_eq_on_Ico hT (periodic_toAngle f) (periodic_periodize T hT g) hlocal
    refine ⟨g, hg, ?_⟩
    simpa [T] using heq
  · rintro ⟨g, hg, hfg⟩
    apply (suppLower_iff_angle f).2
    intro θ hθ
    have hθco : θ ∈ Set.Ico 0 T := by
      constructor
      · exact hθ.1.le
      · have hpiT : Real.pi < T := by
          dsimp [T]
          linarith [Real.pi_pos]
        exact hθ.2.trans hpiT
    calc
      toAngle f θ = periodize T g θ := congrFun hfg θ
      _ = g θ := periodize_eq_self hT hθco
      _ = 0 := hg.zero_outside θ (by
        intro hθ'
        exact (not_lt_of_ge (le_of_lt hθ.2)) hθ'.1)

/-- [T26], §3; an upper-flat angle function periodizes to an upper-supported test function. -/
theorem exists_suppUpper_toAngle_eq_periodize {g : ℝ → ℂ} (hg : IsUpperFlat g) :
    ∃ f : TestFn, toAngle f = periodize (2 * Real.pi) g ∧ SuppUpper f := by
  have hzero : ∀ θ : ℝ, θ ∉ Set.Ioo 0 (2 * Real.pi) → g θ = 0 := by
    intro θ hθ
    apply hg.zero_outside θ
    intro hθ'
    exact hθ ⟨hθ'.1, hθ'.2.trans (by linarith [Real.pi_pos])⟩
  have hcont : ContDiff ℝ ∞ (periodize (2 * Real.pi) g) :=
    contDiff_periodize Real.two_pi_pos hg.contDiff hzero
  have hper : Function.Periodic (periodize (2 * Real.pi) g) (2 * Real.pi) :=
    periodic_periodize (2 * Real.pi) Real.two_pi_pos g
  obtain ⟨f, hf⟩ := exists_toAngle_eq hcont hper
  refine ⟨f, hf, (suppUpper_iff_zeroExtension f).2 ?_⟩
  exact ⟨g, hg, hf⟩

/-- [T26], §3; a lower-flat angle function periodizes to a lower-supported test function. -/
theorem exists_suppLower_toAngle_eq_periodize {g : ℝ → ℂ} (hg : IsLowerFlat g) :
    ∃ f : TestFn, toAngle f = periodize (2 * Real.pi) g ∧ SuppLower f := by
  have hzero : ∀ θ : ℝ, θ ∉ Set.Ioo 0 (2 * Real.pi) → g θ = 0 := by
    intro θ hθ
    apply hg.zero_outside θ
    intro hθ'
    exact hθ ⟨Real.pi_pos.trans hθ'.1, hθ'.2⟩
  have hcont : ContDiff ℝ ∞ (periodize (2 * Real.pi) g) :=
    contDiff_periodize Real.two_pi_pos hg.contDiff hzero
  have hper : Function.Periodic (periodize (2 * Real.pi) g) (2 * Real.pi) :=
    periodic_periodize (2 * Real.pi) Real.two_pi_pos g
  obtain ⟨f, hf⟩ := exists_toAngle_eq hcont hper
  refine ⟨f, hf, (suppLower_iff_zeroExtension f).2 ?_⟩
  exact ⟨g, hg, hf⟩

/-- [T26], §3; endpoint flatness permits decomposition into upper- and lower-supported parts. -/
theorem exists_suppUpper_add_suppLower_of_flat {f : TestFn}
    (h0 : ∀ j : ℕ, iteratedDeriv j (toAngle f) 0 = 0)
    (hpi : ∀ j : ℕ, iteratedDeriv j (toAngle f) Real.pi = 0) :
    ∃ fUpper fLower : TestFn, SuppUpper fUpper ∧ SuppLower fLower ∧ f = fUpper + fLower := by
  let T : ℝ := 2 * Real.pi
  let gUpper : ℝ → ℂ := cutIcc 0 Real.pi (toAngle f)
  let gLower : ℝ → ℂ := cutIcc Real.pi T (toAngle f)
  have hT : 0 < T := by
    exact Real.two_pi_pos
  have hflatT : ∀ j : ℕ, iteratedDeriv j (toAngle f) T = 0 := by
    intro j
    calc
      iteratedDeriv j (toAngle f) T = iteratedDeriv j (toAngle f) 0 := by
        simpa [T] using periodic_iteratedDeriv (periodic_toAngle f) j 0
      _ = 0 := h0 j
  have hgUpper : IsUpperFlat gUpper := by
    refine ⟨contDiff_cutIcc Real.pi_pos.le (contDiff_toAngle f) h0 hpi, ?_⟩
    intro θ hθ
    by_cases hθIcc : θ ∈ Set.Icc 0 Real.pi
    · by_cases hθ0 : θ = 0
      · subst θ
        rw [show gUpper 0 = toAngle f 0 by
          exact cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, Real.pi_pos.le⟩]
        simpa only [iteratedDeriv_zero] using h0 0
      · by_cases hθpi : θ = Real.pi
        · subst θ
          rw [show gUpper Real.pi = toAngle f Real.pi by
            exact cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩]
          simpa only [iteratedDeriv_zero] using hpi 0
        · exact False.elim (hθ ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθ0),
            lt_of_le_of_ne hθIcc.2 hθpi⟩)
    · exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc
  have hgLower : IsLowerFlat gLower := by
    refine ⟨contDiff_cutIcc (by linarith [Real.pi_pos]) (contDiff_toAngle f) hpi hflatT,
      ?_⟩
    intro θ hθ
    by_cases hθIcc : θ ∈ Set.Icc Real.pi T
    · by_cases hθpi : θ = Real.pi
      · subst θ
        rw [show gLower Real.pi = toAngle f Real.pi by
          exact cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by linarith [Real.pi_pos]⟩]
        simpa only [iteratedDeriv_zero] using hpi 0
      · by_cases hθT : θ = T
        · subst θ
          rw [show gLower T = toAngle f T by
            exact cutIcc_eq_of_mem (toAngle f) ⟨by linarith [Real.pi_pos], le_rfl⟩]
          simpa only [iteratedDeriv_zero] using hflatT 0
        · exact False.elim (hθ ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθpi),
            lt_of_le_of_ne hθIcc.2 hθT⟩)
    · exact cutIcc_eq_zero_of_notMem (toAngle f) hθIcc
  obtain ⟨fUpper, hfUpperAngle, hfUpper⟩ := exists_suppUpper_toAngle_eq_periodize hgUpper
  obtain ⟨fLower, hfLowerAngle, hfLower⟩ := exists_suppLower_toAngle_eq_periodize hgLower
  refine ⟨fUpper, fLower, hfUpper, hfLower, toAngle_injective ?_⟩
  rw [toAngle_add, hfUpperAngle, hfLowerAngle]
  apply periodic_eq_of_eq_on_Ico hT (periodic_toAngle f)
    ((periodic_periodize T hT gUpper).add (periodic_periodize T hT gLower))
  intro θ hθ
  rw [Pi.add_apply, periodize_eq_self hT hθ, periodize_eq_self hT hθ]
  by_cases hθpi : θ = Real.pi
  · subst θ
    rw [show gUpper Real.pi = toAngle f Real.pi by
      exact cutIcc_eq_of_mem (toAngle f) ⟨Real.pi_pos.le, le_rfl⟩]
    rw [show gLower Real.pi = toAngle f Real.pi by
      exact cutIcc_eq_of_mem (toAngle f) ⟨le_rfl, by linarith [Real.pi_pos]⟩]
    have hzero : toAngle f Real.pi = 0 := by
      simpa only [iteratedDeriv_zero] using hpi 0
    simp only [hzero, add_zero]
  · by_cases hθlt : θ < Real.pi
    · rw [show gUpper θ = toAngle f θ by
        exact cutIcc_eq_of_mem (toAngle f) ⟨hθ.1, hθlt.le⟩]
      rw [show gLower θ = 0 by
        exact cutIcc_eq_zero_of_notMem (toAngle f) (fun hmem => not_le_of_gt hθlt hmem.1)]
      exact (add_zero _).symm
    · have hθgt : Real.pi < θ := lt_of_le_of_ne (le_of_not_gt hθlt) (Ne.symm hθpi)
      rw [show gUpper θ = 0 by
        exact cutIcc_eq_zero_of_notMem (toAngle f) (fun hmem => not_le_of_gt hθgt hmem.2)]
      rw [show gLower θ = toAngle f θ by
        exact cutIcc_eq_of_mem (toAngle f) ⟨hθgt.le, hθ.2.le⟩]
      exact (zero_add _).symm

/-- [T26], §3; the closure of the open upper semicircle is the closed upper semicircle. -/
theorem closure_upperArc :
    closure upperArc = {z : Circle | 0 ≤ (z : ℂ).im} := by
  have hclosed : IsClosed {z : Circle | 0 ≤ (z : ℂ).im} :=
    isClosed_le continuous_const (Complex.continuous_im.comp continuous_subtype_val)
  have hsubset : upperArc ⊆ {z : Circle | 0 ≤ (z : ℂ).im} := by
    intro z hz
    change 0 < (z : ℂ).im at hz
    exact hz.le
  apply Subset.antisymm
  · exact closure_minimal hsubset hclosed
  · intro z hz
    by_cases hzpos : 0 < (z : ℂ).im
    · exact subset_closure hzpos
    change 0 ≤ (z : ℂ).im at hz
    have hzim : (z : ℂ).im = 0 := le_antisymm (le_of_not_gt hzpos) hz
    have hnorm : Complex.normSq (z : ℂ) = 1 := by
      exact Circle.normSq_coe z
    have hresq : ((z : ℂ).re) ^ 2 = 1 := by
      simpa [Complex.normSq_apply, hzim, pow_two] using hnorm
    have hzero_mem : (0 : ℝ) ∈ closure (Set.Ioo 0 Real.pi) := by
      rw [closure_Ioo (ne_of_lt Real.pi_pos)]
      exact ⟨le_rfl, Real.pi_pos.le⟩
    have hpi_mem : Real.pi ∈ closure (Set.Ioo 0 Real.pi) := by
      rw [closure_Ioo (ne_of_lt Real.pi_pos)]
      exact ⟨Real.pi_pos.le, le_rfl⟩
    have hone : (1 : Circle) ∈ closure upperArc := by
      apply mem_closure_iff_nhds.mpr
      intro U hU
      have hU' : U ∈ 𝓝 (Circle.exp 0) := by simpa using hU
      have hpre : Circle.exp ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
        Circle.exp.continuous.continuousAt.preimage_mem_nhds hU'
      obtain ⟨θ, hθ⟩ := (mem_closure_iff_nhds.mp hzero_mem) (Circle.exp ⁻¹' U) hpre
      refine ⟨Circle.exp θ, hθ.1, ?_⟩
      exact (mem_upperArc_circleExp).2 ⟨0, by simpa using hθ.2⟩
    have hminus : Circle.exp Real.pi = (-1 : Circle) := by
      apply Circle.ext
      simp [Circle.coe_exp, Complex.exp_pi_mul_I]
    have hneg : (-1 : Circle) ∈ closure upperArc := by
      apply mem_closure_iff_nhds.mpr
      intro U hU
      have hU' : U ∈ 𝓝 (Circle.exp Real.pi) := by simpa [hminus] using hU
      have hpre : Circle.exp ⁻¹' U ∈ 𝓝 Real.pi :=
        Circle.exp.continuous.continuousAt.preimage_mem_nhds hU'
      obtain ⟨θ, hθ⟩ := (mem_closure_iff_nhds.mp hpi_mem) (Circle.exp ⁻¹' U) hpre
      refine ⟨Circle.exp θ, hθ.1, ?_⟩
      exact (mem_upperArc_circleExp).2 ⟨0, by simpa using hθ.2⟩
    rcases (sq_eq_one_iff.mp hresq) with hre | hre
    · have hz1 : z = (1 : Circle) := by
        apply Circle.ext
        apply Complex.ext
        · simpa using hre
        · simpa using hzim
      simpa [hz1] using hone
    · have hzminus : z = (-1 : Circle) := by
        apply Circle.ext
        apply Complex.ext
        · simpa using hre
        · simpa using hzim
      simpa [hzminus] using hneg

/-- [T26], §3; upper support is equivalent to closed topological support in the closed upper
semicircle. -/
theorem suppUpper_iff_tsupport (f : TestFn) :
    SuppUpper f ↔ tsupport (f : Circle → ℂ) ⊆ closure upperArc := by
  constructor
  · intro h
    rw [tsupport]
    apply closure_minimal _ isClosed_closure
    intro z hz
    by_contra hzclosure
    have hzlower : z ∈ lowerArc := by
      rw [closure_upperArc] at hzclosure
      change ¬ (0 ≤ (z : ℂ).im) at hzclosure
      exact lt_of_not_ge hzclosure
    exact hz (h z hzlower)
  · intro h z hz
    by_contra hne
    have hzsupport : z ∈ Function.support (f : Circle → ℂ) := hne
    have hzclosure := h (subset_tsupport (f : Circle → ℂ) hzsupport)
    rw [closure_upperArc] at hzclosure
    change 0 ≤ (z : ℂ).im at hzclosure
    change (z : ℂ).im < 0 at hz
    exact (not_lt_of_ge hzclosure) hz

/-- [T26], §3; support compactly contained in the open upper semicircle implies upper support. -/
theorem suppUpper_of_tsupport_subset {f : TestFn}
    (h : tsupport (f : Circle → ℂ) ⊆ upperArc) : SuppUpper f := by
  apply (suppUpper_iff_tsupport f).2
  exact h.trans subset_closure

/-- [T26], §3; compact containment in the open upper semicircle is strictly stronger than the
closure support convention. -/
theorem exists_suppUpper_not_tsupport_subset :
    ∃ f : TestFn, SuppUpper f ∧ ¬ tsupport (f : Circle → ℂ) ⊆ upperArc := by
  let g : ℝ → ℂ := fun θ =>
    ((expNegInvGlue θ * expNegInvGlue (Real.pi - θ) : ℝ) : ℂ)
  have hreal : ContDiff ℝ ∞
      (fun θ : ℝ => expNegInvGlue θ * expNegInvGlue (Real.pi - θ)) := by
    exact expNegInvGlue.contDiff.mul
      (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))
  have hgcont : ContDiff ℝ ∞ g := by
    simpa only [g, Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_mul] using
      Complex.ofRealCLM.contDiff.comp hreal
  have hgzero : ∀ θ : ℝ, θ ∉ Set.Ioo 0 Real.pi → g θ = 0 := by
    intro θ hθ
    by_cases hθ0 : θ ≤ 0
    · simp [g, expNegInvGlue.zero_of_nonpos hθ0]
    · have hθpi : Real.pi ≤ θ := by
        apply le_of_not_gt
        intro hθlt
        exact hθ ⟨lt_of_not_ge hθ0, hθlt⟩
      have hnonpos : Real.pi - θ ≤ 0 := sub_nonpos.mpr hθpi
      simp [g, expNegInvGlue.zero_of_nonpos hnonpos]
  have hg : IsUpperFlat g := ⟨hgcont, hgzero⟩
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by
    dsimp [T]
    exact Real.two_pi_pos
  have hg_periodize_zero : ∀ θ : ℝ, θ ∉ Set.Ioo 0 T → g θ = 0 := by
    intro θ hθ
    apply hgzero θ
    intro hθ'
    have hpiT : Real.pi < T := by
      dsimp [T]
      linarith [Real.pi_pos]
    exact hθ ⟨hθ'.1, hθ'.2.trans hpiT⟩
  have hperiodized : ContDiff ℝ ∞ (periodize T g) :=
    contDiff_periodize hT hgcont hg_periodize_zero
  have hperiodized_periodic : Function.Periodic (periodize T g) T :=
    periodic_periodize T hT g
  obtain ⟨f, hf⟩ := exists_toAngle_eq hperiodized hperiodized_periodic
  have hfupper : SuppUpper f := by
    apply (suppUpper_iff_zeroExtension f).2
    refine ⟨g, hg, ?_⟩
    simpa [T] using hf
  have hgpos : ∀ θ ∈ Set.Ioo 0 Real.pi,
      0 < expNegInvGlue θ * expNegInvGlue (Real.pi - θ) := by
    intro θ hθ
    exact mul_pos (expNegInvGlue.pos_of_pos hθ.1)
      (expNegInvGlue.pos_of_pos (sub_pos.mpr hθ.2))
  have hfnonzero : ∀ z ∈ upperArc, f z ≠ 0 := by
    intro z hz
    obtain ⟨θ, hθz⟩ := Circle.exp_surjective z
    have hz' : Circle.exp θ ∈ upperArc := by simpa [hθz] using hz
    obtain ⟨k, hk⟩ := (mem_upperArc_circleExp).1 hz'
    have hxco : θ - T * (k : ℝ) ∈ Set.Ico 0 T := by
      have hxI : θ - T * (k : ℝ) ∈ Set.Ioo 0 Real.pi := by
        simpa [T, mul_comm] using hk
      exact ⟨le_of_lt hxI.1, lt_trans hxI.2 (by
        dsimp [T]
        linarith [Real.pi_pos])⟩
    have hxperiodize : periodize T g (θ - T * (k : ℝ)) =
        g (θ - T * (k : ℝ)) := periodize_eq_self hT hxco
    have hxpos : 0 < expNegInvGlue (θ - T * (k : ℝ)) *
        expNegInvGlue (Real.pi - (θ - T * (k : ℝ))) := by
      have hxI : θ - T * (k : ℝ) ∈ Set.Ioo 0 Real.pi := by
        simpa [T, mul_comm] using hk
      exact hgpos _ hxI
    have hxne : g (θ - T * (k : ℝ)) ≠ 0 := by
      dsimp [g]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hxpos)
    have hxangle : toAngle f (θ - T * (k : ℝ)) ≠ 0 := by
      rw [hf, hxperiodize]
      exact hxne
    have hexp : Circle.exp (θ - T * (k : ℝ)) = z := by
      calc
        Circle.exp (θ - T * (k : ℝ)) = Circle.exp θ := by
          apply Circle.exp_eq_exp.mpr
          refine ⟨-k, ?_⟩
          rw [Int.cast_neg]
          dsimp [T]
          ring
        _ = z := hθz
    intro hfzero
    apply hxangle
    change f (Circle.exp (θ - T * (k : ℝ))) = 0
    rw [hexp]
    exact hfzero
  have hupper_ts : upperArc ⊆ tsupport (f : Circle → ℂ) := by
    intro z hz
    exact subset_tsupport (f : Circle → ℂ) (hfnonzero z hz)
  have hone_closure : (1 : Circle) ∈ closure upperArc := by
    rw [closure_upperArc]
    simp
  have hone_ts : (1 : Circle) ∈ tsupport (f : Circle → ℂ) := by
    exact closure_minimal hupper_ts (isClosed_tsupport (f : Circle → ℂ)) hone_closure
  refine ⟨f, hfupper, ?_⟩
  intro hsubset
  have hone_upper : (1 : Circle) ∈ upperArc := hsubset hone_ts
  simp [upperArc] at hone_upper

/-! ### General closed support -/

/-- [T26], §2.2 and Definition 2.5; the closed support of a test function, namely the closure in
`Circle` of the set where the function is nonzero. This is the general notion used in Wightman
locality (W2); `SuppUpper` and `SuppLower` are the two specific semicircle cases. -/
def support (f : TestFn) : Set Circle :=
  tsupport (f : Circle → ℂ)

/-- The closed support is the closure of the set on which the test function is nonzero. -/
theorem support_def (f : TestFn) : support f = closure {z : Circle | f z ≠ 0} :=
  rfl

/-- The support of a test function is closed. -/
theorem isClosed_support (f : TestFn) : IsClosed (support f) :=
  isClosed_tsupport (f : Circle → ℂ)

/-- A test function vanishes at every point outside its closed support. -/
theorem notMem_support (f : TestFn) {z : Circle} (h : z ∉ support f) : f z = 0 :=
  image_eq_zero_of_notMem_tsupport h

/-- The zero test function has empty support. -/
theorem support_zero : support (0 : TestFn) = ∅ := by
  change tsupport ((0 : TestFn) : Circle → ℂ) = ∅
  rw [TestFn.coe_zero]
  exact tsupport_zero

/-- Negation does not change the support of a test function. -/
theorem support_neg (f : TestFn) : support (-f) = support f := by
  change tsupport ((-f : TestFn) : Circle → ℂ) = tsupport (f : Circle → ℂ)
  rw [TestFn.coe_neg]
  exact tsupport_neg (f : Circle → ℂ)

/-- Scalar multiplication cannot enlarge the support of a test function. -/
theorem support_smul_subset (c : ℂ) (f : TestFn) : support (c • f) ⊆ support f := by
  change tsupport (fun z : Circle => c * f z) ⊆ tsupport (f : Circle → ℂ)
  simpa only [smul_eq_mul] using
    (tsupport_smul_subset_right (fun _ : Circle => c) (f : Circle → ℂ))

/-- The support of a sum is contained in the union of the two supports. -/
theorem support_add_subset (f g : TestFn) : support (f + g) ⊆ support f ∪ support g := by
  change tsupport ((f + g : TestFn) : Circle → ℂ) ⊆
    tsupport (f : Circle → ℂ) ∪ tsupport (g : Circle → ℂ)
  rw [TestFn.coe_add]
  exact tsupport_add (f : Circle → ℂ) (g : Circle → ℂ)

/-- [T26], Definition 2.5; the disjoint-supports relation used in locality (W2).

Upper and lower support do not imply this relation: their closed supports may both contain the
endpoints `{1, -1}`. -/
def DisjointSupport (f g : TestFn) : Prop :=
  Disjoint (support f) (support g)

/-- Disjoint support is symmetric. -/
theorem disjointSupport_comm (f g : TestFn) :
    DisjointSupport f g ↔ DisjointSupport g f := by
  unfold DisjointSupport
  exact disjoint_comm

/-- At every point, one of two test functions with disjoint supports vanishes. -/
theorem DisjointSupport.eq_zero_or_eq_zero {f g : TestFn} (h : DisjointSupport f g)
    (z : Circle) : f z = 0 ∨ g z = 0 := by
  by_cases hf : f z = 0
  · exact Or.inl hf
  · right
    apply notMem_support g
    intro hzg
    have hzf : z ∈ support f := subset_tsupport (f : Circle → ℂ) hf
    exact (Set.disjoint_left.mp h) hzf hzg

/-- The zero test function has support disjoint from every test function. -/
theorem disjointSupport_zero_left (g : TestFn) : DisjointSupport 0 g := by
  simpa only [DisjointSupport, support_zero] using Set.empty_disjoint (support g)

/-- [T26], §3; the closure of the open lower semicircle is the closed lower semicircle. -/
theorem closure_lowerArc :
    closure lowerArc = {z : Circle | (z : ℂ).im ≤ 0} := by
  have hpreimage : (Homeomorph.inv Circle) ⁻¹' upperArc = lowerArc := by
    ext z
    change 0 < ((z⁻¹ : Circle) : ℂ).im ↔ (z : ℂ).im < 0
    rw [Circle.coe_inv_eq_conj, Complex.conj_im]
    exact neg_pos
  calc
    closure lowerArc = closure ((Homeomorph.inv Circle) ⁻¹' upperArc) := by
      rw [hpreimage]
    _ = (Homeomorph.inv Circle) ⁻¹' closure upperArc :=
      ((Homeomorph.inv Circle).preimage_closure upperArc).symm
    _ = {z : Circle | (z : ℂ).im ≤ 0} := by
      rw [closure_upperArc]
      ext z
      change 0 ≤ ((z⁻¹ : Circle) : ℂ).im ↔ (z : ℂ).im ≤ 0
      rw [Circle.coe_inv_eq_conj, Complex.conj_im]
      exact neg_nonneg

/-- [T26], §3; `SuppUpper` is the general closed-support condition for the closed upper
semicircle. -/
theorem suppUpper_iff_support (f : TestFn) :
    SuppUpper f ↔ support f ⊆ closure upperArc :=
  suppUpper_iff_tsupport f

/-- [T26], §3; `SuppLower` is the general closed-support condition for the closed lower
semicircle. -/
theorem suppLower_iff_support (f : TestFn) :
    SuppLower f ↔ support f ⊆ closure lowerArc := by
  constructor
  · intro h
    rw [support, tsupport]
    apply closure_minimal _ isClosed_closure
    intro z hz
    by_contra hzclosure
    have hzupper : z ∈ upperArc := by
      rw [closure_lowerArc] at hzclosure
      change ¬(z : ℂ).im ≤ 0 at hzclosure
      exact lt_of_not_ge hzclosure
    exact hz (h z hzupper)
  · intro h z hz
    by_contra hne
    have hzsupport : z ∈ Function.support (f : Circle → ℂ) := hne
    have hzclosure := h (subset_tsupport (f : Circle → ℂ) hzsupport)
    rw [closure_lowerArc] at hzclosure
    change (z : ℂ).im ≤ 0 at hzclosure
    change 0 < (z : ℂ).im at hz
    exact (not_lt_of_ge hzclosure) hz

/-- [T26], §3; lower support is equivalent to closed topological support in the closed lower
semicircle. -/
theorem suppLower_iff_tsupport (f : TestFn) :
    SuppLower f ↔ tsupport (f : Circle → ℂ) ⊆ closure lowerArc :=
  suppLower_iff_support f

/-- [T26], §3; support compactly contained in the open lower semicircle implies lower support. -/
theorem suppLower_of_tsupport_subset {f : TestFn}
    (h : tsupport (f : Circle → ℂ) ⊆ lowerArc) : SuppLower f := by
  apply (suppLower_iff_tsupport f).2
  exact h.trans subset_closure

/-- [T26], §3; compact containment in the open lower semicircle is strictly stronger than the
closure support convention. -/
theorem exists_suppLower_not_tsupport_subset :
    ∃ f : TestFn, SuppLower f ∧ ¬ tsupport (f : Circle → ℂ) ⊆ lowerArc := by
  obtain ⟨f, hf, hnot⟩ := exists_suppUpper_not_tsupport_subset
  let f' : TestFn :=
    ⟨fun z => f z⁻¹, by
      change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
        ((f : Circle → ℂ) ∘ (fun z : Circle => z⁻¹))
      exact (ContMDiffMap.contMDiff f).comp (contMDiff_inv (𝓡 1) ∞)⟩
  have hf' : SuppLower f' := by
    intro z hz
    change 0 < (z : ℂ).im at hz
    apply hf z⁻¹
    change ((z⁻¹ : Circle) : ℂ).im < 0
    rw [Circle.coe_inv_eq_conj, Complex.conj_im]
    exact neg_lt_zero.mpr hz
  obtain ⟨z, hzts, hzupper⟩ := Set.not_subset.mp hnot
  refine ⟨f', hf', ?_⟩
  intro hsubset
  have htsupport :
      tsupport (fun w : Circle => f w⁻¹) =
        (Homeomorph.inv Circle) ⁻¹' tsupport (f : Circle → ℂ) := by
    simpa only [Function.comp_def, Homeomorph.coe_inv] using
      tsupport_comp_eq_preimage (f : Circle → ℂ) (Homeomorph.inv Circle)
  have hzinv : z⁻¹ ∈ tsupport (f' : Circle → ℂ) := by
    change z⁻¹ ∈ tsupport (fun w : Circle => f w⁻¹)
    rw [htsupport]
    simpa using hzts
  have hzlower := hsubset hzinv
  apply hzupper
  change 0 < (z : ℂ).im
  change ((z⁻¹ : Circle) : ℂ).im < 0 at hzlower
  rw [Circle.coe_inv_eq_conj, Complex.conj_im] at hzlower
  exact neg_lt_zero.mp hzlower

/-- [T26], §3; not every test function splits into upper- and lower-supported summands. -/
theorem not_forall_exists_suppUpper_add_suppLower :
    ¬ ∀ f : TestFn, ∃ fUpper fLower : TestFn,
      SuppUpper fUpper ∧ SuppLower fLower ∧ f = fUpper + fLower := by
  intro h
  let one : TestFn := ⟨fun _ : Circle => (1 : ℂ), contMDiff_const⟩
  obtain ⟨fUpper, fLower, hfUpper, hfLower, hsum⟩ := h one
  have hfUpperOne : Set.EqOn (fun z : Circle => fUpper z) (fun _ => (1 : ℂ)) upperArc := by
    intro z hz
    have hpoint := congrArg (fun q : TestFn => q z) hsum
    change (1 : ℂ) = fUpper z + fLower z at hpoint
    rw [hfLower z hz, add_zero] at hpoint
    exact hpoint.symm
  have hfUpperZero : Set.EqOn (fun z : Circle => fUpper z) (fun _ => (0 : ℂ)) lowerArc :=
    hfUpper
  have hfUpperOneClosure := hfUpperOne.closure
    (ContMDiffMap.contMDiff fUpper).continuous continuous_const
  have hfUpperZeroClosure := hfUpperZero.closure
    (ContMDiffMap.contMDiff fUpper).continuous continuous_const
  have hone_upper : (1 : Circle) ∈ closure upperArc := by
    rw [closure_upperArc]
    simp
  have hone_lower : (1 : Circle) ∈ closure lowerArc := by
    rw [closure_lowerArc]
    simp
  have hone : fUpper (1 : Circle) = 1 := hfUpperOneClosure hone_upper
  have hzero : fUpper (1 : Circle) = 0 := hfUpperZeroClosure hone_lower
  exact one_ne_zero (hone.symm.trans hzero)

end

end MobiusCPT
