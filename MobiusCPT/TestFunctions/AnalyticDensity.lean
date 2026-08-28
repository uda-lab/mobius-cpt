import MobiusCPT.Analysis.BoostDictionary
import MobiusCPT.Analysis.BoostWeights
import MobiusCPT.TestFunctions.CNorm
import MobiusCPT.TestFunctions.AnalyticApprox

/-!
# [T26], Lemma 3.4: density of the analytic restrictions

The upper-supported test functions lie in the closure of `{F|_{I₊} : F ∈ 𝓧}`.  The approximants are
the Gaussian smoothings of the boost picture of `z · f`, transported back to `𝕆` by
`MobiusCPT.stripApprox`; the convergence is read off in the boost coordinate, where the
`C^N(S¹)` seminorms become the exponentially weighted `C^N(ℝ)` seminorms of
`MobiusCPT.exists_norm_iteratedDeriv_boostChart_le`.
-/

namespace MobiusCPT

noncomputable section

open Filter Set
open scoped ContDiff Topology

/-! ### The boost picture of an upper-supported test function -/

/-- [T26], proof of Lemma 3.4; the angle picture of `z · f` on the closed upper semicircle. -/
def upperAnglePicture (f : TestFn) : ℝ → ℂ :=
  fun θ => Complex.exp (θ * Complex.I) * cutIcc 0 Real.pi (toAngle f) θ

/-- The angle picture of `z · f` is smooth and supported in the upper semicircle. -/
theorem isUpperFlat_upperAnglePicture {f : TestFn} (hf : SuppUpper f) :
    IsUpperFlat (upperAnglePicture f) := by
  have hcut : IsUpperFlat (cutIcc 0 Real.pi (toAngle f)) :=
    (IsEndpointFlat.of_suppUpper hf).isUpperFlat_cutIcc
  refine ⟨?_, ?_⟩
  · exact contDiff_circle_map.mul hcut.contDiff
  · intro θ hθ
    rw [upperAnglePicture, hcut.zero_outside θ hθ, mul_zero]

/-- The angle bridge is additive on differences. -/
theorem toAngle_sub (g h : TestFn) : toAngle (g - h) = toAngle g - toAngle h := by
  funext θ
  have h1 : toAngle (g - h + h) θ = toAngle (g - h) θ + toAngle h θ := by
    rw [toAngle_add]
    rfl
  have h2 : g - h + h = g := by abel
  rw [h2] at h1
  show toAngle (g - h) θ = toAngle g θ - toAngle h θ
  rw [h1]
  ring

/-- [T26], proof of Lemma 3.4; the boost picture of `z · f`. -/
def boostPicture (f : TestFn) : ℝ → ℂ :=
  fun x => upperAnglePicture f (boostToAngle x)

/-- The boost picture of an upper-supported test function decays faster than every exponential. -/
theorem isRapidlyDecaying_boostPicture {f : TestFn} (hf : SuppUpper f) :
    IsRapidlyDecaying (boostPicture f) :=
  isRapidlyDecaying_comp_boostToAngle (isUpperFlat_upperAnglePicture hf)

/-- [T26], proof of Lemma 3.4; the approximating sequence in `𝓧`. -/
def approx (f : TestFn) (hf : SuppUpper f) (n : ℕ) : AnalyticTestFn :=
  stripApproxX (s := 1 / (n + 1)) (by positivity) (isRapidlyDecaying_boostPicture hf)

/-! ### The difference, read in the boost coordinate -/

/-- The angle picture of the error, with the phase `z` removed. -/
def errorAngle (f : TestFn) (hf : SuppUpper f) (n : ℕ) : ℝ → ℂ :=
  fun θ => Complex.exp (θ * Complex.I) *
    toAngle (xRestrictUpper (approx f hf n) - f) θ

/-- The angle picture of the error is smooth. -/
theorem contDiff_errorAngle (f : TestFn) (hf : SuppUpper f) (n : ℕ) :
    ContDiff ℝ ∞ (errorAngle f hf n) :=
  contDiff_circle_map.mul (contDiff_toAngle _)

/-- [T26], proof of Lemma 3.4; in the boost coordinate the error is exactly the Gaussian
smoothing error of the boost picture. -/
theorem errorAngle_boostToAngle (f : TestFn) (hf : SuppUpper f) (n : ℕ) (x : ℝ) :
    errorAngle f hf n (boostToAngle x) =
      gaussConv (1 / (n + 1)) (boostPicture f) (x : ℂ) - boostPicture f x := by
  have hθ : boostToAngle x ∈ Set.Ioo 0 Real.pi := boostToAngle_mem_Ioo x
  have hθIcc : boostToAngle x ∈ Set.Icc 0 Real.pi := ⟨hθ.1.le, hθ.2.le⟩
  have hx : angleToBoost (boostToAngle x) = x := angleToBoost_boostToAngle x
  have hne : Complex.exp ((boostToAngle x : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hsub : toAngle (xRestrictUpper (approx f hf n) - f) (boostToAngle x) =
      toAngle (xRestrictUpper (approx f hf n)) (boostToAngle x) -
        toAngle f (boostToAngle x) := by
    rw [toAngle_sub]
    rfl
  have hupper : toAngle (xRestrictUpper (approx f hf n)) (boostToAngle x) =
      toAngle (xRestrictS1 (approx f hf n)) (boostToAngle x) :=
    toAngle_splitUpper_of_mem (AnalyticTestFn.isEndpointFlat _) hθIcc
  have hval : toAngle (xRestrictS1 (approx f hf n)) (boostToAngle x) =
      gaussConv (1 / (n + 1)) (boostPicture f) (x : ℂ) /
        Complex.exp ((boostToAngle x : ℝ) * Complex.I) := by
    rw [toAngle_xRestrictS1]
    show (approx f hf n).toFun (Circle.exp (boostToAngle x)) = _
    rw [Circle.coe_exp]
    show stripApprox (1 / (n + 1)) (boostPicture f)
      (Complex.exp ((boostToAngle x : ℝ) * Complex.I)) = _
    rw [stripApprox_circleExp hθ, hx]
  have hf' : toAngle f (boostToAngle x) =
      boostPicture f x / Complex.exp ((boostToAngle x : ℝ) * Complex.I) := by
    have hcut : cutIcc 0 Real.pi (toAngle f) (boostToAngle x) = toAngle f (boostToAngle x) :=
      cutIcc_eq_of_mem (toAngle f) hθIcc
    rw [boostPicture, upperAnglePicture, hcut]
    field_simp
  rw [errorAngle, hsub, hupper, hval, hf']
  field_simp

/-! ### The `C^N` estimate -/

/-- Every iterated derivative of the phase `e^{iθ}` has norm one. -/
theorem norm_iteratedFDeriv_circle_map_eq (q : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ q (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) θ‖ = 1 := by
  have hiter : ∀ i : ℕ,
      iteratedDeriv i (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.I ^ i * Complex.exp ((t : ℂ) * Complex.I) := by
    intro i
    induction i with
    | zero => funext t; simp
    | succ i ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        have hbase : HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I))
            (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
          have h1 : HasDerivAt (fun u : ℝ => ((u : ℂ) * Complex.I)) Complex.I t := by
            simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
          simpa using h1.cexp
        have hd : HasDerivAt (fun u : ℝ => Complex.I ^ i * Complex.exp ((u : ℂ) * Complex.I))
            (Complex.I ^ i * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)) t :=
          hbase.const_mul _
        rw [hd.deriv]
        ring
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter q]
  simp [Complex.norm_exp_ofReal_mul_I]

/-- The `C^N` norm is controlled by a uniform bound on the angle derivatives. -/
theorem cnorm_le_of_forall {N : ℕ} {h : TestFn} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ j : ℕ, j ≤ N → ∀ θ : ℝ, ‖angleDeriv j h θ‖ ≤ C) :
    (cnorm N h : ℝ) ≤ (N + 1) * C := by
  rw [cnorm_eq]
  have hterm : ∀ j ∈ Finset.range (N + 1), ‖angleDerivB j h‖ ≤ C := by
    intro j hj
    refine (BoundedContinuousFunction.norm_le hC).mpr ?_
    intro θ
    rw [angleDerivB_apply]
    exact hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) θ
  calc
    ∑ j ∈ Finset.range (N + 1), ‖angleDerivB j h‖ ≤ ∑ _j ∈ Finset.range (N + 1), C :=
      Finset.sum_le_sum hterm
    _ = (N + 1) * C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- Every iterated derivative of the conjugate phase `e^{-iθ}` has norm one. -/
theorem norm_iteratedFDeriv_circle_map_neg_eq (q : ℕ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ q (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) θ‖ = 1 := by
  have hiter : ∀ i : ℕ,
      iteratedDeriv i (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) =
        fun t : ℝ => (-Complex.I) ^ i * Complex.exp (-(t : ℂ) * Complex.I) := by
    intro i
    induction i with
    | zero => funext t; simp
    | succ i ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        have hbase : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ) * Complex.I))
            (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := by
          have h1 : HasDerivAt (fun u : ℝ => (-(u : ℂ) * Complex.I)) (-Complex.I) t := by
            simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).neg).mul_const Complex.I
          simpa using h1.cexp
        have hd : HasDerivAt
            (fun u : ℝ => (-Complex.I) ^ i * Complex.exp (-(u : ℂ) * Complex.I))
            ((-Complex.I) ^ i * (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I))) t :=
          hbase.const_mul _
        rw [hd.deriv]
        ring
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter q]
  have hnorm : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    have : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, norm_pow, hnorm, norm_neg, Complex.norm_I]
  simp

/-- The angle picture of the error is the conjugate phase times `errorAngle`. -/
theorem toAngle_error_eq (f : TestFn) (hf : SuppUpper f) (n : ℕ) :
    toAngle (xRestrictUpper (approx f hf n) - f) =
      fun θ : ℝ => Complex.exp (-(θ : ℂ) * Complex.I) * errorAngle f hf n θ := by
  funext θ
  rw [errorAngle, ← mul_assoc, ← Complex.exp_add]
  have hzero : -(θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]

/-- An upper-supported test function has vanishing angle derivatives on the closed lower
semicircle. -/
theorem angleDeriv_eq_zero_of_suppUpper {h : TestFn} (hh : SuppUpper h) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Icc Real.pi (2 * Real.pi)) : angleDeriv j h θ = 0 := by
  have hzero : Set.EqOn (toAngle h) (fun _ : ℝ => (0 : ℂ)) (Set.Ioo Real.pi (2 * Real.pi)) := by
    intro y hy
    exact (suppUpper_iff_angle h).1 hh y hy
  have hopen : IsOpen (Set.Ioo Real.pi (2 * Real.pi)) := isOpen_Ioo
  rcases eq_or_lt_of_le hθ.1 with hpi | hpi
  · rw [angleDeriv, ← hpi]
    exact (iteratedDeriv_toAngle_eq_zero_of_suppUpper hh j).2
  rcases eq_or_lt_of_le hθ.2 with htwo | htwo
  · have hper : Function.Periodic (angleDeriv j h) (2 * Real.pi) := periodic_angleDeriv j h
    have h0 : angleDeriv j h 0 = 0 := (iteratedDeriv_toAngle_eq_zero_of_suppUpper hh j).1
    have := hper 0
    rw [zero_add] at this
    rw [htwo, this, h0]
  · have hmem : θ ∈ Set.Ioo Real.pi (2 * Real.pi) := ⟨hpi, htwo⟩
    have := hzero.iteratedDeriv_of_isOpen hopen j hmem
    simpa [angleDeriv] using this

/-- [T26], proof of Lemma 3.4; the boost-side smallness of the error transfers to the
`C^N` seminorms on the circle. -/
theorem exists_norm_angleDeriv_le {f : TestFn} (hf : SuppUpper f) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (M : ℝ), 0 ≤ M →
      (∀ i : ℕ, i ≤ N → ∀ x : ℝ,
        ‖iteratedDeriv i (fun y : ℝ =>
            gaussConv (1 / (n + 1)) (boostPicture f) (y : ℂ) - boostPicture f y) x‖ ≤
          M * Real.exp (-(N : ℝ) * |x|)) →
      ∀ j : ℕ, j ≤ N → ∀ θ : ℝ,
        ‖angleDeriv j (xRestrictUpper (approx f hf n) - f) θ‖ ≤ K * M := by
  choose K hK0 hK using fun q : ℕ => exists_norm_iteratedDeriv_boostChart_le q
  refine ⟨((N : ℝ) + 1) * (∑ j ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j + 1),
      (j.choose p : ℝ)) * (∑ q ∈ Finset.range (N + 1), K q), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j + 1),
        (j.choose p : ℝ) := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ => by positivity
    have h2 : (0 : ℝ) ≤ ∑ q ∈ Finset.range (N + 1), K q :=
      Finset.sum_nonneg fun q _ => hK0 q
    positivity
  intro n M hM hbound j hj θ
  set h : TestFn := xRestrictUpper (approx f hf n) - f with hhdef
  have hsupp : SuppUpper h := by
    rw [hhdef]
    exact suppUpper_sub (xRestrictUpper_supp _) hf
  set v : ℝ → ℂ := fun y : ℝ =>
    gaussConv (1 / (n + 1)) (boostPicture f) (y : ℂ) - boostPicture f y with hvdef
  have hbin : (0 : ℝ) ≤ ∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ) :=
    Finset.sum_nonneg fun p _ => by positivity
  have hKsum : (0 : ℝ) ≤ ∑ q ∈ Finset.range (N + 1), K q :=
    Finset.sum_nonneg fun q _ => hK0 q
  have hbinsum : ∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ) ≤
      ∑ j' ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j' + 1), (j'.choose p : ℝ) := by
    refine Finset.single_le_sum
      (f := fun j' : ℕ => ∑ p ∈ Finset.range (j' + 1), (j'.choose p : ℝ))
      (fun j' _ => Finset.sum_nonneg fun p _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  -- the total constant
  set Ktot : ℝ := ((N : ℝ) + 1) * (∑ j' ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j' + 1),
    (j'.choose p : ℝ)) * (∑ q ∈ Finset.range (N + 1), K q) with hKtot
  have hKtot0 : 0 ≤ Ktot := by
    rw [hKtot]
    have hb : (0 : ℝ) ≤ ∑ j' ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j' + 1),
        (j'.choose p : ℝ) := Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun p _ => by positivity
    positivity
  -- the bound at a point of the open upper semicircle
  have hmain : ∀ x : ℝ, ‖angleDeriv j h (boostToAngle x)‖ ≤ Ktot * M := by
    intro x
    have hW : ContDiff ℝ ∞ (errorAngle f hf n) := contDiff_errorAngle f hf n
    have hv : ContDiff ℝ ∞ v := by
      rw [hvdef]
      have h1 : ContDiff ℝ ∞
          (fun y : ℝ => gaussConv (1 / ((n : ℝ) + 1)) (boostPicture f) (y : ℂ)) := by
        have hC : ContDiff ℂ ∞ (gaussConv (1 / ((n : ℝ) + 1)) (boostPicture f)) :=
          (differentiable_gaussConv (by positivity)
            (isRapidlyDecaying_boostPicture hf)).contDiff
        exact (hC.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
      exact h1.sub (isRapidlyDecaying_boostPicture hf).contDiff
    -- Leibniz for the phase times the boost-side error
    have hphase : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) := by
      have h1 : (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) =
          fun t : ℝ => ((Circle.exp (-t) : Circle) : ℂ) := by
        funext t
        rw [Circle.coe_exp]
        push_cast
        ring_nf
      rw [h1]
      have h2 : ContDiff ℝ ∞
          ((fun θ : ℝ => ((Circle.exp θ : Circle) : ℂ)) ∘ fun t : ℝ => -t) :=
        contDiff_circle_map.comp contDiff_neg
      exact h2
    have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
      (f := fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) (g := errorAngle f hf n)
      hphase hW (boostToAngle x) (n := j) (by exact_mod_cast le_top)
    have hterm : ∀ p ∈ Finset.range (j + 1),
        (j.choose p : ℝ) * ‖iteratedFDeriv ℝ p
            (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I)) (boostToAngle x)‖ *
          ‖iteratedFDeriv ℝ (j - p) (errorAngle f hf n) (boostToAngle x)‖ ≤
        (j.choose p : ℝ) * ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) := by
      intro p hp
      have hpj : p ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hq : j - p ≤ N := le_trans (Nat.sub_le j p) hj
      rw [norm_iteratedFDeriv_circle_map_neg_eq p (boostToAngle x), mul_one]
      have hchart := hK (j - p) (errorAngle f hf n) v hW hv
        (fun y => errorAngle_boostToAngle f hf n y) x
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hchart
      have hsum : ∑ i ∈ Finset.range (j - p + 1), ‖iteratedDeriv i v x‖ ≤
          ((N : ℝ) + 1) * (M * Real.exp (-(N : ℝ) * |x|)) := by
        have hle : ∀ i ∈ Finset.range (j - p + 1),
            ‖iteratedDeriv i v x‖ ≤ M * Real.exp (-(N : ℝ) * |x|) := by
          intro i hi
          exact hbound i (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hq) x
        calc
          ∑ i ∈ Finset.range (j - p + 1), ‖iteratedDeriv i v x‖ ≤
              ∑ _i ∈ Finset.range (j - p + 1), M * Real.exp (-(N : ℝ) * |x|) :=
            Finset.sum_le_sum hle
          _ = ((j - p : ℕ) + 1 : ℝ) * (M * Real.exp (-(N : ℝ) * |x|)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
          _ ≤ ((N : ℝ) + 1) * (M * Real.exp (-(N : ℝ) * |x|)) := by
            have hcast : ((j - p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq
            have hMe : 0 ≤ M * Real.exp (-(N : ℝ) * |x|) :=
              mul_nonneg hM (Real.exp_nonneg _)
            nlinarith [hMe, hcast]
      have hexp : Real.exp (((j - p : ℕ) : ℝ) * |x|) * Real.exp (-(N : ℝ) * |x|) ≤ 1 := by
        rw [← Real.exp_add]
        apply Real.exp_le_one_iff.mpr
        have hcast : ((j - p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq
        nlinarith [abs_nonneg x, hcast]
      have hKq : K (j - p) ≤ ∑ q ∈ Finset.range (N + 1), K q :=
        Finset.single_le_sum (f := K) (fun q _ => hK0 q)
          (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hq))
      have hstep : ‖iteratedFDeriv ℝ (j - p) (errorAngle f hf n) (boostToAngle x)‖ ≤
          (∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M) := by
        calc
          ‖iteratedFDeriv ℝ (j - p) (errorAngle f hf n) (boostToAngle x)‖ ≤
              K (j - p) * Real.exp (((j - p : ℕ) : ℝ) * |x|) *
                ∑ i ∈ Finset.range (j - p + 1), ‖iteratedDeriv i v x‖ := hchart
          _ ≤ K (j - p) * Real.exp (((j - p : ℕ) : ℝ) * |x|) *
                (((N : ℝ) + 1) * (M * Real.exp (-(N : ℝ) * |x|))) := by
              apply mul_le_mul_of_nonneg_left hsum
              exact mul_nonneg (hK0 _) (Real.exp_nonneg _)
          _ = K (j - p) * ((N : ℝ) + 1) * M *
                (Real.exp (((j - p : ℕ) : ℝ) * |x|) * Real.exp (-(N : ℝ) * |x|)) := by ring
          _ ≤ K (j - p) * ((N : ℝ) + 1) * M * 1 := by
              apply mul_le_mul_of_nonneg_left hexp
              have : 0 ≤ K (j - p) * ((N : ℝ) + 1) := by
                have := hK0 (j - p)
                positivity
              positivity
          _ = K (j - p) * (((N : ℝ) + 1) * M) := by ring
          _ ≤ (∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M) := by
              apply mul_le_mul_of_nonneg_right hKq
              have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
              positivity
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    have hchain : ‖iteratedFDeriv ℝ j (toAngle h) (boostToAngle x)‖ ≤
        (∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ)) *
          ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) := by
      have hfun : toAngle h = fun θ : ℝ =>
          Complex.exp (-(θ : ℂ) * Complex.I) * errorAngle f hf n θ := by
        rw [hhdef]
        exact toAngle_error_eq f hf n
      rw [hfun]
      calc
        ‖iteratedFDeriv ℝ j (fun θ : ℝ =>
            Complex.exp (-(θ : ℂ) * Complex.I) * errorAngle f hf n θ) (boostToAngle x)‖ ≤
            ∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ) *
              ‖iteratedFDeriv ℝ p (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I))
                (boostToAngle x)‖ *
              ‖iteratedFDeriv ℝ (j - p) (errorAngle f hf n) (boostToAngle x)‖ := hleib
        _ ≤ ∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ) *
              ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) :=
            Finset.sum_le_sum hterm
        _ = (∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ)) *
              ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) := by
            rw [← Finset.sum_mul]
    rw [angleDeriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    refine hchain.trans ?_
    rw [hKtot]
    have hMK : (0 : ℝ) ≤ (∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M) := by
      have : (0 : ℝ) ≤ ((N : ℝ) + 1) * M := by positivity
      positivity
    calc
      (∑ p ∈ Finset.range (j + 1), (j.choose p : ℝ)) *
          ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) ≤
          (∑ j' ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j' + 1), (j'.choose p : ℝ)) *
            ((∑ q ∈ Finset.range (N + 1), K q) * (((N : ℝ) + 1) * M)) :=
        mul_le_mul_of_nonneg_right hbinsum hMK
      _ = ((N : ℝ) + 1) *
            (∑ j' ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (j' + 1), (j'.choose p : ℝ)) *
            (∑ q ∈ Finset.range (N + 1), K q) * M := by ring
  -- transport the bound to an arbitrary angle
  have hper : Function.Periodic (angleDeriv j h) (2 * Real.pi) := periodic_angleDeriv j h
  obtain ⟨θ', hθ', hval⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos θ
  rw [hval]
  rcases lt_or_ge θ' Real.pi with hlt | hge
  · rcases eq_or_lt_of_le hθ'.1 with h0 | h0
    · rw [← h0, angleDeriv]
      rw [(iteratedDeriv_toAngle_eq_zero_of_suppUpper hsupp j).1, norm_zero]
      positivity
    · have hmem : θ' ∈ Set.Ioo 0 Real.pi := ⟨h0, hlt⟩
      have hx := boostToAngle_angleToBoost hmem
      have := hmain (angleToBoost θ')
      rwa [hx] at this
  · have hzero := angleDeriv_eq_zero_of_suppUpper hsupp j ⟨hge, hθ'.2.le⟩
    rw [hzero, norm_zero]
    positivity

/-! ### The Gaussian side -/

/-- The Gaussian convolution of a rapidly decaying function is smooth on the line. -/
theorem contDiff_gaussConvReal {s : ℝ} (hs : 0 < s) {a : ℝ → ℂ} (ha : IsRapidlyDecaying a) :
    ContDiff ℝ ∞ (gaussConvReal s a) := by
  have hC : ContDiff ℂ ∞ (gaussConv s a) := (differentiable_gaussConv hs ha).contDiff
  have hcomp : ContDiff ℝ ∞ fun y : ℝ => gaussConv s a (y : ℂ) :=
    (hC.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hfun : gaussConvReal s a = fun y : ℝ => gaussConv s a (y : ℂ) := by
    funext y
    rw [gaussConv_ofReal hs ha]
  rw [hfun]
  exact hcomp

/-- [T26], proof of Lemma 3.4; in the boost coordinate the smoothing error is eventually below
any prescribed weighted bound. -/
theorem eventually_boost_error_le {f : TestFn} (hf : SuppUpper f) (N : ℕ) {M : ℝ} (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i ≤ N → ∀ x : ℝ,
      ‖iteratedDeriv i (fun y : ℝ =>
          gaussConv (1 / ((n : ℝ) + 1)) (boostPicture f) (y : ℂ) - boostPicture f y) x‖ ≤
        M * Real.exp (-(N : ℝ) * |x|) := by
  have ha : IsRapidlyDecaying (boostPicture f) := isRapidlyDecaying_boostPicture hf
  have hstep : ∀ i ∈ Finset.range (N + 1), ∀ᶠ n : ℕ in atTop, ∀ x : ℝ,
      ‖iteratedDeriv i (fun y : ℝ =>
          gaussConv (1 / ((n : ℝ) + 1)) (boostPicture f) (y : ℂ) - boostPicture f y) x‖ ≤
        M * Real.exp (-(N : ℝ) * |x|) := by
    intro i _
    obtain ⟨δ, hδ, hbound⟩ := exists_norm_gaussConvReal_sub_le (ha.iteratedDeriv i) N hM
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ := by
      have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact hlim.eventually (eventually_lt_nhds hδ)
    filter_upwards [hev] with n hn x
    have hs : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hfun : (fun y : ℝ =>
        gaussConv (1 / ((n : ℝ) + 1)) (boostPicture f) (y : ℂ) - boostPicture f y) =
        gaussConvReal (1 / ((n : ℝ) + 1)) (boostPicture f) - boostPicture f := by
      funext y
      rw [gaussConv_ofReal hs ha]
      rfl
    rw [hfun]
    have hcd1 : ContDiff ℝ ∞ (gaussConvReal (1 / ((n : ℝ) + 1)) (boostPicture f)) :=
      contDiff_gaussConvReal hs ha
    have hsplit : iteratedDeriv i
        (gaussConvReal (1 / ((n : ℝ) + 1)) (boostPicture f) - boostPicture f) x =
        iteratedDeriv i (gaussConvReal (1 / ((n : ℝ) + 1)) (boostPicture f)) x -
          iteratedDeriv i (boostPicture f) x :=
      iteratedDeriv_sub (hcd1.contDiffAt.of_le (by exact_mod_cast le_top))
        (ha.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [hsplit, iteratedDeriv_gaussConvReal hs ha i]
    exact hbound (1 / ((n : ℝ) + 1)) hs hn x
  rw [← Filter.eventually_all_finset] at hstep
  filter_upwards [hstep] with n hn i hi x
  exact hn i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi)) x

/-! ### Lemma 3.4 -/

/-- [T26], proof of Lemma 3.4; the approximants converge to `f` in `C^∞(S¹)`. -/
theorem tendsto_xRestrictUpper_approx {f : TestFn} (hf : SuppUpper f) :
    Tendsto (fun n : ℕ => xRestrictUpper (approx f hf n)) atTop (nhds f) := by
  rw [tendsto_iff_cnorm]
  intro N
  obtain ⟨K, hK0, hKb⟩ := exists_norm_angleDeriv_le hf N
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  set M : ℝ := ε / (2 * ((N : ℝ) + 1) * (K + 1)) with hMdef
  have hM : 0 < M := by
    rw [hMdef]
    positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (eventually_boost_error_le hf N hM)
  refine ⟨n₀, fun n hn => ?_⟩
  have hbound := hn₀ n hn
  have hcn : (cnorm N (xRestrictUpper (approx f hf n) - f) : ℝ) ≤ ((N : ℝ) + 1) * (K * M) := by
    refine cnorm_le_of_forall (by positivity) ?_
    intro j hj θ
    exact hKb n M hM.le hbound j hj θ
  have hlt : ((N : ℝ) + 1) * (K * M) < ε := by
    have hfac : ((N : ℝ) + 1) * K < 2 * ((N : ℝ) + 1) * (K + 1) := by nlinarith [hK0]
    calc
      ((N : ℝ) + 1) * (K * M) = (((N : ℝ) + 1) * K) * M := by ring
      _ < (2 * ((N : ℝ) + 1) * (K + 1)) * M := mul_lt_mul_of_pos_right hfac hM
      _ = ε := by
        rw [hMdef]
        field_simp
  have hnonneg : (0 : ℝ) ≤ (cnorm N (xRestrictUpper (approx f hf n) - f) : ℝ) :=
    (cnorm N _).coe_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hcn hlt

/-- [T26], Lemma 3.4; every upper-supported test function lies in the closure of the
restrictions to `I₊` of the analytic class `𝓧`. -/
theorem lemma_3_4_density_upper :
    { f : TestFn | SuppUpper f } ⊆
      closure { g : TestFn | ∃ F : AnalyticTestFn, xRestrictUpper F = g } := by
  intro f hf
  refine mem_closure_of_tendsto (tendsto_xRestrictUpper_approx hf) ?_
  filter_upwards with n
  exact ⟨approx f hf n, rfl⟩

end

end MobiusCPT
