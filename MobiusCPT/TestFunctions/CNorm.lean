import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Field.Periodic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Finset.Sigma
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import MobiusCPT.TestFunctions.Basic

/-!
# MobiusCPT.TestFunctions.CNorm

The angle-derivative seminorms and the induced Fréchet topology on the smooth test-function
space.
-/

namespace MobiusCPT

open scoped ContDiff Topology

noncomputable section

/-! ### Periodic smooth functions -/

/-- A continuous periodic function on the real line is bounded. -/
theorem exists_norm_le_of_periodic {g : ℝ → ℂ} (hg : Continuous g) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic g T) : ∃ C : ℝ, ∀ x : ℝ, ‖g x‖ ≤ C := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hxy]
  exact hC y ⟨hy.1, hy.2.le⟩

/-! ### Angle derivatives -/

/-- [T26], §3; the `j`-th angle derivative `d^j f/dθ^j` of a test function. -/
noncomputable def angleDeriv (j : ℕ) (f : TestFn) : ℝ → ℂ :=
  iteratedDeriv j (toAngle f)

/-- [T26], §3; every angle derivative of a test function is smooth. -/
theorem contDiff_angleDeriv (j : ℕ) (f : TestFn) : ContDiff ℝ ∞ (angleDeriv j f) := by
  rw [angleDeriv, iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j (contDiff_toAngle f)

/-- [T26], §3; every angle derivative has the period of the original angle function. -/
theorem periodic_angleDeriv (j : ℕ) (f : TestFn) :
    Function.Periodic (angleDeriv j f) (2 * Real.pi) := by
  intro θ
  change iteratedDeriv j (toAngle f) (θ + 2 * Real.pi) =
    iteratedDeriv j (toAngle f) θ
  have hperiod : (fun z : ℝ => toAngle f (z + 2 * Real.pi)) = toAngle f := by
    funext z
    exact periodic_toAngle f z
  calc
    iteratedDeriv j (toAngle f) (θ + 2 * Real.pi) =
        iteratedDeriv j (fun z : ℝ => toAngle f (z + 2 * Real.pi)) θ := by
          exact congrFun (iteratedDeriv_comp_add_const j (toAngle f) (2 * Real.pi)).symm θ
    _ = iteratedDeriv j (toAngle f) θ := by rw [hperiod]

/-- [T26], §3; an angle derivative bundled as a bounded continuous function. -/
noncomputable def angleDerivB (j : ℕ) (f : TestFn) : BoundedContinuousFunction ℝ ℂ := by
  let hbound : ∃ C : ℝ, ∀ x : ℝ, ‖angleDeriv j f x‖ ≤ C :=
    exists_norm_le_of_periodic (T := 2 * Real.pi) (contDiff_angleDeriv j f).continuous
      (by positivity)
      (periodic_angleDeriv j f)
  exact BoundedContinuousFunction.ofNormedAddCommGroup (angleDeriv j f)
    (contDiff_angleDeriv j f).continuous (Classical.choose hbound)
      (Classical.choose_spec hbound)

/-- Evaluation of the bundled angle derivative agrees with its unbundled function. -/
theorem angleDerivB_apply (j : ℕ) (f : TestFn) (θ : ℝ) :
    angleDerivB j f θ = angleDeriv j f θ := by
  simp [angleDerivB]

/-- The pointwise norm of an angle derivative is bounded by its sup norm. -/
theorem norm_angleDeriv_le (j : ℕ) (f : TestFn) (θ : ℝ) :
    ‖angleDeriv j f θ‖ ≤ ‖angleDerivB j f‖ := by
  rw [← angleDerivB_apply]
  exact BoundedContinuousFunction.norm_coe_le_norm _ _

/-- [T26], §3; angle derivatives are additive. -/
theorem angleDeriv_add (j : ℕ) (f g : TestFn) :
    angleDeriv j (f + g) = angleDeriv j f + angleDeriv j g := by
  funext θ
  change iteratedDeriv j (toAngle (f + g)) θ =
    iteratedDeriv j (toAngle f) θ + iteratedDeriv j (toAngle g) θ
  rw [toAngle_add]
  exact iteratedDeriv_add
    ((contDiff_toAngle f).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_toAngle g).contDiffAt.of_le (by exact_mod_cast le_top))

/-- [T26], §3; angle derivatives are homogeneous for complex scalars. -/
theorem angleDeriv_smul (j : ℕ) (c : ℂ) (f : TestFn) :
    angleDeriv j (c • f) = c • angleDeriv j f := by
  funext θ
  change iteratedDeriv j (toAngle (c • f)) θ = c • iteratedDeriv j (toAngle f) θ
  rw [toAngle_smul, iteratedDeriv_const_smul_field]

/-- [T26], §3; every angle derivative of the zero test function is zero. -/
theorem angleDeriv_zero (j : ℕ) : angleDeriv j (0 : TestFn) = 0 := by
  funext θ
  change iteratedDeriv j (toAngle (0 : TestFn)) θ = 0
  rw [toAngle_zero]
  exact iteratedDeriv_const_zero

/-- The bundled `j`-th angle derivative as a complex-linear map. -/
noncomputable def angleDerivBₗ (j : ℕ) :
    TestFn →ₗ[ℂ] BoundedContinuousFunction ℝ ℂ where
  toFun f := angleDerivB j f
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro θ
    simpa only [BoundedContinuousFunction.coe_add, Pi.add_apply, angleDerivB_apply] using
      congrFun (angleDeriv_add j f g) θ
  map_smul' c f := by
    apply BoundedContinuousFunction.ext
    intro θ
    simpa only [BoundedContinuousFunction.coe_smul, Pi.smul_apply, angleDerivB_apply,
      RingHom.id_apply] using
      congrFun (angleDeriv_smul j c f) θ

/-! ### The induced topology -/

/-- [T26], §2.2; the bundled family of all angle derivatives. -/
noncomputable def angleDerivsₗ :
    TestFn →ₗ[ℂ] (ℕ → BoundedContinuousFunction ℝ ℂ) where
  toFun f := fun j => angleDerivB j f
  map_add' f g := by
    funext j
    exact (angleDerivBₗ j).map_add f g
  map_smul' c f := by
    funext j
    exact (angleDerivBₗ j).map_smul c f

/-- [T26], §2.2; the `C^∞` topology of uniform convergence of every angle derivative. -/
instance testFnTopologicalSpace : TopologicalSpace TestFn :=
  TopologicalSpace.induced angleDerivsₗ inferInstance

/-- The real module structure on `TestFn`, by restriction of the complex scalars. -/
instance instRealModule : Module ℝ TestFn :=
  Module.compHom TestFn (algebraMap ℝ ℂ)

/-- The restricted real and complex scalar actions form a scalar tower. -/
instance instRealComplexScalarTower : IsScalarTower ℝ ℂ TestFn :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The seminorm family obtained from the sup norms of all bundled angle derivatives. -/
noncomputable def angleDerivSupFamily :
    SeminormFamily ℂ TestFn (Σ _j : ℕ, Fin 1) :=
  SeminormFamily.comp
    (SeminormFamily.sigma
      (fun j : ℕ =>
        SeminormFamily.comp
          (fun _ : Fin 1 => normSeminorm ℂ (BoundedContinuousFunction ℝ ℂ))
          (LinearMap.proj (R := ℂ)
            (φ := fun _ : ℕ => BoundedContinuousFunction ℝ ℂ) j)))
    angleDerivsₗ

/-- The sup-family seminorm at an index is the sup norm of the corresponding derivative. -/
theorem angleDerivSupFamily_apply (i : Σ _j : ℕ, Fin 1) (f : TestFn) :
    angleDerivSupFamily i f = ‖angleDerivB i.1 f‖ := by
  rcases i with ⟨j, k⟩
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  simp [angleDerivSupFamily, angleDerivsₗ, SeminormFamily.sigma, SeminormFamily.comp_apply,
    LinearMap.proj_apply, coe_normSeminorm]

/-- [T26], §2.2; the sup-family has the induced topology. -/
theorem withSeminorms_angleDerivs : WithSeminorms angleDerivSupFamily := by
  unfold angleDerivSupFamily
  exact LinearMap.withSeminorms_induced
    (withSeminorms_pi
      (p := fun _ : ℕ => fun _ : Fin 1 =>
        normSeminorm ℂ (BoundedContinuousFunction ℝ ℂ))
      (fun _ => norm_withSeminorms ℂ (BoundedContinuousFunction ℝ ℂ)))
    (angleDerivsₗ : TestFn →ₛₗ[RingHom.id ℂ] (ℕ → BoundedContinuousFunction ℝ ℂ))

/-! ### The literal `C^N` seminorm family -/

/-- [T26], §3 and Lemma 3.9; the `C^N` seminorm, with the sum starting at `j = 0`. -/
noncomputable def cnormSeminorm (N : ℕ) : Seminorm ℂ TestFn :=
  ∑ j ∈ Finset.range (N + 1), (normSeminorm ℂ (BoundedContinuousFunction ℝ ℂ)).comp
    (angleDerivBₗ j)

/-- [T26], §3; the literal `C^N` seminorm evaluates as the sum of the bundled sup norms. -/
theorem cnormSeminorm_apply (N : ℕ) (f : TestFn) :
    cnormSeminorm N f = ∑ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ := by
  simp [cnormSeminorm, angleDerivBₗ]

/-- [T26] §2.2; the `C^N` family generates the `C^∞` topology. -/
theorem withSeminorms_cnorm : WithSeminorms cnormSeminorm := by
  apply withSeminorms_angleDerivs.congr
  · apply Seminorm.IsBounded.of_real
    intro N
    let s : Finset (Σ j : ℕ, Fin 1) :=
      (Finset.range (N + 1)).sigma (fun _ => ({0} : Finset (Fin 1)))
    refine ⟨s, (N + 1 : ℝ), ?_⟩
    intro f
    simp only [LinearMap.id_apply]
    rw [cnormSeminorm_apply]
    have hterm : ∀ j ∈ Finset.range (N + 1),
        ‖angleDerivB j f‖ ≤ (s.sup angleDerivSupFamily) f := by
      intro j hj
      apply le_trans ?_ (Seminorm.le_finset_sup_apply (p := angleDerivSupFamily)
        (s := s) (x := f) (i := (⟨j, 0⟩ : Σ j : ℕ, Fin 1)) ?_)
      · rw [angleDerivSupFamily_apply]
      · simp [s, hj]
    have hsum := Finset.sum_le_card_nsmul (Finset.range (N + 1))
      (fun j => ‖angleDerivB j f‖) ((s.sup angleDerivSupFamily) f) hterm
    simpa [Finset.card_range, nsmul_eq_mul] using hsum
  · apply Seminorm.IsBounded.of_real
    intro i
    refine ⟨{i.1}, 1, ?_⟩
    intro f
    simp only [LinearMap.id_apply, Finset.sup_singleton, one_mul]
    rcases i with ⟨j, k⟩
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    rw [angleDerivSupFamily_apply, cnormSeminorm_apply]
    have hsub : ({j} : Finset ℕ) ⊆ Finset.range (j + 1) := by
      intro i hi
      have : i = j := Finset.mem_singleton.mp hi
      subst i
      simp
    have hsum :
        (∑ i ∈ ({j} : Finset ℕ), ‖angleDerivB i f‖) ≤
          ∑ i ∈ Finset.range (j + 1), ‖angleDerivB i f‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
    simpa using hsum

/-! ### The nonnegative Contract-facing version -/

/-- [T26], §3 and Lemma 3.9; the angle-derivative `C^N` norm as a nonnegative real. -/
noncomputable def cnorm (N : ℕ) (f : TestFn) : NNReal :=
  ⟨cnormSeminorm N f, by
    rw [cnormSeminorm_apply]
    exact Finset.sum_nonneg fun j _ => norm_nonneg (angleDerivB j f)⟩

/-- The real coercion of `cnorm` is the corresponding `C^N` seminorm. -/
theorem cnorm_coe (N : ℕ) (f : TestFn) : (cnorm N f : ℝ) = cnormSeminorm N f :=
  rfl

/-- The `C^N` norm is the sum of the bundled angle-derivative sup norms. -/
theorem cnorm_eq (N : ℕ) (f : TestFn) :
    (cnorm N f : ℝ) = ∑ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ := by
  rw [cnorm_coe, cnormSeminorm_apply]

/-- [T26], §3 and Lemma 3.9; the `C^N` norm is subadditive. -/
theorem cnorm_add_le (N : ℕ) (f g : TestFn) : cnorm N (f + g) ≤ cnorm N f + cnorm N g := by
  apply NNReal.coe_le_coe.mp
  simpa only [cnorm_coe, NNReal.coe_add] using map_add_le_add (cnormSeminorm N) f g

/-- [T26], §3 and Lemma 3.9; the `C^N` norm is homogeneous for complex scalars. -/
theorem cnorm_smul (N : ℕ) (c : ℂ) (f : TestFn) :
    cnorm N (c • f) = ‖c‖₊ * cnorm N f := by
  apply NNReal.eq
  simpa only [cnorm_coe, NNReal.coe_mul, coe_nnnorm] using
    map_smul_eq_mul (cnormSeminorm N) c f

/-- [T26], §3 and Lemma 3.9; the zero test function has zero `C^N` norm. -/
theorem cnorm_zero (N : ℕ) : cnorm N (0 : TestFn) = 0 := by
  apply NNReal.eq
  simpa only [cnorm_coe, NNReal.coe_zero] using map_zero (cnormSeminorm N)

/-- [T26], §3 and Lemma 3.9; the `C^N` norms are monotone in `N`. -/
theorem cnorm_mono {M N : ℕ} (h : M ≤ N) (f : TestFn) : cnorm M f ≤ cnorm N f := by
  apply NNReal.coe_le_coe.mp
  rw [cnorm_coe, cnorm_coe, cnormSeminorm_apply, cnormSeminorm_apply]
  have hMN : M + 1 ≤ N + 1 := Nat.add_le_add_right h 1
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hMN)
    (fun j _ _ => norm_nonneg _)

/-- [T26], §3; because the sum starts at `j = 0`, `cnorm` is a genuine norm. -/
theorem cnorm_eq_zero (N : ℕ) (f : TestFn) : cnorm N f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hf' : (cnorm N f : ℝ) = 0 := by rw [hf, NNReal.coe_zero]
    rw [cnorm_eq] at hf'
    have hterms : ∀ j ∈ Finset.range (N + 1), ‖angleDerivB j f‖ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg (angleDerivB j f))).mp hf'
    have hzero : ‖angleDerivB 0 f‖ = 0 := hterms 0 (by simp)
    have hB : angleDerivB 0 f = 0 := norm_eq_zero.mp hzero
    apply toAngle_injective
    rw [toAngle_zero]
    funext θ
    calc
      toAngle f θ = angleDeriv 0 f θ := by simp [angleDeriv]
      _ = angleDerivB 0 f θ := (angleDerivB_apply 0 f θ).symm
      _ = (0 : BoundedContinuousFunction ℝ ℂ) θ := congrArg (fun q => q θ) hB
      _ = 0 := rfl
  · intro hf
    subst f
    exact cnorm_zero N

/-- [T26] §2.2; convergence in `C^∞(S¹)` is convergence in every `C^N` norm. -/
theorem tendsto_iff_cnorm (u : ℕ → TestFn) (f : TestFn) :
    Filter.Tendsto u Filter.atTop (nhds f) ↔
      ∀ N : ℕ, Filter.Tendsto (fun n => ((cnorm N (u n - f) : NNReal) : ℝ))
        Filter.atTop (nhds 0) := by
  rw [WithSeminorms.tendsto_nhds_atTop withSeminorms_cnorm u f]
  have hN (N : ℕ) :
      Filter.Tendsto (fun n => ((cnorm N (u n - f) : NNReal) : ℝ))
          Filter.atTop (nhds 0) ↔
        ∀ ε, 0 < ε → ∃ n₀, ∀ n, n₀ ≤ n → cnormSeminorm N (u n - f) < ε := by
    rw [Metric.tendsto_atTop]
    simp only [Real.dist_eq, sub_zero, cnorm_coe,
      abs_of_nonneg (apply_nonneg (cnormSeminorm N) _)]
  constructor
  · intro h N
    exact (hN N).2 (h N)
  · intro h N ε hε
    exact (hN N).1 (h N) ε hε

/-! ### Structural topological instances -/

/-- [T26], §2.2; the induced `C^∞` topology makes `TestFn` a topological additive group. -/
instance : IsTopologicalAddGroup TestFn :=
  WithSeminorms.topologicalAddGroup withSeminorms_cnorm

/-- [T26], §2.2; scalar multiplication on `TestFn` is continuous in the induced topology. -/
instance : ContinuousSMul ℂ TestFn :=
  WithSeminorms.continuousSMul withSeminorms_cnorm

/-- [T26], §2.2; the induced `C^∞` topology on `TestFn` is locally convex over `ℝ`. -/
instance : LocallyConvexSpace ℝ TestFn :=
  WithSeminorms.toLocallyConvexSpace withSeminorms_cnorm

/-- [T26], §2.2; the `C^N` family separates points of `TestFn`, so the topology is `T₁`. -/
instance : T1Space TestFn := by
  apply WithSeminorms.T1_of_separating withSeminorms_cnorm
  intro f hf
  refine ⟨0, ?_⟩
  intro hzero
  have hc : cnorm 0 f = 0 := by
    apply NNReal.eq
    simpa only [cnorm_coe, NNReal.coe_zero] using hzero
  exact hf ((cnorm_eq_zero 0 f).mp hc)

/-- [T26], §2.2; the induced `C^∞` topology on `TestFn` is first countable. -/
instance : FirstCountableTopology TestFn :=
  WithSeminorms.firstCountableTopology withSeminorms_cnorm

end

end MobiusCPT
