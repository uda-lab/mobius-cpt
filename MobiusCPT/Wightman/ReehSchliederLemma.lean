import MobiusCPT.Wightman.RotationCurve
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Geometric prerequisites for the Reeh--Schlieder lemma

Block R3, Part A, of Issue #13.  Following [CRTT25], Appendix A, Lemma A.2, this file supplies
the geometric support lemmas and smooth finite decomposition used by the rotation-curve
argument.
-/

namespace MobiusCPT

open Set Filter
open scoped BigOperators ContDiff Manifold Pointwise Topology

noncomputable section

/-- Rotation of the circle as a homeomorphism. -/
private def rotationHomeomorph (θ : ℝ) : Circle ≃ₜ Circle where
  toEquiv :=
    { toFun := fun z => Mob.rot θ • z
      invFun := fun z => Mob.rot (-θ) • z
      left_inv := by
        intro z
        show Mob.rot (-θ) • (Mob.rot θ • z) = z
        rw [← mul_smul, ← Mob.rot_add, neg_add_cancel, Mob.rot_zero, one_smul]
      right_inv := by
        intro z
        show Mob.rot θ • (Mob.rot (-θ) • z) = z
        rw [← mul_smul, ← Mob.rot_add, add_neg_cancel, Mob.rot_zero, one_smul] }
  continuous_toFun := by
    simpa only [Mob.rot, Mob.mk_smul] using
      (contMDiff_smul (rotMat θ)).continuous
  continuous_invFun := by
    simpa only [Mob.rot, Mob.mk_smul] using
      (contMDiff_smul (rotMat (-θ))).continuous

private theorem rot_inv (θ : ℝ) :
    (Mob.rot θ)⁻¹ = Mob.rot (-θ) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← Mob.rot_add, add_neg_cancel, Mob.rot_zero]

/-- [CRTT25], Appendix A, Lemma A.2: pullback by a rotation rotates topological support. -/
theorem tsupport_rotPullback (θ : ℝ) (f : TestFn) :
    tsupport (rotPullback θ f : Circle → ℂ) =
      (Mob.rot θ) • tsupport (f : Circle → ℂ) := by
  change tsupport ((f : Circle → ℂ) ∘ rotationHomeomorph (-θ)) = _
  rw [tsupport_comp_eq_preimage]
  change (fun z : Circle => Mob.rot (-θ) • z) ⁻¹'
      tsupport (f : Circle → ℂ) = _
  rw [← rot_inv θ, Set.preimage_smul_inv]

/-- The rotation action, jointly in the angle and the point, is continuous. -/
private theorem continuous_rot_smul :
    Continuous (fun p : ℝ × Circle => Mob.rot p.1 • p.2) := by
  have hfun : (fun p : ℝ × Circle => Mob.rot p.1 • p.2) =
      fun p => Circle.exp p.1 * p.2 := by
    funext p
    exact Mob.rot_smul p.1 p.2
  rw [hfun]
  exact (Circle.exp.continuous.comp continuous_fst).mul continuous_snd

/-- [CRTT25], Appendix A, Lemma A.2: a compactly supported test function whose support lies in
an open set remains supported there under all sufficiently small rotations. -/
theorem exists_rotStable (d : ℕ) {A : Set Circle} (hAopen : IsOpen A) {h : TestFn}
    (hh : tsupport (h : Circle → ℂ) ⊆ A) :
    ∃ ε > 0, ∀ θ : ℝ, |θ| < ε →
      tsupport (Mob.beta d (Mob.rot θ) h : Circle → ℂ) ⊆ A := by
  let K : Set Circle := tsupport (h : Circle → ℂ)
  have hKcompact : IsCompact K := (isClosed_tsupport (h : Circle → ℂ)).isCompact
  have hlocal : ∀ z ∈ K,
      ∀ᶠ p : ℝ × Circle in 𝓝 ((0 : ℝ), z), Mob.rot p.1 • p.2 ∈ A := by
    intro z hz
    apply continuous_rot_smul.continuousAt.eventually_mem
    apply hAopen.mem_nhds
    simpa [K] using hh hz
  have huniform :
      ∀ᶠ θ : ℝ in 𝓝 0, ∀ z ∈ K, Mob.rot θ • z ∈ A :=
    hKcompact.eventually_forall_of_forall_eventually hlocal
  obtain ⟨ε, hε, hstable⟩ := Metric.eventually_nhds_iff.mp huniform
  refine ⟨ε, hε, fun θ hθ => ?_⟩
  have hθstable : ∀ z ∈ K, Mob.rot θ • z ∈ A :=
    hstable (by simpa only [Real.dist_eq, sub_zero] using hθ)
  rw [beta_rot_eq_rotPullback, tsupport_rotPullback]
  rintro _ ⟨z, hz, rfl⟩
  exact hθstable z hz

/-- Multiply a complex test function by a smooth real-valued bump function. -/
def bumpMul (χ : C^∞⟮𝓡 1, Circle; 𝓘(ℝ), ℝ⟯) (f : TestFn) : TestFn :=
  ⟨fun z => (χ z : ℂ) * f z, by
    have hχ : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
        (fun z : Circle => (χ z : ℂ)) := by
      change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
        (Complex.ofRealCLM ∘ (χ : Circle → ℝ))
      exact Complex.ofRealCLM.contDiff.comp_contMDiff
        (ContMDiffMap.contMDiff χ)
    intro z
    have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ => p.1 * p.2) :=
      contDiff_fst.mul contDiff_snd
    exact hmul.contDiffAt.comp_contMDiffAt
      (hχ.contMDiffAt.prodMk_space (ContMDiffMap.contMDiff f).contMDiffAt)⟩

@[simp]
theorem bumpMul_apply (χ : C^∞⟮𝓡 1, Circle; 𝓘(ℝ), ℝ⟯)
    (f : TestFn) (z : Circle) :
    bumpMul χ f z = (χ z : ℂ) * f z :=
  rfl

/-- [CRTT25], Appendix A, Lemma A.2: multiplying by a bump cannot enlarge the bump's
topological support.  The target is exactly the support bound supplied by
`SmoothPartitionOfUnity.IsSubordinate`. -/
theorem tsupport_bumpMul_subset
    (χ : C^∞⟮𝓡 1, Circle; 𝓘(ℝ), ℝ⟯) (f : TestFn) :
    tsupport (bumpMul χ f : Circle → ℂ) ⊆
      tsupport (χ : Circle → ℝ) := by
  have hχ : tsupport (fun z : Circle => (χ z : ℂ)) =
      tsupport (χ : Circle → ℝ) := by
    change tsupport (Complex.ofReal ∘ (χ : Circle → ℝ)) = _
    exact tsupport_comp_eq (by simp) (χ : Circle → ℝ)
  change tsupport (fun z : Circle => (χ z : ℂ) * f z) ⊆ _
  rw [← hχ]
  exact tsupport_mul_subset_left

/-- Evaluation commutes with finite sums of test functions. -/
private theorem sum_testFn_apply {ι : Type*} [Fintype ι]
    (g : ι → TestFn) (z : Circle) :
    (∑ i, g i) z = ∑ i, g i z := by
  let ev : TestFn →+ ℂ :=
    { toFun := fun q => q z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i, g i) = ∑ i, ev (g i)
  exact map_sum ev g Finset.univ

private theorem isOpen_rot_smul {A : Set Circle} (hAopen : IsOpen A) (θ : ℝ) :
    IsOpen (Mob.rot θ • A) := by
  change IsOpen ((rotationHomeomorph θ) '' A)
  exact (rotationHomeomorph θ).isOpenMap A hAopen

/-- [CRTT25], Appendix A, Lemma A.2: finitely many rotated copies of any nonempty open subset
cover the circle. -/
theorem exists_finite_rotate_cover {A : Set Circle} (hAopen : IsOpen A)
    (hAne : A.Nonempty) :
    ∃ (n : ℕ) (θs : Fin n → ℝ),
      (Set.univ : Set Circle) ⊆ ⋃ j, Mob.rot (θs j) • A := by
  classical
  obtain ⟨a, ha⟩ := hAne
  have hcover : (Set.univ : Set Circle) ⊆ ⋃ θ : ℝ, Mob.rot θ • A := by
    intro z _
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective (z * a⁻¹)
    have hza : Mob.rot θ • a = z := by
      rw [Mob.rot_smul, hθ]
      simp
    refine Set.mem_iUnion.2 ⟨θ, ?_⟩
    rw [← hza]
    exact Set.smul_mem_smul_set ha
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun θ : ℝ => Mob.rot θ • A) (fun θ => isOpen_rot_smul hAopen θ) hcover
  refine ⟨t.card, fun j => (t.equivFin.symm j).1, ?_⟩
  intro z hz
  obtain ⟨θ, hθt, hzθ⟩ := Set.mem_iUnion₂.1 (ht hz)
  let i : t := ⟨θ, hθt⟩
  refine Set.mem_iUnion.2 ⟨t.equivFin i, ?_⟩
  simpa [i] using hzθ

/-- [CRTT25], Appendix A, Lemma A.2: every test function is a finite sum of smooth pieces,
each supported in a rotated copy of an arbitrary nonempty open subset of the circle. -/
theorem exists_finite_bumpMul_decomposition {A : Set Circle} (hAopen : IsOpen A)
    (hAne : A.Nonempty) (f : TestFn) :
    ∃ (n : ℕ) (θs : Fin n → ℝ) (pieces : Fin n → TestFn),
      f = ∑ j, pieces j ∧
        ∀ j, tsupport (pieces j : Circle → ℂ) ⊆ Mob.rot (θs j) • A := by
  obtain ⟨n, θs, hcover⟩ := exists_finite_rotate_cover hAopen hAne
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓡 1) (s := (Set.univ : Set Circle)) isClosed_univ
    (fun j : Fin n => Mob.rot (θs j) • A)
    (fun j => isOpen_rot_smul hAopen (θs j)) hcover
  refine ⟨n, θs, fun j => bumpMul (ρ j) f, ?_, ?_⟩
  · apply TestFn.ext
    intro z
    have hsumReal : ∑ j, ρ j z = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using
        ρ.sum_eq_one (show z ∈ (Set.univ : Set Circle) by simp)
    have hsumComplex : ∑ j, (ρ j z : ℂ) = 1 := by
      rw [← Complex.ofReal_sum, hsumReal]
      simp
    rw [sum_testFn_apply]
    simp only [bumpMul_apply]
    rw [← Finset.sum_mul, hsumComplex, one_mul]
  · intro j
    exact (tsupport_bumpMul_subset (ρ j) f).trans (hρ j)

private noncomputable def smearedProductSlotLinear
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕)
    (lam : W.toWightmanStruct.Compat) (l₁ : List (𝓕 × TestFn))
    (φ : 𝓕) (tail : List (𝓕 × TestFn)) : TestFn →ₗ[ℂ] ℂ where
  toFun := fun f => W.toWightmanStruct.compatApply lam
    (W.smearedProduct (l₁ ++ ((φ, f) :: tail)))
  map_add' := by
    intro f g
    simp only [W.toWightmanStruct.smearedProduct_append,
      W.toWightmanStruct.smearedProduct_cons]
    rw [(W.toWightmanStruct.smear_addLinear φ f g
        (W.smearedProduct tail)).1,
      (W.toWightmanStruct.smearedProductOn_linear l₁ _ _).1,
      (W.toWightmanStruct.compatApply_linear lam _ _).1]
  map_smul' := by
    intro c f
    have heq : W.toWightmanStruct.compatApply lam
        (W.smearedProduct (l₁ ++ ((φ, c • f) :: tail))) =
      c • W.toWightmanStruct.compatApply lam
        (W.smearedProduct (l₁ ++ ((φ, f) :: tail))) := by
      simp only [W.toWightmanStruct.smearedProduct_append,
        W.toWightmanStruct.smearedProduct_cons]
      rw [(W.toWightmanStruct.smear_addLinear φ f f
          (W.smearedProduct tail)).2 c,
        (W.toWightmanStruct.smearedProductOn_linear l₁
          (W.smear φ f (W.smearedProduct tail))
          (W.smear φ f (W.smearedProduct tail))).2 c,
        (W.toWightmanStruct.compatApply_linear lam
          (W.toWightmanStruct.smearedProductOn l₁ (W.smear φ f (W.smearedProduct tail)))
          (W.toWightmanStruct.smearedProductOn l₁ (W.smear φ f (W.smearedProduct tail)))).2 c]
    exact heq

private theorem zip_fst_snd {α β : Type*} (l : List (α × β)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  simpa [List.unzip_eq_map] using List.zip_unzip l

private theorem map_fst_zip_of_length_eq {α β : Type*}
    (xs : List α) (ys : List β) (hlen : ys.length = xs.length) :
    (xs.zip ys).map Prod.fst = xs := by
  induction xs generalizing ys with
  | nil =>
      have hys : ys = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : ys.length = xs.length := Nat.succ.inj hlen
          simp only [List.zip_cons_cons, List.map_cons, Prod.fst]
          exact congrArg (List.cons x) (ih ys htail)

private theorem beta_rot_cancel (d : ℕ) (θ : ℝ) (f : TestFn) :
    Mob.beta d (Mob.rot θ) (Mob.beta d (Mob.rot (-θ)) f) = f := by
  have hmul :
      Mob.beta d (Mob.rot θ * Mob.rot (-θ)) =
        (Mob.beta d (Mob.rot θ)).comp (Mob.beta d (Mob.rot (-θ))) :=
    MobiusAction.beta_mul (G := Mob) (TF := TestFn) d (Mob.rot θ) (Mob.rot (-θ))
  have hstep : Mob.beta d (Mob.rot θ * Mob.rot (-θ)) f =
      Mob.beta d (Mob.rot θ) (Mob.beta d (Mob.rot (-θ)) f) :=
    congrFun (congrArg DFunLike.coe hmul) f
  rw [← hstep, ← Mob.rot_add, add_neg_cancel, Mob.rot_zero]
  have hone : Mob.beta d (1 : Mob) = LinearMap.id :=
    MobiusAction.beta_one (G := Mob) (TF := TestFn) d
  exact congrFun (congrArg DFunLike.coe hone) f

private theorem upperArc_nonempty : upperArc.Nonempty := by
  refine ⟨Circle.exp (Real.pi / 2), (mem_upperArc_circleExp).2 ⟨0, ?_⟩⟩
  simpa using (show Real.pi / 2 ∈ Set.Ioo 0 Real.pi by
    constructor <;> linarith [Real.pi_pos])

private theorem lowerArc_nonempty : lowerArc.Nonempty := by
  refine ⟨Circle.exp (3 * Real.pi / 2), (mem_lowerArc_circleExp).2 ⟨0, ?_⟩⟩
  simpa using (show 3 * Real.pi / 2 ∈ Set.Ioo Real.pi (2 * Real.pi) by
    constructor <;> linarith [Real.pi_pos])

/-- [CRTT25], Appendix A, Lemma A.2: vanishing on products whose test functions are
supported in any fixed nonempty open arc forces a compatible functional to vanish. -/
theorem eq_zero_of_forall_smearedProduct_supp_eq_zero
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (A : Set Circle) (hAopen : IsOpen A) (hAne : A.Nonempty)
    (Supp : TestFn → Prop)
    (hSuppOfTsupport : ∀ f : TestFn, tsupport (f : Circle → ℂ) ⊆ A → Supp f)
    (lam : W.toWightmanStruct.Compat)
    (hlam : ∀ l : List (𝓕 × TestFn), (∀ p ∈ l, Supp p.2) →
      W.toWightmanStruct.compatApply lam (W.smearedProduct l) = 0) :
    lam = 0 := by
  classical
  let Q : List (𝓕 × TestFn) → List 𝓕 → Prop := fun l₁ φRest =>
    (∀ p ∈ l₁, Supp p.2) → ∀ fRest : List TestFn,
      fRest.length = φRest.length →
        W.toWightmanStruct.compatApply lam
          (W.smearedProduct (l₁ ++ φRest.zip fRest)) = 0
  have hQ : ∀ φRest : List 𝓕, ∀ l₁ : List (𝓕 × TestFn), Q l₁ φRest := by
    intro φRest
    induction φRest with
    | nil =>
        intro l₁
        dsimp only [Q]
        intro hl₁ fRest hlen
        have hfRest : fRest = [] :=
          List.length_eq_zero_iff.mp (by simpa using hlen)
        subst fRest
        simpa using hlam l₁ hl₁
    | cons φ_p φRest' ih =>
        intro l₁
        dsimp only [Q]
        intro hl₁ fRest hlen
        cases fRest with
        | nil => simp at hlen
        | cons g fRest' =>
            have htail : fRest'.length = φRest'.length := Nat.succ.inj hlen
            have hgoal : ∀ g' : TestFn,
                W.toWightmanStruct.compatApply lam
                  (W.smearedProduct
                    (l₁ ++ (φ_p, g') :: φRest'.zip fRest')) = 0 := by
              intro g'
              obtain ⟨n, θs, pieces, hsum, hsupp⟩ :=
                exists_finite_bumpMul_decomposition hAopen hAne g'
              have hpieceZero : ∀ j : Fin n,
                  W.toWightmanStruct.compatApply lam
                    (W.smearedProduct
                      (l₁ ++ (φ_p, pieces j) :: φRest'.zip fRest')) = 0 := by
                intro j
                let d : ℕ := W.dim φ_p
                let hpiece : TestFn :=
                  Mob.beta d (Mob.rot (-(θs j))) (pieces j)
                have hpieceSupp : tsupport (hpiece : Circle → ℂ) ⊆ A := by
                  dsimp only [hpiece]
                  rw [beta_rot_eq_rotPullback, tsupport_rotPullback]
                  rintro z ⟨y, hy, rfl⟩
                  rcases hsupp j hy with ⟨x, hx, rfl⟩
                  simpa only [← mul_smul, ← Mob.rot_add, neg_add_cancel,
                    Mob.rot_zero, one_smul] using hx
                obtain ⟨ε, hε, hstable⟩ :=
                  exists_rotStable d hAopen hpieceSupp
                let tail₀ : List (𝓕 × TestFn) :=
                  (φRest'.zip fRest').map fun p =>
                    (p.1, Mob.beta (W.dim p.1) (Mob.rot (-(θs j))) p.2)
                let l₂ : List (𝓕 × TestFn) := (φ_p, hpiece) :: tail₀
                have hcov : ∀ p ∈ l₂,
                    W.IsCovariant p.1 (W.dim p.1) := by
                  intro p _
                  exact hW.w1.2 p.1
                obtain ⟨G, hG, hcurve⟩ :=
                  W.exists_isDiscBoundaryClass_rotationCurve hW lam l₁ l₂
                have hGarc : ∀ θ ∈ Set.Ioo (-ε) ε,
                    G (Complex.exp (θ * Complex.I)) = 0 := by
                  intro θ hθ
                  have hθabs : |θ| < ε := (abs_lt).2 hθ
                  let headθ : 𝓕 × TestFn :=
                    (φ_p, Mob.beta d (Mob.rot θ) hpiece)
                  let tailθ : List (𝓕 × TestFn) := tail₀.map fun p =>
                    (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)
                  have hheadSupp : Supp headθ.2 := by
                    exact hSuppOfTsupport _ (hstable θ hθabs)
                  have hprefix : ∀ p ∈ l₁ ++ [headθ], Supp p.2 := by
                    intro p hp
                    rcases List.mem_append.mp hp with hp | hp
                    · exact hl₁ p hp
                    · have hp' : p = headθ := by simpa using hp
                      subst p
                      exact hheadSupp
                  have hfieldsθ : tailθ.map Prod.fst = φRest' := by
                    simpa [tailθ, tail₀, List.map_map, Function.comp_def] using
                      map_fst_zip_of_length_eq φRest' fRest' htail
                  have hlenθ : (tailθ.map Prod.snd).length = φRest'.length := by
                    simpa only [List.length_map] using congrArg List.length hfieldsθ
                  have hzipθ : φRest'.zip (tailθ.map Prod.snd) = tailθ := by
                    rw [← hfieldsθ]
                    exact zip_fst_snd tailθ
                  have ih' := ih (l₁ ++ [headθ])
                  dsimp only [Q] at ih'
                  have hih := ih' hprefix (tailθ.map Prod.snd) hlenθ
                  have hmapθ : l₂.map (fun p =>
                      (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)) =
                      headθ :: tailθ := by
                    rfl
                  have hcombined :
                      l₁ ++ l₂.map (fun p =>
                        (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)) =
                        (l₁ ++ [headθ]) ++
                          φRest'.zip (tailθ.map Prod.snd) := by
                    rw [hmapθ, hzipθ]
                    simp
                  have hrot :
                      W.U (Mob.rot θ) (W.smearedProduct l₂) =
                        W.smearedProduct (l₂.map fun p =>
                          (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)) :=
                    W.rotation_smearedProduct hW.w4 θ l₂ hcov
                  calc
                    G (Complex.exp (θ * Complex.I)) =
                        W.toWightmanStruct.compatApply lam
                          (W.toWightmanStruct.smearedProductOn l₁
                            (W.U (Mob.rot θ) (W.smearedProduct l₂))) := hcurve θ
                    _ = W.toWightmanStruct.compatApply lam
                          (W.toWightmanStruct.smearedProductOn l₁
                            (W.smearedProduct (l₂.map fun p =>
                              (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)))) := by
                          rw [hrot]
                    _ = W.toWightmanStruct.compatApply lam
                          (W.smearedProduct (l₁ ++ l₂.map fun p =>
                            (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2))) := by
                          rw [W.toWightmanStruct.smearedProduct_append]
                    _ = 0 := by
                          rw [hcombined]
                          exact hih
                have hclosed := hG.eq_zero_of_eqOn_arc
                  (show -ε < ε by linarith) hGarc
                have hexp : Complex.exp ((θs j) * Complex.I) ∈
                    Metric.closedBall (0 : ℂ) 1 := by
                  rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
                have hGzero : G (Complex.exp ((θs j) * Complex.I)) = 0 :=
                  hclosed _ hexp
                have hmapCancel : l₂.map (fun p =>
                    (p.1, Mob.beta (W.dim p.1) (Mob.rot (θs j)) p.2)) =
                    (φ_p, pieces j) :: φRest'.zip fRest' := by
                  simp [l₂, hpiece, tail₀, d, List.map_map, Function.comp_def,
                    beta_rot_cancel]
                have hrotj :
                    W.U (Mob.rot (θs j)) (W.smearedProduct l₂) =
                      W.smearedProduct (l₂.map fun p =>
                        (p.1, Mob.beta (W.dim p.1) (Mob.rot (θs j)) p.2)) :=
                  W.rotation_smearedProduct hW.w4 (θs j) l₂ hcov
                have hcurvePiece :
                    G (Complex.exp ((θs j) * Complex.I)) =
                      W.toWightmanStruct.compatApply lam
                        (W.smearedProduct
                          (l₁ ++ (φ_p, pieces j) :: φRest'.zip fRest')) := by
                  calc
                    G (Complex.exp ((θs j) * Complex.I)) =
                        W.toWightmanStruct.compatApply lam
                          (W.toWightmanStruct.smearedProductOn l₁
                            (W.U (Mob.rot (θs j)) (W.smearedProduct l₂))) :=
                      hcurve (θs j)
                    _ = W.toWightmanStruct.compatApply lam
                          (W.toWightmanStruct.smearedProductOn l₁
                            (W.smearedProduct (l₂.map fun p =>
                              (p.1, Mob.beta (W.dim p.1)
                                (Mob.rot (θs j)) p.2)))) := by
                          rw [hrotj]
                    _ = W.toWightmanStruct.compatApply lam
                          (W.toWightmanStruct.smearedProductOn l₁
                            (W.smearedProduct
                              ((φ_p, pieces j) :: φRest'.zip fRest'))) := by
                          rw [hmapCancel]
                    _ = W.toWightmanStruct.compatApply lam
                          (W.smearedProduct
                            (l₁ ++ (φ_p, pieces j) :: φRest'.zip fRest')) := by
                          rw [W.toWightmanStruct.smearedProduct_append]
                calc
                  W.toWightmanStruct.compatApply lam
                      (W.smearedProduct
                        (l₁ ++ (φ_p, pieces j) :: φRest'.zip fRest')) =
                    G (Complex.exp ((θs j) * Complex.I)) := hcurvePiece.symm
                  _ = 0 := hGzero
              change smearedProductSlotLinear W lam l₁ φ_p
                (φRest'.zip fRest') g' = 0
              rw [hsum, map_sum]
              simp [smearedProductSlotLinear, hpieceZero]
            exact hgoal g
  have hall : ∀ l : List (𝓕 × TestFn),
      W.toWightmanStruct.compatApply lam (W.smearedProduct l) = 0 := by
    intro l
    have h := hQ (l.map Prod.fst) []
    dsimp only [Q] at h
    have hzip : (l.map Prod.fst).zip (l.map Prod.snd) = l := zip_fst_snd l
    simpa only [List.nil_append, hzip] using
      h (by simp) (l.map Prod.snd) (by simp)
  have htop_le_ker : (⊤ : Submodule ℂ 𝓓) ≤ LinearMap.ker lam.1 := by
    rw [hW.w4.2]
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨l, rfl⟩
    change W.toWightmanStruct.compatApply lam (W.smearedProduct l) = 0
    exact hall l
  have hlam_zero : lam.1 = 0 := by
    apply LinearMap.ext
    intro Φ
    have hΦ := htop_le_ker (show Φ ∈ (⊤ : Submodule ℂ 𝓓) by simp)
    simpa using hΦ
  apply Subtype.ext
  exact hlam_zero

/-- The upper-semicircle specialization of the generic Reeh--Schlieder lemma. -/
theorem eq_zero_of_forall_smearedProduct_suppUpper_eq_zero
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (lam : W.toWightmanStruct.Compat)
    (hlam : ∀ l : List (𝓕 × TestFn), (∀ p ∈ l, SuppUpper p.2) →
      W.toWightmanStruct.compatApply lam (W.smearedProduct l) = 0) :
    lam = 0 := by
  exact eq_zero_of_forall_smearedProduct_supp_eq_zero W hW upperArc isOpen_upperArc
    upperArc_nonempty SuppUpper (fun _ => suppUpper_of_tsupport_subset) lam hlam

/-- The lower-semicircle specialization of the generic Reeh--Schlieder lemma. -/
theorem eq_zero_of_forall_smearedProduct_suppLower_eq_zero
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (lam : W.toWightmanStruct.Compat)
    (hlam : ∀ l : List (𝓕 × TestFn), (∀ p ∈ l, SuppLower p.2) →
      W.toWightmanStruct.compatApply lam (W.smearedProduct l) = 0) :
    lam = 0 := by
  exact eq_zero_of_forall_smearedProduct_supp_eq_zero W hW lowerArc isOpen_lowerArc
    lowerArc_nonempty SuppLower (fun _ => suppLower_of_tsupport_subset) lam hlam

end

end MobiusCPT
