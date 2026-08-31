import MobiusCPT.Analysis.DiscArcVanishing
import MobiusCPT.Wightman.Compat
import MobiusCPT.Wightman.W3Bridge
import MobiusCPT.Wightman.Lemma38
import MobiusCPT.Mobius.Beta
import MobiusCPT.TestFunctions.CNorm

/-!
# Rotation curves

Block R2 of Issue #13 ([CRTT25], Appendix A, Lemma A.1). This file records invariance of the
test-function `C^N` seminorms under rotations (`cnorm_beta_rot`, generalising
`MobiusCPT.Mobius.RotationPi`'s θ=π case to arbitrary θ), the closed-disc continuation of a
rotation curve when the product on the rotating side consists of monomial modes
(`exists_isDiscBoundaryClass_rotationCurve_monomial`, via the (W3) vacuum-annihilation bridge of
`MobiusCPT.Wightman.W3Bridge`), and the general rotation-curve theorem for an arbitrary smeared
product (`exists_isDiscBoundaryClass_rotationCurve`), obtained by approximating each test
function in the rotating product by its Fourier partial sum, expanding the resulting bounded
multilinear functional via `MultilinearMap.map_sum_finset`, and passing to the closed-disc
uniform limit via `MobiusCPT.isDiscBoundaryClass_of_tendstoUniformlyOn` (Block R1).
-/

namespace MobiusCPT

open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

/-- Pullback of a test function by rotation through the angle `-θ`. -/
def rotPullback (θ : ℝ) (f : TestFn) : TestFn :=
  ⟨fun z => f (Mob.rot (-θ) • z), by
    change ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      ((f : Circle → ℂ) ∘ (fun z : Circle => Mob.rot (-θ) • z))
    have hrot : (fun z : Circle => Mob.rot (-θ) • z) =
        fun z : Circle => rotMat (-θ) • z := by
      funext z
      rw [Mob.rot, Mob.mk_smul]
    rw [hrot]
    exact (ContMDiffMap.contMDiff f).comp (contMDiff_smul (rotMat (-θ)))⟩

/-- Evaluation of pullback by a rotation. -/
@[simp]
theorem rotPullback_apply (θ : ℝ) (f : TestFn) (z : Circle) :
    rotPullback θ f z = f (Mob.rot (-θ) • z) :=
  rfl

/-- The conformal action of a rotation is ordinary pullback by its inverse rotation. -/
theorem beta_rot_eq_rotPullback (d : ℕ) (θ : ℝ) (f : TestFn) :
    Mob.beta d (Mob.rot θ) f = rotPullback θ f := by
  apply TestFn.ext
  intro z
  rw [Mob.rot, Mob.beta_mk, beta_apply, X_rotMat]
  simp only [one_zpow, Complex.ofReal_one, one_mul, rotMat_inv,
    rotPullback_apply, rotMat_smul, Mob.rot_smul]

/-- In angle coordinates, rotation pullback is translation by `-θ`. -/
theorem toAngle_rotPullback (θ : ℝ) (f : TestFn) :
    toAngle (rotPullback θ f) = fun φ => toAngle f (φ - θ) := by
  funext φ
  calc
    toAngle (rotPullback θ f) φ =
        f (Mob.rot (-θ) • Circle.exp φ) := by rfl
    _ = f (Circle.exp (-θ) * Circle.exp φ) := by rw [Mob.rot_smul]
    _ = f (Circle.exp (-θ + φ)) := by rw [Circle.exp_add]
    _ = f (Circle.exp (φ - θ)) := by
      congr 1
      ring
    _ = toAngle f (φ - θ) := by rfl

/-- Angle derivatives are translated by rotation pullback. -/
theorem angleDeriv_rotPullback (j : ℕ) (θ : ℝ) (f : TestFn) :
    angleDeriv j (rotPullback θ f) = fun φ => angleDeriv j f (φ - θ) := by
  funext φ
  change iteratedDeriv j (toAngle (rotPullback θ f)) φ =
    iteratedDeriv j (toAngle f) (φ - θ)
  rw [toAngle_rotPullback]
  simpa only [sub_eq_add_neg] using
    congrFun (iteratedDeriv_comp_add_const j (toAngle f) (-θ)) φ

/-- The sup norm of every angle derivative is invariant under rotation pullback. -/
theorem norm_angleDerivB_rotPullback (j : ℕ) (θ : ℝ) (f : TestFn) :
    ‖angleDerivB j (rotPullback θ f)‖ = ‖angleDerivB j f‖ := by
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j (rotPullback θ f)) (C := ‖angleDerivB j f‖)
        (norm_nonneg _)).2
    intro φ
    rw [angleDerivB_apply, angleDeriv_rotPullback]
    exact norm_angleDeriv_le j f (φ - θ)
  · apply (BoundedContinuousFunction.norm_le
      (f := angleDerivB j f) (C := ‖angleDerivB j (rotPullback θ f)‖)
        (norm_nonneg _)).2
    intro φ
    rw [angleDerivB_apply]
    have hφ := norm_angleDeriv_le j (rotPullback θ f) (φ + θ)
    rw [angleDeriv_rotPullback] at hφ
    simpa only [add_sub_cancel_right] using hφ

/-- Every `C^N` seminorm is invariant under rotation pullback. -/
theorem cnorm_rotPullback (N : ℕ) (θ : ℝ) (f : TestFn) :
    cnorm N (rotPullback θ f) = cnorm N f := by
  apply NNReal.eq
  rw [cnorm_eq, cnorm_eq]
  exact Finset.sum_congr rfl (fun j _ => norm_angleDerivB_rotPullback j θ f)

/-- Every `C^N` seminorm is invariant under the conformal action of a rotation. -/
theorem cnorm_beta_rot (N d : ℕ) (θ : ℝ) (f : TestFn) :
    cnorm N (Mob.beta d (Mob.rot θ) f) = cnorm N f := by
  rw [beta_rot_eq_rotPullback, cnorm_rotPullback]

namespace WightmanData

/-- A rotation curve whose rotating smeared product consists of pure monomial modes is the
boundary value of a function continuous on the closed disc and holomorphic on the open disc. -/
theorem exists_isDiscBoundaryClass_rotationCurve_monomial
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (lam : W.toWightmanStruct.Compat) (l₁ : List (𝓕 × TestFn)) (l₂ : List (𝓕 × ℤ)) :
    ∃ G : ℂ → ℂ, IsDiscBoundaryClass G ∧
      ∀ θ : ℝ, G (Complex.exp (θ * Complex.I)) =
        W.toWightmanStruct.compatApply lam
          (W.toWightmanStruct.smearedProductOn l₁
            (W.U (Mob.rot θ)
              (W.smearedProduct (l₂.map fun p => (p.1, monomial p.2))))) := by
  let n : ℤ := (l₂.map Prod.snd).sum
  let V₂ : 𝓓 := W.smearedProduct (l₂.map fun p => (p.1, monomial p.2))
  have hcov : ∀ p ∈ l₂, W.IsCovariant p.1 (W.dim p.1) := by
    intro p hp
    exact hW.w1.2 p.1
  have hdim : W.HasConformalDim V₂ (-n) := by
    simpa only [V₂, n] using
      W.hasConformalDim_smearedProduct_monomial hW.w4 l₂ hcov
  by_cases hn : 0 < n
  · have hV₂ : V₂ = 0 := by
      simpa only [V₂] using
        W.smearedProduct_monomial_eq_zero hW.w3 hW.w4 l₂ hcov
          (by simpa only [n] using hn)
    have hsmearedZero :
        W.toWightmanStruct.smearedProductOn l₁ (0 : 𝓓) = 0 := by
      simpa using
        (W.toWightmanStruct.smearedProductOn_linear l₁ (0 : 𝓓) (0 : 𝓓)).2 (0 : ℂ)
    refine ⟨fun _ => 0, ⟨continuousOn_const, differentiableOn_const (0 : ℂ)⟩, ?_⟩
    intro θ
    change (0 : ℂ) = W.toWightmanStruct.compatApply lam
      (W.toWightmanStruct.smearedProductOn l₁ (W.U (Mob.rot θ) V₂))
    rw [hV₂, map_zero, hsmearedZero]
    exact (LinearMap.map_zero lam.1).symm
  · have hn_nonpos : n ≤ 0 := le_of_not_gt hn
    have hminus_nonneg : 0 ≤ -n := neg_nonneg_of_nonpos hn_nonpos
    let m : ℕ := (-n).toNat
    have hm : (m : ℤ) = -n := by
      change ((-n).toNat : ℤ) = -n
      exact Int.toNat_of_nonneg hminus_nonneg
    let C₀ : ℂ := W.toWightmanStruct.compatApply lam
      (W.toWightmanStruct.smearedProductOn l₁ V₂)
    have hrot (θ : ℝ) :
        W.U (Mob.rot θ) V₂ =
          Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) • V₂ := by
      exact hdim θ
    have hcurve (θ : ℝ) :
        W.toWightmanStruct.compatApply lam
            (W.toWightmanStruct.smearedProductOn l₁ (W.U (Mob.rot θ) V₂)) =
          Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * C₀ := by
      calc
        W.toWightmanStruct.compatApply lam
            (W.toWightmanStruct.smearedProductOn l₁ (W.U (Mob.rot θ) V₂)) =
            W.toWightmanStruct.compatApply lam
              (W.toWightmanStruct.smearedProductOn l₁
                (Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) • V₂)) := by
                  rw [hrot]
        _ = W.toWightmanStruct.compatApply lam
              (Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) •
                W.toWightmanStruct.smearedProductOn l₁ V₂) := by
                  rw [(W.toWightmanStruct.smearedProductOn_linear l₁ V₂ V₂).2
                    (Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I))]
        _ = Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) •
              W.toWightmanStruct.compatApply lam
                (W.toWightmanStruct.smearedProductOn l₁ V₂) :=
                  (W.toWightmanStruct.compatApply_linear lam
                    (W.toWightmanStruct.smearedProductOn l₁ V₂)
                    (W.toWightmanStruct.smearedProductOn l₁ V₂)).2 _
        _ = Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * C₀ := by
              rw [smul_eq_mul]
    refine ⟨fun z : ℂ => C₀ * z ^ m, ?_, ?_⟩
    · constructor
      · exact (continuous_const.mul (continuous_pow m)).continuousOn
      · exact ((differentiable_const C₀).mul (differentiable_pow m)).differentiableOn
    · intro θ
      change C₀ * Complex.exp ((θ : ℂ) * Complex.I) ^ m =
        W.toWightmanStruct.compatApply lam
          (W.toWightmanStruct.smearedProductOn l₁ (W.U (Mob.rot θ) V₂))
      rw [hcurve]
      calc
        C₀ * Complex.exp ((θ : ℂ) * Complex.I) ^ m =
            C₀ * Complex.exp ((m : ℂ) * ((θ : ℂ) * Complex.I)) := by
              rw [Complex.exp_nat_mul]
        _ = C₀ * Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
              apply congrArg (fun z : ℂ => C₀ * Complex.exp z)
              rw [← hm]
              push_cast
              ring
        _ = Complex.exp (((-n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * C₀ := by
              rw [mul_comm]

open Set Filter

/-- An arbitrary rotation curve of a smeared product is the boundary value of a function
continuous on the closed disc and holomorphic on the open disc. -/
theorem exists_isDiscBoundaryClass_rotationCurve
    {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]
    (W : WightmanData Mob TestFn 𝓓 𝓕) (hW : W.IsWightmanCFT)
    (lam : W.toWightmanStruct.Compat) (l₁ l₂ : List (𝓕 × TestFn)) :
    ∃ G : ℂ → ℂ, IsDiscBoundaryClass G ∧
      ∀ θ : ℝ, G (Complex.exp (θ * Complex.I)) =
        W.toWightmanStruct.compatApply lam
          (W.toWightmanStruct.smearedProductOn l₁
            (W.U (Mob.rot θ) (W.smearedProduct l₂))) := by
  classical
  let k₂ := l₂.length
  let φs₂ : Fin k₂ → 𝓕 := fun i => (l₂.get i).1
  let g₀ : Fin k₂ → TestFn := fun i => (l₂.get i).2
  let L : 𝓓 →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => W.toWightmanStruct.compatApply lam
        (W.toWightmanStruct.smearedProductOn l₁ Φ)
      map_add' := by
        intro Φ Ψ
        rw [(W.toWightmanStruct.smearedProductOn_linear l₁ Φ Ψ).1]
        exact (W.toWightmanStruct.compatApply_linear lam _ _).1
      map_smul' := by
        intro c Φ
        show W.toWightmanStruct.compatApply lam
            (W.toWightmanStruct.smearedProductOn l₁ (c • Φ)) =
          c • W.toWightmanStruct.compatApply lam
            (W.toWightmanStruct.smearedProductOn l₁ Φ)
        rw [(W.toWightmanStruct.smearedProductOn_linear l₁ Φ Φ).2 c]
        exact (W.toWightmanStruct.compatApply_linear lam
          (W.toWightmanStruct.smearedProductOn l₁ Φ)
          (W.toWightmanStruct.smearedProductOn l₁ Φ)).2 c }
  let M : MultilinearMap ℂ (fun _ : Fin k₂ => TestFn) ℂ :=
    L.compMultilinearMap
      (W.toWightmanStruct.multiSmearMultilinear φs₂ W.vac)
  have hM_apply (g : Fin k₂ → TestFn) :
      M g = W.toWightmanStruct.compatApply lam
        (W.toWightmanStruct.smearedProductOn l₁
          (W.toWightmanStruct.multiSmear φs₂ W.vac g)) := by
    rfl
  have hMcont : Continuous M := by
    let ψs : Fin (l₁.length + k₂) → 𝓕 :=
      Fin.append (fun j => (l₁.get j).1) φs₂
    let cs : Fin l₁.length → TestFn := fun j => (l₁.get j).2
    have happend : Continuous
        (fun g : Fin k₂ → TestFn => Fin.append cs g) := by
      apply continuous_pi
      intro q
      induction q using Fin.addCases with
      | left j =>
          simpa [Fin.append] using
            (continuous_const : Continuous (fun _ : Fin k₂ → TestFn => cs j))
      | right j =>
          simpa [Fin.append] using (continuous_apply j)
    have hmulti (g : Fin k₂ → TestFn) :
        W.toWightmanStruct.smearedProductOn l₁
            (W.toWightmanStruct.multiSmear φs₂ W.vac g) =
          W.toWightmanStruct.multiSmear ψs W.vac (Fin.append cs g) := by
      have hconcat :
          (fun q : Fin (l₁.length + k₂) => (ψs q, Fin.append cs g q)) =
            Fin.append (fun j : Fin l₁.length => l₁.get j)
              (fun j : Fin k₂ => (φs₂ j, g j)) := by
        funext q
        induction q using Fin.addCases with
        | left j => simp [ψs, cs, Fin.append]
        | right j => simp [ψs, cs, Fin.append]
      have hlist :
          List.ofFn (fun q : Fin (l₁.length + k₂) =>
            (ψs q, Fin.append cs g q)) =
            l₁ ++ List.ofFn (fun j : Fin k₂ => (φs₂ j, g j)) := by
        rw [hconcat, List.ofFn_fin_append, List.ofFn_get]
      change W.toWightmanStruct.smearedProductOn l₁
          (W.toWightmanStruct.smearedProductOn
            (List.ofFn fun j : Fin k₂ => (φs₂ j, g j)) W.vac) =
        W.toWightmanStruct.smearedProductOn
          (List.ofFn fun q : Fin (l₁.length + k₂) =>
            (ψs q, Fin.append cs g q)) W.vac
      rw [← W.toWightmanStruct.smearedProductOn_append, hlist]
    change Continuous (fun g : Fin k₂ → TestFn =>
      W.toWightmanStruct.compatApply lam
        (W.toWightmanStruct.smearedProductOn l₁
          (W.toWightmanStruct.multiSmear φs₂ W.vac g)))
    exact ((lam.2 _ ψs W.vac).comp happend).congr fun g =>
      congrArg lam.1 (hmulti g).symm
  obtain ⟨N₀, A, hA, hbound⟩ :=
    cnorm_bound_of_continuous_multilinear M hMcont
  have hl₂ : List.ofFn (fun i : Fin k₂ => (φs₂ i, g₀ i)) = l₂ := by
    simpa [k₂, φs₂, g₀] using List.ofFn_get l₂
  let d : Fin k₂ → ℕ := fun i => W.dim (φs₂ i)
  let gθ : ℝ → Fin k₂ → TestFn := fun θ i =>
    Mob.beta (d i) (Mob.rot θ) (g₀ i)
  let gN : ℕ → Fin k₂ → TestFn := fun N i => fourierPartialSum (g₀ i) N
  let gθN : ℕ → ℝ → Fin k₂ → TestFn := fun N θ i =>
    Mob.beta (d i) (Mob.rot θ) (gN N i)
  have hrot (g : Fin k₂ → TestFn) (θ : ℝ) :
      W.U (Mob.rot θ) (W.toWightmanStruct.multiSmear φs₂ W.vac g) =
        W.toWightmanStruct.multiSmear φs₂ W.vac
          (fun i => Mob.beta (d i) (Mob.rot θ) (g i)) := by
    have hcov : ∀ p ∈ (List.ofFn fun i : Fin k₂ => (φs₂ i, g i)),
        W.IsCovariant p.1 (W.dim p.1) := by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hW.w1.2 (φs₂ i)
    have hraw :
        W.U (Mob.rot θ)
            (W.smearedProduct (List.ofFn fun i : Fin k₂ => (φs₂ i, g i))) =
          W.smearedProduct
            ((List.ofFn fun i : Fin k₂ => (φs₂ i, g i)).map
              fun p => (p.1, Mob.beta (W.dim p.1) (Mob.rot θ) p.2)) :=
      W.rotation_smearedProduct hW.w4 θ
        (List.ofFn fun i : Fin k₂ => (φs₂ i, g i)) hcov
    change W.U (Mob.rot θ)
        (W.smearedProduct (List.ofFn fun i : Fin k₂ => (φs₂ i, g i))) =
      W.smearedProduct (List.ofFn fun i : Fin k₂ =>
        (φs₂ i, Mob.beta (d i) (Mob.rot θ) (g i)))
    rw [hraw, List.map_ofFn]
    rfl
  have hcurve (θ : ℝ) :
      W.toWightmanStruct.compatApply lam
          (W.toWightmanStruct.smearedProductOn l₁
            (W.U (Mob.rot θ) (W.smearedProduct l₂))) = M (gθ θ) := by
    rw [← hl₂]
    change W.toWightmanStruct.compatApply lam
        (W.toWightmanStruct.smearedProductOn l₁
          (W.U (Mob.rot θ)
            (W.toWightmanStruct.multiSmear φs₂ W.vac g₀))) = M (gθ θ)
    rw [hrot]
    rfl
  let Gr : (Fin k₂ → ℤ) → ℂ → ℂ := fun r => Classical.choose
    (exists_isDiscBoundaryClass_rotationCurve_monomial W hW lam l₁
      (List.ofFn fun i : Fin k₂ => (φs₂ i, r i)))
  have hGr (r : Fin k₂ → ℤ) : IsDiscBoundaryClass (Gr r) ∧
      ∀ θ : ℝ, Gr r (Complex.exp (θ * Complex.I)) =
        W.toWightmanStruct.compatApply lam
          (W.toWightmanStruct.smearedProductOn l₁
            (W.U (Mob.rot θ)
              (W.smearedProduct
                ((List.ofFn fun i : Fin k₂ => (φs₂ i, r i)).map
                  fun p => (p.1, monomial p.2))))) := by
    exact Classical.choose_spec
      (exists_isDiscBoundaryClass_rotationCurve_monomial W hW lam l₁
        (List.ofFn fun i : Fin k₂ => (φs₂ i, r i)))
  have hGrM (r : Fin k₂ → ℤ) (θ : ℝ) :
      Gr r (Complex.exp (θ * Complex.I)) =
        M (fun i => Mob.beta (d i) (Mob.rot θ) (monomial (r i))) := by
    rw [(hGr r).2 θ]
    rw [List.map_ofFn]
    change W.toWightmanStruct.compatApply lam
        (W.toWightmanStruct.smearedProductOn l₁
          (W.U (Mob.rot θ)
            (W.toWightmanStruct.multiSmear φs₂ W.vac
              (fun i => monomial (r i))))) = _
    rw [hrot]
    rfl
  let modes : ℕ → Finset (Fin k₂ → ℤ) := fun N =>
    Fintype.piFinset fun _ : Fin k₂ => Finset.Icc (-(N : ℤ)) (N : ℤ)
  let coeff : (Fin k₂ → ℤ) → ℂ := fun r =>
    ∏ i, fourierCoef (g₀ i) (r i)
  let GN : ℕ → ℂ → ℂ := fun N z =>
    ∑ r ∈ modes N, coeff r * Gr r z
  have hGNclass (N : ℕ) : IsDiscBoundaryClass (GN N) := by
    constructor
    · exact continuousOn_finsetSum (modes N) fun r _ =>
        continuousOn_const.mul (hGr r).1.1
    · exact DifferentiableOn.fun_sum fun r _ =>
        (differentiableOn_const (coeff r)).mul (hGr r).1.2
  have hbetaSum (N : ℕ) (θ : ℝ) (i : Fin k₂) :
      gθN N θ i =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          fourierCoef (g₀ i) n • Mob.beta (d i) (Mob.rot θ) (monomial n) := by
    simp only [gθN, gN, fourierPartialSum, map_sum, map_smul]
  have hGNboundary (N : ℕ) (θ : ℝ) :
      GN N (Complex.exp (θ * Complex.I)) = M (gθN N θ) := by
    calc
      GN N (Complex.exp (θ * Complex.I)) =
          ∑ r ∈ modes N, coeff r *
            M (fun i => Mob.beta (d i) (Mob.rot θ) (monomial (r i))) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hGrM]
      _ = ∑ r ∈ modes N, M (fun i =>
            fourierCoef (g₀ i) (r i) •
              Mob.beta (d i) (Mob.rot θ) (monomial (r i))) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [M.map_smul_univ, smul_eq_mul]
      _ = M (fun i => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            fourierCoef (g₀ i) n •
              Mob.beta (d i) (Mob.rot θ) (monomial n)) := by
        exact (M.map_sum_finset
          (A := fun _ : Fin k₂ => Finset.Icc (-(N : ℤ)) (N : ℤ))
          (g := fun i n => fourierCoef (g₀ i) n •
            Mob.beta (d i) (Mob.rot θ) (monomial n))).symm
      _ = M (gθN N θ) := by
        congr 1
        funext i
        exact (hbetaSum N θ i).symm
  have hcnorm_tendsto (i : Fin k₂) :
      Tendsto (fun n => (cnorm N₀ (gN n i) : ℝ)) atTop
        (nhds (cnorm N₀ (g₀ i) : ℝ)) := by
    exact ((withSeminorms_cnorm.continuous_seminorm N₀).tendsto (g₀ i)).comp
      (tendsto_fourierPartialSum (g₀ i))
  choose C hC using fun i : Fin k₂ => (hcnorm_tendsto i).bddAbove_range
  have hCbound (i : Fin k₂) (n : ℕ) : (cnorm N₀ (gN n i) : ℝ) ≤ C i :=
    hC i (Set.mem_range_self n)
  have hCnonneg (i : Fin k₂) : 0 ≤ C i :=
    (NNReal.coe_nonneg (cnorm N₀ (gN 0 i))).trans (hCbound i 0)
  have hGNcauchy :
      UniformCauchySeqOn GN atTop (Metric.closedBall (0 : ℂ) 1) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let B : ℝ := ∏ i : Fin k₂, (1 + C i + C i)
    have hB : 0 < B := by
      dsimp [B]
      exact Finset.prod_pos fun i _ => by linarith [hCnonneg i]
    let K : ℝ := A * (k₂ : ℝ) * B
    have hK : 0 ≤ K := by positivity
    let δ : ℝ := ε / (K + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hKδ : K * δ < ε := by
      have hK1 : (0 : ℝ) < K + 1 := by linarith
      rw [show K * δ = K * ε / (K + 1) by dsimp [δ]; ring]
      rw [div_lt_iff₀ hK1]
      nlinarith
    have herr (i : Fin k₂) :
        Tendsto (fun n => (cnorm N₀ (gN n i - g₀ i) : ℝ)) atTop (nhds 0) := by
      simpa only [gN] using tendsto_cnorm_fourierPartialSum N₀ (g₀ i)
    choose q hq using fun i : Fin k₂ => eventually_atTop.mp
      ((herr i).eventually (eventually_lt_nhds (by positivity : 0 < δ / 2)))
    let n₀ : ℕ := Finset.univ.sup q
    refine ⟨n₀, fun m hm n hn z hz => ?_⟩
    have hqle (i : Fin k₂) : q i ≤ n₀ :=
      Finset.le_sup (f := q) (Finset.mem_univ i)
    have hpair (i : Fin k₂) :
        (cnorm N₀ (gN m i - gN n i) : ℝ) < δ := by
      have hm' := hq i m ((hqle i).trans hm)
      have hn' := hq i n ((hqle i).trans hn)
      have hneg : cnorm N₀ (g₀ i - gN n i) = cnorm N₀ (gN n i - g₀ i) := by
        rw [show g₀ i - gN n i = -(gN n i - g₀ i) by abel]
        simpa only [neg_one_smul, nnnorm_neg, nnnorm_one, one_mul] using
          cnorm_smul N₀ (-1 : ℂ) (gN n i - g₀ i)
      calc
        (cnorm N₀ (gN m i - gN n i) : ℝ) =
            (cnorm N₀ ((gN m i - g₀ i) + (g₀ i - gN n i)) : ℝ) := by
              congr 2
              abel
        _ ≤ (cnorm N₀ (gN m i - g₀ i) : ℝ) +
            (cnorm N₀ (g₀ i - gN n i) : ℝ) := by
              exact_mod_cast cnorm_add_le N₀ (gN m i - g₀ i) (g₀ i - gN n i)
        _ = (cnorm N₀ (gN m i - g₀ i) : ℝ) +
            (cnorm N₀ (gN n i - g₀ i) : ℝ) := by rw [hneg]
        _ < δ := by linarith
    have hboundary (θ : ℝ) :
        ‖GN m (Complex.exp (θ * Complex.I)) -
            GN n (Complex.exp (θ * Complex.I))‖ ≤ K * δ := by
      rw [hGNboundary, hGNboundary]
      have htel := MultilinearMap.norm_sub_le_of_cnorm_bound
        M N₀ A hA.le hbound (gθN m θ) (gθN n θ)
      have hsupNN :
          Finset.univ.sup (fun i => cnorm N₀ (gθN m θ i - gθN n θ i)) ≤
            (⟨δ, hδ.le⟩ : NNReal) := by
        apply Finset.sup_le
        intro i hi
        apply NNReal.coe_le_coe.mp
        have hdiff : gθN m θ i - gθN n θ i =
            Mob.beta (d i) (Mob.rot θ) (gN m i - gN n i) := by
          simp only [gθN, map_sub]
        rw [hdiff, cnorm_beta_rot]
        exact (hpair i).le
      have hsup :
          ((Finset.univ.sup fun i => cnorm N₀
            (gθN m θ i - gθN n θ i) : NNReal) : ℝ) ≤ δ := by
        exact NNReal.coe_le_coe.mpr hsupNN
      have hprod :
          (∏ i : Fin k₂, (1 + (cnorm N₀ (gθN m θ i) : ℝ) +
            (cnorm N₀ (gθN n θ i) : ℝ))) ≤ B := by
        dsimp [B]
        apply Finset.prod_le_prod
        · intro i hi
          positivity
        · intro i hi
          simp only [gθN, cnorm_beta_rot]
          exact add_le_add (add_le_add le_rfl (hCbound i m)) (hCbound i n)
      calc
        ‖M (gθN m θ) - M (gθN n θ)‖ ≤
            A * (k₂ : ℝ) *
              ((Finset.univ.sup fun i => cnorm N₀
                (gθN m θ i - gθN n θ i) : NNReal) : ℝ) *
              ∏ i : Fin k₂, (1 + (cnorm N₀ (gθN m θ i) : ℝ) +
                (cnorm N₀ (gθN n θ i) : ℝ)) := htel
        _ ≤ A * (k₂ : ℝ) * δ * B := by gcongr
        _ = K * δ := by dsimp [K]; ring
    rw [dist_eq_norm]
    calc
      ‖GN m z - GN n z‖ ≤ K * δ := by
        have hdiffClass : DiffContOnCl ℂ (fun w => GN m w - GN n w)
            (Metric.ball (0 : ℂ) 1) :=
          DiffContOnCl.mk_ball ((hGNclass m).2.sub (hGNclass n).2)
            ((hGNclass m).1.sub (hGNclass n).1)
        apply Complex.norm_le_of_forall_mem_frontier_norm_le
          Metric.isBounded_ball hdiffClass
        · intro w hw
          rw [frontier_ball (0 : ℂ) (by norm_num)] at hw
          have hwnorm : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
          have hwexp : Complex.exp (Complex.arg w * Complex.I) = w := by
            have h := Complex.norm_mul_exp_arg_mul_I w
            rw [hwnorm] at h
            simpa only [Complex.ofReal_one, one_mul] using h
          rw [← hwexp]
          exact hboundary (Complex.arg w)
        · rw [closure_ball (0 : ℂ) (by norm_num)]
          exact hz
      _ < ε := hKδ
  let G : ℂ → ℂ := fun z => limUnder atTop (fun N => GN N z)
  have hGNtendsto : TendstoUniformlyOn GN G atTop
      (Metric.closedBall (0 : ℂ) 1) :=
    hGNcauchy.tendstoUniformlyOn_of_tendsto fun z hz =>
      (hGNcauchy.cauchySeq hz).tendsto_limUnder
  have hGclass : IsDiscBoundaryClass G :=
    isDiscBoundaryClass_of_tendstoUniformlyOn hGNclass hGNtendsto
  refine ⟨G, hGclass, ?_⟩
  intro θ
  have hz : Complex.exp (θ * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]
  have htuple : Tendsto (fun N => gθN N θ) atTop (nhds (gθ θ)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_cnorm]
    intro q
    have h := tendsto_cnorm_fourierPartialSum q (g₀ i)
    have heq : (fun N : ℕ => (cnorm q (gθN N θ i - gθ θ i) : ℝ)) =
        fun N : ℕ => (cnorm q (fourierPartialSum (g₀ i) N - g₀ i) : ℝ) := by
      funext N
      show (cnorm q (Mob.beta (d i) (Mob.rot θ) (gN N i) -
        Mob.beta (d i) (Mob.rot θ) (g₀ i)) : ℝ) = _
      rw [← map_sub, cnorm_beta_rot]
    rw [heq]
    exact h
  have hcurveTendsto : Tendsto
      (fun N => GN N (Complex.exp (θ * Complex.I))) atTop
      (nhds (M (gθ θ))) := by
    have h := (hMcont.tendsto (gθ θ)).comp htuple
    exact Tendsto.congr (fun N => (hGNboundary N θ).symm) h
  rw [hcurve θ]
  exact tendsto_nhds_unique (hGNtendsto.tendsto_at hz) hcurveTendsto

end WightmanData

end

end MobiusCPT
