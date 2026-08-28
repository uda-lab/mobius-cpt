import MobiusCPT.Wightman.Modes
import MobiusCPT.Wightman.Axioms
import MobiusCPT.Mobius.Beta
import MobiusCPT.TestFunctions.Fourier

/-!
# MobiusCPT.Wightman.W3Bridge

[T26], proof of Lemma 3.7, and the Issue #2 source gate (part 3 §1): the (W3)
vacuum-annihilation bridge on the concrete instance `G = Mob`, `TF = TestFn`.

[T26] disposes of this in one sentence — `F ∘ z⁻¹` is holomorphic on the disc and vanishes
at the origin, "and thus `φ(F∘z⁻¹|_{S¹})` strictly lowers conformal dimension", whence
`φ(F∘z⁻¹|_{S¹})Ω = 0`.  The three steps that sentence compresses are:

1. `φ(z^n)Ω` has conformal dimension `-n` (`MobiusCPT.Wightman.Modes`, discharged here for
   the monomials by `Mob.beta_rot_monomial`);
2. for `n > 0` the dimension is negative, so (W3) gives `φ(z^n)Ω = 0` — **mode by mode**;
3. for a test function `f` whose Fourier coefficients vanish for `n ≤ 0`, every compatible
   functional `λ ∈ D*_𝓕` kills `φ(f)Ω`, because `f ↦ λ(φ(f)Ω)` is continuous
   (compatibility at `k = 1`) and the Fourier series converges in `C^∞(S¹)`; regularity
   (separation of points by `D*_𝓕`) then upgrades this to `φ(f)Ω = 0`.

(W3) is never applied to `φ(f)Ω` for a general `f`: that vector is not a rotation
eigenvector and carries no conformal dimension.  Every (W3) application in this development
— `WightmanData.smear_vac_eq_zero_of_rotWeight_pos`, `WightmanData.weightedProduct_eq_zero_of_sum_pos`
and `WightmanData.smearedProduct_monomial_eq_zero` — is on a vector with a proved conformal
dimension.

**The `n ≤ 0` hypothesis is the source's and cannot be weakened to `n < 0`.** [T26] uses
`F ∘ z⁻¹` holomorphic on the disc *and vanishing at `0`*, so its Taylor expansion has only
*strictly positive* powers.  The zero mode must be excluded: `φ(z^0)Ω` has conformal
dimension `0`, and (W3) only annihilates vectors of dimension `d < 0`.
-/

namespace MobiusCPT

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- [T26], Definition 2.4 and the Issue #2 source gate: the monomial `z^n` is a rotation
eigenvector of weight `n` for every conformal weight `d`, i.e. `β_d(r_θ)z^n = e^{-inθ}z^n`.
This is `Mob.beta_rot_monomial`, i.e. it is **proved** from the conformal action, not
assumed. -/
theorem isRotWeight_monomial (d : ℕ) (n : ℤ) :
    IsRotWeight Mob d (monomial n) n := by
  intro θ
  exact Mob.beta_rot_monomial d θ n

namespace WightmanData

/-- [T26], proof of Lemma 3.7, step 1, on the concrete instance: `φ(z^n)Ω` has conformal
dimension `-n`. -/
theorem hasConformalDim_smear_monomial_vac (W : WightmanData Mob TestFn 𝓓 𝓕) (hW4 : W.W4)
    {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d) (n : ℤ) :
    W.HasConformalDim (W.smear φ (monomial n) W.vac) (-n) := by
  exact W.hasConformalDim_smear_vac hW4 hcov (isRotWeight_monomial d n)

/-- [T26], proof of Lemma 3.7, step 2, on the concrete instance: for `n > 0`, (W3) gives
`φ(z^n)Ω = 0`. -/
theorem smear_monomial_vac_eq_zero (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW3 : W.W3) (hW4 : W.W4) {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d)
    {n : ℤ} (hn : 0 < n) :
    W.smear φ (monomial n) W.vac = 0 := by
  exact W.smear_vac_eq_zero_of_rotWeight_pos hW3 hW4 hcov
    (isRotWeight_monomial d n) hn

/-- [T26], proof of Lemma 3.7, step 1, and [CRTT25] §2, on the concrete instance:
`φ₁(z^{n₁})⋯φ_k(z^{n_k})Ω` has conformal dimension `-(n₁+⋯+n_k)`. -/
theorem hasConformalDim_smearedProduct_monomial (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW4 : W.W4) (l : List (𝓕 × ℤ))
    (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1)) :
    W.HasConformalDim (W.smearedProduct (l.map fun p => (p.1, monomial p.2)))
      (-(l.map Prod.snd).sum) := by
  let weighted := l.map fun p => (p.1, monomial p.2, p.2)
  have hcovWeighted : ∀ q ∈ weighted, W.IsCovariant q.1 (W.dim q.1) := by
    intro q hq
    simp only [weighted, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hcov p hp
  have hwWeighted :
      ∀ q ∈ weighted, IsRotWeight Mob (W.dim q.1) q.2.1 q.2.2 := by
    intro q hq
    simp only [weighted, List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact isRotWeight_monomial (W.dim p.1) p.2
  simpa only [WightmanData.weightedProduct, weighted, List.map_map,
    Function.comp_def] using
    W.hasConformalDim_weightedProduct hW4 weighted hcovWeighted hwWeighted

/-- [T26], proof of Lemma 3.7, step 2, for products on the concrete instance: a product of
monomial modes whose exponents sum to a strictly positive integer annihilates the vacuum. -/
theorem smearedProduct_monomial_eq_zero (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW3 : W.W3) (hW4 : W.W4) (l : List (𝓕 × ℤ))
    (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1))
    (hsum : 0 < (l.map Prod.snd).sum) :
    W.smearedProduct (l.map fun p => (p.1, monomial p.2)) = 0 := by
  exact hW3 _ (-(l.map Prod.snd).sum) (by omega)
    (W.hasConformalDim_smearedProduct_monomial hW4 l hcov)

/-- [T26], Definition 2.4: `f ↦ φ(f)Ω` as a complex-linear map on test functions. -/
noncomputable def smearVac (W : WightmanData Mob TestFn 𝓓 𝓕) (φ : 𝓕) : TestFn →ₗ[ℂ] 𝓓 where
  toFun f := W.smear φ f W.vac
  map_add' := by
    intro f g
    exact (W.toWightmanStruct.smear_addLinear φ f g W.vac).1
  map_smul' := by
    intro c f
    exact (W.toWightmanStruct.smear_addLinear φ f f W.vac).2 c

/-- [T26], Definition 2.4: `smearVac` computes the smeared field on the vacuum. -/
@[simp] theorem smearVac_apply (W : WightmanData Mob TestFn 𝓓 𝓕) (φ : 𝓕) (f : TestFn) :
    W.smearVac φ f = W.smear φ f W.vac := rfl

/-- [T26], Definition 2.4, at `k = 1`: compatibility of `λ` makes `f ↦ λ(φ(f)Ω)`
continuous on `C^∞(S¹)`.  This is the continuity that lets the Fourier expansion be
exchanged with `λ` in step 3; it is not a formal manipulation of the series. -/
theorem continuous_compatApply_smearVac (W : WightmanData Mob TestFn 𝓓 𝓕)
    (lam : W.toWightmanStruct.Compat) (φ : 𝓕) :
    Continuous fun f : TestFn =>
      W.toWightmanStruct.compatApply lam (W.smearVac φ f) := by
  have hdiag : Continuous (fun f : TestFn => (fun _ : Fin 1 => f)) :=
    continuous_pi fun _ => continuous_id
  simpa [WightmanStruct.compatApply, WightmanStruct.multiSmear,
    WightmanStruct.smearedProductOn, Function.comp_def] using
    (lam.2 1 (fun _ => φ) W.vac).comp hdiag

/-- [T26], proof of Lemma 3.7, step 3: the Fourier expansion of `f` is transported through
the continuous linear functional `f ↦ λ(φ(f)Ω)`.  The exchange of the sum with `λ` is
`hasSum_fourierSeries` — convergence in the `C^∞(S¹)` topology — mapped through that
continuous map, not a formal rearrangement. -/
theorem hasSum_compatApply_smearVac (W : WightmanData Mob TestFn 𝓓 𝓕)
    (lam : W.toWightmanStruct.Compat) (φ : 𝓕) (f : TestFn) :
    HasSum
      (fun n : ℤ => fourierCoef f n *
        W.toWightmanStruct.compatApply lam (W.smear φ (monomial n) W.vac))
      (W.toWightmanStruct.compatApply lam (W.smear φ f W.vac)) := by
  let g : TestFn →ₗ[ℂ] ℂ := lam.1.comp (W.smearVac φ)
  have hg : Continuous g := W.continuous_compatApply_smearVac lam φ
  have hs := (hasSum_fourierSeries f).map g hg
  simpa only [g, Function.comp_def, LinearMap.comp_apply, W.smearVac_apply,
    WightmanStruct.compatApply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] using hs

/-- [T26], proof of Lemma 3.7, step 3, the value on the dual: for `φ` covariant of
dimension `d` and `f` whose Fourier coefficients vanish for `n ≤ 0`, every compatible
functional kills `φ(f)Ω`. -/
theorem compatApply_smear_vac_eq_zero (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW3 : W.W3) (hW4 : W.W4) {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d)
    (f : TestFn) (hf : ∀ n : ℤ, n ≤ 0 → fourierCoef f n = 0)
    (lam : W.toWightmanStruct.Compat) :
    W.toWightmanStruct.compatApply lam (W.smear φ f W.vac) = 0 := by
  have hs := W.hasSum_compatApply_smearVac lam φ f
  have hsZero : HasSum
      (fun n : ℤ => fourierCoef f n *
        W.toWightmanStruct.compatApply lam (W.smear φ (monomial n) W.vac)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0) using 1
    funext n
    rcases le_or_gt n 0 with hn | hn
    · rw [hf n hn, zero_mul]
    · rw [W.smear_monomial_vac_eq_zero hW3 hW4 hcov hn]
      simp only [WightmanStruct.compatApply, map_zero, mul_zero]
  exact hs.unique hsZero

/-- **The (W3) vacuum-annihilation bridge.** [T26], proof of Lemma 3.7, and the Issue #2
source gate, part 3 §1.  For a Möbius-covariant Wightman CFT, a field `φ` covariant of
conformal dimension `d`, and a test function `f ∈ C^∞(S¹)` whose Fourier coefficients
vanish for every `n ≤ 0` — i.e. `f = Σ_{n>0} f̂ₙ zⁿ`, the boundary value of a function
holomorphic on the disc and vanishing at the origin — we have `φ(f)Ω = 0`.

Issues #7 and #9 instantiate this with `f = (F ∘ z⁻¹)|_{S¹}` for `F ∈ 𝓧`, which is exactly
the hypothesis [T26] supplies there.  The `n ≤ 0` hypothesis is the source's and is sharp
for this argument: the zero mode `φ(z⁰)Ω` has conformal dimension `0`, which (W3) — a
statement about `d < 0` — does not annihilate. -/
theorem smear_vac_eq_zero_of_fourierCoef_eq_zero (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW : W.IsWightmanCFT) {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d)
    (f : TestFn) (hf : ∀ n : ℤ, n ≤ 0 → fourierCoef f n = 0) :
    W.smear φ f W.vac = 0 := by
  apply (W.toWightmanStruct.actsRegularly_iff.mp hW.actsRegularly)
    (W.smear φ f W.vac) 0
  intro lam
  rw [W.compatApply_smear_vac_eq_zero hW.w3 hW.w4 hcov f hf lam]
  simp only [WightmanStruct.compatApply, map_zero]

/-- **The (W3) vacuum-annihilation bridge, covariance supplied by (W1).**  The form Issues
#7 and #9 consume: under `IsWightmanCFT` every field is covariant at its own conformal
dimension, so no covariance hypothesis need be carried. -/
theorem smear_vac_eq_zero_of_fourierCoef_eq_zero' (W : WightmanData Mob TestFn 𝓓 𝓕)
    (hW : W.IsWightmanCFT) (φ : 𝓕)
    (f : TestFn) (hf : ∀ n : ℤ, n ≤ 0 → fourierCoef f n = 0) :
    W.smear φ f W.vac = 0 := by
  exact W.smear_vac_eq_zero_of_fourierCoef_eq_zero hW (hW.w1.2 φ) f hf

end WightmanData

end MobiusCPT
