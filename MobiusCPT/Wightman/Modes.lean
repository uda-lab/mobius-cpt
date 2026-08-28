import MobiusCPT.Mobius.Covariance

/-!
# MobiusCPT.Wightman.Modes

[T26], proof of Lemma 3.7, and the Issue #2 source gate (part 3 §1), steps 1 and 2:
the conformal dimension of a smeared rotation eigenvector applied to the vacuum, and
the mode-by-mode application of the (W3) spectrum condition.

Everything here is stated over the abstract `[MobiusAction G TF]` interface, with the
explicit rotation form `β_d(r_θ)f = e^{-inθ}f` taken as a hypothesis (`IsRotWeight`).
The concrete instance `G = Mob`, `TF = TestFn`, where the hypothesis is discharged for
the monomials `z^n` by `MobiusCPT.Mob.beta_rot_monomial`, is in
`MobiusCPT.Wightman.W3Bridge`.

(W3) is applied here **only** to vectors carrying a genuine conformal dimension.  For a
general test function `f`, `φ(f)Ω` is not a rotation eigenvector and has no conformal
dimension; the passage from modes to such an `f` goes through `D*_𝓕` and regularity in
`MobiusCPT.Wightman.W3Bridge`, never through this file.
-/

namespace MobiusCPT

/-- [T26], §2.2 and the Issue #2 source gate, part 3 §1: the test function `f` is a
rotation eigenvector of weight `n` for the conformal action `β_d`, i.e.
`β_d(r_θ) f = e^{-inθ} f`.  On the concrete model the monomials `z^n` satisfy this for
every conformal weight `d` — the conformal factor `X_{r_θ}` is identically `1`, so `d`
drops out — which is why the conformal dimension computed below does not depend on `d`. -/
def IsRotWeight (G : Type*) [Group G] {TF : Type*} [AddCommGroup TF] [Module ℂ TF]
    [TopologicalSpace TF] [TestFunctions TF] [MobiusAction G TF]
    (d : ℕ) (f : TF) (n : ℤ) : Prop :=
  ∀ θ : ℝ,
    MobiusAction.beta (G := G) (TF := TF) d (MobiusAction.rot (G := G) (TF := TF) θ) f =
      Complex.exp (-(n : ℂ) * (θ : ℂ) * Complex.I) • f

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], proof of Lemma 3.7, step 1: for `φ` covariant of dimension `d` and `f` a
rotation eigenvector of weight `n`, the vector `φ(f)Ω` has conformal dimension `-n`.
The proof is rotation covariance together with the (W4) invariance `U(r_θ)Ω = Ω`. -/
theorem hasConformalDim_smear_vac (W : WightmanData G TF 𝓓 𝓕) (hW4 : W.W4)
    {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d) {f : TF} {n : ℤ}
    (hf : IsRotWeight G d f n) :
    W.HasConformalDim (W.smear φ f W.vac) (-n) := by
  intro θ
  rw [hcov.smear_comm, hW4.1, hf θ]
  simp only [map_smul, LinearMap.smul_apply]
  push_cast
  rfl

/-- [T26], proof of Lemma 3.7, step 2: (W3) applied to a single mode.  For a rotation
eigenvector of strictly positive weight `n`, the vector `φ(f)Ω` has conformal dimension
`-n < 0` and therefore vanishes.  (W3) is applied here to a genuine conformal-dimension
eigenvector; the product form is `weightedProduct_eq_zero_of_sum_pos`. -/
theorem smear_vac_eq_zero_of_rotWeight_pos (W : WightmanData G TF 𝓓 𝓕)
    (hW3 : W.W3) (hW4 : W.W4) {φ : 𝓕} {d : ℕ} (hcov : W.IsCovariant φ d)
    {f : TF} {n : ℤ} (hf : IsRotWeight G d f n) (hn : 0 < n) :
    W.smear φ f W.vac = 0 := by
  exact hW3 _ (-n) (by omega) (W.hasConformalDim_smear_vac hW4 hcov hf)

/-- [T26], proof of Lemma 3.7, step 1: the smeared product `φ₁(f₁)⋯φ_k(f_k)Ω` of a list of
fields paired with test functions, each test function carrying its rotation weight. -/
def weightedProduct (W : WightmanData G TF 𝓓 𝓕) (l : List (𝓕 × TF × ℤ)) : 𝓓 :=
  W.smearedProduct (l.map fun p => (p.1, p.2.1))

/-- [T26], proof of Lemma 3.7, step 1: the empty weighted product is the vacuum. -/
theorem weightedProduct_nil (W : WightmanData G TF 𝓓 𝓕) :
    W.weightedProduct ([] : List (𝓕 × TF × ℤ)) = W.vac := rfl

/-- [T26], proof of Lemma 3.7, step 1: a cons of a weighted product. -/
theorem weightedProduct_cons (W : WightmanData G TF 𝓓 𝓕) (p : 𝓕 × TF × ℤ)
    (l : List (𝓕 × TF × ℤ)) :
    W.weightedProduct (p :: l) = W.smear p.1 p.2.1 (W.weightedProduct l) := rfl

/-- [T26], proof of Lemma 3.7, step 1, and [CRTT25] §2: the product
`φ₁(f₁)⋯φ_k(f_k)Ω` of rotation eigenvectors of weights `n₁,…,n_k` has conformal dimension
`-(n₁+⋯+n_k)`. -/
theorem hasConformalDim_weightedProduct (W : WightmanData G TF 𝓓 𝓕) (hW4 : W.W4)
    (l : List (𝓕 × TF × ℤ))
    (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1))
    (hw : ∀ p ∈ l, IsRotWeight G (W.dim p.1) p.2.1 p.2.2) :
    W.HasConformalDim (W.weightedProduct l) (-(l.map fun p => p.2.2).sum) := by
  revert hcov hw
  induction l with
  | nil =>
      intro hcov hw θ
      rw [W.weightedProduct_nil, hW4.1]
      simp
  | cons p l ih =>
      intro hcov hw
      have hp : W.IsCovariant p.1 (W.dim p.1) := hcov p (by simp)
      have hcovTail : ∀ q ∈ l, W.IsCovariant q.1 (W.dim q.1) := by
        intro q hq
        exact hcov q (List.mem_cons_of_mem p hq)
      have hwHead : IsRotWeight G (W.dim p.1) p.2.1 p.2.2 := hw p (by simp)
      have hwTail : ∀ q ∈ l, IsRotWeight G (W.dim q.1) q.2.1 q.2.2 := by
        intro q hq
        exact hw q (List.mem_cons_of_mem p hq)
      intro θ
      rw [W.weightedProduct_cons, hp.smear_comm, ih hcovTail hwTail θ,
        hwHead θ]
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [← Complex.exp_add]
      congr 2
      push_cast [List.map_cons, List.sum_cons]
      ring

/-- [T26], proof of Lemma 3.7, step 2, for products: a product of rotation eigenvectors
whose weights sum to a strictly positive integer annihilates the vacuum. -/
theorem weightedProduct_eq_zero_of_sum_pos (W : WightmanData G TF 𝓓 𝓕)
    (hW3 : W.W3) (hW4 : W.W4) (l : List (𝓕 × TF × ℤ))
    (hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1))
    (hw : ∀ p ∈ l, IsRotWeight G (W.dim p.1) p.2.1 p.2.2)
    (hsum : 0 < (l.map fun p => p.2.2).sum) :
    W.weightedProduct l = 0 := by
  exact hW3 _ (-(l.map fun p => p.2.2).sum) (by omega)
    (W.hasConformalDim_weightedProduct hW4 l hcov hw)

end WightmanData

end MobiusCPT
