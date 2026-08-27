import MobiusCPT.Wightman.Mobius
import MobiusCPT.Wightman.StrongTopology

namespace MobiusCPT

open scoped Topology

/-!
# The Wightman covariance axiom

[T26], Definition 2.5: this module defines the two parts of Möbius covariance
in (W1), together with the immediate continuity consequences.

Do not define `W2` here.  [T26], Definition 2.5, requires locality for
disjoint supports, namely `supp f ∩ supp g = ∅` implies that the corresponding
smeared fields commute.  The frozen test-function interface in
`MobiusCPT/Wightman/TestFn.lean` exposes only `SuppUpper` and `SuppLower`, not
a general support notion.  Restricting locality to that semicircle pair would
specialise the axiom and would break the cutoff argument in Tener's Lemma 3.7,
which needs a cutoff supported strictly inside the open `I_-`.  A general
support notion has been requested from Issue #3.

Do not define `IsWightmanCFT` here either.  [T26], Definition 2.5, makes it the
conjunction of regularity with (W1)--(W4), so it must wait for `W2`.
-/

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanCFT

private abbrev strongTop (W : WightmanCFT G TF 𝓓 𝓕) : TopologicalSpace 𝓓 :=
  W.toWightmanStruct.fStrongTopology

/-- [T26], Definition 2.5(3) and (W1): Möbius covariance.  The first
conjunct says that `U` takes values in the `𝓕`-strong continuous endomorphisms;
the second is (W1) proper. -/
def W1 (W : WightmanCFT G TF 𝓓 𝓕) : Prop :=
  (∀ γ : G, Continuous[strongTop W, strongTop W] (W.U γ)) ∧
    (∀ φ : 𝓕, W.IsCovariant φ (W.dim φ))

/-- [T26], Definition 2.5(3): the representation `U` is strong-continuous
when `W1` holds. -/
theorem W1.continuous (W : WightmanCFT G TF 𝓓 𝓕) (h : W.W1) (γ : G) :
    Continuous[strongTop W, strongTop W] (W.U γ) := by
  exact h.1 γ

/-- [T26], Definition 2.5 (W1): every field is Möbius-covariant at its supplied
conformal dimension when `W1` holds. -/
theorem W1.covariant (W : WightmanCFT G TF 𝓓 𝓕) (h : W.W1) :
    ∀ φ : 𝓕, W.IsCovariant φ (W.dim φ) := by
  exact h.2

/-- [T26], Definition 2.5(3) and (W1): under `W1`, each `U γ` is a strong
homeomorphism-like equivalence.  Its inverse is strongly continuous, and the
two inverse identities express the fact that `U(γ) ∈ GL_𝓕(𝓓)`, with
invertibility automatic for a group representation. -/
theorem w1_homeomorph_like (W : WightmanCFT G TF 𝓓 𝓕) (h : W.W1) (γ : G) :
    Continuous[strongTop W, strongTop W] (W.U γ) ∧
      Continuous[strongTop W, strongTop W] (W.U (γ⁻¹)) ∧
      (∀ Φ : 𝓓, W.U γ (W.U (γ⁻¹) Φ) = Φ) ∧
      (∀ Φ : 𝓓, W.U (γ⁻¹) (W.U γ Φ) = Φ) := by
  refine ⟨W1.continuous W h γ, W1.continuous W h (γ⁻¹), ?_, ?_⟩
  · intro Φ
    exact (W.U_inv_apply γ Φ).1
  · intro Φ
    exact (W.U_inv_apply γ Φ).2

/-- [T26], Definition 3.1 and Definition 2.5(3): every boost is strongly
continuous when `W1` holds. -/
theorem w1_continuous_boost (W : WightmanCFT G TF 𝓓 𝓕) (h : W.W1) (t : ℝ) :
    Continuous[strongTop W, strongTop W] (W.boost t) := by
  change Continuous[strongTop W, strongTop W]
    (W.U (MobiusAction.boostElt (G := G) (TF := TF) t))
  exact W1.continuous W h _

end WightmanCFT

end MobiusCPT
