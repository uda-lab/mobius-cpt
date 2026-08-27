import MobiusCPT.Wightman.Mobius
import MobiusCPT.Wightman.StrongTopology

namespace MobiusCPT

open scoped Topology

/-!
# The Wightman covariance axiom

[T26], Definition 2.5: this module defines the two parts of Möbius covariance
in (W1), their immediate continuity consequences, and the bundled predicate
`IsWightmanCFT` for regularity together with (W1)--(W4). Locality (W2) lives on
`WightmanStruct` in `MobiusCPT.Wightman.Basic` because it needs only `smear`.
-/

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 2.5(3): the `𝓕`-strong topology of the underlying
`WightmanStruct`, exposed so downstream continuity statements can name it. -/
abbrev strongTop (W : WightmanData G TF 𝓓 𝓕) : TopologicalSpace 𝓓 :=
  W.toWightmanStruct.fStrongTopology

/-- [T26], Definition 2.5(3) and (W1): Möbius covariance.  The first
conjunct says that `U` takes values in the `𝓕`-strong continuous endomorphisms;
the second is (W1) proper. -/
def W1 (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  (∀ γ : G, Continuous[strongTop W, strongTop W] (W.U γ)) ∧
    (∀ φ : 𝓕, W.IsCovariant φ (W.dim φ))

/-- [T26], Definition 2.5(3): the representation `U` is strong-continuous
when `W1` holds. -/
theorem W1.continuous (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (γ : G) :
    Continuous[strongTop W, strongTop W] (W.U γ) := by
  exact h.1 γ

/-- [T26], Definition 2.5 (W1): every field is Möbius-covariant at its supplied
conformal dimension when `W1` holds. -/
theorem W1.covariant (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) :
    ∀ φ : 𝓕, W.IsCovariant φ (W.dim φ) := by
  exact h.2

/-- [T26], Definition 2.5(3) and (W1): `U γ` and `U γ⁻¹` are both
`𝓕`-strong continuous and cancel in both orders. This is [T26]'s
`U(γ) ∈ GL_𝓕(𝓓)`, with invertibility automatic for a group representation. -/
theorem w1_U_bicontinuous (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (γ : G) :
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
theorem w1_continuous_boost (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (t : ℝ) :
    Continuous[strongTop W, strongTop W] (W.boost t) := by
  change Continuous[strongTop W, strongTop W]
    (W.U (MobiusAction.boostElt (G := G) (TF := TF) t))
  exact W1.continuous W h _

/-- [T26], Definition 2.5: a Möbius-covariant Wightman CFT — the regular action of `𝓕`
together with (W1)–(W4). Definition 2.5(3)'s `𝓕`-strong continuity of `U` is the first
conjunct of `W1`, and Definition 2.5(4)'s `Ω ≠ 0` is already the `vac_ne_zero` field of
`WightmanData`, so neither is repeated here. -/
def IsWightmanCFT (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  W.toWightmanStruct.ActsRegularly ∧ W.W1 ∧ W.toWightmanStruct.W2 ∧ W.W3 ∧ W.W4

/-- [T26], Definition 2.5: unpacking the bundled Wightman CFT conjunction. -/
theorem isWightmanCFT_iff (W : WightmanData G TF 𝓓 𝓕) :
    W.IsWightmanCFT ↔
      (W.toWightmanStruct.ActsRegularly ∧ W.W1 ∧ W.toWightmanStruct.W2 ∧ W.W3 ∧ W.W4) :=
  Iff.rfl

/-- [T26], Definition 2.5: a Wightman CFT acts regularly. -/
theorem IsWightmanCFT.actsRegularly (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.toWightmanStruct.ActsRegularly :=
  h.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W1). -/
theorem IsWightmanCFT.w1 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W1 :=
  h.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W2). -/
theorem IsWightmanCFT.w2 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.toWightmanStruct.W2 :=
  h.2.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W3). -/
theorem IsWightmanCFT.w3 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W3 :=
  h.2.2.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W4). -/
theorem IsWightmanCFT.w4 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W4 :=
  h.2.2.2.2

end WightmanData

end MobiusCPT
