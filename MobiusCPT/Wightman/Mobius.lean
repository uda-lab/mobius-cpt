import MobiusCPT.Wightman.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MobiusCPT

/-!
# Möbius action and Wightman CFT interface

This module records the Möbius-action and representation interfaces consumed by
the later PCT formalisation.  It deliberately does not define `W1`, `W2`, or
`IsWightmanCFT`.  In [T26], Definition 2.5, `W1` also requires the
`𝓕`-strong continuity of the representation, whose topology is not yet
available.  The full `W2` locality axiom requires disjoint supports, whereas
the current test-function interface exposes only the two semicircle predicates.
Consequently, defining either axiom here would weaken its statement, and
`IsWightmanCFT`, which combines them, must wait as well.
-/

/-!
[T26], Definition 2.4: `MobiusAction` is deliberately an INTERFACE, not a
construction.  Issue #5 owns the concrete `Möb = PSU(1,1)`, the boost `v_t`, the
rotations `r_θ`, the conformal factor `X_γ`, and the action
`β_d(γ)f = (X_γ^{d−1} · f) ∘ γ⁻¹`, and will supply the instance.  Consequently,
the laws here are only the group/action laws; a group with no circle geometry can
satisfy them.  That is sound: every theorem stated over an arbitrary instance
applies in particular to the real one.  It means NO result in this branch is by
itself a statement about the Möbius group.  The capstone must be stated over
Issue #5's instance.
-/
/-- [T26], §2.2 and Definition 2.4: the Möbius-group data #4 consumes and
Issue #5 supplies. -/
class MobiusAction (G : Type*) [Group G] (TF : Type*) [AddCommGroup TF]
    [Module ℂ TF] [TopologicalSpace TF] [TestFunctions TF] where
  /-- [T26], §2.2: the rotation subgroup `r_θ`, with `r_θ · z = e^{iθ} z`. -/
  rot : ℝ → G
  /-- [T26], §2.2: the boost subgroup `v_t`. -/
  boostElt : ℝ → G
  /-- [T26], Definition 2.4: the conformal action `β_d(γ)` on test functions. -/
  beta : ℕ → G → TF →ₗ[ℂ] TF
  /-- [T26], §2.2: the rotation subgroup at zero is the identity. -/
  rot_zero : rot 0 = 1
  /-- [T26], §2.2: rotations form a one-parameter subgroup. -/
  rot_add : ∀ θ ψ : ℝ, rot (θ + ψ) = rot θ * rot ψ
  /-- [T26], §2.2: the boost subgroup at zero is the identity. -/
  boostElt_zero : boostElt 0 = 1
  /-- [T26], §2.2 and Definition 3.1: boosts form a one-parameter subgroup. -/
  boostElt_add : ∀ s t : ℝ, boostElt (s + t) = boostElt s * boostElt t
  /-- [T26], Definition 2.4: the conformal action of the group identity. -/
  beta_one : ∀ d : ℕ, beta d (1 : G) = LinearMap.id
  /-- [T26], Definition 2.4: the conformal action respects multiplication. -/
  beta_mul : ∀ (d : ℕ) (γ δ : G),
    beta d (γ * δ) = (beta d γ).comp (beta d δ)

export MobiusAction (rot boostElt beta)

/-- The data of [T26], Definition 2.5: the quadruple `(𝓓, 𝓕, U, Ω)`, with the
representation laws and `Ω ≠ 0`. This carries NO Wightman axiom: the available axioms
are the separate predicates `W1`, `W3`, and `W4`, while the bundled `IsWightmanCFT`
is not yet available. -/
structure WightmanData (G : Type*) [Group G] (TF : Type*) [AddCommGroup TF]
    [Module ℂ TF] [TopologicalSpace TF] [TestFunctions TF]
    [MobiusAction G TF] (𝓓 : Type*) [AddCommGroup 𝓓] [Module ℂ 𝓓] (𝓕 : Type*)
    extends WightmanStruct TF 𝓓 𝓕 where
  /-- [T26], Definition 2.5(4): the vacuum is non-zero. -/
  vac_ne_zero : toWightmanStruct.vac ≠ 0
  /-- [T26], Definition 2.5: the Möbius representation `U(γ) ∈ End(𝓓)`. -/
  U : G → 𝓓 →ₗ[ℂ] 𝓓
  /-- [T26], Definition 2.5: the representation at the group identity. -/
  U_one : U 1 = LinearMap.id
  /-- [T26], Definition 2.5: the representation respects multiplication. -/
  U_mul : ∀ γ δ : G, U (γ * δ) = (U γ).comp (U δ)

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 2.5: a representation sends each group element to an
invertible linear map, expressed in both inverse-composition directions. -/
theorem U_inv_apply (W : WightmanData G TF 𝓓 𝓕) (γ : G) (Φ : 𝓓) :
    W.U γ (W.U γ⁻¹ Φ) = Φ ∧ W.U γ⁻¹ (W.U γ Φ) = Φ := by
  constructor
  · have h := congrArg (fun L : 𝓓 →ₗ[ℂ] 𝓓 => L Φ) (W.U_mul γ γ⁻¹).symm
    simpa [W.U_one] using h
  · have h := congrArg (fun L : 𝓓 →ₗ[ℂ] 𝓓 => L Φ) (W.U_mul γ⁻¹ γ).symm
    simpa [W.U_one] using h

/-- [T26], §2 and Definition 3.1: `V_t = U(v_t)`. -/
def boost (W : WightmanData G TF 𝓓 𝓕) (t : ℝ) : 𝓓 →ₗ[ℂ] 𝓓 :=
  W.U (MobiusAction.boostElt (G := G) (TF := TF) t)

/-- [T26], §2 and Definition 3.1: the boost action is linear on the domain. -/
theorem boost_linear (W : WightmanData G TF 𝓓 𝓕) :
    ∀ (t : ℝ) (Φ Ψ : 𝓓),
      (W.boost t (Φ + Ψ) = W.boost t Φ + W.boost t Ψ) ∧
        (∀ c : ℂ, W.boost t (c • Φ) = c • W.boost t Φ) := by
  intro t Φ Ψ
  exact ⟨(W.boost t).map_add Φ Ψ, fun c => (W.boost t).map_smul c Φ⟩

/-- [T26], Definition 3.1: the boost at zero is the identity. -/
theorem boost_zero (W : WightmanData G TF 𝓓 𝓕) :
    ∀ Φ : 𝓓, W.boost 0 Φ = Φ := by
  intro Φ
  simp [boost, MobiusAction.boostElt_zero, W.U_one]

/-- [T26], §3: the boosts form a one-parameter group. -/
theorem boost_add (W : WightmanData G TF 𝓓 𝓕) :
    ∀ (s t : ℝ) (Φ : 𝓓),
      W.boost s (W.boost t Φ) = W.boost (s + t) Φ := by
  intro s t Φ
  change W.U (MobiusAction.boostElt (G := G) (TF := TF) s)
      (W.U (MobiusAction.boostElt (G := G) (TF := TF) t) Φ) =
    W.U (MobiusAction.boostElt (G := G) (TF := TF) (s + t)) Φ
  calc
    W.U (MobiusAction.boostElt (G := G) (TF := TF) s)
          (W.U (MobiusAction.boostElt (G := G) (TF := TF) t) Φ) =
        W.U (MobiusAction.boostElt (G := G) (TF := TF) s *
          MobiusAction.boostElt (G := G) (TF := TF) t) Φ := by
            rw [W.U_mul, LinearMap.comp_apply]
    _ = W.U (MobiusAction.boostElt (G := G) (TF := TF) (s + t)) Φ := by
      rw [MobiusAction.boostElt_add]

/-- [T26], Definition 2.4: `φ` is Möbius-covariant with conformal dimension
`d`, i.e. `U(γ) φ(f) U(γ)⁻¹ = φ(β_d(γ) f)`. -/
def IsCovariant (W : WightmanData G TF 𝓓 𝓕) (φ : 𝓕) (d : ℕ) : Prop :=
  ∀ (γ : G) (f : TF) (Φ : 𝓓),
    W.U γ (W.smear φ f (W.U γ⁻¹ Φ)) =
      W.smear φ (MobiusAction.beta (G := G) (TF := TF) d γ f) Φ

/-- [T26], Definition 2.4: `Φ ∈ 𝓓` has conformal dimension `d`, with vector
dimensions ranging over `ℤ`. -/
def HasConformalDim (W : WightmanData G TF 𝓓 𝓕) (Φ : 𝓓) (d : ℤ) : Prop :=
  ∀ θ : ℝ, W.U (MobiusAction.rot (G := G) (TF := TF) θ) Φ =
    Complex.exp ((d : ℂ) * (θ : ℂ) * Complex.I) • Φ

/-- [T26], Definition 2.4: the zero vector has every conformal dimension. -/
theorem hasConformalDim_zero (W : WightmanData G TF 𝓓 𝓕) (d : ℤ) :
    W.HasConformalDim (0 : 𝓓) d := by
  intro θ
  simp

/-- [T26], Definition 2.4: vectors of the same conformal dimension are
closed under addition. -/
theorem hasConformalDim_add (W : WightmanData G TF 𝓓 𝓕)
    (Φ Ψ : 𝓓) (d : ℤ) :
    W.HasConformalDim Φ d → W.HasConformalDim Ψ d →
      W.HasConformalDim (Φ + Ψ) d := by
  intro hΦ hΨ θ
  simp only [map_add, hΦ θ, hΨ θ, smul_add]

/-- [T26], Definition 2.4: conformal dimension is preserved by complex scalar
multiplication. -/
theorem hasConformalDim_smul (W : WightmanData G TF 𝓓 𝓕)
    (c : ℂ) (Φ : 𝓓) (d : ℤ) :
    W.HasConformalDim Φ d → W.HasConformalDim (c • Φ) d := by
  intro hΦ θ
  calc
    W.U (MobiusAction.rot (G := G) (TF := TF) θ) (c • Φ) =
        c • W.U (MobiusAction.rot (G := G) (TF := TF) θ) Φ :=
      (W.U (MobiusAction.rot (G := G) (TF := TF) θ)).map_smul c Φ
    _ = c • (Complex.exp ((d : ℂ) * (θ : ℂ) * Complex.I) • Φ) := by
      rw [hΦ θ]
    _ = Complex.exp ((d : ℂ) * (θ : ℂ) * Complex.I) • (c • Φ) := by
      rw [smul_smul, smul_smul, mul_comm]

/-- [T26], Definition 2.5 (W3), the spectrum condition: a vector of negative
conformal dimension vanishes. -/
def W3 (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  ∀ (Φ : 𝓓) (d : ℤ), d < 0 → W.HasConformalDim Φ d → Φ = 0

/-- [T26], Definition 2.5 (W4), the vacuum axiom: `Ω` is Möbius-invariant
and the smeared products applied to `Ω` span `𝓓`. -/
def W4 (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  (∀ γ : G, W.U γ W.vac = W.vac) ∧
    (⊤ : Submodule ℂ 𝓓) = Submodule.span ℂ
      { Φ | ∃ l : List (𝓕 × TF), Φ = W.smearedProduct l }

/-- [T26], Definition 2.5 (W4): Möbius invariance of the vacuum implies
invariance under every real boost. -/
theorem w4_vacuum_invariant (W : WightmanData G TF 𝓓 𝓕) :
    W.W4 → ∀ t : ℝ, W.boost t W.vac = W.vac := by
  intro h t
  change W.U (MobiusAction.boostElt (G := G) (TF := TF) t) W.vac = W.vac
  exact h.1 _

/-- [T26], Definition 2.5 (W4): Möbius invariance of the vacuum implies
invariance under every rotation. -/
theorem w4_rotation_invariant (W : WightmanData G TF 𝓓 𝓕) :
    W.W4 → ∀ θ : ℝ,
      W.U (MobiusAction.rot (G := G) (TF := TF) θ) W.vac = W.vac := by
  intro h θ
  exact h.1 _

end WightmanData

end MobiusCPT
