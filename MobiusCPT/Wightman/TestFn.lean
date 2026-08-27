import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Real.Lemmas

namespace MobiusCPT

/-- [T26], §2.2 and §3: the abstract interface required of `C^∞(S¹)`.
The field `starInv` is the Contract's `inv`, namely `f ↦ f ∘ z⁻¹`. -/
class TestFunctions (TF : Type*) [AddCommGroup TF] [Module ℂ TF]
    [TopologicalSpace TF] where
  /-- [T26], Lemma 3.9: the `C^N` seminorm. -/
  cnorm : ℕ → TF → NNReal
  /-- [T26], §3: inversion `f ↦ f ∘ z⁻¹`, named `starInv` to avoid `Inv.inv`. -/
  starInv : TF → TF
  /-- [T26], §3: upper semicircle support. -/
  SuppUpper : TF → Prop
  /-- [T26], §3: lower semicircle support. -/
  SuppLower : TF → Prop
  /-- [T26], §2.2: the topology is characterized by the `C^N` seminorms. -/
  tendsto_iff_cnorm : ∀ (u : ℕ → TF) (f : TF),
      Filter.Tendsto u Filter.atTop (nhds f) ↔
        ∀ N : ℕ, Filter.Tendsto (fun n => ((cnorm N (u n - f) : NNReal) : ℝ))
          Filter.atTop (nhds 0)
  /-- [T26], §3: inversion is additive. -/
  starInv_add : ∀ f g : TF, starInv (f + g) = starInv f + starInv g
  /-- [T26], §3: inversion is involutive. -/
  starInv_involutive : ∀ f : TF, starInv (starInv f) = f
  /-- [T26], §3: inversion exchanges upper and lower support. -/
  starInv_supp : ∀ f : TF, SuppUpper f ↔ SuppLower (starInv f)
  /-- [T26], Lemma 3.9: the `C^N` seminorm is invariant under inversion. -/
  cnorm_starInv : ∀ (N : ℕ) (f : TF), cnorm N (starInv f) = cnorm N f

end MobiusCPT
