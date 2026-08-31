import MobiusCPT.Mobius.RotationPi
import MobiusCPT.Mobius.Covariance
import MobiusCPT.Wightman.Vtilde

/-!
# Reflection of continued boosts by rotation through `pi`

Rotation through `pi` conjugates the real boost flow to the oppositely parametrized flow.
This module transports compatible functionals through that rotation, reflects continuation
witnesses across the origin in the complex boost parameter, and records the resulting domain
and value laws for `Ṽ`.
-/

namespace MobiusCPT

open Set

variable {𝓓 𝓕 : Type*} [AddCommGroup 𝓓] [Module ℂ 𝓓]

/-- Negation identifies the interiors of the strips with opposite parameters. -/
theorem neg_mem_interior_strip_iff (τ z : ℂ) :
    -z ∈ interior (strip (-τ)) ↔ z ∈ interior (strip τ) := by
  rcases le_total 0 τ.im with hτ | hτ
  · simp only [interior_strip, Set.mem_setOf_eq, Complex.neg_im,
      min_eq_left hτ, max_eq_right hτ,
      min_eq_right (neg_nonpos.mpr hτ), max_eq_left (neg_nonpos.mpr hτ),
      neg_lt_neg_iff]
    constructor <;> intro h <;> constructor <;> linarith
  · simp only [interior_strip, Set.mem_setOf_eq, Complex.neg_im,
      min_eq_right hτ, max_eq_left hτ,
      min_eq_left (neg_nonneg.mpr hτ), max_eq_right (neg_nonneg.mpr hτ),
      neg_lt_neg_iff]
    constructor <;> intro h <;> constructor <;> linarith

namespace WightmanData

/-- At the concrete `Mob` action, the abstract and concrete beta actions agree definitionally. -/
private theorem beta_rot_pi_eq_mob (d : ℕ) (f : TestFn) :
    MobiusAction.beta (G := Mob) (TF := TestFn) d (Mob.rot Real.pi) f =
      Mob.beta d (Mob.rot Real.pi) f := rfl

/-- Precomposition by `U(r_pi)` preserves compatibility. -/
noncomputable def compatRotPi {W : WightmanData Mob TestFn 𝓓 𝓕} (hW : W.IsWightmanCFT)
    (lam : W.toWightmanStruct.Compat) : W.toWightmanStruct.Compat := by
  refine ⟨lam.1.comp (W.U (Mob.rot Real.pi)), ?_⟩
  intro k φs Φ
  have hargs : Continuous (fun f : Fin k → TestFn => negTestFn ∘ f) := by
    apply continuous_pi
    intro i
    exact continuous_negTestFn.comp (continuous_apply i)
  have hmulti :=
    (lam.2 k φs (W.U (Mob.rot Real.pi) Φ)).comp hargs
  apply hmulti.congr
  intro f
  apply congrArg lam.1
  symm
  change W.U (Mob.rot Real.pi)
      (W.smearedProductOn (List.ofFn fun i => (φs i, f i)) Φ) =
    W.smearedProductOn
      (List.ofFn fun i => (φs i, negTestFn ((f : Fin k → TestFn) i)))
      (W.U (Mob.rot Real.pi) Φ)
  have hlist :
      (List.ofFn fun i => (φs i, f i)).map
          (fun p => (p.1, MobiusAction.beta (G := Mob) (TF := TestFn)
            (W.dim p.1) (Mob.rot Real.pi) p.2)) =
        List.ofFn fun i => (φs i, negTestFn ((f : Fin k → TestFn) i)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, beta_rot_pi_eq_mob,
      beta_rot_pi_eq_negTestFn]
  rw [WightmanData.U_smearedProductOn (Mob.rot Real.pi)
    (List.ofFn fun i => (φs i, f i))
    (fun p _ => W1.covariant W hW.w1 p.1) Φ, hlist]

/-- Rotation through `pi` intertwines a boost with the boost of opposite parameter. -/
theorem U_boost_rot_pi_comm {W : WightmanData Mob TestFn 𝓓 𝓕} (t : ℝ) (Φ : 𝓓) :
    W.U (Mob.rot Real.pi) (W.boost t Φ) =
      W.boost (-t) (W.U (Mob.rot Real.pi) Φ) := by
  have hU :
      W.U (Mob.rot Real.pi * Mob.boost t * (Mob.rot Real.pi)⁻¹) =
        W.U (Mob.boost (-t)) :=
    congrArg W.U (Mob.rot_pi_conj_boost t)
  have hpoint := congrArg
    (fun L : 𝓓 →ₗ[ℂ] 𝓓 => L (W.U (Mob.rot Real.pi) Φ)) hU
  rw [W.U_mul, LinearMap.comp_apply, W.U_mul, LinearMap.comp_apply,
    (W.U_inv_apply (Mob.rot Real.pi) Φ).2] at hpoint
  change W.U (Mob.rot Real.pi) (W.boost t Φ) =
    W.boost (-t) (W.U (Mob.rot Real.pi) Φ) at hpoint
  exact hpoint

/-- Applying the representation of rotation through `pi` twice is the identity. -/
private theorem U_rot_pi_rot_pi {W : WightmanData Mob TestFn 𝓓 𝓕} (Φ : 𝓓) :
    W.U (Mob.rot Real.pi) (W.U (Mob.rot Real.pi) Φ) = Φ := by
  calc
    W.U (Mob.rot Real.pi) (W.U (Mob.rot Real.pi) Φ) =
        W.U (Mob.rot Real.pi * Mob.rot Real.pi) Φ := by
      rw [W.U_mul, LinearMap.comp_apply]
    _ = W.U 1 Φ := by rw [Mob.rot_pi_sq]
    _ = Φ := by rw [W.U_one, LinearMap.id_apply]

/-- Reflecting the complex parameter and conjugating both boundary vectors by `U(r_pi)`
turns any boost-continuation witness into another one. -/
theorem isBoostContinuation_mirror {W : WightmanData Mob TestFn 𝓓 𝓕}
    (hW : W.IsWightmanCFT) {σ : ℂ} {X Y : 𝓓}
    {Gf : W.toWightmanStruct.Compat → ℂ → ℂ}
    (h : W.IsBoostContinuation σ X Y Gf) :
    W.IsBoostContinuation (-σ) (W.U (Mob.rot Real.pi) X)
      (W.U (Mob.rot Real.pi) Y)
      (fun lam z => Gf (compatRotPi hW lam) (-z)) := by
  intro lam
  have hsource := h (compatRotPi hW lam)
  have hcont : ContinuousOn (fun z : ℂ => -z) (strip (-σ)) :=
    continuous_neg.continuousOn
  have hmaps : Set.MapsTo (fun z : ℂ => -z) (strip (-σ)) (strip σ) := by
    intro z hz
    have hz' := (neg_mem_strip_iff (-σ) z).2 hz
    simpa only [neg_neg] using hz'
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => -z)
      (interior (strip (-σ))) :=
    (differentiable_id.neg).differentiableOn
  have hmaps' : Set.MapsTo (fun z : ℂ => -z)
      (interior (strip (-σ))) (interior (strip σ)) := by
    intro z hz
    have hz' := (neg_mem_interior_strip_iff (-σ) z).2 hz
    simpa only [neg_neg] using hz'
  refine ⟨hsource.1.comp' hcont hmaps,
    hsource.2.1.fun_comp hdiff hmaps', ?_, ?_⟩
  · intro t
    change Gf (compatRotPi hW lam) (-(t : ℂ)) =
      W.toWightmanStruct.compatApply lam
        (W.boost t (W.U (Mob.rot Real.pi) X))
    calc
      Gf (compatRotPi hW lam) (-(t : ℂ)) =
          Gf (compatRotPi hW lam) ((-t : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg]
      _ = W.toWightmanStruct.compatApply (compatRotPi hW lam)
          (W.boost (-t) X) := hsource.2.2.1 (-t)
      _ = W.toWightmanStruct.compatApply lam
          (W.U (Mob.rot Real.pi) (W.boost (-t) X)) := rfl
      _ = W.toWightmanStruct.compatApply lam
          (W.boost t (W.U (Mob.rot Real.pi) X)) := by
        rw [U_boost_rot_pi_comm, neg_neg]
  · intro t
    change Gf (compatRotPi hW lam) (-((-σ) + (t : ℂ))) =
      W.toWightmanStruct.compatApply lam
        (W.boost t (W.U (Mob.rot Real.pi) Y))
    calc
      Gf (compatRotPi hW lam) (-((-σ) + (t : ℂ))) =
          Gf (compatRotPi hW lam) (σ + ((-t : ℝ) : ℂ)) := by
        congr 1
        rw [Complex.ofReal_neg]
        ring
      _ = W.toWightmanStruct.compatApply (compatRotPi hW lam)
          (W.boost (-t) Y) := hsource.2.2.2 (-t)
      _ = W.toWightmanStruct.compatApply lam
          (W.U (Mob.rot Real.pi) (W.boost (-t) Y)) := rfl
      _ = W.toWightmanStruct.compatApply lam
          (W.boost t (W.U (Mob.rot Real.pi) Y)) := by
        rw [U_boost_rot_pi_comm, neg_neg]

/-- A continuation at `-τ` reflects to one at `τ`, including its uniquely determined value. -/
private theorem vtildeDom_and_map_mirror_to_pos
    {W : WightmanData Mob TestFn 𝓓 𝓕} (hW : W.IsWightmanCFT)
    {τ : ℂ} {Φ : 𝓓} (hdom : W.VtildeDom (-τ) Φ) :
    W.VtildeDom τ (W.U (Mob.rot Real.pi) Φ) ∧
      W.vtildeMap τ (W.U (Mob.rot Real.pi) Φ) =
        W.U (Mob.rot Real.pi) (W.vtildeMap (-τ) Φ) := by
  obtain ⟨Gf, hGf⟩ := W.vtildeVal_vtildeMap hW.actsRegularly hdom
  have hmirror := isBoostContinuation_mirror hW hGf
  have hmirror' :
      W.IsBoostContinuation τ (W.U (Mob.rot Real.pi) Φ)
        (W.U (Mob.rot Real.pi) (W.vtildeMap (-τ) Φ))
        (fun lam z => Gf (compatRotPi hW lam) (-z)) := by
    simpa only [neg_neg] using hmirror
  exact W.vtildeDom_and_vtildeMap_eq hW.actsRegularly hmirror'

/-- A continuation at `τ` of the rotated vector reflects back to one at `-τ`. -/
private theorem vtildeDom_and_map_mirror_to_neg
    {W : WightmanData Mob TestFn 𝓓 𝓕} (hW : W.IsWightmanCFT)
    {τ : ℂ} {Φ : 𝓓} (hdom : W.VtildeDom τ (W.U (Mob.rot Real.pi) Φ)) :
    W.VtildeDom (-τ) Φ ∧
      W.vtildeMap (-τ) Φ =
        W.U (Mob.rot Real.pi)
          (W.vtildeMap τ (W.U (Mob.rot Real.pi) Φ)) := by
  obtain ⟨Gf, hGf⟩ := W.vtildeVal_vtildeMap hW.actsRegularly hdom
  have hmirror := isBoostContinuation_mirror hW hGf
  have hmirror' :
      W.IsBoostContinuation (-τ) Φ
        (W.U (Mob.rot Real.pi)
          (W.vtildeMap τ (W.U (Mob.rot Real.pi) Φ)))
        (fun lam z => Gf (compatRotPi hW lam) (-z)) := by
    simpa only [U_rot_pi_rot_pi] using hmirror
  exact W.vtildeDom_and_vtildeMap_eq hW.actsRegularly hmirror'

/-- The domain of `Ṽ` is reflected by rotation through `pi`. -/
theorem vtildeDom_mirror_iff {W : WightmanData Mob TestFn 𝓓 𝓕}
    (hW : W.IsWightmanCFT) (τ : ℂ) (Φ : 𝓓) :
    W.VtildeDom (-τ) Φ ↔ W.VtildeDom τ (W.U (Mob.rot Real.pi) Φ) := by
  constructor
  · intro hdom
    exact (vtildeDom_and_map_mirror_to_pos hW hdom).1
  · intro hdom
    exact (vtildeDom_and_map_mirror_to_neg hW hdom).1

/-- The values of `Ṽ` obey the same reflected rotation law as its domain. -/
theorem vtildeMap_mirror {W : WightmanData Mob TestFn 𝓓 𝓕}
    (hW : W.IsWightmanCFT) (τ : ℂ) (Φ : 𝓓)
    (h : W.VtildeDom (-τ) Φ) :
    W.vtildeMap (-τ) Φ =
      W.U (Mob.rot Real.pi)
        (W.vtildeMap τ (W.U (Mob.rot Real.pi) Φ)) := by
  exact (vtildeDom_and_map_mirror_to_neg hW
    (vtildeDom_and_map_mirror_to_pos hW h).1).2

end WightmanData

end MobiusCPT
