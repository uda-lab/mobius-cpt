import MobiusCPT.Wightman.Thm310Upper
import MobiusCPT.Wightman.VtildeMirror
import MobiusCPT.Mobius.RotationPi
import MobiusCPT.Mobius.Covariance

/-!
# [T26], Theorem 3.10

The lower-half-circle statement is transported from the upper-half-circle statement by
rotation through `pi`.  Linearity of the continuation domain then extends the two product
statements to the corresponding localized subspaces.
-/

namespace MobiusCPT

noncomputable section

namespace WightmanData

variable {𝓓 𝓕 : Type} [AddCommGroup 𝓓] [Module ℂ 𝓓]
variable {W : WightmanData Mob TestFn 𝓓 𝓕}

/-- At the concrete action, rotation by `pi` sends every test function to `negTestFn`. -/
private theorem beta_rotation_pi_eq_negTestFn (d : ℕ) (f : TestFn) :
    MobiusAction.beta (G := Mob) (TF := TestFn) d
        (MobiusAction.rot (G := Mob) (TF := TestFn) Real.pi) f =
      negTestFn f := by
  change Mob.beta d (Mob.rot Real.pi) f = negTestFn f
  exact beta_rot_pi_eq_negTestFn d f

/-- Rotation by `pi` acts pointwise by `negTestFn` on a smeared product. -/
private theorem rotation_smearedProduct_negTestFn
    (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn)) :
    W.U (Mob.rot Real.pi) (W.smearedProduct l) =
      W.smearedProduct (l.map fun p => (p.1, negTestFn p.2)) := by
  have hcov : ∀ p ∈ l, W.IsCovariant p.1 (W.dim p.1) := by
    intro p _
    exact W1.covariant W hW.w1 p.1
  have hlist :
      l.map (fun p =>
          (p.1, MobiusAction.beta (G := Mob) (TF := TestFn) (W.dim p.1)
            (MobiusAction.rot (G := Mob) (TF := TestFn) Real.pi) p.2)) =
        l.map (fun p => (p.1, negTestFn p.2)) := by
    apply List.map_congr_left
    intro p _
    simp only [beta_rotation_pi_eq_negTestFn]
  calc
    W.U (Mob.rot Real.pi) (W.smearedProduct l) =
        W.U (MobiusAction.rot (G := Mob) (TF := TestFn) Real.pi)
          (W.smearedProduct l) := by
      rfl
    _ = W.smearedProduct
        (l.map fun p =>
          (p.1, MobiusAction.beta (G := Mob) (TF := TestFn) (W.dim p.1)
            (MobiusAction.rot (G := Mob) (TF := TestFn) Real.pi) p.2)) :=
      WightmanData.rotation_smearedProduct hW.w4 Real.pi l hcov
    _ = W.smearedProduct (l.map fun p => (p.1, negTestFn p.2)) := by
      rw [hlist]

/-- The two rotations surrounding inversion cancel. -/
private theorem negTestFn_inv_negTestFn (f : TestFn) :
    negTestFn (inv (negTestFn f)) = inv f := by
  have h := inv_negTestFn (negTestFn f)
  rw [negTestFn_negTestFn] at h
  exact h.symm

/-- Reverse, invert, and rotate after first rotating a list gives reverse and inversion. -/
private theorem rotate_reverse_inv_neg_list (l : List (𝓕 × TestFn)) :
    (((l.map fun p => (p.1, negTestFn p.2)).reverse.map
          (fun p => (p.1, inv p.2))).map
        (fun p => (p.1, negTestFn p.2))) =
      l.reverse.map (fun p => (p.1, inv p.2)) := by
  have hreverse :
      (l.map fun p => (p.1, negTestFn p.2)).reverse =
        l.reverse.map (fun p => (p.1, negTestFn p.2)) := by
    rw [List.map_reverse]
  rw [hreverse, List.map_map, List.map_map]
  apply List.map_congr_left
  intro p _
  cases p with
  | mk φ f =>
      simp only [Function.comp_apply, Prod.fst, Prod.snd]
      rw [negTestFn_inv_negTestFn]

/-- [T26], Theorem 3.10(iii), at the data level. -/
theorem thm_3_10_iii_core (hW : W.IsWightmanCFT) (l : List (𝓕 × TestFn))
    (hl : ∀ p ∈ l, SuppLower p.2) :
    W.VtildeDom (-(Complex.I * Real.pi)) (W.smearedProduct l) ∧
      W.vtildeMap (-(Complex.I * Real.pi)) (W.smearedProduct l) =
        (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) •
          W.smearedProduct (l.reverse.map (fun p => (p.1, inv p.2))) := by
  let l' : List (𝓕 × TestFn) :=
    l.map (fun p => (p.1, negTestFn p.2))
  have hl' : ∀ q ∈ l', SuppUpper q.2 := by
    intro q hq
    change q ∈ l.map (fun p => (p.1, negTestFn p.2)) at hq
    simp only [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact (suppLower_iff_suppUpper_negTestFn p.2).mp (hl p hp)
  have hrot_l :
      W.U (Mob.rot Real.pi) (W.smearedProduct l) = W.smearedProduct l' := by
    simpa only [l'] using rotation_smearedProduct_negTestFn (W := W) hW l
  have hii := thm_3_10_ii_core hW l' hl'
  have hdim :
      (l'.map (fun p => W.dim p.1)).sum =
        (l.map (fun p => W.dim p.1)).sum := by
    dsimp [l']
    rw [List.map_map]
    rfl
  have hlist :
      ((l'.reverse.map (fun p => (p.1, inv p.2))).map
          (fun p => (p.1, negTestFn p.2))) =
        l.reverse.map (fun p => (p.1, inv p.2)) := by
    dsimp [l']
    exact rotate_reverse_inv_neg_list l
  have hdom_neg :
      W.VtildeDom (-(Complex.I * Real.pi)) (W.smearedProduct l) := by
    apply (vtildeDom_mirror_iff hW (Complex.I * Real.pi)
      (W.smearedProduct l)).mpr
    rw [hrot_l]
    exact hii.1
  refine ⟨hdom_neg, ?_⟩
  calc
    W.vtildeMap (-(Complex.I * Real.pi)) (W.smearedProduct l) =
        W.U (Mob.rot Real.pi)
          (W.vtildeMap (Complex.I * Real.pi)
            (W.U (Mob.rot Real.pi) (W.smearedProduct l))) :=
      vtildeMap_mirror hW (Complex.I * Real.pi) (W.smearedProduct l) hdom_neg
    _ = W.U (Mob.rot Real.pi)
        (W.vtildeMap (Complex.I * Real.pi) (W.smearedProduct l')) := by
      rw [hrot_l]
    _ = W.U (Mob.rot Real.pi) (upperLimitVector (W := W) l') := by
      rw [hii.2]
    _ = W.U (Mob.rot Real.pi)
        (((-1 : ℂ) ^ ((l'.map (fun p => W.dim p.1)).sum)) •
          W.smearedProduct
            (l'.reverse.map (fun p => (p.1, inv p.2)))) := by
      rfl
    _ = ((-1 : ℂ) ^ ((l'.map (fun p => W.dim p.1)).sum)) •
        W.U (Mob.rot Real.pi)
          (W.smearedProduct
            (l'.reverse.map (fun p => (p.1, inv p.2)))) :=
      (W.U (Mob.rot Real.pi)).map_smul
        ((-1 : ℂ) ^ ((l'.map (fun p => W.dim p.1)).sum)) _
    _ = ((-1 : ℂ) ^ ((l'.map (fun p => W.dim p.1)).sum)) •
        W.smearedProduct
          ((l'.reverse.map (fun p => (p.1, inv p.2))).map
            (fun p => (p.1, negTestFn p.2))) := by
      rw [rotation_smearedProduct_negTestFn (W := W) hW]
    _ = ((-1 : ℂ) ^ ((l'.map (fun p => W.dim p.1)).sum)) •
        W.smearedProduct
          (l.reverse.map (fun p => (p.1, inv p.2))) := by
      rw [hlist]
    _ = (-1 : ℂ) ^ ((l.map (fun p => W.dim p.1)).sum) •
        W.smearedProduct
          (l.reverse.map (fun p => (p.1, inv p.2))) := by
      rw [hdim]

/-- [T26], Theorem 3.10(i), at the data level. -/
theorem thm_3_10_i_core (hW : W.IsWightmanCFT) :
    (∀ Φ : 𝓓, W.toWightmanStruct.MemPUpperOmega Φ →
      W.VtildeDom (Complex.I * Real.pi) Φ) ∧
      (∀ Φ : 𝓓, W.toWightmanStruct.MemPLowerOmega Φ →
        W.VtildeDom (-(Complex.I * Real.pi)) Φ) := by
  constructor
  · intro Φ hΦ
    obtain ⟨n, c, ls, hls, rfl⟩ :=
      (WightmanStruct.memPUpperOmega_iff W.toWightmanStruct Φ).mp hΦ
    apply (mem_vtildeDomain W (Complex.I * Real.pi) _).mp
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ (c i)
        ((mem_vtildeDomain W (Complex.I * Real.pi) _).mpr
          (thm_3_10_ii_core hW (ls i) (hls i)).1))
  · intro Φ hΦ
    obtain ⟨n, c, ls, hls, rfl⟩ :=
      (WightmanStruct.memPLowerOmega_iff W.toWightmanStruct Φ).mp hΦ
    apply (mem_vtildeDomain W (-(Complex.I * Real.pi)) _).mp
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ (c i)
        ((mem_vtildeDomain W (-(Complex.I * Real.pi)) _).mpr
          (thm_3_10_iii_core hW (ls i) (hls i)).1))

end WightmanData

namespace WightmanBundle

theorem thm_3_10_i (W : WightmanBundle) (h : W.data.IsWightmanCFT) :
    (∀ Φ : W.𝓓,
      W.data.toWightmanStruct.MemPUpperOmega Φ → W.data.VtildeDom (Complex.I * Real.pi) Φ) ∧
      (∀ Φ : W.𝓓,
        W.data.toWightmanStruct.MemPLowerOmega Φ →
          W.data.VtildeDom (-(Complex.I * Real.pi)) Φ) :=
  WightmanData.thm_3_10_i_core h

theorem thm_3_10_ii (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (l : List (W.𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppUpper p.2) :
    W.data.VtildeDom (Complex.I * Real.pi) (W.data.toWightmanStruct.smearedProduct l) ∧
      W.data.vtildeMap (Complex.I * Real.pi) (W.data.toWightmanStruct.smearedProduct l) =
        (-1 : ℂ) ^ ((l.map (fun p => W.data.dim p.1)).sum) •
          W.data.toWightmanStruct.smearedProduct
            (l.reverse.map (fun p => (p.1, inv p.2))) :=
  WightmanData.thm_3_10_ii_core h l hl

theorem thm_3_10_iii (W : WightmanBundle) (h : W.data.IsWightmanCFT)
    (l : List (W.𝓕 × TestFn)) (hl : ∀ p ∈ l, SuppLower p.2) :
    W.data.VtildeDom (-(Complex.I * Real.pi)) (W.data.toWightmanStruct.smearedProduct l) ∧
      W.data.vtildeMap (-(Complex.I * Real.pi)) (W.data.toWightmanStruct.smearedProduct l) =
        (-1 : ℂ) ^ ((l.map (fun p => W.data.dim p.1)).sum) •
          W.data.toWightmanStruct.smearedProduct
            (l.reverse.map (fun p => (p.1, inv p.2))) :=
  WightmanData.thm_3_10_iii_core h l hl

end WightmanBundle

end

end MobiusCPT
