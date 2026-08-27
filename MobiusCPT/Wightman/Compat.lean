import MobiusCPT.Wightman.Mobius
import Mathlib.Topology.Algebra.Monoid

namespace MobiusCPT

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanStruct

/-- [T26], §2: appending operator lists composes their actions on a domain vector. -/
theorem smearedProductOn_append (W : WightmanStruct TF 𝓓 𝓕)
    (L l : List (𝓕 × TF)) (Φ : 𝓓) :
    W.smearedProductOn (L ++ l) Φ =
      W.smearedProductOn L (W.smearedProductOn l Φ) := by
  simp [smearedProductOn, List.foldr_append]

/-- [T26], §2: appending operator lists composes their vacuum products. -/
theorem smearedProduct_append (W : WightmanStruct TF 𝓓 𝓕)
    (L l : List (𝓕 × TF)) :
    W.smearedProduct (L ++ l) =
      W.smearedProductOn L (W.smearedProduct l) := by
  simpa [smearedProduct] using
    (smearedProductOn_append W L l W.vac)

/-- [T26], §3: the form of Definition 2.4 that [T26] §3 recalls, with `Ω`
in the last slot. -/
def IsCompatibleVac (W : WightmanStruct TF 𝓓 𝓕) (lam : 𝓓 →ₗ[ℂ] ℂ) : Prop :=
  ∀ (k : ℕ) (φs : Fin k → 𝓕),
    Continuous fun f : Fin k → TF => lam (W.multiSmear φs W.vac f)

/-- [T26], Definition 2.4 and §3: general-vector compatibility implies its
vacuum-slot form. -/
theorem isCompatibleVac_of_isCompatible (W : WightmanStruct TF 𝓓 𝓕)
    (lam : 𝓓 →ₗ[ℂ] ℂ) :
    W.IsCompatible lam → W.IsCompatibleVac lam := by
  intro h k φs
  exact h k φs W.vac

/-- [T26], Definition 2.4 and §3: the vacuum-slot form implies compatibility
for a Wightman CFT satisfying the spanning clause of (W4). -/
theorem isCompatible_of_isCompatibleVac (W : WightmanCFT G TF 𝓓 𝓕)
    (h4 : W.W4) (lam : 𝓓 →ₗ[ℂ] ℂ)
    (h : IsCompatibleVac W.toWightmanStruct lam) :
    IsCompatible W.toWightmanStruct lam := by
  intro k φs Φ
  have hΦspan :
      Φ ∈ Submodule.span ℂ
        { Ψ : 𝓓 | ∃ l : List (𝓕 × TF),
          Ψ = W.toWightmanStruct.smearedProduct l } := by
    rw [← h4.2]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_set'.mp hΦspan) with ⟨n, c, g, hg⟩
  let ls : Fin n → List (𝓕 × TF) :=
    fun i => (g i).property.choose
  have hls : ∀ i, (g i : 𝓓) =
      W.toWightmanStruct.smearedProduct (ls i) := by
    intro i
    dsimp [ls]
    exact (g i).property.choose_spec
  have hmulti_sum (f : Fin k → TF) :
      W.toWightmanStruct.multiSmear φs
          (∑ i, c i • (g i : 𝓓)) f =
        ∑ i, c i • W.toWightmanStruct.multiSmear φs (g i : 𝓓) f := by
    let S : 𝓓 →ₗ[ℂ] 𝓓 :=
      { toFun := W.toWightmanStruct.smearedProductOn
          (List.ofFn fun i : Fin k => (φs i, f i))
        map_add' := fun x y =>
          (W.toWightmanStruct.smearedProductOn_linear _ x y).1
        map_smul' := fun a x =>
          (W.toWightmanStruct.smearedProductOn_linear _ x x).2 a }
    change S (∑ i, c i • (g i : 𝓓)) =
      ∑ i, c i • S (g i : 𝓓)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact S.map_smul (c i) (g i : 𝓓)
  have hsum_eq :
      (fun f : Fin k → TF =>
        lam (W.toWightmanStruct.multiSmear φs Φ f)) =
      (fun f : Fin k → TF =>
        ∑ i, c i *
          lam (W.toWightmanStruct.multiSmear φs (g i : 𝓓) f)) := by
    funext f
    rw [← hg, hmulti_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hterm : ∀ i : Fin n, Continuous (fun f : Fin k → TF =>
      c i * lam (W.toWightmanStruct.multiSmear φs (g i : 𝓓) f)) := by
    intro i
    let l : List (𝓕 × TF) := ls i
    let m : ℕ := l.length
    let cs : Fin m → TF := fun j => (l.get j).2
    let ψs : Fin (k + m) → 𝓕 :=
      Fin.append φs (fun j => (l.get j).1)
    have hls' : (g i : 𝓓) =
        W.toWightmanStruct.smearedProduct l := by
      simpa [l] using hls i
    have happend : Continuous
        (fun f : Fin k → TF => Fin.append f cs) := by
      apply continuous_pi
      intro q
      induction q using Fin.addCases with
      | left j =>
          simpa [Fin.append] using (continuous_apply j)
      | right j =>
          simpa [Fin.append] using
            (continuous_const : Continuous (fun _ : Fin k → TF => cs j))
    have hmulti (f : Fin k → TF) :
        W.toWightmanStruct.multiSmear φs
            (W.toWightmanStruct.smearedProduct l) f =
          W.toWightmanStruct.multiSmear ψs W.toWightmanStruct.vac
            (Fin.append f cs) := by
      have hconcat :
          (fun q : Fin (k + m) => (ψs q, Fin.append f cs q)) =
            Fin.append (fun j : Fin k => (φs j, f j))
              (fun j : Fin m => l.get j) := by
        funext q
        induction q using Fin.addCases with
        | left j =>
            simp [ψs, cs, Fin.append]
        | right j =>
            simp [ψs, cs, Fin.append]
      have hlist :
          List.ofFn (fun q : Fin (k + m) =>
            (ψs q, Fin.append f cs q)) =
            List.ofFn (fun j : Fin k => (φs j, f j)) ++ l := by
        calc
          List.ofFn (fun q : Fin (k + m) =>
              (ψs q, Fin.append f cs q)) =
              List.ofFn (Fin.append (fun j : Fin k => (φs j, f j))
                (fun j : Fin m => l.get j)) := by rw [hconcat]
          _ = List.ofFn (fun j : Fin k => (φs j, f j)) ++
              List.ofFn (fun j : Fin m => l.get j) :=
            List.ofFn_fin_append _ _
          _ = List.ofFn (fun j : Fin k => (φs j, f j)) ++ l := by
            rw [List.ofFn_get]
      change W.toWightmanStruct.smearedProductOn
          (List.ofFn fun j : Fin k => (φs j, f j))
          (W.toWightmanStruct.smearedProduct l) =
        W.toWightmanStruct.smearedProductOn
          (List.ofFn fun q : Fin (k + m) =>
            (ψs q, Fin.append f cs q)) W.toWightmanStruct.vac
      rw [← W.toWightmanStruct.smearedProduct_append
        (List.ofFn fun j : Fin k => (φs j, f j)) l, hlist]
      rfl
    have hcont : Continuous (fun f : Fin k → TF =>
        lam (W.toWightmanStruct.multiSmear φs
          (W.toWightmanStruct.smearedProduct l) f)) := by
      have hfun :
          (fun f : Fin k → TF =>
            lam (W.toWightmanStruct.multiSmear φs
              (W.toWightmanStruct.smearedProduct l) f)) =
            (fun f : Fin k → TF =>
              lam (W.toWightmanStruct.multiSmear ψs
                W.toWightmanStruct.vac (Fin.append f cs))) := by
        funext f
        rw [hmulti f]
      rw [hfun]
      apply ((h (k + m) ψs).comp happend).congr
      intro f
      rfl
    rw [hls']
    apply (continuous_const.mul hcont).congr
    intro f
    rfl
  rw [hsum_eq]
  exact continuous_finsetSum _ (fun i _ => hterm i)

/-- [T26], Definition 2.4 and §3: under (W4), the two presentations of
the compatible-functional space `D*_𝓕` are equivalent. -/
theorem isCompatible_iff_isCompatibleVac (W : WightmanCFT G TF 𝓓 𝓕)
    (h4 : W.W4) (lam : 𝓓 →ₗ[ℂ] ℂ) :
    IsCompatible W.toWightmanStruct lam ↔
      IsCompatibleVac W.toWightmanStruct lam := by
  constructor
  · exact isCompatibleVac_of_isCompatible W.toWightmanStruct lam
  · exact isCompatible_of_isCompatibleVac W h4 lam

end WightmanStruct

end MobiusCPT
