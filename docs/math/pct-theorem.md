# The PCT theorem for Möbius-covariant Wightman CFTs — formalisation digest

Working mathematical source of truth for this repository: the definitions, conventions and
exact statements that the Lean development targets, in the (non-unitary) setting of
Tener [T26] and Carpi–Raymond–Tanimoto–Tener [CRTT25] (see `references.md`). The primary
papers are authoritative; wherever this digest could not be checked against them the point is
marked `[verify: …]` and must be resolved in the Issue that formalises it, never silently.

Out of scope of this digest (and of the charter): Haag–Kastler nets, Tomita–Takesaki theory,
the Bisognano–Wichmann property, and the equivalence with Möbius vertex algebras. They motivate
the theorem but no statement below depends on them.

## 1. The Möbius group and the circle

- `S¹ = { z ∈ ℂ : |z| = 1 }`. `C^∞(S¹)` is the complex vector space of smooth complex-valued
  functions on `S¹`, made a Fréchet space by the `C^n` norms
  `‖f‖_{C^n} = Σ_{i=0}^{n} max_{z∈S¹} |f^{(i)}(z)|`.
- Fourier expansion: every `f ∈ C^∞(S¹)` is `f(z) = Σ_{n∈ℤ} f̂_n z^n` with
  `f̂_n = (1/2π) ∫_0^{2π} f(e^{iθ}) e^{−inθ} dθ`, and `(f̂_n)` is rapidly decreasing
  (`sup_n |n|^m |f̂_n| < ∞` for every `m ≥ 0`). The monomials `{ z^n : n ∈ ℤ }` are linearly
  independent and form a (Schauder-type) basis of the complete topological vector space `C^∞(S¹)`.
- `SU(1,1) = { (α β ; β̄ ᾱ) ∈ Mat₂(ℂ) : |α|² − |β|² = 1 }` and the **Möbius group**
  `Möb := PSU(1,1) = SU(1,1)/{±1}`. It acts on `S¹` by `γ·z = (αz + β)/(β̄z + ᾱ)`
  (well defined on `S¹` because `|αz+β| = |β̄z+ᾱ|` when `|z| = 1`). `Möb ≅ PSL(2,ℝ)`.
- Distinguished one-parameter subgroups:
  - rotations `r_θ = diag(e^{iθ/2}, e^{−iθ/2})`, `r_θ·z = e^{iθ} z` (`θ ∈ ℝ`);
  - boosts (dilations) `v_t = ( cosh(t/2)  −sinh(t/2) ; −sinh(t/2)  cosh(t/2) )` (`t ∈ ℝ`),
    the real-entry elements.
- Complexified Lie algebra: differentiating the flow `γ(ε) = 1 + ε(α β ; β̄ ᾱ)` at `ε = 0` gives the
  vector field `β + (α + ᾱ) z − β̄ z²` on `S¹`, hence
  `Lie(Möb)_ℂ = span_ℂ{ L_0, L_1, L_{−1} }`, `L_n = −z^{n+1} d/dz`, with
  `[L_m, L_n] = (m − n) L_{m+n}` for `m, n ∈ {0, ±1}`; so `Lie(Möb)_ℂ ≅ sl₂(ℂ)`.
- Intervals: `Î = { I ⊂ S¹ : I ≠ ∅, closure(I) ≠ S¹, I connected and open }`, the proper open
  intervals of `S¹`. For `I ∈ Î` its complementary interval is `I' = S¹ \ closure(I)`.
  The reference intervals are `I_± = { z ∈ S¹ : ±Im z > 0 }`, with `(I_±)' = I_∓`.
- The reflection `z ↦ z⁻¹` (complex conjugation on `S¹`) swaps `I_+` and `I_−`.

## 2. Möbius-covariant Wightman conformal field theories

Topological preliminaries (as used by the definition):

- A seminorm `p : T → ℝ_{≥0}` on a complex vector space satisfies `p(x+y) ≤ p(x)+p(y)` and
  `p(λx) = |λ| p(x)`. A family of seminorms defines a locally convex topology with the finite
  intersections `⋂_i { x : p_{n_i}(x) < ε }` as a basis of neighbourhoods of `0`; it is Hausdorff iff
  `p_n(x) = 0 ∀n ⇒ x = 0`. A countable such family gives the metric
  `d(x,y) = Σ_n 2^{−n} p_n(x−y)/(1 + p_n(x−y))`; complete ⇒ **Fréchet space**.

Data. Let `D` be a complex vector space and `𝓕 ⊂ Hom_ℂ(C^∞(S¹), End(D))` a set of linear maps
("fields": each `φ ∈ 𝓕` sends a test function `f` to an operator `φ(f)` on `D`).

- For `k ∈ ℕ`, `φ_1,…,φ_k ∈ 𝓕`, `Φ ∈ D`, the multilinear map
  `S_{φ_1,…,φ_k,Φ} : C^∞(S¹)^k → D`, `(f_1,…,f_k) ↦ φ_1(f_1)⋯φ_k(f_k)Φ`.
- `λ ∈ D*` (algebraic dual) is **compatible with `𝓕`** if for every such tuple the multilinear
  functional `λ ∘ S_{φ_1,…,φ_k,Φ} : C^∞(S¹)^k → ℂ` is separately continuous (equivalently, jointly
  continuous for the product topology, `C^∞(S¹)` being Fréchet). Write
  `D*_𝓕 = { λ ∈ D* : λ compatible with 𝓕 }`. Because `{z^n}` is a basis, a compatible `λ` is
  determined by the values of `λ ∘ S` on tuples of monomials.
- `𝓕` **acts regularly** on `D` if for every `Φ ∈ D`, `Φ ≠ 0`, there is `λ ∈ D*_𝓕` with `λ(Φ) ≠ 0`.
- The **`𝓕`-weak topology** on `D` is the weakest making every `λ ∈ D*_𝓕` continuous; the
  **`𝓕`-strong topology** is the strongest locally convex topology making every
  `S_{φ_1,…,φ_k,Φ}` continuous. The following are equivalent: `𝓕` acts regularly; the `𝓕`-weak
  topology is Hausdorff; the `𝓕`-strong topology is Hausdorff. `[verify: T26/CRTT25 for the exact
  statement of this equivalence]`
- Assume `D` is locally convex Hausdorff for the `𝓕`-strong topology. `GL_𝓕(D)` is the group of
  linear automorphisms of `D` continuous for that topology, and `U : Möb → GL_𝓕(D)` a group
  homomorphism. `[verify: whether T26 imposes a continuity condition on `U`; the digest states none]`
- For `γ ∈ Möb` define `X_γ ∈ C^∞(S¹)` by `X_γ(e^{iθ}) = −i (d/dθ) log(γ(e^{iθ}))`, and for
  `d ∈ ℤ_{≥0}` the action
  `β_d : Möb → End(C^∞(S¹))`, `(β_d(γ) f)(z) = X_γ(γ⁻¹(z))^{d−1} · f(γ⁻¹(z))`.
  `[verify: the exponent `d−1` and the branch of `log`; T26 fixes the density convention]`
- `φ ∈ 𝓕` is a **Möbius-covariant distribution of conformal dimension `d`** (w.r.t. `U`) if
  `U(γ) φ(f) U(γ)⁻¹ = φ(β_d(γ) f)` for all `γ ∈ Möb`, `f ∈ C^∞(S¹)`.
- `Φ ∈ D` **has conformal dimension `d`** (w.r.t. `U`) if `U(r_θ) Φ = e^{idθ} Φ` for all `θ ∈ ℝ`.

**Definition (Möbius-covariant Wightman CFT).** A quadruple `(D, 𝓕, U, Ω)` where

1. `D` is a complex vector space;
2. `𝓕 ⊂ Hom_ℂ(C^∞(S¹), End(D))` acts regularly on `D`;
3. `U : Möb → GL_𝓕(D)` is a representation (for the `𝓕`-strong topology);
4. `Ω ∈ D`, `Ω ≠ 0` (the vacuum);

subject to

- **(W1) covariance** — every `φ ∈ 𝓕` is a Möbius-covariant distribution of some conformal
  dimension `d ∈ ℤ_{≥0}` w.r.t. `U`;
- **(W2) locality** — if `f, g ∈ C^∞(S¹)` have `supp f ∩ supp g = ∅` then `[φ_1(f), φ_2(g)] = 0`
  for all `φ_1, φ_2 ∈ 𝓕`;
- **(W3) positivity of energy** — if `Φ ∈ D` has conformal dimension `d < 0` then `Φ = 0`;
- **(W4) vacuum** — `U(γ) Ω = Ω` for all `γ ∈ Möb`, and
  `D = span_ℂ { S_{φ_1,…,φ_k,Ω}(f_1,…,f_k) : k ∈ ℤ_{≥0}, φ_i ∈ 𝓕, f_i ∈ C^∞(S¹) }`.

No Hilbert space, inner product or unitarity is part of the data: this is the non-unitary setting
of [T26]. (Unitary Wightman CFTs and their PCT operator `θ` are treated in [RTT22].)

Consequence used later: for `φ ∈ 𝓕` of dimension `d`, the vector `φ(z^{−d})Ω` has conformal
dimension `d`, and more generally `φ_1(z^{n_1})⋯φ_k(z^{n_k})Ω` has conformal dimension
`−(n_1 + ⋯ + n_k)`; with (W3) this forces `φ(f)Ω = 0` whenever `f` has only strictly positive
Fourier modes `[verify: T26 for the precise form of this vanishing statement]`.

## 3. Analytic continuation of the boost flow

Fix a Möbius-covariant Wightman CFT `(D, 𝓕, U, Ω)` and write `V_t = U(v_t) : D → D` (`t ∈ ℝ`).
The goal is to extend `t ↦ V_t` to complex `τ`, allowing the domain to shrink.

- For `τ ∈ ℂ` let `𝕊_τ ⊂ ℂ` be the closed strip of points whose imaginary part lies between `0`
  and `Im τ` (so `∂𝕊_τ = ℝ ∪ (ℝ + τ)`; for `τ ∈ ℝ`, `𝕊_τ = ℝ`).

**Lemma (uniqueness; `lem:G_lambda`).** Let `τ ∈ ℂ` and `Φ ∈ D`. A family of continuous
functions `G_λ : 𝕊_τ → ℂ` (`λ ∈ D*_𝓕`), each holomorphic in the interior of `𝕊_τ` and satisfying
`G_λ(t) = λ(V_t Φ)` for all `t ∈ ℝ`, is unique if it exists.
*Proof sketch.* Two such families agree on `ℝ`; by the Schwarz reflection principle each extends
holomorphically to a neighbourhood of `ℝ`, so by the identity theorem they agree on the interior
of `𝕊_τ`, and by continuity on all of the connected closed strip. `[verify: the case `Im τ = 0`,
where the interior is empty and the lemma is trivial]`

- For `τ ∈ ℂ` define `D_τ ⊂ D` as the set of `Φ ∈ D` for which there exists a family of continuous
  `G_λ : 𝕊_τ → ℂ` (`λ ∈ D*_𝓕`) with
  - **(Φ1)** `G_λ` holomorphic in the interior of `𝕊_τ` and `G_λ(t) = λ(V_t Φ)` for all `t ∈ ℝ`;
  - **(Φ2)** there is `Ψ ∈ D` such that `G_λ(τ + t) = λ(V_t Ψ)` for all `λ ∈ D*_𝓕`, `t ∈ ℝ`.
- By the lemma the family `(G_λ)` is unique, and `Ψ` is unique: if `Ψ'` also satisfies (Φ2) then
  `λ(V_t Ψ) = λ(V_t Ψ')` for all compatible `λ`, so `V_t Ψ = V_t Ψ'` by regularity, hence `Ψ = Ψ'`.
- Hence `Ṽ_τ : D_τ → D`, `Φ ↦ Ψ`, is well defined, and:
  - for `τ ∈ ℝ`: `D_τ = D` and `Ṽ_τ = V_τ` (take `G_λ(t) = λ(V_t Φ)`, `Ψ = V_τ Φ`);
  - `Ω ∈ D_τ` and `Ṽ_τ Ω = Ω` for every `τ` (take `G_λ ≡ λ(Ω)`, using `V_t Ω = Ω`).

Test functions adapted to `I_+`:

- `𝕆 = { z ∈ ℂ : |z| ≥ 1 } ∪ {∞}` and `𝓧` = the set of `F : 𝕆 → ℂ` that are `C^∞` on `𝕆`,
  holomorphic in its interior, with `F(∞) = 0` and `F^{(i)}(1) = F^{(i)}(−1) = 0` for all `i ≥ 0`.
  Restriction `𝓧 → C^∞(S¹)`, `F ↦ F|_{S¹}`, is injective (Schwarz reflection + identity theorem);
  via it `𝓧` is a closed subspace of `C^∞(S¹)`, hence Fréchet.
- `C^∞_0(I_±)` = smooth functions on `I_±` all of whose derivatives tend to `0` at the endpoints
  `±1`; extended by zero they are elements of `C^∞(S¹)`. For `F ∈ 𝓧`,
  `F|_{S¹} = F|_{I_+} + F|_{I_−}` with `F|_{I_±} ∈ C^∞_0(I_±)`.
- For `F ∈ 𝓧` and `τ ∈ ℝ`,
  `(β_d(v_τ) F|_{I_+})(z) = X_{v_τ}(v_{−τ}·z)^{d−1} F(v_{−τ}·z) = (cosh τ + Re(z) sinh τ)^{d−1} F(v_{−τ}·z)`.
  `[verify: this closed form against T26 — the digest writes `cosh τ` while `v_τ` has entries
  `cosh(τ/2)`]` The right-hand side makes sense for `τ ∈ 𝕊_{iπ}` because then `v_{−τ}·z ∈ 𝕆`;
  it lies in `C^∞_0(I_+)`, and `β_d(v_t) β_d(v_τ) F|_{I_+} = β_d(v_{τ+t}) F|_{I_+}` for `t ∈ ℝ`.
- For `F_1,…,F_k ∈ 𝓧`, `φ_1,…,φ_k ∈ 𝓕` of dimensions `d_1,…,d_k`, the functions
  `G_λ(τ) = λ( φ_1(β_{d_1}(v_τ)F_1|_{I_+}) ⋯ φ_k(β_{d_k}(v_τ)F_k|_{I_+}) Ω )` (`λ ∈ D*_𝓕`) are
  continuous on `𝕊_{iπ}` and holomorphic in its interior. `[verify: proved in T26; asserted here]`
- Hence, with `P_𝓧(I_±) = alg⟨ φ(F|_{I_±}) : φ ∈ 𝓕, F ∈ 𝓧 ⟩ ⊂ End(D)`:
  `P_𝓧(I_±) Ω ⊂ D_τ` for `τ ∈ 𝕊_{iπ}`, and for `Φ = φ_1(F_1|_{I_+})⋯φ_k(F_k|_{I_+})Ω`
  `Ṽ_τ Φ = φ_1(β_{d_1}(v_τ)F_1|_{I_+}) ⋯ φ_k(β_{d_k}(v_τ)F_k|_{I_+}) Ω`.
  Since `{ F|_{I_+} : F ∈ 𝓧 }` is dense in `C^∞_0(I_+)`, `P_𝓧(I_±)Ω` is dense in `D`, so `Ṽ_τ` is
  densely defined for `τ ∈ 𝕊_{iπ}`.

The value at `τ = iπ`:

- `v_{iπ}·z = z⁻¹`, hence `β_d(v_{iπ}) F|_{I_+} = (−1)^{d−1} (F ∘ z⁻¹)|_{I_+} = (−1)^{d−1} (F|_{I_−} ∘ z⁻¹)`.
  `[verify: the sign `(−1)^{d−1}` from `(cosh iπ + …)^{d−1}`]`
- For `F ∈ 𝓧`, `F ∘ z⁻¹` is holomorphic in the open unit disc and vanishes at `0`, so its Taylor
  expansion has only strictly positive powers of `z`; therefore `φ(F∘z⁻¹|_{S¹})Ω` has strictly
  negative conformal dimension and vanishes by (W3). With `g_j = F_j∘z⁻¹|_{I_+}` and
  `h_j = F_j∘z⁻¹|_{I_−}` this gives `φ(g)Ω = −φ(h)Ω`, and repeatedly using locality (W2) to move
  `φ_k(h_k)` to the front:
  `φ_1(g_1)⋯φ_k(g_k)Ω = (−1)^k φ_k(h_k)⋯φ_1(h_1)Ω`.

## 4. The PCT theorem

**Theorem (PCT).** Let `(D, 𝓕, U, Ω)` be a Möbius-covariant Wightman CFT. For `j = 1,…,k` let
`φ_j ∈ 𝓕` be Möbius covariant of conformal dimension `d_j`, and `f_j ∈ C^∞(S¹)` with
`supp f_j ⊂ I_+`. Then `φ_1(f_1)⋯φ_k(f_k)Ω ∈ D_{iπ}` and

    Ṽ_{iπ} φ_1(f_1) ⋯ φ_k(f_k) Ω = (−1)^{d_1+⋯+d_k} φ_k(f_k ∘ z⁻¹) ⋯ φ_1(f_1 ∘ z⁻¹) Ω .

Likewise, for `g_j ∈ C^∞(S¹)` with `supp g_j ⊂ I_−`,

    Ṽ_{−iπ} φ_1(g_1) ⋯ φ_k(g_k) Ω = (−1)^{d_1+⋯+d_k} φ_k(g_k ∘ z⁻¹) ⋯ φ_1(g_1 ∘ z⁻¹) Ω .

The sign is `(−1)^k · ∏_j (−1)^{d_j−1} = (−1)^{Σ d_j}`. `[verify: T26 states the theorem for general
`f_j` supported in `I_+`; §3 derives it for restrictions of `F_j ∈ 𝓧` and the passage to general
`f_j` is by density/continuity — the Lean statement must make that step explicit]`

Hypothesis checklist for a faithful Lean statement:

1. the full Wightman data `(D, 𝓕, U, Ω)` with (W1)–(W4), including regularity of `𝓕` and the
   `𝓕`-strong topology in which `U` takes values;
2. the conformal dimension `d_j` of each `φ_j`, as an explicit witness of (W1);
3. `supp f_j ⊂ I_+` (open upper half circle), not merely `⊂ closure(I_+)`;
4. `D_{iπ}` and `Ṽ_{iπ}` exactly as in §3 (existence of the family `(G_λ)` over all of `D*_𝓕`,
   (Φ1)–(Φ2), and uniqueness of `Ψ` via regularity);
5. the reflected test functions `f_j ∘ z⁻¹` (supported in `I_−`) and the reversed operator order.

## 5. Conventions and terminology

Conventions fixed above (change any of them only through an Issue that records the source):

- `S¹` is oriented counter-clockwise; `I_+` is the open upper half circle, `I_−` the lower.
- The boost `v_t` is the real-entry element with `cosh(t/2)` on the diagonal and `−sinh(t/2)` off it.
- `β_d(γ)` carries the factor `X_γ(γ⁻¹(z))^{d−1}` (exponent `d − 1`).
- Conformal dimensions of fields are non-negative integers; conformal dimension of a vector is its
  `L_0`-eigenvalue read off `U(r_θ)Φ = e^{idθ}Φ`.
- The reflection is `z ↦ z⁻¹` on `S¹` (equivalently `z ↦ z̄`).

| Japanese (source note) | English | Symbol / intended Lean name (suggestion) |
|---|---|---|
| メビウス変換群 | Möbius group | `Möb = PSU(1,1)`; `MobiusCPT.Mob` |
| 回転 / ブースト | rotation / boost (dilation) | `r_θ`, `v_t`; `Mob.rot`, `Mob.boost` |
| 開区間 | (proper open) interval of `S¹` | `Î`, `I ∈ Î`; `MobiusCPT.Interval` |
| 共形次元 | conformal dimension | `d`; `conformalDim` |
| メビウス共変な超関数 | Möbius-covariant (operator-valued) distribution | `φ ∈ 𝓕`; `IsCovariant φ d` |
| 正則な作用 | regular action (of `𝓕` on `D`) | `IsRegular 𝓕` |
| `𝓕`-弱位相 / `𝓕`-強位相 | `𝓕`-weak / `𝓕`-strong topology | — |
| メビウス共変Wightman共形場理論 | Möbius-covariant Wightman CFT | `(D, 𝓕, U, Ω)`; `MobiusCPT.WightmanCFT` |
| 真空 | vacuum | `Ω` |
| 局所性 | locality | (W2) |
| 帯状領域 | (closed) strip | `𝕊_τ` |
| 鏡像の原理 / 一致の原理 | Schwarz reflection principle / identity theorem | — |
| 稠密 / 急減少 | dense / rapidly decreasing | — |
| smeared 場 | smeared field | `φ(f)` |
