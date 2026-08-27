# The PCT theorem for Möbius-covariant Wightman CFTs — formalisation digest

Reviewed mathematical source of truth for this repository, subordinate to the primary papers
[T26] and [CRTT25] (see `references.md`): the definitions, conventions and exact statements the
Lean development targets, in the non-unitary setting. Every statement carries its source; the
primary papers decide any conflict. Genuine open source questions, if any arise, are tracked as
Issues, not as markers in this file.

Out of scope of this digest (and of the charter): Haag–Kastler / conformal nets, Tomita–Takesaki
theory, the Bisognano–Wichmann property, invariant Hermitian forms and PCT involutions ([T26] §4),
and the equivalence with Möbius vertex algebras. They motivate the theorem but no statement below
depends on them.

## 0. Conventions fixed for this project

- **Tuple order.** [T26] writes a Wightman CFT as `(𝓕, 𝓓, U, Ω)`; this project writes
  `(D, 𝓕, U, Ω)` (domain first). The order is a project convention only and carries no
  mathematical content.
- **Domain of the continued boost.** [T26] Def. 3.1 writes the domain of the partially defined
  operator `Ṽ_τ` as `D(Ṽ_τ)`. This digest uses `D(Ṽ_τ)` and, as an explicit alias, `D_τ := D(Ṽ_τ)`
  (the notation of the Japanese note). The two are never distinguished.
- **Support.** `supp f ⊆ I_±` means the support of `f` is contained in the *open* semicircle
  `I_±`, not merely in its closure.
- **Boost.** The one-parameter subgroup `v_t` below is called the *boost*; no second name is used.
- **`C_0^∞(I_±)`.** Smooth functions on `I_±` that *vanish to all orders at the endpoints* `±1`
  (equivalently: all derivatives tend to `0` there). "Flat at the endpoints" is an explanatory
  synonym, not the definition.
- Orientation: `S¹` is oriented counter-clockwise; `I_+` is the open upper semicircle.

## 1. The Möbius group and the circle

- `S¹ = { z ∈ ℂ : |z| = 1 }`. `C^∞(S¹)` is the complex vector space of smooth complex-valued
  functions on `S¹`, a Fréchet space for the `C^n` norms
  `‖f‖_{C^n} = Σ_{i=0}^{n} max_{z∈S¹} |f^{(i)}(z)|`.
- Fourier expansion: every `f ∈ C^∞(S¹)` has a unique expansion `f(z) = Σ_{n∈ℤ} f̂_n z^n` with
  `f̂_n = (1/2π) ∫_0^{2π} f(e^{iθ}) e^{−inθ} dθ`, converging in `C^∞(S¹)`, and `(f̂_n)` is rapidly
  decreasing (`sup_n |n|^m |f̂_n| < ∞` for every `m ≥ 0`). Consequently a continuous multilinear
  functional on `C^∞(S¹)^k` is determined by its values on tuples of monomials `z^n`. ([CRTT25] §2)
- `SU(1,1) = { (α β ; β̄ ᾱ) ∈ Mat₂(ℂ) : |α|² − |β|² = 1 }` and the **Möbius group**
  `Möb := PSU(1,1) = SU(1,1)/{±1}`, acting on `S¹` by `γ·z = (αz + β)/(β̄z + ᾱ)`
  (well defined on `S¹` since `|αz+β| = |β̄z+ᾱ|` for `|z| = 1`). `Möb ≅ PSL(2,ℝ)`.
- Distinguished one-parameter subgroups:
  - rotations `r_θ = diag(e^{iθ/2}, e^{−iθ/2})`, `r_θ·z = e^{iθ} z` (`θ ∈ ℝ`);
  - boosts `v_t = ( cosh(t/2)  −sinh(t/2) ; −sinh(t/2)  cosh(t/2) )`, i.e.
    `v_t·z = (cosh(t/2) z − sinh(t/2)) / (−sinh(t/2) z + cosh(t/2))` (`t ∈ ℝ`). ([T26] §3)
- Complexified Lie algebra: differentiating the flow `γ(ε) = 1 + ε(α β ; β̄ ᾱ)` at `ε = 0` gives the
  vector field `β + (α + ᾱ) z − β̄ z²` on `S¹`, hence
  `Lie(Möb)_ℂ = span_ℂ{ L_0, L_1, L_{−1} }`, `L_n = −z^{n+1} d/dz`, with
  `[L_m, L_n] = (m − n) L_{m+n}` for `m, n ∈ {0, ±1}`; so `Lie(Möb)_ℂ ≅ sl₂(ℂ)`.
- Intervals: `Î = { I ⊆ S¹ : I ≠ ∅, closure(I) ≠ S¹, I connected and open }`, the proper open
  intervals of `S¹`. For `I ∈ Î` its complementary interval is `I' = S¹ \ closure(I)`.
  The reference semicircles are `I_± = { z ∈ S¹ : ±Im z > 0 }`, with `(I_±)' = I_∓`.
- The inversion `z ↦ z⁻¹` (complex conjugation on `S¹`) swaps `I_+` and `I_−`.

## 2. Möbius-covariant Wightman conformal field theories

Sources: [T26] Defs. 2.4–2.5; [CRTT25] Defs. 2.1, 2.4–2.5 and Lemma 2.7.

Topological preliminaries:

- A seminorm `p : T → ℝ_{≥0}` on a complex vector space satisfies `p(x+y) ≤ p(x)+p(y)` and
  `p(λx) = |λ| p(x)`. A family of seminorms defines a locally convex topology with the finite
  intersections `⋂_i { x : p_{n_i}(x) < ε }` as a basis of neighbourhoods of `0`; it is Hausdorff iff
  `p_n(x) = 0 ∀n ⇒ x = 0`. A countable such family gives the metric
  `d(x,y) = Σ_n 2^{−n} p_n(x−y)/(1 + p_n(x−y))`; complete ⇒ **Fréchet space**.

Data. Let `D` be a complex vector space and `𝓕 ⊆ Hom_ℂ(C^∞(S¹), End(D))` a set of
**operator-valued distributions** (each `φ ∈ 𝓕` sends a test function `f` to an operator `φ(f)`
on `D`).

- For `k ∈ ℕ`, `φ_1,…,φ_k ∈ 𝓕`, `Φ ∈ D`, the multilinear map
  `S_{φ_1,…,φ_k,Φ} : C^∞(S¹)^k → D`, `(f_1,…,f_k) ↦ φ_1(f_1)⋯φ_k(f_k)Φ`.
- `λ ∈ D*` (algebraic dual) is **compatible with `𝓕`** if for every such tuple the multilinear
  functional `λ ∘ S_{φ_1,…,φ_k,Φ} : C^∞(S¹)^k → ℂ` is separately continuous (equivalently jointly
  continuous, `C^∞(S¹)` being Fréchet). `D*_𝓕 = { λ ∈ D* : λ compatible with 𝓕 }`. By the Fourier
  remark in §1, a compatible `λ` is determined by the values of `λ ∘ S` on tuples of monomials.
- `𝓕` **acts regularly** on `D` if for every `Φ ∈ D`, `Φ ≠ 0`, there is `λ ∈ D*_𝓕` with `λ(Φ) ≠ 0`.
- The **`𝓕`-weak topology** on `D` is the weakest making every `λ ∈ D*_𝓕` continuous; the
  **`𝓕`-strong topology** is the strongest locally convex topology making every
  `S_{φ_1,…,φ_k,Φ}` continuous. The following are equivalent ([CRTT25] Lemma 2.7): `𝓕` acts
  regularly; the `𝓕`-weak topology is Hausdorff; the `𝓕`-strong topology is Hausdorff. The
  continuous dual of `D` for the `𝓕`-strong topology is `D*_𝓕` ([T26] §2).
- Assume `𝓕` acts regularly, so `D` is locally convex Hausdorff for the `𝓕`-strong topology.
  `U : Möb → End(D)` is a representation by `𝓕`-strong continuous endomorphisms (hence
  `U(γ) ∈ GL_𝓕(D)`, the `𝓕`-strong continuous automorphisms). Continuity of the action in `γ` is
  a proved consequence in the sources, not an additional axiom ([T26] §2).
- For `γ ∈ Möb` and `d ∈ ℤ_{≥0}` the conformal action on test functions is
  `β_d(γ) f = (X_γ^{d−1} · f) ∘ γ⁻¹`, i.e. `(β_d(γ) f)(z) = X_γ(γ⁻¹(z))^{d−1} f(γ⁻¹(z))`,
  where `X_γ ∈ C^∞(S¹)` is the (positive, real) conformal factor of `γ` — for the circle
  parametrised by `e^{iθ}`, `X_γ(e^{iθ}) = −i (d/dθ) log γ(e^{iθ})`, where the logarithmic
  derivative is a well-defined real quantity and no branch choice enters. ([T26] Def. 2.4, eq. (2.2))
- `φ ∈ 𝓕` is **Möbius-covariant with conformal dimension `d`** (w.r.t. `U`) if
  `U(γ) φ(f) U(γ)⁻¹ = φ(β_d(γ) f)` for all `γ ∈ Möb`, `f ∈ C^∞(S¹)`.
- `Φ ∈ D` **has conformal dimension `d`** (w.r.t. `U`) if `U(r_θ) Φ = e^{idθ} Φ` for all `θ ∈ ℝ`.

**Definition (Möbius-covariant Wightman CFT; [T26] Def. 2.5, [CRTT25] Def. 2.5).** A quadruple
`(D, 𝓕, U, Ω)` where

1. `D` is a complex vector space;
2. `𝓕 ⊆ Hom_ℂ(C^∞(S¹), End(D))` acts regularly on `D`;
3. `U : Möb → GL_𝓕(D)` is a representation (for the `𝓕`-strong topology);
4. `Ω ∈ D`, `Ω ≠ 0` (the vacuum);

subject to

- **(W1) Möbius covariance** — every `φ ∈ 𝓕` is Möbius-covariant with some conformal dimension
  `d ∈ ℤ_{≥0}` w.r.t. `U`;
- **(W2) Locality** — if `f, g ∈ C^∞(S¹)` have `supp f ∩ supp g = ∅` then `[φ_1(f), φ_2(g)] = 0`
  for all `φ_1, φ_2 ∈ 𝓕`;
- **(W3) Spectrum condition** — if `Φ ∈ D` has conformal dimension `d < 0` then `Φ = 0`
  (informally: positivity of the energy `L_0`);
- **(W4) Vacuum** — `U(γ) Ω = Ω` for all `γ ∈ Möb`, and
  `D = span_ℂ { S_{φ_1,…,φ_k,Ω}(f_1,…,f_k) : k ∈ ℤ_{≥0}, φ_i ∈ 𝓕, f_i ∈ C^∞(S¹) }`.

No Hilbert space, inner product or unitarity is part of the data ([T26]; the unitary case and the
PCT operator `θ` are in [RTT22]).

Consequence used in §3 ([T26], proof of Lemma 3.7). For `φ ∈ 𝓕` of dimension `d` and `n ∈ ℤ`,
the vector `φ(z^n)Ω` has conformal dimension `−n` (rotation covariance plus `U(r_θ)Ω = Ω`; more
generally `φ_1(z^{n_1})⋯φ_k(z^{n_k})Ω` has dimension `−(n_1+⋯+n_k)`). Hence for `n > 0`, (W3)
gives `φ(z^n)Ω = 0` mode by mode. If `f ∈ C^∞(S¹)` has only strictly positive Fourier modes,
`φ(f)Ω` is in general not an `L_0`-eigenvector, so (W3) is not applied to it directly: for every
`λ ∈ D*_𝓕`, compatibility (continuity of `f ↦ λ(φ(f)Ω)` on `C^∞(S¹)`) and the convergence of
the Fourier expansion in `C^∞(S¹)` give `λ(φ(f)Ω) = Σ_{n>0} f̂_n λ(φ(z^n)Ω) = 0`, and regularity
of `𝓕` then yields `φ(f)Ω = 0`.

## 3. Analytic continuation of the boost flow

Sources: [T26] Defs. 3.1–3.5, Lemmas 3.4, 3.6, 3.7.

Fix a Möbius-covariant Wightman CFT `(D, 𝓕, U, Ω)` and write `V_t = U(v_t) : D → D` (`t ∈ ℝ`).

- For `τ ∈ ℂ` let `𝕊_τ ⊆ ℂ` be the closed strip of points whose imaginary part lies between `0`
  and `Im τ` (so `∂𝕊_τ = ℝ ∪ (ℝ + τ)`; for `τ ∈ ℝ`, `𝕊_τ = ℝ`).

**Lemma (uniqueness; [T26] §3, Japanese note `lem:G_lambda`).** Let `τ ∈ ℂ` and `Φ ∈ D`. A
family of continuous functions `G_λ : 𝕊_τ → ℂ` (`λ ∈ D*_𝓕`), each holomorphic in the interior of
`𝕊_τ` and satisfying `G_λ(t) = λ(V_t Φ)` for all `t ∈ ℝ`, is unique if it exists.
*Proof.* Two such families agree on `ℝ`; by the Schwarz reflection principle each extends
holomorphically to a neighbourhood of `ℝ`, so by the identity theorem they agree on the interior
of `𝕊_τ`, and by continuity on all of the connected closed strip. For `Im τ = 0` the interior is
empty and the statement is trivial.

**Definition ([T26] Def. 3.1).** For `τ ∈ ℂ` the **partially defined operator** `Ṽ_τ` has domain
`D(Ṽ_τ)` (alias `D_τ`) = the set of `Φ ∈ D` for which there exists a family of continuous
`G_λ : 𝕊_τ → ℂ` (`λ ∈ D*_𝓕`) with

- **(Φ1)** `G_λ` holomorphic in the interior of `𝕊_τ` and `G_λ(t) = λ(V_t Φ)` for all `t ∈ ℝ`;
- **(Φ2)** there is `Ψ ∈ D` such that `G_λ(τ + t) = λ(V_t Ψ)` for all `λ ∈ D*_𝓕`, `t ∈ ℝ`;

and `Ṽ_τ Φ := Ψ`. This is well defined: the family `(G_λ)` is unique by the lemma, and `Ψ` is
unique because `λ(V_t Ψ) = λ(V_t Ψ')` for all compatible `λ` forces `V_t Ψ = V_t Ψ'` by regularity,
hence `Ψ = Ψ'`. Moreover:

- for `τ ∈ ℝ`: `D(Ṽ_τ) = D` and `Ṽ_τ = V_τ` (take `G_λ(t) = λ(V_t Φ)`, `Ψ = V_τ Φ`);
- `Ω ∈ D(Ṽ_τ)` and `Ṽ_τ Ω = Ω` for every `τ` (take `G_λ ≡ λ(Ω)`, using `V_t Ω = Ω`).

Test functions adapted to `I_+` ([T26] Defs. 3.2–3.3, Lemma 3.4):

- `𝕆 = { z ∈ ℂ : |z| ≥ 1 } ∪ {∞}` and `𝓧` = the set of `F : 𝕆 → ℂ` that are `C^∞` on `𝕆`,
  holomorphic in its interior, with `F(∞) = 0` and `F^{(i)}(1) = F^{(i)}(−1) = 0` for all `i ≥ 0`
  ([T26] Def. 3.2). Restriction `𝓧 → C^∞(S¹)`, `F ↦ F|_{S¹}`, is injective (Schwarz reflection and
  the identity theorem), so `𝓧` is regarded as a subset of `C^∞(S¹)` with the relative topology.
- `C_0^∞(I_±)` = smooth functions on `I_±` vanishing to all orders at the endpoints `±1`; extended
  by zero they are elements of `C^∞(S¹)`. For `F ∈ 𝓧`, `F|_{S¹} = F|_{I_+} + F|_{I_−}` with
  `F|_{I_±} ∈ C_0^∞(I_±)`.
- **Lemma 3.4 ([T26]).** `{ F|_{I_+} : F ∈ 𝓧 }` is dense in `C_0^∞(I_+)` (for the `C^∞` topology).
- For `F ∈ 𝓧` and `τ ∈ ℝ`,
  `(β_d(v_τ) F|_{I_+})(z) = X_{v_τ}(v_{−τ}·z)^{d−1} F(v_{−τ}·z) = (cosh τ + Re(z) sinh τ)^{d−1} F(v_{−τ}·z)`
  ([T26] eqs. (3.4)–(3.5); the closed form is in the full argument `τ` although the matrix of `v_τ`
  uses half-arguments). The right-hand side makes sense for `τ ∈ 𝕊_{iπ}` because
  `v_{−τ}(I_+) ⊆ 𝕆` for `0 ≤ Im τ ≤ π` ([T26] Def. 3.5 and discussion); it lies in `C_0^∞(I_+)`,
  and `β_d(v_t) β_d(v_τ) F|_{I_+} = β_d(v_{τ+t}) F|_{I_+}` for `t ∈ ℝ`.
- **Lemma 3.6 ([T26]).** For `F_1,…,F_k ∈ 𝓧`, `φ_1,…,φ_k ∈ 𝓕` of dimensions `d_1,…,d_k`, the map
  `τ ↦ β_d(v_τ)F|_{I_+}` is continuous on `𝕊_{iπ}` and holomorphic in its interior, and so are the
  functions `G_λ(τ) = λ( φ_1(β_{d_1}(v_τ)F_1|_{I_+}) ⋯ φ_k(β_{d_k}(v_τ)F_k|_{I_+}) Ω )`
  (`λ ∈ D*_𝓕`).
- Let `P_𝓧(I_±)` be the unital subalgebra of `End(D)` generated by `{ φ(F|_{I_±}) : φ ∈ 𝓕, F ∈ 𝓧 }`,
  and `P(I_±)` the unital subalgebra generated by `{ φ(f) : φ ∈ 𝓕, f ∈ C^∞(S¹), supp f ⊆ I_± }`.
  Then `P_𝓧(I_±) Ω ⊆ D(Ṽ_τ)` for `τ ∈ 𝕊_{iπ}` (resp. `𝕊_{−iπ}`), and for
  `Φ = φ_1(F_1|_{I_+})⋯φ_k(F_k|_{I_+})Ω`
  `Ṽ_τ Φ = φ_1(β_{d_1}(v_τ)F_1|_{I_+}) ⋯ φ_k(β_{d_k}(v_τ)F_k|_{I_+}) Ω`.
- Density of the analytic core: Lemma 3.4 gives density of `{F|_{I_+}}` in `C_0^∞(I_+)` only.
  Density of `P_𝓧(I_+)Ω` in `D` additionally uses the Reeh–Schlieder property, i.e. density of
  `P(I_+)Ω` in `D` ([CRTT25] Appendix A; [T26] discussion). It is needed to justify the phrase
  "densely defined" for `Ṽ_{±iπ}`, not for the inclusion and formula in the theorem below.

The value at `τ = iπ` ([T26] Lemma 3.7):

- `v_{iπ}·z = z⁻¹`, hence `β_d(v_{iπ}) F|_{I_+} = (−1)^{d−1} (F ∘ z⁻¹)|_{I_+} = (−1)^{d−1} (F|_{I_−} ∘ z⁻¹)`
  (the sign is `(cosh iπ + Re(z) sinh iπ)^{d−1} = (−1)^{d−1}`).
- For `F ∈ 𝓧`, `F ∘ z⁻¹` is holomorphic in the open unit disc and vanishes at `0`, so its Taylor
  expansion has only strictly positive powers of `z`; by the consequence of (W3) recorded in §2,
  `φ(F∘z⁻¹|_{S¹})Ω = 0`. Write `g_j := (F_j∘z⁻¹)|_{I_+} = (F_j|_{I_−})∘z⁻¹` (supported in `I_+`)
  and `h_j := (F_j∘z⁻¹)|_{I_−} = (F_j|_{I_+})∘z⁻¹`, both zero-extended elements of `C^∞(S¹)`
  lying in `C_0^∞(I_+)` resp. `C_0^∞(I_−)`; since `F_j∘z⁻¹|_{S¹} = g_j + h_j`, this gives
  `φ_j(g_j)Ω = −φ_j(h_j)Ω`. Moving `φ_k(h_k)` to the front uses locality, but not directly: `g_i`
  and `h_k` vanish to all orders at `±1` while their closed supports may both contain `±1`, so (W2)
  does not apply to the pair as it stands. *Cutoff-and-continuity argument:* choose smooth cutoffs
  `χ_ε ∈ C^∞(S¹)` equal to `1` outside the `ε`-neighbourhoods of `±1` and to `0` inside the
  `ε/2`-neighbourhoods, with `supp(χ_ε h_k)` contained in the open `I_−`. Because `h_k` vanishes to
  all orders at `±1`, `χ_ε h_k → h_k` in `C^∞(S¹)` as `ε → 0`. For each `ε`,
  `supp(g_i) ∩ supp(χ_ε h_k) = ∅`, so (W2) gives `[φ_i(g_i), φ_k(χ_ε h_k)] = 0` and hence
  `φ_1(g_1)⋯φ_{k−1}(g_{k−1})φ_k(χ_ε h_k)Ω = φ_k(χ_ε h_k)φ_1(g_1)⋯φ_{k−1}(g_{k−1})Ω`; applying any
  `λ ∈ D*_𝓕` and letting `ε → 0` (compatibility: continuity in the `h`-slot), the two sides converge
  to the corresponding expressions with `h_k`, and regularity of `𝓕` turns the equality of all
  `λ`-values into equality of vectors. Iterating the same step for `h_{k−1}, …, h_1`:
  `φ_1(g_1)⋯φ_k(g_k)Ω = (−1)^k φ_k(h_k)⋯φ_1(h_1)Ω`. ([T26], proof of Lemma 3.7.)
- **Lemma 3.7 ([T26]).** For `F_j ∈ 𝓧` and covariant `φ_j` of dimension `d_j`, with
  `f_j := F_j|_{I_+}` (so `f_j ∘ z⁻¹ = h_j`, supported in `I_−`),
  `Ṽ_{iπ} φ_1(f_1)⋯φ_k(f_k)Ω = (−1)^{d_1+⋯+d_k} φ_k(f_k∘z⁻¹)⋯φ_1(f_1∘z⁻¹)Ω`,
  the sign being `(−1)^k · ∏_j (−1)^{d_j−1} = (−1)^{Σ d_j}`; this is Theorem 3.10 (i) on the
  analytic core.

Extension from the analytic core to general test functions ([T26] Lemmas 3.8–3.9): the passage
from `F|_{I_+}` (`F ∈ 𝓧`) to arbitrary `f ∈ C^∞(S¹)` with `supp f ⊆ I_+` is **not** a bare
density/continuity remark. It is the limiting argument of Theorem 3.10 built on Lemma 3.4
(density) together with Lemma 3.8 (a real-boundary `C^N` growth estimate for the boundary values)
and Lemma 3.9 (uniform control on the closed strip via the maximum principle), which show that the
families `G_λ` of the approximants converge to a family satisfying (Φ1)–(Φ2) for the limit vector.
A faithful Lean proof must formalise these two estimates.

## 4. The PCT theorem

**Theorem ([T26] Thm. 3.10).** Let `(D, 𝓕, U, Ω)` be a Möbius-covariant Wightman CFT. For
`j = 1,…,k` let `φ_j ∈ 𝓕` be Möbius-covariant with conformal dimension `d_j`.

(i) If `f_j ∈ C^∞(S¹)` with `supp f_j ⊆ I_+`, then `φ_1(f_1)⋯φ_k(f_k)Ω ∈ D(Ṽ_{iπ})` and

    Ṽ_{iπ} φ_1(f_1) ⋯ φ_k(f_k) Ω = (−1)^{d_1+⋯+d_k} φ_k(f_k ∘ z⁻¹) ⋯ φ_1(f_1 ∘ z⁻¹) Ω .

(iii) If `g_j ∈ C^∞(S¹)` with `supp g_j ⊆ I_−`, then `φ_1(g_1)⋯φ_k(g_k)Ω ∈ D(Ṽ_{−iπ})` and

    Ṽ_{−iπ} φ_1(g_1) ⋯ φ_k(g_k) Ω = (−1)^{d_1+⋯+d_k} φ_k(g_k ∘ z⁻¹) ⋯ φ_1(g_1 ∘ z⁻¹) Ω .

(Numbering (i), (iii) follows [T26]; the omitted part (ii) concerns density and is the
Reeh–Schlieder companion statement, cf. §3.) In both cases the reflected test functions
`f_j ∘ z⁻¹` are supported in the opposite semicircle and the operator order is reversed.

Hypothesis checklist for a faithful Lean statement:

1. the full Wightman data `(D, 𝓕, U, Ω)` with (W1)–(W4), including regularity of `𝓕` and the
   `𝓕`-strong topology in which `U` takes values;
2. the conformal dimension `d_j` of each `φ_j`, as an explicit witness of (W1);
3. `supp f_j ⊆ I_+` (open semicircle), not merely `⊆ closure(I_+)`; likewise for `I_−`;
4. `D(Ṽ_{±iπ})` and `Ṽ_{±iπ}` exactly as in §3 (existence of the family `(G_λ)` over all of `D*_𝓕`,
   (Φ1)–(Φ2), uniqueness of `Ψ` via regularity);
5. the reflected test functions `f_j ∘ z⁻¹` and the reversed operator order;
6. the domain membership as part of the conclusion in both (i) and (iii).

## 5. Terminology

Canonical vocabulary is that of the primary papers (English); the Japanese column records the
wording of the local note for cross-reference.

| Japanese (source note) | Canonical English ([T26]/[CRTT25]) | Symbol / intended Lean name (suggestion) |
|---|---|---|
| メビウス変換群 | Möbius group | `Möb = PSU(1,1)`; `MobiusCPT.Mob` |
| 回転 / ブースト | rotation / boost | `r_θ`, `v_t`; `Mob.rot`, `Mob.boost` |
| 開区間 | (proper open) interval of `S¹` | `Î`, `I ∈ Î`; `MobiusCPT.Interval` |
| 共形次元 | conformal dimension | `d`; `conformalDim` |
| メビウス共変な超関数 | operator-valued distribution, Möbius-covariant with conformal dimension `d` | `φ ∈ 𝓕`; `IsCovariant φ d` |
| `𝓕` と compatible | compatible with `𝓕` | `λ ∈ D*_𝓕` |
| 正則な作用 | `𝓕` acts regularly | `ActsRegularly 𝓕` |
| `𝓕`-弱位相 / `𝓕`-強位相 | `𝓕`-weak topology / `𝓕`-strong topology | — |
| メビウス共変Wightman共形場理論 | Möbius-covariant Wightman CFT | `(D, 𝓕, U, Ω)`; `MobiusCPT.WightmanCFT` |
| 真空 | vacuum | `Ω` |
| 局所性 | locality | (W2) |
| (W3) | spectrum condition | (W3) |
| 帯状領域 | closed strip | `𝕊_τ` |
| `D_τ`, `Ṽ_τ` | domain `D(Ṽ_τ)` of the partially defined operator `Ṽ_τ` | `D(Ṽ_τ) = D_τ` |
| 鏡像の原理 / 一致の原理 | Schwarz reflection principle / identity theorem | — |
| 稠密 / 急減少 | dense / rapidly decreasing | — |
| smeared 場 | smeared field | `φ(f)` |
| 端点で全階の導関数が 0 | vanishes to all orders at the endpoints | `C_0^∞(I_±)` |
| 生成する部分代数 | unital subalgebra generated by … | `P_𝓧(I_±)`, `P(I_±)` |
| Reeh–Schlieder 性 | Reeh–Schlieder property | density of `P(I_±)Ω` |
