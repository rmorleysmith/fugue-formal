# Results, file by file

The complete list of what is proved in this repository. For the pictures behind the main results,
see the [README](README.md); for plain-language explanations, see [`EXPLAINED.md`](EXPLAINED.md).

## Status

Two libraries, both sorry-free; `Audit.lean` checks **103** headline theorems (all
`[propext, Classical.choice, Quot.sound]`) plus non-vacuity examples.

### `QuasiRH` — building on OpenAI's quasi-Riemann theorem

| File | Content | Status |
|---|---|---|
| `QuasiRH/Basic.lean` | `ZeroFreeRight θ`, `QuasiRiemannHypothesis`, `OpenAIStatement` (verbatim); `RH ⇒ ZeroFreeRight ½`; zero-free ⇒ `−ζ′/ζ` holomorphic ⇒ the von Mangoldt series continues | ✅ |
| `QuasiRH/Characterisation.lean` | at a zero of ζ, `−ζ′/ζ` has a simple pole; **`ZeroFreeRight θ ↔ −ζ′/ζ holomorphic on {θ < Re s, s ≠ 1}`** | ✅ |
| `QuasiRH/Continuation.lean` | *any* holomorphic continuation of `∑Λ(n)n^{-s}` to the region forces `ZeroFreeRight θ` (identity theorem on the connected region) | ✅ |
| `QuasiRH/Reflection.lean` | **`RH ↔ ZeroFreeRight (1/2)`** via the functional equation | ✅ |
| `QuasiRH/InghamEasy.lean` | **`ψ(x) − x = O(x^θ) ⇒ ZeroFreeRight θ`** (partial summation + Mellin holomorphy); hence `ψ(x) = x + O(x^{1/2+ε}) ∀ε ⇒ RH`; Chebyshev `PsiError 1` as non-vacuity | ✅ |
| `QuasiRH/Dirichlet.lean` | the characterisation for every Dirichlet `L(s,χ)`; OpenAI's Dirichlet statement (verbatim) ⇒ every `∑χ(n)Λ(n)n^{-s}` continues to `Re s > 7/8` | ✅ |

### `Fugue` — theorems extracted from the HSLN corpus (ledger rows cited in each file)

| File | Content | Status |
|---|---|---|
| `Fugue/E8Lattice.lean` | E8 Cartan form is even and positive definite (with Mathlib's `det = 1`: even unimodular), finite norm-fibres, and `Θ_{E8⊕E8} = Θ_{E8}²` (A1, C13) | ✅ |
| `Fugue/TwoRings.lean` | Ring A (Cauchy, `K⟦X⟧`) and Ring B (Dirichlet) are **not isomorphic** (Dirichlet ring not a PID); C1, C3, C4, C5, C8 (refutation `σ₃ ≠ ζ⁴`), C9 (log is a derivation), C11 | ✅ |
| `Fugue/EllipticPoints.lean` | every level-1 form of weight `6 ∤ k` vanishes at `ρ`, of weight `4 ∤ k` at `i`; `E₄(ρ) = 0`, `E₆(i) = 0`, `E₄(i) ≠ 0`, `E₆(ρ) ≠ 0` (A3, A8) | ✅ |
| `Fugue/Dynamics.lean` | minimum modulus: attractors of `|F|` are the zeros (A9); coupling matrix PSD ⟺ `|κ| ≤ 1`, PD ⟺ `|κ| < 1`; equilibria preserved for *any* `K` (E2, E3, E5) | ✅ |
| `Fugue/Theta.lean` | `Θ_{L⊕M} = Θ_L·Θ_M` as a Cauchy product (C13; settles B9) | ✅ |
| `Fugue/TwoSquares.lean` | **Jacobi's two-square theorem** `r₂(n) = 4·Σ_{d∣n} χ₋₄(d)` (C6) — not in Mathlib; via Gaussian integers, strong induction on the least prime factor | ✅ |
| `Fugue/LeibnizL.lean` | **`L(1, χ₋₄) = π/4`** (D6) — not in Mathlib (which has no `s = 1` values of odd Hurwitz/sine zeta) | ✅ |
| `Fugue/Ramanujan.lean` | **`E₄² = E₈`** and Ramanujan's **`σ₇(n) = σ₃(n) + 120 Σ σ₃(a)σ₃(n−a)`** — Ring A (Cauchy) of Ring B (Dirichlet) objects | ✅ |
| `Fugue/HeckeRefutation.lean` | ledger C12 refuted in Lean: `a₂(Δ·E₄) = 216 ≠ a₂(Δ)·a₂(E₄)`; Ramanujan `τ(2) = −24` from `Δ = (E₄³−E₆²)/1728` | ✅ |
| `Fugue/SieveEta.lean` | D9 sieve by `{2,3,5,7}` = Eratosthenes; C15 eta quotients never vanish on `ℍ` | ✅ |
| `Fugue/ThetaE8*.lean` | **`Θ_{E8} = E₄`** (A2): `E8 = D8 ∪ (D8+½𝟙)` gives `Θ_{E8} = (θ₂⁸+θ₃⁸+θ₄⁸)/2`, which is a level-one weight-4 form, hence `E₄`; **#E8 vectors of norm 2n = 240σ₃(n)** (240, 2160, 6720) | ✅ |
| `Fugue/HeteroticE8.lean`, `Fugue/D16Plus.lean` | **heterotic lattices**: `Θ_{E8⊕E8} = E₈` (480σ₇(n) vectors of norm 2n) and **Witt's isospectrality** `Θ_{D16⁺} = Θ_{E8⊕E8}` — the lattices of the `E8×E8` and `Spin(32)/ℤ₂` heterotic strings have the same theta series | ✅ |
| `Fugue/RamanujanL.lean` | **Ramanujan's L-function** `Σ τ(n)n^{−s}` of `Δ = η²⁴`: completed `Λ` is **entire** with `Λ(12−s) = Λ(s)`; `τ(1..3) = 1, −24, 252`; Hecke's bound `τ(n) = O(n⁶)` (Mordell multiplicativity and Deligne's bound not formalised) | ✅ |
| `Fugue/PrimonGas.lean` | **primon gas** (Julia, Spector 1990): bosonic partition function `ζ(s)`, **fermionic** `ζ(s)/ζ(2s)` (Pauli = squarefree), fermion parity `(−1)^F = μ`, Witten index `1/ζ(s)`, fermionic Fock states ↔ finite sets of primes — an analogy made precise | ✅ |
| `Fugue/Epstein.lean` | **Epstein zeta functions**: `Z_{E8} = 240ζ(s)ζ(s−3)`, `Z_{E8⊕E8} = 480ζ(s)ζ(s−7)`, `Z_{ℤ²} = 4ζ(s)L(s,χ₋₄)`, `Z_{hex} = 6ζ(s)L(s,χ₋₃)` | ✅ |
| `Fugue/GoldenPrimes.lean` | **golden-ratio primes**: `p = x² + xy − y²` (the norm of `ℤ[φ]`) ⇔ `p = 5` or `p ≡ ±1 (mod 5)`; inert primes stay prime; `√5 = 2φ − 1` ramifies; `φⁿ⁺¹ = F_n + F_{n+1}φ` and Cassini's identity | ✅ |
| `Fugue/Partitions.lean` | **partitions**: Euler's `Σp(n)qⁿ·∏(1−qⁿ) = 1` and recurrence (p(0..10) checked); **Jacobi's identity** `∏(1−qⁿ)³ = Σ(−1)ᵏ(2k+1)q^{k(k+1)/2}` (not in Mathlib); **Ramanujan's congruence `p(5n+4) ≡ 0 (mod 5)`** for all n | ✅ |
| `Fugue/Tau691.lean` | **Ramanujan's `τ(n) ≡ σ₁₁(n) (mod 691)`**; integrality of `τ` from `Δ = q∏(1−qⁿ)²⁴` (`qExpansion_discriminant_eq`); `E₁₂ = E₄³ − (432000/691)Δ` | ✅ |
| `Fugue/DirectSumGenus.lean` | direct sum = block-diagonal Gram matrix: `E8⊕E8` is even unimodular (det 1); a direct sum multiplies theta series and adds weights, but does not raise the Siegel degree | ✅ |
| `Fugue/EulerCompose.lean` | **composing per-prime Euler factors** (fig 32, ledger D1): `∏_{p∈S} eulerFactor p = smooth S` (indicator of the `S`-smooth numbers — unique factorisation coefficient by coefficient), all-ones row for `n ≤ N`, coefficientwise limit `ζ`, Mathlib's analytic Euler product | ✅ |
| `Fugue/EntropicAction.lean` | **Bianconi's gravity-from-entropy, warm-up case**: `−ln det(1 + α∇φ∇φᵀ) = −ln(1 + α|∇φ|²)` (matrix determinant lemma), low-energy limit = massless Klein–Gordon (`HasDerivAt`), emergent cosmological constant `Σ(λ−1−ln λ) ≥ 0` with equality iff all `λ = 1` (vacuum) | ✅ |
| `Fugue/HeckeE4.lean` | **Hecke for `E₄`**: modularity ⇒ `(2π)^{−s}Γ(s)·240ζ(s)ζ(s−3)` continues to `ℂ∖{0,4}`, symmetric under `s ↔ 4−s`, residues `±1` | ✅ |
| `Fugue/HeckeEk.lean` | Hecke for **every** `E_k` (`k ≥ 4` even): root number `(−1)^{k/2}`, identification with `−(2k/B_k)(2π)^{−s}Γ(s)ζ(s)ζ(s−k+1)` on `ℂ∖{1,k,0,−1,…}`; `E₆`'s forced centre zero `Λ₆(3) = 0` *is* the trivial zero `ζ(−2) = 0` | ✅ |
| `Fugue/RankinSelberg.lean` | **Ramanujan's formula** `Σσ_a(n)σ_b(n)n^{−s}·ζ(2s−a−b) = ζ(s)ζ(s−a)ζ(s−b)ζ(s−a−b)` (Re s > a+b+1) — the Rankin–Selberg prototype; C11's "Rankin–Selberg closure" made precise | ✅ |
| `Fugue/HexagonalCount.lean` | **`#{a²−ab+b²=n} = 6Σ_{d∣n} χ₋₃(d)`** (C7) — the Eisenstein integers / hexagonal lattice, `ζ_{ℚ(√−3)}` | ✅ |
| `Fugue/Factoring.lean` | root-of-unity detector = divisibility test = trial division (D12, D13); `φ(pq)` reveals `p, q` (Miller); **`pos = frac∘log₂` is injective on odd numbers** — corrects appendix A §§4, 6 | ✅ |

### `fugue-formal-pnt` — Ingham's theorem, the hard direction (✅ complete)

Same pins plus PrimeNumberTheoremAnd at OpenAI's commit `c39a751` and this library as a dependency. **`Ingham.zeroFreeRight_iff_psiError`**: for `1/2 ≤ θ < 1`, *no zeros right of θ ⟺
`ψ(x) = x + O(x^{θ+δ})` for all δ > 0*; hence RH ⟺ square-root error, and **OpenAI's 7/8 ⟺
`ψ(x) = x + O(x^{7/8+δ})`**. 11 theorems audited, standard axioms. See
[rmorleysmith/fugue-formal-pnt](https://github.com/rmorleysmith/fugue-formal-pnt).

Every claim in these tables was established by `lake build` + `lake env lean Audit.lean`.

## What is new, and what is not

**Not new:** the mathematics of chapters 1–5 is textbook (Titchmarsh, Davenport). The
identity `∑ Λ(n)n^{-s} = −ζ′/ζ` for `Re s > 1` is already in Mathlib
(`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`), as is the theorem that a
log-derivative has a simple pole at a zero (`meromorphicOrderAt_logDeriv_eq_neg_one`).

**New in the formal sense** (as far as we could find — each claim checked against Mathlib at our
pin, `formal-conjectures`, PrimeNumberTheoremAnd and OpenAI's repository):

1. the quasi-Riemann hypothesis as a Lean `Prop` outside OpenAI's repository, and its
   characterisation by holomorphy of `−ζ′/ζ` (chapters 1–3, also for every `L(s,χ)`);
2. **Ingham's theorem in both directions** ([fugue-formal-pnt](https://github.com/rmorleysmith/fugue-formal-pnt), [palomar-ingham](https://github.com/rmorleysmith/palomar-ingham)): zero-free right of
   θ ⟺ `ψ(x) = x + O(x^{θ+δ})`; RH ⟺ square-root error; **OpenAI's 7/8 ⟺ `ψ(x) = x + O(x^{7/8+δ})`**; and in `palomar-ingham` (`PalomarIngham/Dirichlet/`), **OpenAI's Dirichlet theorem ⇒ `ψ(x; q, a) = x/φ(q) + O(x^{7/8+δ})`** (primes in progressions).
   PrimeNumberTheoremAnd has RH-conditional error terms only as `sorry`'d statements; OpenAI's
   prime-counting files have no error term;
3. classical theorems absent from Mathlib at our pin, extracted from the corpus: **Jacobi's
   two-square theorem**, **`L(1,χ₋₄) = π/4`**, the elliptic-point vanishing of level-one forms
   (`E₄(ρ) = 0`, `E₆(i) = 0`), Ramanujan's `σ₇` identity via `E₄² = E₈`, positive definiteness of
   the E8 form and `Θ_{E8⊕E8} = Θ_{E8}²`, and non-isomorphism of the Cauchy and Dirichlet rings.

None of the *mathematics* is new; it is classical. What is new is that it is now machine-checked,
connected to the corpus' claims, and (for item 2) packaged for the Palomar registry.

## Contribution paths found during the research

1. **`formal-conjectures` (small, concrete, ready).** The repo has RH, GRH, and four RH
   equivalents, but **no quasi-RH**. Its contribution guide provides exactly the right mechanism:
   `@[category research solved, AMS 11, formal_proof using lean4 at "<url>"]`, linking to
   `OAI/NumberTheory/DirichletL/Nonvanishing.lean` at a pinned commit. Their guide "strongly
   recommends" a Palomar entry for research proofs; OpenAI's result is **not** on Palomar
   (checked against the registry's 200-entry recent feed, 22 Oct 2026), so whether to mark it
   `solved` is the maintainers' call. A PR adding the *statement* with an accurate docstring is
   uncontroversial either way.
2. **Mathlib (small).** `riemannZeta_not_eventually_zero` / the order-−1 lemma at zeros of ζ are
   natural Mathlib lemmas near `NumberTheory/LSeries/ZetaZeros.lean` (which already has
   `isDiscrete_riemannZetaZeros`).
3. **Palomar (large, later).** A registry entry needs "credible research interest". The chapters
   below build toward one that would qualify (chapter 6).

## Roadmap

| # | Chapter | Content | State |
|---|---|---|---|
| 1 | `Basic` | zero-free ⇒ prime series continues | ✅ |
| 2 | `Characterisation` | …and conversely (zeros = poles) | ✅ |
| 3 | `Dirichlet` | the same for every `L(s,χ)` | ✅ |
| 4 | `Continuation`, `Reflection` | any continuation suffices; RH ⟺ `ZeroFreeRight ½` | ✅ |
| 5 | `InghamEasy` | `ψ(x) − x = O(x^θ) ⇒ ZeroFreeRight θ` | ✅ |
| 6 | ✅ `Ingham` (in `fugue-formal-pnt`) | `ZeroFreeRight θ ⇒ ψ(x) = x + O(x^{θ+ε})` for `½ ≤ θ < 1`. With OpenAI's proof: **`ψ(x) = x + O(x^{7/8+ε})`**. As far as we could find, no proof assistant has a machine-checked power-saving error term in the PNT (PrimeNumberTheoremAnd contains RH-conditional ones only as `sorry`'d blueprint statements). Plan: smoothed Chebyshev function from PNT+'s `MediumPNT`, contour moved to the straight line `Re s = θ + δ`, with a new bound `ζ′/ζ ≪ log|t|` there from Borel–Carathéodory | ✅ |

Chapter 6 is the Palomar candidate; the Palomar-ready port is [palomar-ingham](https://github.com/rmorleysmith/palomar-ingham) (✅ `lake comparator` passes; awaiting a public repo + human submission). Chapters 1–5 are the steps toward it.
## Toolchain, and why it is pinned where it is

| | |
|---|---|
| Lean | `v4.34.1` |
| Mathlib | commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |

These are **exactly** the versions in `openai/math/lean/lake-manifest.json`. OpenAI's quasi-RH
proof, `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, was checked against them. Pinning to
the same commit means the statement we assume (`OpenAIStatement`) is *literally* the statement of
their comparator challenge, and the hypothesis can later be discharged by their proof without a
version mismatch.

Physlib is **not** a dependency yet: nothing in the number theory needs it, its Mathlib pin would
constrain ours, and Palomar `Challenge.lean` files may import only Lean core, Mathlib and Tau Ceti.
The physics side (the Siegel/heterotic geometry) should be a separate Lake project when we get to
it.
