# Formal — a Lean/Mathlib workspace for the number theory in the HSLN corpus

The working formalisation space that follows on from the `Fugue/` extraction. Where `Fugue/`
*graded* the corpus' claims, this directory *proves* things — small, sorry-free, machine-checked
steps, each one explainable in plain language.

For what each theorem means and how to explain it, read [`EXPLAINED.md`](EXPLAINED.md).

## Build

```bash
cd /home/rms/Math/Formal
lake exe cache get      # once; downloads prebuilt Mathlib
lake build              # builds the QuasiRH library (~10 s after cache)
lake env lean Audit.lean   # axiom audit + sanity checks
```

`Audit.lean` must print only `[propext, Classical.choice, Quot.sound]` for every theorem: these
are Lean's three standard axioms. If `sorryAx` ever appears, something is unproved.

## Toolchain — and why it is pinned where it is

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

## Status

| File | Content | Status |
|---|---|---|
| `QuasiRH/Basic.lean` | `ZeroFreeRight θ`, `QuasiRiemannHypothesis`, `OpenAIStatement` (verbatim); `RH ⇒ zero-free right of ½`; **zero-free ⇒ `−ζ′/ζ` holomorphic ⇒ the von Mangoldt series continues** | ✅ sorry-free |
| `QuasiRH/Characterisation.lean` | **The converse**: at a zero of ζ, `−ζ′/ζ` has a simple pole (meromorphic order −1), hence `ZeroFreeRight θ ↔ −ζ′/ζ holomorphic on {θ < Re s, s ≠ 1}`; restatements of OpenAI's theorem and of the quasi-RH as statements about the prime series | ✅ sorry-free |
| `Audit.lean` | `#print axioms` for all 9 headline theorems + 3 non-vacuity checks (characterisation true at θ = 1, **false** at θ = −3 because ζ(−2) = 0) | ✅ passes |

Every claim in this table was established by `lake build` + `lake env lean Audit.lean`, not by
reading the code.

## What is new, and what is not — honestly

**Not new:** the mathematics of chapter 1 and 2 is textbook (Titchmarsh, Davenport). The
identity `∑ Λ(n)n^{-s} = −ζ′/ζ` for `Re s > 1` is already in Mathlib
(`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`), as is the theorem that a
log-derivative has a simple pole at a zero (`meromorphicOrderAt_logDeriv_eq_neg_one`).

**New in the formal sense:** as far as we can find, nobody has formally stated

1. the quasi-Riemann hypothesis as a Lean `Prop` outside OpenAI's own repository
   (Google DeepMind's `formal-conjectures` has no such statement; checked on its `main`);
2. the **characterisation** `ZeroFreeRight θ ↔ DifferentiableOn ℂ (−ζ′/ζ) {θ < Re s, s ≠ 1}`,
   which turns OpenAI's statement about *zeros* into an equivalent statement about the
   *prime-counting series*.

That is a modest contribution. It is a correct, checked, reusable first step — not a result.

## Contribution paths found during the research

1. **`formal-conjectures` (small, concrete, ready).** The repo has RH, GRH, and four RH
   equivalents, but **no quasi-RH**. Its contribution guide provides exactly the right mechanism:
   `@[category research solved, AMS 11, formal_proof using lean4 at "<url>"]`, linking to
   `OAI/NumberTheory/DirichletL/Nonvanishing.lean` at a pinned commit. Their guide "strongly
   recommends" a Palomar entry for research proofs; OpenAI's result is **not** on Palomar
   (checked against the registry's 200-entry recent feed, 22 Oct 2026), so whether to mark it
   `solved` is the maintainers' call. A PR adding the *statement* with an honest docstring is
   uncontroversial either way.
2. **Mathlib (small).** `riemannZeta_not_eventually_zero` / the order-−1 lemma at zeros of ζ are
   natural Mathlib lemmas near `NumberTheory/LSeries/ZetaZeros.lean` (which already has
   `isDiscrete_riemannZetaZeros`).
3. **Palomar (large, later).** A registry entry needs "credible research interest". The chapters
   below build toward one that would qualify (chapter 6).

## Roadmap

Each chapter is one file, sorry-free before the next one starts.

| # | Chapter | Mathematical content | Difficulty |
|---|---|---|---|
| 1 | ✅ `Basic` | zero-free ⇒ prime series continues | glue |
| 2 | ✅ `Characterisation` | …and conversely (zeros = poles) | small |
| 3 | `Dirichlet` | the same for every Dirichlet L-function, `−L′/L(χ) = ∑ χ(n)Λ(n)n^{-s}` — OpenAI's *main* theorem is about all of these, and Mathlib has `LSeries_twist_vonMangoldt_eq` | small, same template |
| 4 | `PoleAtOne` | `−ζ′/ζ(s) − 1/(s−1)` is holomorphic on `Re s > θ` (removes the pole at 1) — the exact input for prime-counting error terms | medium |
| 5 | `InghamEasy` | `ψ(x) − x = O(x^{θ+ε}) ⇒ ZeroFreeRight θ`, by Abel summation: regular primes force a zero-free half-plane | medium |
| 6 | `InghamHard` | `ZeroFreeRight θ ⇒ ψ(x) = x + O(x^{θ+ε})`. **Combined with OpenAI's proof, this gives `ψ(x) = x + O(x^{7/8+ε})` — the first power-saving error term in the prime number theorem in any proof assistant.** That would be Palomar-worthy. Needs contour integration / Perron; `PrimeNumberTheoremAnd` and `math-inc/strongpnt` (both already in OpenAI's dependency set) likely contain most of the analytic machinery | hard |

Chapter 6 is the real target. Chapters 3–5 are the honest steps toward it.
