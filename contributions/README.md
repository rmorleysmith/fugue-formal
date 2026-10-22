# Contribution packages

Things in this workspace that are ready (or nearly ready) to go to someone else's repository,
ordered from smallest to largest. Nothing here has been submitted; each needs a human decision.

## 1. `formal-conjectures` — the quasi-Riemann hypothesis (ready)

File: [`formal-conjectures/QuasiRiemannHypothesis.lean`](formal-conjectures/QuasiRiemannHypothesis.lean)
→ destination `FormalConjectures/Paper/QuasiRiemannHypothesis.lean`.

* **Builds** inside a clone of `google-deepmind/formal-conjectures` at commit
  `5be487be1b2dd553821e3c8a9b34f6caa9f0e6e0` (Lean v4.33.1):
  `lake build FormalConjectures.Paper.QuasiRiemannHypothesis` — 8964 jobs, no errors.
* Contents: `ZeroFreeRight θ`; `quasi_riemann_hypothesis` (∃ θ < 1);
  `riemannZeta_ne_zero_of_seven_eighths_lt_re`; the Dirichlet version — each
  `@[category research solved, AMS 11, formal_proof using lean4 at …]` pointing at OpenAI's
  Lean file pinned at commit `1581d4cb…`, lines 29 and 19. Plus two `category test` sanity
  checks (θ = 1 holds; θ < −2 fails because ζ(−2) = 0), proved, and one `category API` lemma
  (RH ⇒ θ = ½), proved.
* As in the rest of that repository, the research statements have `sorry` bodies: the database
  records statements, the attribute records where the proof lives.
* **Open question for the maintainers:** their guide recommends a Palomar entry for research
  proofs. OpenAI's result is not on Palomar (checked against the registry's recent feed). Marking
  it `solved` on the strength of OpenAI's Lean file is their call; the PR description should say
  so.

## 2. Mathlib — candidate lemmas (need polishing to Mathlib style)

| Lemma (this workspace) | Proposed home | Notes |
|---|---|---|
| `Fugue.eq_zero_at_rho`, `Fugue.eq_zero_at_I`, `E₄_rho`, `E₆_I` | `NumberTheory/ModularForms/LevelOne/…` | Mathlib has `E₄`, `E₆`, `Δ = (E₄³−E₆²)/1728` but (as of `d13f23b`) not the elliptic-point vanishing |
| `QuasiRH.riemannHypothesis_iff_zeroFreeRight_half` | `NumberTheory/LSeries/RiemannZeta.lean` | RH as a half-plane statement, via `riemannZeta_one_sub` |
| `QuasiRH.zeroFreeRight_of_psiError`, `riemannHypothesis_of_psiError` | `NumberTheory/Chebyshev.lean` or a new file | "PNT error `O(x^θ)` ⇒ no zeros right of θ"; uses only Mathlib (`LSeries_eq_mul_integral`, Mellin holomorphy) |
| `QuasiRH.zeroFree_iff_differentiableOn_negLogDeriv` | `Analysis/Meromorphic/…` | general: zero-free ⟺ `−f′/f` holomorphic |
| `Fugue.ArithmeticFunction.not_isPrincipalIdealRing` | `NumberTheory/ArithmeticFunction/…` | curiosity; short |
| `Fugue.pmul_log_mul` | `NumberTheory/ArithmeticFunction/VonMangoldt.lean` | `·log` is a derivation of the Dirichlet ring; check it is not already there under another name |

## 3. Palomar — the candidate (in progress, `../../FormalPNT`)

**Statement** (Challenge imports only Mathlib):

> If `ζ(s) ≠ 0` for `Re s > θ` with `1/2 ≤ θ < 1`, then `ψ(x) = x + O(x^{θ+δ})` for every
> `δ > 0`. Combined with OpenAI's theorem: `ψ(x) = x + O(x^{7/8+δ})`.

Status: interfaces fixed and building (`FormalPNT/Ingham/Basic.lean`); the three proof pieces
are being written. "Credible research interest": the unconditional instance is a new
consequence of a 2026 result, and — as far as we could find — no proof assistant has a
machine-checked power-saving error term in the prime number theorem (PrimeNumberTheoremAnd has
RH-conditional ones only as `sorry`'d blueprint statements; OpenAI's `PrimeCounting` files use
Wiener–Ikehara, i.e. no error term).
