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
| **`Fugue.card_sq_add_sq`** (Jacobi two squares) | `NumberTheory/SumTwoSquares.lean` | the strongest Mathlib candidate here: a named classical theorem absent from Mathlib, 486 lines, needs Mathlib-style cleanup |
| `Fugue.ArithmeticFunction.not_isPrincipalIdealRing` | `NumberTheory/ArithmeticFunction/…` | curiosity; short |
| `Fugue.pmul_log_mul` | `NumberTheory/ArithmeticFunction/VonMangoldt.lean` | `·log` is a derivation of the Dirichlet ring; check it is not already there under another name |

## 3. Palomar — Ingham's theorem (ready, needs a human to publish)

Project: [`../../PalomarIngham`](../../PalomarIngham/README.md) (Lean v4.35.0, Mathlib v4.35.0,
every file a `module`, PrimeNumberTheoremAnd vendored under Apache-2.0).

* `Challenge.lean` (Mathlib only, no new definitions) states:
  `zeta_ne_zero_iff_psi_error` (1/2 ≤ θ < 1: zero-free right of θ ⟺ ψ(x) = x + O(x^{θ+δ}) ∀δ>0),
  `riemannHypothesis_iff_psi_error`, and `psi_error_of_zeta_ne_zero_seven_eighths` (OpenAI's
  hypothesis verbatim ⇒ ψ(x) = x + O(x^{7/8+δ})).
* `lake comparator` (built into Lean v4.35.0, sandboxed with bubblewrap): **"Lean default kernel
  accepts the solution — Your solution is okay!"**
* Palomar's mechanical rules checked by hand: toolchain ≥ v4.35.0-rc2 and equal to Mathlib's;
  `lake-manifest.json` committed; all 27 `.lean` files start with `module`; largest file 3511
  lines; no `sorry`/`native_decide` outside the Challenge.
* Remaining human steps: fill the `TEMPLATE` names in `formalization.yaml`, push to a public
  GitHub repository, submit the 40-character SHA at <https://submit.palomar-registry.org/>.
* Bar check: recent Palomar entries include classical results registered "with no novelty or
  priority claim", so a classical theorem is admissible; the new ingredient here is the
  conditional consequence of OpenAI's 2026 result, and (as far as we found) the first
  machine-checked power-saving PNT error term statement.
