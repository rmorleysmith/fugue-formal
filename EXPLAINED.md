# What we proved, explained

This is written so you can explain every piece in your own words, at three levels: one
sentence, one paragraph, and "what a referee would ask". The Lean names are given so you can
point at the exact checked statement.

---

## The one-minute version

> The primes are encoded in the function `−ζ′(s)/ζ(s)`, which for `Re s > 1` is literally the
> series `∑ Λ(n) n^{-s}` over prime powers. That function blows up exactly where `ζ` has a zero.
> So "`ζ` has no zeros to the right of θ" and "the prime series extends smoothly to the right of
> θ" are **the same statement**. We proved that equivalence in Lean, and used it to restate
> OpenAI's quasi-Riemann theorem — a claim about *zeros* — as an equivalent claim about *primes*.

---

## The objects

**`ζ(s)`, the Riemann zeta function.** For `Re s > 1` it is `∑ n^{-s}`. It extends to all of `ℂ`
except a simple pole at `s = 1`. (Lean quirk: Mathlib assigns `ζ(1)` the junk value
`(γ − log 4π)/2`, which is nonzero. Every theorem below handles `s = 1` explicitly.)

**`Λ(n)`, the von Mangoldt function.** `Λ(n) = log p` if `n = p^k` is a prime power, else `0`.
It is "the primes, weighted by their logarithms". Summing it gives Chebyshev's
`ψ(x) = ∑_{n≤x} Λ(n)`, and the prime number theorem is `ψ(x) ~ x`.

**The bridge, `∑ Λ(n) n^{-s} = −ζ′(s)/ζ(s)` for `Re s > 1`.** Take the log of the Euler product
`ζ(s) = ∏_p (1 − p^{-s})^{-1}` and differentiate. In the corpus' language this is
"the Lie derivative gives the primes": in the Dirichlet ring, `log * μ = Λ`, where multiplying by
`log n` is the derivation `D` and `μ` is the inverse of `ζ`. Applying `L` turns `D` into `−d/ds`
and `μ` into `1/ζ`. Mathlib: `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.

**`ZeroFreeRight θ`** (`QuasiRH.ZeroFreeRight`): `ζ(s) ≠ 0` whenever `θ < Re s`.

**`QuasiRiemannHypothesis`**: `ZeroFreeRight θ` for **some** `θ < 1`. This is the classical name
for the problem. Before October 2026 nobody could do *any* `θ < 1`: the best known zero-free
regions (de la Vallée Poussin, Vinogradov–Korobov) shrink toward `Re s = 1` as `|Im s| → ∞`.

**`OpenAIStatement`**: `ZeroFreeRight (7/8)`, copied character-for-character from OpenAI's Lean
comparator challenge. We **assume** it; we do not prove it.

---

## Chapter 1 — `QuasiRH/Basic.lean`

**`zeroFreeRight_one`** — `ζ` has no zeros with `Re s > 1`.
*One line:* the Euler product converges there and a convergent product of nonzero factors is
nonzero. (Mathlib proves the stronger `Re s ≥ 1`, which is the hard 1896 theorem.)

**`zeroFreeRight_half_of_RH`** — RH implies `ZeroFreeRight (1/2)`.
*One line:* RH says every nontrivial zero has `Re s = 1/2`; we check a zero with `Re s > 1/2` can't
be a trivial zero (those are at `−2, −4, …`) or the point `1`, so RH applies and contradicts.
*Why it is worth a lemma:* it is the sanity check that our definition is the right one — RH is
the strongest possible quasi-RH.

**`differentiableOn_negLogDerivZeta`** — if `ZeroFreeRight θ`, then `−ζ′/ζ` is holomorphic on
`{θ < Re s, s ≠ 1}`.
*One line:* `ζ` and `ζ′` are holomorphic away from `1`, and a quotient of holomorphic functions
is holomorphic wherever the denominator is nonzero.

**`vonMangoldt_LSeries_continuation`** — packages the above: there is a holomorphic `F` on that
region with `F(s) = ∑ Λ(n) n^{-s}` for `Re s > 1`. *The prime series continues analytically.*

**`vonMangoldt_LSeries_continuation_of_openAI`** — the same with `θ = 7/8`, from OpenAI's
statement.

---

## Chapter 2 — `QuasiRH/Characterisation.lean`

This is the chapter with actual content: the converse.

**`riemannZeta_not_eventually_zero`** — `ζ` is not identically zero near any point `s ≠ 1`.
*One line:* if it were, the identity theorem (analytic functions on a connected set that agree
near one point agree everywhere) would make it zero on all of `ℂ \ {1}`, but `ζ(2) = π²/6`.
*Referee question: why does connectedness matter?* On a disconnected set an analytic function
can be zero on one piece and not another. `ℂ` minus a point is connected; the proof uses
Mathlib's `isConnected_compl_singleton_of_one_lt_rank` (removing a point from a real space of
dimension > 1 keeps it connected — `ℂ` has real dimension 2).

**`meromorphicOrderAt_negLogDerivZeta`** — at a zero `ρ ≠ 1` of `ζ`, `−ζ′/ζ` has meromorphic
order exactly `−1`: a simple pole.
*One paragraph:* by the previous lemma the zero has some finite order `m ≥ 1`, so
`ζ(s) = (s−ρ)^m g(s)` with `g(ρ) ≠ 0`. Differentiating, `ζ′/ζ = m/(s−ρ) + g′/g`. The second
term is holomorphic near `ρ`; the first is a pole of order 1 with residue `m`. Mathlib does the
calculation in general (`meromorphicOrderAt_logDeriv_eq_neg_one`); our job is to verify its
hypotheses for `ζ` — finite and nonzero order — which is where the identity theorem enters.
*Nice fact for later:* the residue is the multiplicity `m`. That is why
`(1/2πi)∮ ζ′/ζ = (number of zeros inside)`, the argument principle behind zero-counting.

**`zeroFreeRight_iff_differentiableOn`** — **the characterisation**:

  `ZeroFreeRight θ  ⟺  −ζ′/ζ is holomorphic on {θ < Re s, s ≠ 1}`.

*One line:* forward is chapter 1; backward because a zero would be a pole, and poles are not
holomorphic.

**`openAIStatement_iff_differentiableOn`** — OpenAI's theorem is *equivalent* to `−ζ′/ζ` being
holomorphic on `{7/8 < Re s, s ≠ 1}`. A statement about zeros, turned into a statement about the
analytic continuation of the prime series.

**`quasiRiemannHypothesis_iff`** — the quasi-RH is equivalent to: for some `θ < 1`, `−ζ′/ζ`
is holomorphic on `{θ < Re s, s ≠ 1}`.

---

## Continuation — `QuasiRH/Continuation.lean`

**`zeroFreeRight_of_eqOn`** — if *any* function `G` is holomorphic on `{θ < Re s, s ≠ 1}` and
equals `∑ Λ(n) n^{-s}` on `Re s > 1`, then `ζ` has no zeros with `Re s > θ`.
*Why this is needed:* chapter 2 talks about the specific function `−ζ′/ζ`. In practice you
never have that in hand to the left of `Re s = 1`; you have some *formula* (an integral, say)
that agrees with it on `Re s > 1`. This lemma says the formula is enough.
*One paragraph:* `ζ·G` and `−ζ′` are holomorphic on the region and agree on `Re s > 1`; the
region is connected, so by the identity theorem they agree everywhere on it. Near a zero `ρ`
(zeros are isolated) that means `G = −ζ′/ζ` on a punctured disc around `ρ`, so `G` would inherit
the pole of chapter 2 — but `G` is holomorphic at `ρ`. Contradiction.
*Referee question: why is the region connected?* It is a half-plane minus one point. The proof
(`isPreconnected_region`) covers it with four convex pieces — upper half, lower half, right of
`Re s = 1`, and the strip `θ < Re s < 1` — each meeting the next.

---

## Reflection — `QuasiRH/Reflection.lean`

**`riemannHypothesis_iff_zeroFreeRight_half`** — RH ⟺ `ZeroFreeRight (1/2)`.
*One paragraph:* suppose no zeros right of `1/2` and `ρ` is a nontrivial zero with
`Re ρ < 1/2`. The functional equation (Mathlib's `riemannZeta_one_sub`) says
`ζ(ρ) = 2(2π)^{−(1−ρ)} Γ(1−ρ) cos(π(1−ρ)/2) ζ(1−ρ)`. The left side is `0`; on the right `Γ` never
vanishes, the power never vanishes, and `ζ(1−ρ) ≠ 0` because `Re(1−ρ) > 1/2`. So the cosine
would vanish, which forces `ρ` to be an even integer `≤ 0` — that is `0` (but `ζ(0) = −1/2`) or a
trivial zero (excluded). So nontrivial zeros sit on `Re s = 1/2`.

---

## Chapter 5 — `QuasiRH/InghamEasy.lean`: regular primes force a zero-free region

**`PsiError θ`** — `ψ(x) − x = O(x^θ)`: "the prime number theorem with error exponent `θ`".

**`zeroFreeRight_of_psiError`** — `PsiError θ ⇒ ZeroFreeRight θ`.
*The proof in four lines:* for `Re s > 1`, partial summation gives
`∑ Λ(n)n^{-s} = s∫₁^∞ ψ(t) t^{−s−1} dt = s/(s−1) + s∫₁^∞ (ψ(t)−t) t^{−s−1} dt`. If
`ψ(t) − t = O(t^θ)`, the last integral converges — and is holomorphic — for `Re s > θ`. So the
right-hand side is a `G` as in the continuation lemma, and that lemma finishes.
*Which Mathlib tools:* `LSeries_eq_mul_integral` (partial summation for Dirichlet series) and
`mellin_differentiableAt_of_isBigO_rpow` (a Mellin transform of an `O(t^θ)` function is
holomorphic where it converges).

**`riemannHypothesis_of_psiError`** — if `ψ(x) = x + O(x^{1/2+ε})` for every `ε > 0`, RH holds.
This is one direction of the classical "RH ⟺ square-root error in the prime number theorem". The
other direction (von Koch 1901, ε-version) is the hard one; it is the target below.

**`psiError_one`** — Chebyshev: `ψ(x) − x = O(x)`. Not interesting in itself: it is the
non-vacuity check. `PsiError` holds at `θ = 1` and *fails* at `θ = −3` (the audit derives
`¬PsiError(−3)` from the trivial zero `ζ(−2) = 0`). Everything strictly between is the
mathematics; `θ = 1/2 + ε` is RH.

---

## Chapter 3 — `QuasiRH/Dirichlet.lean`: every Dirichlet L-function

OpenAI's theorem covers every `L(s, χ)`, not only `ζ`. Primes in an arithmetic progression
`a mod q` are counted by `∑ χ(n)Λ(n)n^{-s} = −L′/L(s, χ)` (Mathlib: `LSeries_twist_vonMangoldt_eq`).

**`zeroFree_iff_differentiableOn_negLogDeriv`** — the chapter-2 argument for *any* `f`
holomorphic on `ℂ \ {1}` that is not identically zero.

**`zeroFreeRightL_iff`** — `L(s, χ)` zero-free right of `θ` ⟺ `−L′/L` holomorphic on the region.

**`twistedVonMangoldt_continuation_of_openAI`** — granting OpenAI's Dirichlet statement (copied
from their Lean), every twisted prime series continues to `{7/8 < Re s, s ≠ 1}`.

**`openAIStatement_of_dirichlet`** — the Dirichlet statement contains the `ζ` statement (the
character mod 1 has `L(s, χ) = ζ(s)`).

---

## Chapter 6 — `../FormalPNT/Ingham/`: zero-free ⇒ primes are regular

**Target:** if `ζ(s) ≠ 0` for `Re s > θ` (`1/2 ≤ θ < 1`), then `ψ(x) = x + O(x^{θ+δ})` for every
`δ > 0`. With OpenAI's theorem: `ψ(x) = x + O(x^{7/8+δ})`.

*The proof in one paragraph.* Replace `ψ(X)` by a smoothed version `ψ_ε(X)`, which costs
`O(εX log X)`. The smoothed version is a contour integral `(1/2πi)∫ −ζ′/ζ(s) M_ε(s) X^s ds` over
the line `Re s = 1 + 1/log X`. Move the line left to `Re s = σ₁` (just right of `θ`): the only
singularity crossed is the pole at `s = 1`, whose residue is `X·M_ε(1) ≈ X` — the main term.
What is left are integrals on the new line and two short horizontal pieces. On the new line
`|X^s| = X^{σ₁}`, so if `−ζ′/ζ` is not too large there, everything left is `O(X^{σ₁+small})`.
The zero-free hypothesis is what makes `−ζ′/ζ` small: it gives `|ζ′/ζ(σ + it)| ≤ K log|t|` for
`σ ≥ σ₁` (Borel–Carathéodory applied to `log ζ`, which exists because `ζ` has no zeros there).
Choosing `ε = X^{σ₁−1}` balances the smoothing error against the main error.

*What is reused:* PrimeNumberTheoremAnd provides the smoothing, the contour shift with its
residue, and bounds for the far vertical pieces. *What is new:* the log-derivative bound on a
whole half-plane, the bounds on the new line and horizontal pieces, and the assembly.

*State:* ✅ complete and sorry-free (`../FormalPNT/Audit.lean`: 11 theorems, standard axioms).
Headline theorems:

* `Ingham.zeroFreeRight_iff_psiError` — for `1/2 ≤ θ < 1`: **no zeros right of `θ` ⟺
  `ψ(x) = x + O(x^{θ+δ})` for every `δ > 0`.** (Hard direction here, easy direction chapter 5.)
* `Ingham.riemannHypothesis_iff_psiError` — RH ⟺ `ψ(x) = x + O(x^{1/2+δ})` for every `δ > 0`.
* `Ingham.openAIStatement_iff_psiError` — OpenAI's theorem ⟺ `ψ(x) = x + O(x^{7/8+δ})`.

*Referee questions.* (1) *Why `1/2 ≤ θ`?* Only to get a polynomial bound `|ζ(s)| ≪ |t|` on the
discs used by Borel–Carathéodory; no zero-free half-plane with `θ < 1/2` can exist anyway (there
are zeros on the critical line), though Lean does not know that. (2) *Where exactly is OpenAI's
theorem used?* Only as the hypothesis `ZeroFreeRight (7/8)`; their proof is not imported, so the
unconditional `ψ(x) = x + O(x^{7/8+δ})` is "our Lean proof + their Lean proof", not a single
checked artefact yet. (3) *Why `δ` and not `(log x)²`?* The `ε`-loss comes from the log-derivative
bound and the smoothing; the sharper `x^θ (log x)²` needs zero-counting, which we avoided.

---

## Chapter 7 — `../PalomarIngham/PalomarIngham/Dirichlet/`: primes in arithmetic progressions

**Target and state (✅, sorry-free, Comparator passes):** for a fixed modulus `q` and `a` coprime
to `q`, if `ζ` and every `L(s, χ)` (`χ ≠ 1` mod `q`) have no zeros right of `θ`, then
`ψ(x; q, a) = x/φ(q) + O(x^{θ+δ})`. With OpenAI's Dirichlet theorem: error `O(x^{7/8+δ})`.

*The proof in one paragraph.* Characters separate residue classes:
`ψ(x; q, a) = φ(q)⁻¹ Σ_χ χ̄(a) ψ(x, χ)` with `ψ(x, χ) = Σ_{n≤x} χ(n)Λ(n)`. The trivial character
gives `ψ(x)` up to `O(log x)` (prime powers dividing `q`), handled by chapter 6. Each `χ ≠ 1` is
chapter 6 again with `−L′/L(s, χ)` in place of `−ζ′/ζ` — but now there is *no* main term, because
`L(s, χ)` is entire (no pole at `s = 1`), so the contour shift picks up no residue and `ψ(x, χ)`
is pure error, `O(x^{θ+δ})`. The one genuinely new analytic input is a polynomial bound for
`L(s, χ)` on `Re s ≥ 1/2`, obtained by continuing `L` to `Re s > 0` with an explicitly convergent
series (subtracting a block-constant comparison series whose character sum vanishes).

*Referee questions.* (1) *Is the constant uniform in `q`?* No; the statement is for each fixed `q`.
Uniformity (Siegel–Walfisz type) is a different and much deeper matter. (2) *Why does OpenAI's
theorem suffice for every `q` at once?* Their statement is uniform: one `7/8` for every
Dirichlet character of every modulus.

---

## The Fugue library — theorems extracted from the corpus

Each file cites the ledger rows (`Fugue/02-threads/evidence-ledger.md`) it settles.

### `Fugue/TwoRings.lean` — the corpus' two products on one carrier

The corpus stores a "DNA" as a sequence `a(n)` and multiplies DNAs two ways: **Ring A** is the
Cauchy product (multiplying `q`-series, `PowerSeries`), **Ring B** the Dirichlet product
(multiplying `∑ a(n)n^{-s}`, `ArithmeticFunction`).

* **`not_ringEquiv_powerSeries`** — over a field, the two rings are **not isomorphic**.
  *Why:* every ideal of `K⟦X⟧` is principal; in the Dirichlet ring the ideal "multiples of `δ₂` or
  `δ₃`" is not. *The proof, by hand:* if `(δ₂, δ₃) = (g)`, then `g(1) = 0`; write `δ₂ = hg`,
  `δ₃ = h′g`; at `n = 2`: `h(1)g(2) = 1` and `h′(1)g(2) = 0`, so `h′(1) = 0`; at `n = 3`:
  `1 = h′(1)g(3) + h′(3)g(1) = 0`. *Conceptually:* Ring A has one generator (`X`); Ring B has one
  per prime.
* `cauchy_ne_dirichlet` (ledger C1), `delta_is_X` (C3: the Dirichlet identity is the *variable*
  `X` in Ring A), `sigma_three_ne_zeta_pow_four` (C8 refutation: `σ₃(2) = 9`, `ζ⁴(2) = 4`),
  `pmul_log_mul` (C9: multiplying by `log n` is a derivation — the arithmetic shadow of `−d/ds`),
  `multiplicativeSubmonoid` (C11) and `zeta_add_zeta_not_multiplicative` (it is not closed under
  addition: "compose" must mean multiply).

### `Fugue/EllipticPoints.lean` — why `E₄(ρ) = 0`

* **`eq_zero_at_rho`** — *every* level-one modular form of weight `k` with `6 ∤ k` vanishes at
  `ρ = e^{2πi/3}`. *Why:* `γ = [[0,−1],[1,1]]` fixes `ρ` with automorphy factor `ρ + 1 = e^{iπ/3}`,
  a primitive 6th root of unity `u`; modularity says `f(ρ) = u^k f(ρ)`, and `u^k ≠ 1`.
* **`eq_zero_at_I`** — weight `k` with `4 ∤ k` vanishes at `i` (`S` fixes `i` with factor `i`).
* `E₄_rho`, `E₆_I`; and, using Mathlib's `1728Δ = E₄³ − E₆²` and `Δ ≠ 0`: `E₄_I_ne_zero`,
  `E₆_rho_ne_zero`. At weight 12 both forced zeros disappear (`Δ` never vanishes) — the concrete
  content of ledger refutation A8.

### `Fugue/Dynamics.lean` — neurons, attractors, and the coupling matrix

* **`eq_zero_of_isLocalMin_norm`** (ledger A9) — a local minimum of `|F|` where `F` is not locally
  constant is a zero. *Why:* otherwise `1/F` is holomorphic with a local *maximum* of `|1/F|`, and
  the maximum modulus principle makes it constant.
* **`couplingMatrix_posSemidef_iff`** / **`couplingMatrix_posDef_iff`** (E2/E5) — the corpus'
  `K(κ) = [[y₁², κy₁y₂],[κy₁y₂, y₂²]]` is PSD iff `|κ| ≤ 1`, PD iff `|κ| < 1`. *Why:*
  `xᵀKx = (y₁x₀ + κy₂x₁)² + (1−κ²)(y₂x₁)²`.
* **`equilibrium_preserved`** (E3, sharpened) — common zeros stay equilibria for *any* `K`;
  positivity is not needed for that. What PSD buys is descent (`descends_iff`).

### `Fugue/Theta.lean` — why direct sums multiply theta series

* **`theta_directSum`** — for any two "norm maps" with finite fibres,
  `Θ_{Q₁⊕Q₂} = Θ_{Q₁} · Θ_{Q₂}` as power series. *Why:* a vector of the direct sum has norm `n`
  exactly when its two components have norms `a` and `b` with `a + b = n`, so
  `r(n) = Σ_{a+b=n} r₁(a) r₂(b)` — and that is the Cauchy product. For `E8 ⊕ E8` this is the
  corpus' `Θ = E₄²`. It also settles ledger B9: "direct sum" and "tensor product" of DNAs are the
  same coefficient operation.

### `Fugue/TwoSquares.lean` — Jacobi's two-square theorem

* **`card_sq_add_sq`** — the number of integer pairs `(a, b)` with `a² + b² = n` is
  `4·Σ_{d∣n} χ₋₄(d)`, where `χ₋₄(d)` is `+1` for `d ≡ 1`, `−1` for `d ≡ 3 (mod 4)`, `0` for even `d`.
  E.g. `n = 5`: divisors 1, 5 give `4(1+1) = 8` — `(±1,±2), (±2,±1)`.
  *Why (one paragraph):* pairs `(a,b)` are Gaussian integers `a+bi` of norm `n`. Peel off the
  smallest prime `p ∣ n`. If `p = 2`, everything of norm `2k` is `(1+i)` times something of norm
  `k`. If `p ≡ 3 (mod 4)`, `p` stays prime in `ℤ[i]`, so it divides everything of norm `pk` —
  either the count is `0` or you divide by `p²`. If `p ≡ 1 (mod 4)`, `p = ππ̄` splits into two
  different primes, and everything of norm `pk` is `π` or `π̄` times something of norm `k`, with
  the overlap being the multiples of `p`. The divisor sum obeys exactly the same three rules, and
  both start at `n = 1` with values `4` and `1`. *Corpus link:* ledger C6, `ζ·L(s,χ₋₄) = ζ_{ℚ(i)}`
  at the level of coefficients.

### `Fugue/E8Lattice.lean` — the E8 lattice and `E8 ⊕ E8`

* **`e8Form_even`, `e8Form_pos`** — for the E8 Cartan matrix `A`, `xᵀAx` is even and positive for
  `x ≠ 0`. With Mathlib's `det A = 1`, that is "E8 is an even unimodular positive definite
  lattice" (ledger A1). *Why positive:* completing squares gives
  `xᵀAx = 2y₀² + 2y₁² + (3/2)y₂² + (5/6)y₃² + (4/5)y₄² + (3/4)y₅² + (2/3)y₆² + (1/2)x₇²` with each
  `yᵢ` an `xᵢ` minus a multiple of a later `x`; all coefficients are positive, and if the sum is
  `0`, back-substitution from `x₇` forces `x = 0`.
* **`theta_e8_sum_e8`** — `Θ_{E8⊕E8} = Θ_{E8}²`, from the direct-sum theorem; the needed
  finiteness (`e8_finite_fibre`) comes from the same completed squares bounding every coordinate.
  (That `Θ_{E8} = E₄` is *not* formalised — it needs theta functions as modular forms.)

### `Fugue/LeibnizL.lean` — `L(1, χ₋₄) = π/4`

* **`LFunction_chi4_one`** — the Dirichlet `L`-function of the character mod 4 takes the value
  `π/4` at `s = 1` (ledger D6; Dirichlet's class number formula for `ℚ(i)`: `h = 1`, `w = 4`).
  *Why it is not a one-liner:* `L(s, χ)` is *defined* by its series only for `Re s > 1`; at `s = 1`
  it is the value of the analytic continuation. *The proof:* for real `s > 1`,
  `L(s, χ₋₄) = Σ_k ((4k+1)^{−s} − (4k+3)^{−s})`; each bracket is between `0` and `8/(k+1)²`, so
  dominated convergence lets `s → 1⁺` inside the sum, giving Leibniz's `1 − 1/3 + 1/5 − … = π/4`;
  and `L` is continuous at `1` because it is entire (`χ₋₄ ≠ 1`).

### `Fugue/Ramanujan.lean` — where the two rings meet

* **`E₄sq_eq`** — `E₄² = E₈`. *Why:* level-one modular forms of weight 8 form a one-dimensional
  space (Mathlib's dimension formula), both sides lie in it, and both have constant term 1.
* **`sigma_seven_eq`** — `σ₇(n) = σ₃(n) + 120 Σ_{0<a<n} σ₃(a) σ₃(n−a)`. *Why:* read off the
  `qⁿ`-coefficient of `E₄² = E₈`, with `E₄ = 1 + 240Σσ₃(n)qⁿ`, `E₈ = 1 + 480Σσ₇(n)qⁿ`. The left
  side multiplies power series (Ring A, Cauchy product); the coefficients `σ_k = ζ * Id^k` are
  Dirichlet products (Ring B). This is the precise version of the corpus' claim that Ramanujan's
  Eisenstein identities "link back to divisors and zeta": the rings are *different* (see
  `not_ringEquiv_powerSeries`), and modularity is what makes a Ring-A product of Ring-B objects land
  back in Ring B. Check at `n = 2`: `129 = 9 + 120·1`.

### `Fugue/HeckeRefutation.lean` — a corpus claim refuted in Lean

* **`discriminant_mul_E₄_not_multiplicative_eigenvalue`** — the corpus said the product of two
  Hecke eigenforms is an eigenform with the *product* eigenvalues. For `Δ = q − 24q² + …` and
  `E₄ = 1 + 240q + 2160q² + …`, the `q²`-coefficient of `Δ·E₄` is `1·240 + (−24)·1 = 216`, while
  `a₂(Δ)·a₂(E₄) = −24·2160 = −51840`. *Where the numbers come from:* `τ(2) = −24` (`tau_two`) is
  computed in Lean from `Δ = (E₄³ − E₆²)/1728` and Mathlib's Eisenstein coefficients
  `240σ₃(n)`, `−504σ₅(n)`. The correct closure law is about coefficient *sequences* being
  multiplicative (ledger C11), not about eigenvalues multiplying.

### `Fugue/ThetaE8*.lean` — `Θ_{E8} = E₄`

* **`thetaE8_eq_E₄`** — `Σ_{v∈E8} q^{‖v‖²/2} = E₄(τ)`. *Two steps.* (1) In doubled coordinates
  E8 is `{y ∈ ℤ⁸ : all yᵢ of the same parity, Σyᵢ ≡ 0 mod 4}`, i.e. `D8 ∪ (D8 + ½𝟙)`; splitting by
  parity and using `(−1)^{Σxᵢ}` to select even sums turns the 8-dimensional sum into products of
  one-dimensional theta functions: `Θ_{E8} = (θ₂⁸ + θ₃⁸ + θ₄⁸)/2`. (2) That combination is invariant
  under `τ ↦ τ+1` (θ₃ ↔ θ₄, θ₂ gains `e^{πi/4}`, killed by the 8th power) and transforms with `τ⁴`
  under `τ ↦ −1/τ`, so it is a weight-4 level-one modular form tending to 1 at `i∞`; `dim M₄ = 1`
  forces it to be `E₄`.
* **`reprCount_e8`** — the number of E8 vectors of norm `2n` is `240 σ₃(n)`: 240 roots, 2160 vectors of
  norm 4, 6720 of norm 6 — the corpus' numerical checks, now theorems. *Why:* both sides of
  `Θ_{E8} = E₄` are `q`-series; regrouping the lattice sum by norm gives coefficients `#{v : ‖v‖² = 2n}`,
  and `q`-expansion coefficients are unique.

### `Fugue/HeckeE4.lean` — the Eisenstein road: E₄ knows ζ's functional equation

* **`heckeE4_functional_equation`, `heckeE4_eq`** — let `Λ` be the Mellin transform of `E₄(iy) − 1`.
  For `Re s > 4`, `Λ(s) = 240(2π)^{−s}Γ(s)ζ(s)ζ(s−3)`; `Λ` continues to `ℂ` except simple poles at
  `0` and `4` (residues `−1`, `1`), and `Λ(4 − s) = Λ(s)`. *Why:* `E₄(i/y) = y⁴E₄(iy)` is modularity
  under `S : τ ↦ −1/τ`; splitting the Mellin integral at `y = 1` and substituting `y ↦ 1/y` on the
  lower half turns this symmetry of `E₄` into the symmetry `s ↔ 4 − s` of `Λ` (Mathlib's abstract
  `WeakFEPair` machinery does the analysis). The coefficients `240σ₃(n)` turn the Mellin transform
  into `Σσ₃(n)n^{−s} = ζ(s)ζ(s−3)`. *Lesson (D3):* the symmetry is genuine and the zeros are not on
  its axis `Re s = 2` at all — symmetry does not locate zeros.

### `Fugue/HeckeEk.lean` — all weights, and a forced zero

* **`heckeEk_functional_equation`** — for `E_k` the symmetry is `Λ_k(k − s) = (−1)^{k/2} Λ_k(s)`
  (the sign is `i^k`, from `E_k(i/y) = (iy)^k E_k(iy)`). **`heckeE6_centre_eq_zeta`**: at `k = 6`
  the sign `−1` forces `Λ₆(3) = −Λ₆(3)`, so `Λ₆(3) = 0`; unfolding, `Λ₆(3)` contains the factor
  `ζ(3 − 5) = ζ(−2) = 0` — the forced zero is a trivial zero.

### `Fugue/RankinSelberg.lean` — Ramanujan's formula, the Rankin–Selberg prototype

* **`LSeries_sigma_mul_sigma`** — `Σ σ_a(n)σ_b(n) n^{−s} = ζ(s)ζ(s−a)ζ(s−b)ζ(s−a−b)/ζ(2s−a−b)`.
  *Why:* the *pointwise* product of two multiplicative functions is multiplicative (the corpus'
  C11 closure law), so both sides are Euler products and it suffices to compare one prime: there it
  is the power-series identity `Σ_k σ_a(p^k)σ_b(p^k)X^k = (1 − p^{a+b}X²)/((1−X)(1−p^aX)(1−p^bX)(1−p^{a+b}X))`.
  Sanity case `a = b = 0`: `Σ d(n)² n^{−s} = ζ(s)⁴/ζ(2s)`. In modular-form language this is the
  Rankin–Selberg L-function of `E_{a+1}` with `E_{b+1}` — "composing" two Eisenstein DNAs
  pointwise gives a quotient of four zetas by one.

### `Fugue/HexagonalCount.lean` — the Eisenstein integers

* **`card_hexagonal`** — `#{(a,b) : a² − ab + b² = n} = 6 Σ_{d∣n} χ₋₃(d)`; e.g. `n = 7`: `12`. Same
  architecture as Jacobi's theorem, in `ℤ[ω]` (`ω² = −1 − ω`): 6 units, `3` ramifies (`3 = −ω²(1−ω)²`),
  `p ≡ 2 (mod 3)` stays prime, `p ≡ 1 (mod 3)` splits (found via an element of order 3 mod `p`).
  This is the Dedekind zeta function of `ℚ(√−3)` at the coefficient level — the field over which
  OpenAI's proof works.

### `Fugue/Factoring.lean` — what the factoring scripts really compute

* **`sum_exp_eq`** (D12) — `∑_{j<k} e^{2πijN/k}` is `k` if `k ∣ N` and `0` otherwise; so the
  "E8 torsion detector" is a divisibility test, and scanning `k` upward is trial division
  (`first_spike_is_minFac`).
* **`totient_reveals_factors`** (appendix A §1) — for `N = pq`, `p + q = N + 1 − φ(N)`: knowing
  `φ(N)` is as good as knowing the factors.
* **`pos_injective_odd`** — **a correction to appendix A §§4, 6.** The encoding
  `pos(n) = frac(log₂ n)` is a homomorphism (`pos_mul`), and the appendix concluded it "loses
  exactly the information required to factor". It does not lose it: `pos` is injective on odd
  numbers, so `pos(N)` determines `N` and hence `p, q`. The real obstruction is *computational*:
  the homomorphism does not make the factors easier to *compute* than `N` itself does.

---

## Why the audit's sanity checks matter

A formal equivalence can be "true" for a silly reason — for instance if the region were empty,
both sides would be trivially true. `Audit.lean` rules that out:

1. `region θ` is never empty (it contains `θ + 2 + i`).
2. The right-hand side **holds** at `θ = 1` (because the left does, by de la Vallée Poussin).
3. The right-hand side **fails** at `θ = −3`, because `ζ(−2) = 0` is a (trivial) zero there.

So the equivalence genuinely separates true from false cases. This kind of check is what the
`Fugue/` extraction found missing from the original Lean corpus.

---

## Connection to the HSLN corpus

| Corpus idea | What it becomes here |
|---|---|
| "The Lie derivative gives the primes" — `D(ζ)·μ = Λ` (fig 38) | the arithmetic side of `∑ Λ(n)n^{-s} = −ζ′/ζ`; Mathlib's `log_mul_moebius_eq_vonMangoldt` |
| "The zeros and primes encode each other" — the explicit formula (fig 35) | **chapter 2**: zeros of ζ are *exactly* the singularities of the prime series. The explicit formula is the quantitative version; chapter 6 is where it becomes a theorem about `ψ(x)` |
| "The Euler product, not the symmetry, is load-bearing" (`HSLNZeta.lean`) | the bridge identity *is* the log-derivative of the Euler product. Zero-free regions are proved from it, not from the functional equation |
| `HSLNWeilPositivity.lean`'s "analytic, not algebraic — no finite certificate" | still true: we have not proved any zero-free region. We have proved what one is *worth* |

---

## Questions to test yourself on

Short answers at the bottom. If you can answer these without looking, you can defend the work.

1. Why can't we just say "`ζ` has no zeros right of θ ⇒ `∑ Λ(n)n^{-s}` converges right of θ"?
2. Why does the region exclude `s = 1`, and why doesn't `ZeroFreeRight` need to?
3. In the converse, where exactly would the proof break if `ζ` could vanish on an open set?
4. Is `RH ⇒ ZeroFreeRight(1/2)` actually an equivalence? Why did we prove only one direction?
5. What would chapter 6 add that chapters 1–2 cannot?

<details><summary>Answers</summary>

1. *Convergence* and *continuation* differ. A Dirichlet series can continue analytically far
   beyond where it converges (`∑ n^{-s}` itself converges only for `Re s > 1` but continues to
   `ℂ \ {1}`). Turning continuation into convergence or into bounds on `ψ(x)` needs extra
   analytic input — that is chapters 4–6.
2. `−ζ′/ζ` has a pole at `1` (inherited from ζ's pole), so it is never holomorphic there.
   `ZeroFreeRight` is about *zeros*, and `ζ(1)` (junk value) is nonzero in Lean, so `s = 1`
   causes it no trouble.
3. At the step "the zero has *finite* order": if ζ vanished on an open set, the order would be
   `∞`, Mathlib's order-−1 lemma would not apply, and indeed `ζ′/ζ` would be `0/0` there. The
   identity theorem + `ζ(2) ≠ 0` is what excludes this.
4. Yes, it is an equivalence, and both directions are now proved
   (`riemannHypothesis_iff_zeroFreeRight_half`, chapter 3½ below). The direction in
   chapter 1 is pure logic. The converse needs the **functional equation**: zeros come in
   pairs `ρ ↔ 1 − ρ`, so a nontrivial zero with `Re ρ < 1/2` would produce one with
   `Re(1−ρ) > 1/2`, contradicting `ZeroFreeRight(1/2)`. Its moral: **RH is exactly the
   strongest possible quasi-RH**, and the "1/2" comes from the symmetry `s ↔ 1 − s` — the same
   point `HSLNZeta.lean` makes.
5. A **quantitative** statement about primes: `ψ(x) = x + O(x^{θ+ε})`. Chapters 1–2 are
   qualitative (holomorphic or not). Chapter 6 needs growth bounds on `ζ′/ζ` in vertical strips
   and a contour-integration (Perron) argument.
</details>

### Round two — the later chapters and the corpus library

6. In chapter 6, where exactly is the zero-free hypothesis used, and why does the proof lose an
   `x^δ`?
7. In chapter 7, why is there no main term `x` for `ψ(x, χ)` when `χ ≠ 1`, and where does `x/φ(q)`
   come from in `ψ(x; q, a)`?
8. `r₂(n) = 4 Σ_{d∣n} χ₋₄(d)`: why is `r₂(p) = 0` for a prime `p ≡ 3 (mod 4)`, and `r₂(p) = 8` for
   `p ≡ 1 (mod 4)`?
9. Why does `E₄² = E₈` follow from "weight-8 level-1 forms are one-dimensional", and why is the
   resulting identity `σ₇ = σ₃ + 120 σ₃⋆σ₃` a statement about *both* of the corpus' rings?
10. The appendix said `pos(n) = frac(log₂ n)` "loses the information needed to factor". What did
    `pos_injective_odd` show, and what is the correct reason the factoring demos fail?
11. Why can a functional equation (like the one Hecke's method gives from `E₄`) never by itself
    prove a zero-free region?

<details><summary>Answers</summary>

6. Only in the bound `|ζ′/ζ(σ + it)| ≤ K log |t|` on `σ ≥ σ₁ > θ` (Borel–Carathéodory needs a
   holomorphic `log ζ`, i.e. no zeros, on discs reaching left to `σ₁`), and in the holomorphy
   needed to move the contour to `Re s = σ₁`. The `δ` is the gap `σ₁ − θ` (the discs must stay
   inside the zero-free region) plus the smoothing/`log` losses; removing it needs zero-counting.
7. `L(s, χ)` is entire for `χ ≠ 1`, so moving the contour crosses no pole and picks up no residue;
   the main term of `ψ(x)` *is* the residue of `−ζ′/ζ` at `s = 1`. In `ψ(x; q, a) = φ(q)⁻¹ Σ_χ χ̄(a)ψ(x,χ)`
   only the trivial character has a main term, `x`, hence `x/φ(q)`.
8. The divisors of `p` are `1, p`. For `p ≡ 3`: `χ₋₄(1) + χ₋₄(p) = 1 − 1 = 0` (and indeed `a² + b²`
   is never `3 mod 4`). For `p ≡ 1`: `1 + 1 = 2`, so `r₂ = 8`: `p = a² + b²` in essentially one way
   (Fermat), times 8 sign/order choices.
9. Both `E₄²` and `E₈` lie in the one-dimensional space `M₈` and both have constant term `1`, so
   they are equal. Comparing `qⁿ`-coefficients: the left side is a *Cauchy* product of power series
   (Ring A) whose coefficients `σ_k = ζ * Id^k` are *Dirichlet* products (Ring B).
10. That `pos` is injective on odd numbers: `pos(N)` determines `N`, hence its factors. Nothing is
    lost; the demos fail because computing the factors from `N` (or from `pos(N)`) is no easier —
    every route they tried was trial division in disguise (`first_spike_is_minFac`).
11. A functional equation is a symmetry `s ↔ k − s`; functions with the same symmetry can have
    zeros anywhere (Davenport–Heilbronn has zeros off the line). Excluding zeros needs size or
    positivity information — ledger D3 and H8, and the large-sieve/moment input in OpenAI's proof.
</details>
