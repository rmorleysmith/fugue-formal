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

## Why the audit's three sanity checks matter

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
4. Yes, it is an equivalence. The direction we proved is pure logic. The converse needs the
   **functional equation**: zeros come in pairs `ρ ↔ 1 − ρ`, so a nontrivial zero with
   `Re ρ < 1/2` would produce one with `Re(1−ρ) > 1/2`, contradicting `ZeroFreeRight(1/2)`.
   We did not formalise that direction yet; Mathlib has the functional equation
   (`riemannZeta_one_sub`), so it is a good small exercise. Its moral: **RH is exactly the
   strongest possible quasi-RH**, and the "1/2" comes from the symmetry `s ↔ 1 − s` — the same
   point `HSLNZeta.lean` makes.
5. A **quantitative** statement about primes: `ψ(x) = x + O(x^{θ+ε})`. Chapters 1–2 are
   qualitative (holomorphic or not). Chapter 6 needs growth bounds on `ζ′/ζ` in vertical strips
   and a contour-integration (Perron) argument.
</details>
