# From the Fugue ledger to Lean

Every row of [`Fugue/02-threads/evidence-ledger.md`](../Fugue/02-threads/evidence-ledger.md)
that has been turned into a machine-checked statement, with the exact Lean name. "Mathlib"
means the fact was already in Mathlib (at commit `d13f23b`) and we only restate or use it.
All entries are sorry-free and appear in [`Audit.lean`](Audit.lean) or
[`../FormalPNT`](../FormalPNT).

| Ledger | Corpus claim | Verdict in ledger | Lean | Where |
|---|---|---|---|---|
| A1 | E8 is even unimodular (positive definite) | PROVEN (numerically) | `Fugue.e8Form_even`, `e8Form_pos` (LDLᵀ certificate), Mathlib `E₈_det`; finite fibres `e8_finite_fibre`; **`theta_e8_sum_e8`**: `Θ_{E8⊕E8} = Θ_{E8}²` | `Fugue/E8Lattice.lean` |
| A2 | `Θ_{E8} = E₄` | PROVEN (numerically) | **`Fugue.thetaE8_eq_E₄`** — via `Θ_{E8} = (θ₂⁸+θ₃⁸+θ₄⁸)/2` (E8 = D8 ∪ (D8+½𝟙), `thetaE8_eq_thetaCombo`) and modularity + `dim M₄ = 1` (`thetaCombo_eq_E₄`); **`reprCount_e8`: #vectors of norm 2n = 240σ₃(n)**, `reprCount_e8_one/two/three` = 240, 2160, 6720 (the corpus' `verify:E8.theta.roots` numbers, now theorems) | `Fugue/ThetaE8*.lean` |
| A3 | `E₄(ρ) = 0` | PROVEN | `Fugue.E₄_rho`; general `eq_zero_at_rho` (all weights `6 ∤ k`) | `Fugue/EllipticPoints.lean` |
| A3′ | (not in corpus) `E₆(i) = 0`, `E₄(i) ≠ 0`, `E₆(ρ) ≠ 0` | — | `E₆_I`, `E₄_I_ne_zero`, `E₆_rho_ne_zero`, `eq_zero_at_I` | same |
| A4 | `Δ = (E₄³ − E₆²)/1728` | PROVEN | Mathlib `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq` | used in `EllipticPoints` |
| A8 | "neuron count grows with weight" | REFUTED | `discriminant_rho_ne_zero` (+ Mathlib `discriminant_ne_zero`): weight 12 has no interior zeros | same |
| A9 | zeros = local minima of `|F|` | PROVEN | `Fugue.isLocalMin_norm_of_eq_zero`, `eq_zero_of_isLocalMin_norm` | `Fugue/Dynamics.lean` |
| B1 | zero-union for products | PROVEN | (trivial in a domain: `mul_eq_zero`) | — |
| B9 | direct sum vs tensor are different | REFUTED | `Fugue.theta_directSum`: both are Cauchy convolution | `Fugue/Theta.lean` |
| C1 | two inequivalent rings on one carrier | PROVEN | `cauchy_ne_dirichlet`; **`not_ringEquiv_powerSeries`** (not isomorphic) | `Fugue/TwoRings.lean` |
| C3 | Ring A has the identity `δ` | REFUTED | `delta_is_X`, `X_ne_one` | same |
| C4 | `ζ * μ = δ` | PROVEN | `zeta_mul_moebius` (Mathlib) | same |
| C5 | `ζ * ζ = d` | PROVEN | `zeta_mul_zeta_eq_sigma_zero` | same |
| C6 | `r₂(n) = 4 Σ χ₋₄(d)` | PROVEN (numerically) | **`Fugue.card_sq_add_sq`** — Jacobi's two-square theorem (not in Mathlib) | `Fugue/TwoSquares.lean` |
| C7 | `6(ζ*χ₋₃)(n) = #{a²−ab+b² = n}` (Eisenstein integers) | PROVEN (numerically) | **`Fugue.card_hexagonal`** — via a hand-built Euclidean structure on ℤ[ω]; = coefficients of `ζ_{ℚ(√−3)}`, OpenAI's field | `Fugue/HexagonalCount.lean` |
| C8 | `σ₃ = ζ⁴` | REFUTED | `sigma_three_ne_zeta_pow_four`; correct form `sigma_three_eq` | same |
| C1×C8 | Ramanujan's Eisenstein identities link the rings | (corpus prose, Q2) | **`Fugue.E₄sq_eq`** (`E₄² = E₈`, via `dim M₈ = 1`) and **`sigma_seven_eq`**: `σ₇ = σ₃ + 120 σ₃⋆σ₃` | `Fugue/Ramanujan.lean` |
| C9 | `·log` is a derivation; `log * μ = Λ` | PROVEN | `pmul_log_mul`; Mathlib `log_mul_moebius_eq_vonMangoldt` | same |
| C10 | Ramanujan's `E₂, E₄, E₆` system | PROVEN | Mathlib `normalizedDerivOfComplex_E₂/E₄/E₆`, `serreDerivative_E₄/E₆` | — |
| C11 | multiplicative functions form a submonoid; "Rankin–Selberg closure" | PROVEN | `multiplicativeSubmonoid`; not closed under `+`: `zeta_add_zeta_not_multiplicative`; **`Fugue.LSeries_sigma_mul_sigma`** (Ramanujan 1916: the pointwise product `σ_a·σ_b` has L-series `ζζζζ/ζ`) | `Fugue/TwoRings.lean`, `Fugue/RankinSelberg.lean` |
| C12 | product of eigenforms has product eigenvalues | REFUTED (numerically) | **`Fugue.discriminant_mul_E₄_not_multiplicative_eigenvalue`**: `a₂(ΔE₄) = 216 ≠ (−24)(2160)`; with `tau_two` (`τ(2) = −24`) | `Fugue/HeckeRefutation.lean` |
| C13 | `Θ_{L⊕M} = Θ_L Θ_M` | PROVEN | `reprCount_directSum`, `theta_directSum`, `theta_two_squares` | `Fugue/Theta.lean` |
| C15 | eta quotients can place a neuron anywhere | REFUTED | `Fugue.etaQuotient_ne_zero`: no zeros in `ℍ` at all | `Fugue/SieveEta.lean` |
| D2 | functional equation | PROVEN | Mathlib `riemannZeta_one_sub`; used in `QuasiRH.riemannHypothesis_iff_zeroFreeRight_half` | `QuasiRH/Reflection.lean` |
| A2⇒D2 | (corpus Q2: E8 / E₄ ↔ ζ) | — | **`Fugue.HeckeE4.heckeE4_functional_equation`**, `heckeE4_eq`: modularity of `E₄` ⇒ `Λ(s) = 240(2π)^{−s}Γ(s)ζ(s)ζ(s−3)` continues with `Λ(4−s) = Λ(s)` (Hecke) | `Fugue/HeckeE4.lean` |
| D1 | Euler product over primes `≤ N` gives `a(n) = 1` for all `n ≤ N` | PROVEN | **`Fugue.EulerCompose.prod_eulerFactor_apply_of_le`**; general form `prod_eulerFactor` (`∏_{p∈S} eulerFactor p` = `S`-smooth indicator), `smooth_tendsto_zeta`; analytic `zeta_eulerProduct` (Mathlib) | `Fugue/EulerCompose.lean` |
| D3 | symmetry alone does not force RH; Euler product is load-bearing | PROVEN | the reflection theorem shows exactly what symmetry *does* give: RH ⟺ no zeros right of ½ | same |
| D4 | zeros ↔ primes (explicit formula) | PROVEN (classical) | qualitative form: `zeroFreeRight_iff_differentiableOn`, `zeroFreeRight_of_psiError`; quantitative: `Ingham.*` | `QuasiRH/*`, `../FormalPNT` |
| D6 | `L(1,χ₋₄) = π/4` | PROVEN (numerically) | **`Fugue.LFunction_chi4_one`** (Leibniz series + dominated convergence + continuity of the entire `L`) | `Fugue/LeibnizL.lean` |
| D9/D10 | sieving by {2,3,5,7} gives the primes in [11,100]; "new mechanism" | PROVEN / REFUTED | `Fugue.sieve_2357` (it is Eratosthenes) | `Fugue/SieveEta.lean` |
| D12 | `Σ e^{2πijN/k} = k·[k∣N]` | PROVEN | `Fugue.sum_exp_eq`, `detector_iff` | `Fugue/Factoring.lean` |
| D13 | "E8 torsion" reveals factors | REFUTED as mechanism | `first_spike_is_minFac` (it is trial division) | same |
| E2/E5 | coupling `K(κ)` PSD ⟺ `|κ| ≤ 1`; prose vs Lean (PSD vs PD) | PROVEN / REFUTED | `couplingMatrix_posSemidef_iff`, `couplingMatrix_posDef_iff` | `Fugue/Dynamics.lean` |
| E3 | gravity preserves equilibria | PROVEN | `equilibrium_preserved` — needs **no** hypothesis on `K` | same |
| H12 | `φ(N)` is as hard as factoring | PROVEN | `totient_reveals_factors` | `Fugue/Factoring.lean` |
| H16 / App. A §§4, 6 | `pos` homomorphism "loses the information" | (ledger: PROVEN) **corrected here** | `pos_mul`; `pos_injective_odd` — the information is *not* lost, only not made computable | same |
| (OpenAI link) | quasi-RH, `θ = 7/8` | — | `QuasiRH.OpenAIStatement` (verbatim), `openAIStatement_iff_differentiableOn`, `OpenAIDirichletStatement`, `twistedVonMangoldt_continuation_of_openAI` | `QuasiRH/*` |

## Beyond the ledger

| Idea | Lean | File |
|---|---|---|
| E8×E8 heterotic lattice | `thetaE8_sq_eq_E₈`, `reprCount_e8e8` (480σ₇) | `Fugue/HeteroticE8.lean` |
| E8×E8 vs Spin(32)/ℤ₂ | `thetaD16_eq_thetaE8_sq` (Witt isospectrality) | `Fugue/D16Plus.lean` |
| Ramanujan's L-function from η²⁴ | `RamanujanL.ramanujanΛ_functional_equation`, `ramanujanΛ_differentiable` (entire) | `Fugue/RamanujanL.lean` |
| Epstein zeta / lattice–zeta bridge | `Epstein.epstein_E8`, `epstein_E8E8`, `epstein_square`, `epstein_hexagonal` | `Fugue/Epstein.lean` |
| Fermions via the zeta function | `PrimonGas.fermionic_partition` (ζ(s)/ζ(2s)), `witten_index`, `fockEquiv` | `Fugue/PrimonGas.lean` |
| Rankin–Selberg | `LSeries_sigma_mul_sigma` | `Fugue/RankinSelberg.lean` |
| Partitions and η | `Partitions.ramanujan_congruence_five`, `pentagonalSeries_pow_three` (Jacobi), `partition_recurrence` | `Fugue/Partitions.lean` |
| Δ = η²⁴ and Ramanujan's 691 | `tau_congr_691`, `Tau691.qExpansion_discriminant_eq` | `Fugue/Tau691.lean` |
| Golden ratio and primes | `golden_prime_iff`, `Golden.fib_cassini` | `Fugue/GoldenPrimes.lean` |
| Eisenstein road (E_k ↔ ζ) | `HeckeEk.heckeEk_functional_equation`, `heckeE6_centre_eq_zeta` | `Fugue/HeckeE*.lean` |

## Not formalised, and why

| Ledger | Reason |
|---|---|
| A5 (Hecke eigenform) | Mathlib has no Hecke operators at this commit |
| A6 (zeros of `E₄` are exactly the orbit of `ρ`) | needs the valence formula or the `j`-function's bijectivity, neither in Mathlib |
| C16 (`η²(τ)η²(11τ)` ↔ `11a1`) | modularity of a specific curve; far out of reach |
| D5, D16, D17, D19 | numerical (GUE statistics, `L(E,1)` values, Erdős–Kac measurements) |
| D7 (`L(2,χ₋₄) = G`) | Catalan's constant is *defined* by that series; nothing to prove beyond `LFunction_eq_LSeries` |
| F, G, most of H | machine-learning measurements and cryptographic demos — not mathematical theorems; the negative results that *are* theorems (H12, D12, D13) are formalised above |
