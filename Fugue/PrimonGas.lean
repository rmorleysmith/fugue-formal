import Mathlib
import Fugue.RankinSelberg

set_option autoImplicit false

/-!
# The primon gas (Riemann gas): Dirichlet series as partition functions

The "Riemann gas" or "primon gas" (B. Julia, *Statistical theory of numbers*, in
*Number Theory and Physics*, Springer 1990; D. Spector, *Supersymmetry and the Möbius inversion
function*, Comm. Math. Phys. 127 (1990) 239–252) is a toy free quantum gas whose single-particle
states are the primes `p`, with energies `log p`. A multi-particle state is a choice of
occupation numbers `k_p`, i.e. a positive integer `n = ∏ p^{k_p}`, of energy `log n`; at inverse
temperature `s` its Boltzmann weight is `e^{-s log n} = n^{-s}`. The dictionary:

* **bosons** (any occupation): `Z_B(s) = ∑_{n ≥ 1} n^{-s} = ζ(s)` — `bosonic_partition`;
* **fermions** (Pauli exclusion `k_p ∈ {0, 1}`, i.e. `n` squarefree):
  `Z_F(s) = ∑_{n squarefree} n^{-s} = ζ(s)/ζ(2s)` — `fermionic_partition` (in the
  division-free form `Z_F(s) · ζ(2s) = ζ(s)`) and `fermionic_partition_div`. The arithmetic core is
  `sqf_mul_sqPow_zero`: `1_{squarefree} * 1_{squares} = ζ` as arithmetic functions, i.e. every
  `n ≥ 1` is uniquely (squarefree) × (square); proved by multiplicativity, comparing the
  prime-power generating series `(1 + X) · 1/(1 - X²) = 1/(1 - X)`;
* the fermion-number parity `(-1)^F` of the squarefree state `n` is `μ(n)` — `moebius_eq_parity`
  — so the **Witten index** `∑ (-1)^F e^{-sE} = ∑ μ(n) n^{-s} = 1/ζ(s)` — `witten_index`;
* the fermionic Fock space: squarefree `n` ↔ finite sets of primes (occupied levels), via
  `n ↦ primeFactors n`, `S ↦ ∏ S` — `fockEquiv`; energy is additive (`energy_fock`) and the
  parity of the state `S` is `(-1)^{#S}` (`moebius_fock`). (The fermionic Hilbert space with basis
  indexed by squarefree `n` is thus the exterior algebra on the span of the primes; we formalize
  only the basis-level bijection.)

All identities are for `re s > 1`, where the series converge absolutely.

The functional equation of `ζ` (`bosonic_duality`, a restatement of Mathlib's
`riemannZeta_one_sub`) then reads as a formal "temperature duality" `s ↔ 1 - s` of the bosonic
gas; **no physical interpretation is implied**.

**Caveat.** This is an analogy made precise — the statistical mechanics of a toy gas whose
"spectrum" is `{log p}` — and not a statement about the physics of real fermions. What is proved
here is exactly the classical Dirichlet-series identities above, phrased in that dictionary.

Uses `sqPow`, `P`, `Q`, `G`, `toC`, `LSeriesHasSum_pow`, `LSeriesHasSum_sqPow` from
`Fugue.RankinSelberg`.
-/

namespace Fugue.PrimonGas

open ArithmeticFunction LSeries PowerSeries Fugue.RankinSelberg
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius LSeries.notation

/-- Indicator of squarefree numbers (`0` at `0`, since `0` is not squarefree). -/
def sqf : ArithmeticFunction ℕ := ⟨fun n => if Squarefree n then 1 else 0, by simp⟩

theorem sqf_apply (n : ℕ) : sqf n = if Squarefree n then 1 else 0 := rfl

theorem isMultiplicative_sqf : sqf.IsMultiplicative := by
  refine ⟨by simp [sqf_apply], fun {m n} h => ?_⟩
  simp only [sqf_apply, squarefree_mul_iff, ← Nat.coprime_iff_isRelPrime]
  split_ifs <;> simp_all

theorem sqf_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sqf (p ^ j) = if j ≤ 1 then 1 else 0 := by
  rcases j with _ | _ | j
  · simp [sqf_apply]
  · simp [sqf_apply, hp.squarefree]
  · rw [sqf_apply, ite_eq_right_iff.2 fun h => absurd h ?_, ite_eq_right_iff.2 fun h => absurd h ?_]
    · omega
    · rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      omega

theorem P_sqf {p : ℕ} (hp : p.Prime) : P p sqf = 1 + X := by
  ext j
  rw [P, coeff_mk, sqf_prime_pow hp]
  rcases j with _ | _ | j <;> simp [coeff_X, coeff_one]

theorem one_add_X_mul_Q : (1 + X : PowerSeries ℤ) * Q 1 = G 1 := by
  have h1 := Q_mul (1 : ℤ)
  have h2 := G_mul (1 : ℤ)
  simp only [map_one, one_mul] at h1 h2
  have hne : (1 - X : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    simp at this
  apply mul_right_cancel₀ hne
  linear_combination h1 - h2

/-- **Every `n ≥ 1` is uniquely (squarefree) × (square)**, as an identity of arithmetic
functions: `1_{squarefree} * 1_{squares} = ζ`. -/
theorem sqf_mul_sqPow_zero : sqf * sqPow 0 = ζ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_sqf.mul (isMultiplicative_sqPow 0)) _ isMultiplicative_zeta).2
    fun p k hp => ?_
  have h : P p (sqf * sqPow 0) = P p ζ := by
    rw [P_mul hp, P_sqf hp, P_sqPow hp, ← pow_zero_eq_zeta, P_pow hp, pow_zero,
      one_add_X_mul_Q]
  have := congrArg (PowerSeries.coeff k) h
  simp only [P, PowerSeries.coeff_mk] at this
  exact_mod_cast this

theorem toC_sqf : toC sqf = fun n => if Squarefree n then (1 : ℂ) else 0 := by
  funext n
  simp only [toC, sqf_apply]
  split_ifs <;> simp

theorem LSeriesSummable_sqf {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (toC sqf) s := by
  refine LSeriesSummable_of_le (g := pow 0) (fun n => ?_)
    (LSeriesHasSum_pow 0 (by push_cast; linarith)).LSeriesSummable
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [sqf_apply, pow_apply, hn, and_false, ite_false, pow_zero]
    split_ifs <;> simp

/-- **Bosonic primon gas**: `Z_B(s) = ∑ n^{-s} = ζ(s)`. -/
theorem bosonic_partition {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun _ => 1) s = riemannZeta s :=
  LSeries_one_eq_riemannZeta hs

/-- **Fermionic primon gas**: `Z_F(s) · ζ(2s) = ζ(s)`, i.e. `Z_F(s) = ζ(s)/ζ(2s)`. -/
theorem fermionic_partition {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if Squarefree n then 1 else 0) s * riemannZeta (2 * s) =
      riemannZeta s := by
  have h1 := (LSeriesSummable_sqf hs).LSeriesHasSum
  have h2 := LSeriesHasSum_sqPow 0 (s := s) (by push_cast; linarith)
  have h3 := h1.convolution h2
  rw [← toC_mul, sqf_mul_sqPow_zero, ← pow_zero_eq_zeta] at h3
  have h4 := LSeriesHasSum_pow 0 (s := s) (by push_cast; linarith)
  rw [← toC_sqf]
  simpa using h3.unique h4

/-- **Fermionic primon gas**, division form: `Z_F(s) = ζ(s)/ζ(2s)`. -/
theorem fermionic_partition_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if Squarefree n then 1 else 0) s = riemannZeta s / riemannZeta (2 * s) := by
  have h2 : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp [Complex.mul_re]; linarith)
  rw [eq_div_iff h2, fermionic_partition hs]

/-- **Witten index of the primon gas**: `(∑ μ(n) n^{-s}) · ζ(s) = 1`. -/
theorem witten_index {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ)) s * riemannZeta s = 1 := by
  rw [← LSeries_one_eq_riemannZeta hs, mul_comm]
  exact LSeries_one_mul_Lseries_moebius hs

/-- **`μ = (-1)^F`**: on a squarefree `n` (a fermionic state), the Möbius function is the parity
of the number `F = #primeFactors n` of occupied single-particle states. -/
theorem moebius_eq_parity (n : ℕ) (hn : Squarefree n) :
    μ n = (-1) ^ n.primeFactors.card := by
  rw [moebius_apply_of_squarefree hn, cardFactors_apply, Nat.primeFactors,
    List.toFinset_card_of_nodup hn.nodup_primeFactorsList]

/-! ### Fock space: fermionic occupation states = finite sets of primes -/

/-- A finite set of primes multiplies to a squarefree number. -/
theorem squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun p hp => (hS p hp).squarefree
  show IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hS p hp) (hS q hq)).2 hpq

/-- **Fermionic Fock states.** Squarefree positive integers (fermionic multi-particle states of
the primon gas) are in bijection with finite sets of primes (sets of occupied single-particle
levels), via `n ↦ primeFactors n` with inverse `S ↦ ∏_{p ∈ S} p`. -/
def fockEquiv : {n : ℕ // Squarefree n} ≃ {S : Finset ℕ // ∀ p ∈ S, p.Prime} where
  toFun n := ⟨n.1.primeFactors, fun _ hp => Nat.prime_of_mem_primeFactors hp⟩
  invFun S := ⟨∏ p ∈ S.1, p, squarefree_prod_primes S.2⟩
  left_inv n := Subtype.ext (Nat.prod_primeFactors_of_squarefree n.2)
  right_inv S := Subtype.ext (Nat.primeFactors_prod S.2)

theorem fockEquiv_symm_apply (S : {S : Finset ℕ // ∀ p ∈ S, p.Prime}) :
    (fockEquiv.symm S : ℕ) = ∏ p ∈ S.1, p := rfl

/-- The energy of a Fock state is additive: `E(∏_{p ∈ S} p) = ∑_{p ∈ S} log p`. -/
theorem energy_fock (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Real.log ((∏ p ∈ S, p : ℕ) : ℝ) = ∑ p ∈ S, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (hS p hp).ne_zero

/-- The parity `(-1)^F` of a Fock state with occupied set `S` is `μ(∏_{p ∈ S} p) = (-1)^{#S}`. -/
theorem moebius_fock (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    μ (∏ p ∈ S, p) = (-1) ^ S.card := by
  rw [moebius_eq_parity _ (squarefree_prod_primes hS), Nat.primeFactors_prod hS]

/-- The bosonic "temperature duality" `s ↔ 1 - s`: the functional equation of `ζ` (Mathlib's
`riemannZeta_one_sub`), restated; no physical interpretation is implied. -/
theorem bosonic_duality {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s *
      Complex.cos (Real.pi * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'

end Fugue.PrimonGas
