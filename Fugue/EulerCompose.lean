import Mathlib
import Fugue.RankinSelberg

set_option autoImplicit false

/-!
# Composing per-prime Euler factors (the pattern of `zeta_compose.py`, figure 32)

The corpus builds `ζ(s) = ∑ n^{-s}` "from first principles" by composing one little model
per prime — the Euler factor `1/(1 − p^{-s}) = ∑_k p^{-ks}`, whose Dirichlet coefficients
are `1` at `1, p, p², …` and `0` elsewhere — under Dirichlet multiplication. Figure 32 shows
the coefficient table filling in: after the primes `≤ N` are merged, the row is all ones for
every `n ≤ N`. The owner asked for this pattern to be formalised. The precise statement is:

* `eulerFactor p` is the indicator of the powers of `p` (`eulerFactor_prime_pow`,
  `eulerFactor_eq_one_iff`), and its generating series along the powers of `p` is the
  geometric series `1/(1 − X)` (`P_eulerFactor`, with `RankinSelberg.G_mul`).
* **`prod_eulerFactor`**: `∏_{p ∈ S} eulerFactor p = smooth S`, the indicator of the
  `S`-smooth numbers (`n ≠ 0` with every prime factor in `S`), for *any* finite set `S`.
  The proof is "unique factorisation": both sides are multiplicative, so it suffices to
  compare them on prime powers, where `smooth_mul_smooth` reduces to a one-line case split.
* **`prod_eulerFactor_apply_of_le`** (the figure): with `S` = the primes `≤ N`, the
  coefficient at every `1 ≤ n ≤ N` is `1`, i.e. equals `ζ n`
  (`prod_eulerFactor_eq_zeta_of_le`). Off the window the coefficients are `0` exactly at the
  non-smooth `n` (`prod_eulerFactor_apply`): the green cells of the figure are the `N`-smooth
  numbers, nothing more.
* `smooth_tendsto_zeta`: for each fixed `n`, once `S` contains the prime factors of `n` the
  coefficient is `ζ n` — the Dirichlet-coefficient form of "the Euler product converges to ζ".
  The analytic statement itself is Mathlib's `riemannZeta_eulerProduct`, restated here as
  `zeta_eulerProduct` for the audit.

Nothing here touches zeros or `RH`; the corpus' own "honest scope" note is right.
-/

namespace Fugue.EulerCompose

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta

/-- The indicator of the `S`-smooth numbers: `smooth S n = 1` iff `n ≠ 0` and every prime
factor of `n` lies in `S`. -/
def smooth (S : Finset ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n ≠ 0 ∧ n.primeFactors ⊆ S then 1 else 0, by simp⟩

@[simp] theorem smooth_apply (S : Finset ℕ) (n : ℕ) :
    smooth S n = if n ≠ 0 ∧ n.primeFactors ⊆ S then 1 else 0 := rfl

/-- The Euler factor of `p`: the Dirichlet coefficients of `1/(1 − p^{-s}) = ∑_k p^{-ks}`. -/
def eulerFactor (p : ℕ) : ArithmeticFunction ℕ := smooth {p}

theorem smooth_empty : smooth ∅ = 1 := by
  ext n
  rw [smooth_apply, one_apply]
  rcases n with _ | _ | n <;> simp [Nat.primeFactors_eq_empty, subset_empty]

/-- `smooth S` is multiplicative: for coprime `m, n`, `mn` is `S`-smooth iff both are. -/
theorem isMultiplicative_smooth (S : Finset ℕ) : (smooth S).IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [smooth_apply, ne_eq, mul_eq_zero, hm, hn, or_self, not_false_eq_true, true_and,
    Nat.primeFactors_mul hm hn, union_subset_iff]
  split_ifs <;> simp_all

theorem smooth_prime_pow (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    smooth S (p ^ k) = if k = 0 ∨ p ∈ S then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  rw [smooth_apply, Nat.primeFactors_prime_pow hk hp]
  simp [hk, hp.ne_zero]

theorem eulerFactor_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : eulerFactor p (p ^ k) = 1 := by
  rw [eulerFactor, smooth_prime_pow _ hp]; simp

theorem isMultiplicative_eulerFactor (p : ℕ) : (eulerFactor p).IsMultiplicative :=
  isMultiplicative_smooth _

/-- Explicitly: `eulerFactor p n = 1` iff `n` is a power of `p` (and the only other value is `0`,
by `smooth_apply`). -/
theorem eulerFactor_eq_one_iff {p : ℕ} (hp : p.Prime) (n : ℕ) :
    eulerFactor p n = 1 ↔ ∃ k, n = p ^ k := by
  rw [eulerFactor, smooth_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hp.ne_zero, @eq_comm ℕ 0]
  have key : n.primeFactors ⊆ {p} ↔ ∃ k, n = p ^ k := by
    constructor
    · intro h
      exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn fun {d} hd hdn =>
        mem_singleton.1 (h (Nat.mem_primeFactors.2 ⟨hd, hdn, hn⟩))⟩
    · rintro ⟨k, rfl⟩
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      rw [Nat.primeFactors_prime_pow hk hp]
  constructor
  · intro h1
    split_ifs at h1 with h
    exact key.1 h.2
  · intro hk
    exact if_pos ⟨hn, key.2 hk⟩

/-- Along the powers of `p`, the Euler factor is the geometric series `∑ X^k = 1/(1 − X)`. -/
theorem P_eulerFactor {p : ℕ} (hp : p.Prime) :
    RankinSelberg.P p (eulerFactor p) = RankinSelberg.G 1 := by
  ext j
  simp [RankinSelberg.P, RankinSelberg.G, eulerFactor_prime_pow hp]

theorem P_smooth (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    RankinSelberg.P p (smooth S) = if p ∈ S then RankinSelberg.G 1 else 1 := by
  ext j
  rw [RankinSelberg.P, PowerSeries.coeff_mk, smooth_prime_pow S hp]
  split_ifs with h₁ h₂ <;> simp_all [RankinSelberg.G, PowerSeries.coeff_one]

/-- **Unique factorisation, coefficient by coefficient.** For disjoint `S, T`, every
`(S ∪ T)`-smooth `n` factors uniquely as (`S`-smooth) × (`T`-smooth), so the Dirichlet
product of the indicators is the indicator of the union. -/
theorem smooth_mul_smooth {S T : Finset ℕ} (hST : Disjoint S T) :
    smooth S * smooth T = smooth (S ∪ T) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_smooth S).mul (isMultiplicative_smooth T)) _
    (isMultiplicative_smooth _)).2 fun p k hp => ?_
  have h : RankinSelberg.P p (smooth S * smooth T) = RankinSelberg.P p (smooth (S ∪ T)) := by
    rw [RankinSelberg.P_mul hp, P_smooth S hp, P_smooth T hp, P_smooth (S ∪ T) hp]
    simp only [mem_union]
    by_cases hS : p ∈ S
    · have hT : p ∉ T := disjoint_left.1 hST hS
      simp [hS, hT]
    · by_cases hT : p ∈ T <;> simp [hS, hT]
  have := congrArg (PowerSeries.coeff k) h
  simp only [RankinSelberg.P, PowerSeries.coeff_mk] at this
  exact_mod_cast this

/-- **Composing the per-prime models.** The Dirichlet product of the Euler factors of the
primes in `S` is the indicator of the `S`-smooth numbers. (`S` need not consist of primes:
non-prime members contribute nothing.) -/
theorem prod_eulerFactor (S : Finset ℕ) : ∏ p ∈ S, eulerFactor p = smooth S := by
  induction S using Finset.induction_on with
  | empty => simp [smooth_empty]
  | insert p S hp ih =>
    rw [prod_insert hp, ih, eulerFactor, smooth_mul_smooth (disjoint_singleton_left.2 hp),
      singleton_union]

theorem prod_eulerFactor_apply (S : Finset ℕ) (n : ℕ) :
    (∏ p ∈ S, eulerFactor p) n = if n ≠ 0 ∧ n.primeFactors ⊆ S then 1 else 0 := by
  rw [prod_eulerFactor, smooth_apply]

/-- The primes up to `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ := (range (N + 1)).filter Nat.Prime

theorem primeFactors_subset_primesUpTo {N n : ℕ} (hnN : n ≤ N) :
    n.primeFactors ⊆ primesUpTo N := fun q hq => by
  rw [primesUpTo, mem_filter, mem_range]
  exact ⟨by have := Nat.le_of_mem_primeFactors hq; omega, Nat.prime_of_mem_primeFactors hq⟩

/-- **Figure 32.** After merging the Euler factors of all primes `≤ N`, the coefficient at
every `1 ≤ n ≤ N` is `1`: the all-ones row *is* the `ζ` series on the window. -/
theorem prod_eulerFactor_apply_of_le {N n : ℕ} (hn : n ≠ 0) (hnN : n ≤ N) :
    (∏ p ∈ primesUpTo N, eulerFactor p) n = 1 := by
  rw [prod_eulerFactor_apply, if_pos ⟨hn, primeFactors_subset_primesUpTo hnN⟩]

theorem prod_eulerFactor_eq_zeta_of_le {N n : ℕ} (hnN : n ≤ N) :
    (∏ p ∈ primesUpTo N, eulerFactor p) n = ζ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [prod_eulerFactor_apply_of_le hn hnN, zeta_apply, if_neg hn]

/-- The coefficientwise limit: for each `n`, once `S ⊇ primeFactors n` the composed
coefficient equals `ζ n` — the Dirichlet-series form of `∏_p (1 − p^{-s})^{-1} = ζ(s)`. -/
theorem smooth_tendsto_zeta (n : ℕ) :
    ∀ᶠ S in Filter.atTop, (∏ p ∈ S, eulerFactor p) n = ζ n := by
  refine Filter.eventually_atTop.2 ⟨n.primeFactors, fun S hS => ?_⟩
  rw [prod_eulerFactor_apply, zeta_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [if_pos ⟨hn, hS⟩, if_neg hn]

/-- The analytic Euler product (Mathlib): the partial products over the primes `< N` converge
to `ζ(s)` for `re s > 1`. -/
theorem zeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - (p : ℂ) ^ (-s))⁻¹)
      Filter.atTop (nhds (riemannZeta s)) :=
  riemannZeta_eulerProduct hs

end Fugue.EulerCompose
