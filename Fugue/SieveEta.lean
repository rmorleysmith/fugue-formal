import Mathlib

/-!
# Two small corpus facts (ledger rows D9/D10 and C15)

* **D9/D10, the "prime sieve by composition".** The corpus' figure 31 composes detectors
  `sin(πx/p)` for `p ∈ {2,3,5,7}` and observes that the survivors in `[11, 100]` are exactly the
  primes. `sieve_2357` states this; it is the Sieve of Eratosthenes (every composite `n ≤ 100` has a
  prime factor `≤ √100 = 10`), checked by `decide`.
* **C15, eta quotients never vanish on `ℍ`.** The corpus' scope note: eta-quotient "neurons" can
  only sit at cusps. `etaQuotient_ne_zero`: `∏ᵢ η(mᵢ τ)^{rᵢ} ≠ 0` for every `τ` in the upper
  half-plane, any positive integers `mᵢ` and any integer exponents `rᵢ` — immediate from
  Mathlib's `eta_ne_zero` (both factors of `η = q^{1/24} ∏(1 − qⁿ)` are nonzero).
-/

namespace Fugue

/-- **D9.** Sieving by `2, 3, 5, 7` leaves exactly the primes in `[11, 100]`. -/
theorem sieve_2357 : ∀ n ∈ Finset.Icc 11 100,
    (Nat.Prime n ↔ (¬ 2 ∣ n ∧ ¬ 3 ∣ n ∧ ¬ 5 ∣ n ∧ ¬ 7 ∣ n)) := by
  intro n hn
  rw [Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  interval_cases n <;> norm_num

/-- **C15.** An eta quotient has no zeros in the upper half-plane. -/
theorem etaQuotient_ne_zero {ι : Type*} (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 0 < m i)
    (r : ι → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    ∏ i ∈ s, ModularForm.eta ((m i : ℂ) * τ) ^ r i ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  apply zpow_ne_zero
  apply ModularForm.eta_ne_zero
  show 0 < ((m i : ℂ) * τ).im
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hm i hi) hτ

end Fugue
