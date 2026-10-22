import Mathlib

/-!
# The factoring thread: what is true, and what it does not buy (ledger D12–D14, H12, H16;
# appendix A §§1, 4, 6)

The corpus' factoring scripts all reduce to classical facts. This file proves those facts and
records, formally, the one place where the appendix's "unifying observation" overstated.

1. **D12, the "E8 torsion" detector.** `∑_{j<k} e^{2πijN/k} = k` if `k ∣ N` and `0` otherwise
   (`sum_exp_eq`). So `D(k) = (1/k)|∑| ` is the indicator of `k ∣ N`, and scanning `k = 2, 3, …`
   for the first spike is trial division: it stops at `Nat.minFac N` (`detector_iff`).
2. **H12 / appendix A §1 (Miller).** For `N = pq` with `p ≠ q` prime, `φ(N)` reveals the factors:
   `p + q = N + 1 - φ(N)`, so `p` and `q` are the roots of `X² - (N + 1 - φ(N)) X + N`
   (`totient_reveals_factors`). Computing `φ(N)` is therefore as hard as factoring `N`.
3. **Appendix A §4/§6, a correction.** The encoding `pos(n) = frac(log₂ n)` is a homomorphism
   `(ℕ_{>0}, ×) → ℝ/ℤ` (`pos_mul`), and the appendix says it therefore "loses exactly the
   information required to factor". That is too strong: `pos` is **injective on odd numbers**
   (`pos_injective_odd`). So for an odd semiprime `N`, `pos(N)` determines `N`, hence `p` and
   `q`. Nothing is lost *information-theoretically*; what fails is that the homomorphism does not
   make the factors any *easier to compute* than `N` itself. The obstruction is computational,
   not informational — which is exactly the RSA situation.
-/

open Complex Finset
open scoped Real

namespace Fugue

/-! ### 1. The root-of-unity detector -/

/-- **Ledger D12.** `∑_{j < k} e^{2πi jN/k} = k` if `k ∣ N`, else `0`. -/
theorem sum_exp_eq {k : ℕ} (hk : k ≠ 0) (N : ℕ) :
    ∑ j ∈ range k, cexp (2 * π * I * j * N / k) = if k ∣ N then (k : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp k hk
  set ζ := cexp (2 * π * I / k)
  have hterm : ∀ j : ℕ, cexp (2 * π * I * j * N / k) = (ζ ^ N) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · rw [(hζ.pow_eq_one_iff_dvd N).mpr hdvd]; simp
  · have hne : ζ ^ N ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd N).mp h)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- The detector spikes (`D(k) = 1`) exactly at divisors. -/
theorem detector_iff {k : ℕ} (hk : k ≠ 0) (N : ℕ) :
    ‖(1 / (k : ℂ)) * ∑ j ∈ range k, cexp (2 * π * I * j * N / k)‖ = 1 ↔ k ∣ N := by
  rw [sum_exp_eq hk]
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  split_ifs with h
  · simp [hk', h]
  · simp [h]

/-- **Ledger D13.** The first spike as `k` runs up from `2` is at the least prime factor —
i.e. the scan is trial division. -/
theorem first_spike_is_minFac (N : ℕ) :
    N.minFac ∣ N ∧ ∀ k, 2 ≤ k → k ∣ N → N.minFac ≤ k :=
  ⟨Nat.minFac_dvd N, fun _ hk hd => Nat.minFac_le_of_dvd hk hd⟩

/-! ### 2. Miller: `φ(N)` reveals the factors of `N = pq` -/

/-- **Appendix A §1.** For distinct primes, `p + q = pq + 1 - φ(pq)` and `p` is a root of
`X² - (N + 1 - φ(N)) X + N`. -/
theorem totient_reveals_factors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((p + q : ℕ) : ℤ) = (p * q : ℕ) + 1 - ((p * q).totient : ℕ) ∧
      (p : ℤ) ^ 2 - ((p * q : ℕ) + 1 - ((p * q).totient : ℕ)) * p + (p * q : ℕ) = 0 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have htot : ((p * q).totient : ℤ) = ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
    push_cast [hp.one_le, hq.one_le]
    ring
  constructor
  · rw [htot]; push_cast; ring
  · rw [htot]; push_cast; ring

/-! ### 3. `pos = frac ∘ log₂`: a homomorphism that is nevertheless injective on odd numbers -/

/-- The corpus' encoding `pos(x) = frac(log₂ x)`. -/
noncomputable def pos (x : ℝ) : ℝ := Int.fract (Real.logb 2 x)

/-- `pos` is a homomorphism to `ℝ/ℤ`: `pos(ab) ≡ pos(a) + pos(b) (mod 1)`. -/
theorem pos_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    pos (a * b) = Int.fract (pos a + pos b) := by
  unfold pos
  rw [Real.logb_mul ha.ne' hb.ne', Int.fract_eq_fract]
  refine ⟨⌊Real.logb 2 a⌋ + ⌊Real.logb 2 b⌋, ?_⟩
  rw [Int.fract, Int.fract]; push_cast; ring

/-- `pos` forgets powers of two: `pos(2n) = pos(n)`. -/
theorem pos_two_mul {x : ℝ} (hx : 0 < x) : pos (2 * x) = pos x := by
  unfold pos
  rw [Real.logb_mul two_ne_zero hx.ne', Real.logb_self_eq_one one_lt_two, add_comm,
    Int.fract_add_one]

private theorem eq_of_pow_two_mul {n m : ℕ} (hn : Odd n) (k : ℕ) (h : n = 2 ^ k * m) :
    k = 0 := by
  by_contra hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [h, pow_succ] at hn
  exact Nat.not_even_iff_odd.mpr hn ⟨2 ^ j * m, by ring⟩ |>.elim

/-- **Correction to appendix A §4/§6.** `pos` is injective on odd positive integers. Hence for
an odd semiprime `N`, `pos(N)` determines `N` and thus its factors: the homomorphism hides the
factors no better (and no worse) than `N` itself does. -/
theorem pos_injective_odd {n m : ℕ} (hn : Odd n) (hm : Odd m) (h : pos n = pos m) : n = m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.pos
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
  -- `log₂ n - log₂ m = z`, so `n = 2^z m`
  have hlog : Real.log n = z * Real.log 2 + Real.log m := by
    have h2 : Real.log 2 ≠ 0 := by positivity
    unfold Real.logb at hz
    field_simp at hz
    linarith
  have hexp : (n : ℝ) = (2 : ℝ) ^ (z : ℝ) * m := by
    rw [← Real.exp_log hn0, hlog, Real.exp_add, Real.exp_log hm0, Real.rpow_def_of_pos two_pos,
      mul_comm (z : ℝ)]
  rcases Int.eq_nat_or_neg z with ⟨k, rfl | rfl⟩
  · have hnat : n = 2 ^ k * m := by
      rw [Real.rpow_intCast, zpow_natCast] at hexp; exact_mod_cast hexp
    have := eq_of_pow_two_mul hn k hnat
    simpa [this] using hnat
  · have hnat : m = 2 ^ k * n := by
      have h2k : (0 : ℝ) < 2 ^ k := by positivity
      rw [Real.rpow_intCast, zpow_neg, zpow_natCast] at hexp
      have : (m : ℝ) = 2 ^ k * n := by field_simp at hexp; linarith
      exact_mod_cast this
    have := eq_of_pow_two_mul hm k hnat
    simp [this] at hnat; exact hnat.symm

end Fugue
