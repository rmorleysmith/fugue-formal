import Mathlib
set_option autoImplicit false

/-!
# Partitions, Euler's pentagonal theorem, Jacobi's identity and Ramanujan's congruence mod 5

Let `p(n) = Fintype.card (Nat.Partition n)` be the partition function.  This file proves

1. **Euler's partition identity** (`partitionSeries_mul_tprod`,
   `partitionSeries_mul_pentagonalSeries`):
   `(∑ p(n) Xⁿ) · ∏_{n ≥ 1} (1 - Xⁿ) = 1` in `ℤ⟦X⟧`, using Mathlib's partition generating
   function (`Nat.Partition.genFun` / `hasProd_powerSeriesMk_card_restricted`) and Mathlib's
   pentagonal number theorem (`PowerSeries.WithPiTopology.tprod_one_sub_X_pow`).
2. **Euler's recurrence** (`partition_recurrence`): for `n ≥ 1`,
   `p(n) = ∑_{k ≠ 0} (-1)^{k+1} p(n - k(3k-1)/2)`, with the sanity check
   `p(0), …, p(10) = 1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42` (`partition_values`), computed from
   the recurrence.
3. **Jacobi's identity** (`tprod_one_sub_X_pow_pow_three`, `pentagonalSeries_pow_three`):
   `∏_{n ≥ 1} (1 - Xⁿ)³ = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}` (not in Mathlib).
   Proof: Gaussian binomials `qb` via the q-Pascal rule, the q-binomial theorem (`coeff_gpoly`),
   the *finite* Jacobi triple product `tpoly` (polynomial in `Z` over `ℤ⟦q⟧`), then
   differentiating at `Z = -1` gives the finite identity
   `∏_{i ≤ n}(1-qⁱ)² = ∑_{k ≤ n} (-1)^k (2k+1) [2n+1, n+1+k]_q q^{k(k+1)/2}` (`ep_sq`), and
   `(q)_n [2n+1, n+1+k]_q q^{k(k+1)/2} ≡ q^{k(k+1)/2} (mod q^{n+1})` (`key_cong`) finishes.
4. **Ramanujan's congruence** (`ramanujan_congruence_five`): `5 ∣ p(5n + 4)`.
   Proof (Hardy–Wright Thm 359 style): with `P = ∑ p(n) Xⁿ`, `E = ∏(1 - Xⁿ)`, `P E = 1` gives
   `X P = (X E⁴) P⁵ = (X · E · E³) P⁵`.  Over `ZMod 5`, `P⁵` is a series in `X⁵`
   (Frobenius, `PowerSeries.map_frobenius_expand`), and the coefficients of
   `X · E · E³ = ∑ (-1)^{k+l} (2l+1) X^{1 + k(3k-1)/2 + l(l+1)/2}` at multiples of `5` vanish
   mod 5, since `24 (1 + k(3k-1)/2 + l(l+1)/2) = (6k-1)² + 3(2l+1)² + 20` and
   `x² + 3y² ≡ 0 (mod 5)` forces `5 ∣ 2l+1`.  Comparing coefficients of `X^{5n+5}` gives the result.

## Relation with the Dedekind eta function

With `q = e^{2πiτ}`, the Dedekind eta function is `η(τ) = q^{1/24} ∏_{n ≥ 1} (1 - qⁿ)`
(Mathlib: `ModularForm.eta`).  The power series `∏ (1 - Xⁿ)` treated here is therefore the
`q`-expansion of `q^{-1/24} η(τ)`, and Euler's identity reads
`∑_{n ≥ 0} p(n) q^{n - 1/24} = 1 / η(τ)`.  Jacobi's identity is the `q`-expansion of `η(τ)³`
(`η³ = ∑ (-1)^k (2k+1) q^{(2k+1)²/8}`), the pentagonal theorem that of `η(τ)` itself
(`η = ∑ (-1)^k q^{(6k-1)²/24}`), and the congruence proof above is the mod-5 shadow of
Ramanujan's identity `∑ p(5n+4) qⁿ = 5 ∏ (1 - q^{5n})⁵ / (1 - qⁿ)⁶` (an `η(5τ)⁵/η(τ)⁶` identity,
not proved here).  Finally `Δ = η²⁴ = q ∏ (1 - qⁿ)²⁴ = ∑ τ(n) qⁿ` is Ramanujan's
discriminant, whose coefficients are Ramanujan's `τ` function; e.g. `Δ = q · E⁴ · E²⁰` and
`E²⁰ ≡ ∏(1 - q^{5n})⁴ (mod 5)` relate `τ(n) mod 5` to the series `q E⁴` studied here.

All results are proved without `sorry`; the only axioms used are
`propext`, `Classical.choice`, `Quot.sound`.
-/

open Finset

namespace Fugue.Partitions

/-- Power series over `ℤ` (the variable `PowerSeries.X` plays the role of `q`). -/
abbrev PS := PowerSeries ℤ

local notation "𝕢" => (PowerSeries.X : PowerSeries ℤ)

/-! ## Triangular numbers, finite Euler products, Gaussian binomials -/

/-- Triangular numbers `tri n = n(n+1)/2`, defined recursively. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + (n + 1)

@[simp] lemma tri_zero : tri 0 = 0 := rfl
lemma tri_succ (n : ℕ) : tri (n + 1) = tri n + (n + 1) := rfl

lemma two_mul_tri (n : ℕ) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tri_succ]; ring_nf; ring_nf at ih; nlinarith

lemma tri_eq (n : ℕ) : tri n = n * (n + 1) / 2 := by
  rw [← two_mul_tri]; simp

lemma le_tri (n : ℕ) : n ≤ tri n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [tri_succ]; omega

lemma tri_pred_add (i : ℕ) : tri (i - 1) + i = tri i := by
  cases i with
  | zero => rfl
  | succ j => simp [tri_succ]

/-- The finite Euler product `(q)_n = ∏_{i < n} (1 - q^{i+1})`. -/
noncomputable def ep (n : ℕ) : PS := ∏ i ∈ range n, (1 - 𝕢 ^ (i + 1))

lemma ep_succ (n : ℕ) : ep (n + 1) = ep n * (1 - 𝕢 ^ (n + 1)) := by
  simp [ep, prod_range_succ]

@[simp] lemma ep_zero : ep 0 = 1 := by simp [ep]

lemma one_sub_X_pow_ne_zero (k : ℕ) : (1 - 𝕢 ^ (k + 1) : PS) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  simp at this

lemma ep_ne_zero (n : ℕ) : ep n ≠ 0 := by
  rw [ep, prod_ne_zero_iff]
  exact fun k _ => one_sub_X_pow_ne_zero k

/-- Gaussian binomial coefficients `[n, k]_q ∈ ℤ⟦q⟧`, via the q-Pascal rule
`[n+1, k+1] = [n, k] + q^{k+1} [n, k+1]`. -/
noncomputable def qb : ℕ → ℕ → PS
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qb n k + 𝕢 ^ (k + 1) * qb n (k + 1)

@[simp] lemma qb_zero_right (n : ℕ) : qb n 0 = 1 := by cases n <;> rfl
@[simp] lemma qb_zero_succ (k : ℕ) : qb 0 (k + 1) = 0 := rfl
lemma qb_succ_succ (n k : ℕ) : qb (n + 1) (k + 1) = qb n k + 𝕢 ^ (k + 1) * qb n (k + 1) := rfl

lemma qb_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → qb n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qb_succ_succ, qb_eq_zero_of_lt (by omega : n < k), qb_eq_zero_of_lt (by omega : n < k + 1)]
    simp

@[simp] lemma qb_self : ∀ n : ℕ, qb n n = 1
  | 0 => rfl
  | n + 1 => by rw [qb_succ_succ, qb_self n, qb_eq_zero_of_lt (by omega : n < n + 1)]; simp

lemma qb_mul_ep : ∀ (s a b : ℕ), a + b = s → qb (a + b) a * ep a * ep b = ep (a + b)
  | _, 0, b, _ => by simp
  | _, a + 1, 0, _ => by simp
  | 0, a + 1, b + 1, h => by omega
  | s + 1, a + 1, b + 1, h => by
    have h1 := qb_mul_ep s a (b + 1) (by omega)
    have h2 := qb_mul_ep s (a + 1) b (by omega)
    have e1 : a + 1 + (b + 1) = (a + (b + 1)) + 1 := by ring
    have e2 : a + 1 + b = a + (b + 1) := by ring
    rw [e2] at h2
    rw [e1, qb_succ_succ, ep_succ (a + (b + 1)), ep_succ a, ep_succ b]
    rw [ep_succ b] at h1
    rw [ep_succ a] at h2
    rw [show a + (b + 1) = a + b + 1 by ring] at h1 h2 ⊢
    linear_combination (1 - 𝕢 ^ (a + 1)) * h1 + 𝕢 ^ (a + 1) * (1 - 𝕢 ^ (b + 1)) * h2

lemma qb_symm (a b : ℕ) : qb (a + b) a = qb (a + b) b := by
  have h1 := qb_mul_ep _ a b rfl
  have h2 := qb_mul_ep _ b a rfl
  rw [add_comm b a] at h2
  have h3 : (ep a * ep b) * qb (a + b) a = (ep a * ep b) * qb (a + b) b := by
    linear_combination h1 - h2
  exact mul_left_cancel₀ (mul_ne_zero (ep_ne_zero a) (ep_ne_zero b)) h3

/-! ## The q-binomial theorem and the finite Jacobi triple product -/

section Poly
open Polynomial

lemma coeff_comp_C_mul_X {R : Type*} [CommRing R] (p : R[X]) (a : R) (n : ℕ) :
    (p.comp (C a * X)).coeff n = a ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [add_comp, hp, hr, mul_add]
  | monomial k b =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- `∏_{k<m} (1 + a q^k Z)` as a polynomial in `Z` over `ℤ⟦q⟧`. -/
noncomputable def gpoly (a : PS) (m : ℕ) : PS[X] :=
  ∏ k ∈ range m, (1 + C (a * 𝕢 ^ k) * X)

/-- The q-binomial theorem (Rothe / Gauss). -/
lemma coeff_gpoly (m : ℕ) : ∀ (a : PS) (i : ℕ),
    (gpoly a m).coeff i = a ^ i * 𝕢 ^ tri (i - 1) * qb m i := by
  induction m with
  | zero =>
    intro a i
    cases i with
    | zero => simp [gpoly]
    | succ i => simp [gpoly, coeff_one]
  | succ m ih =>
    intro a i
    have hg : gpoly a (m + 1) = gpoly (a * 𝕢) m * (1 + C a * X) := by
      have e : ∀ k : ℕ, (1 + C (a * 𝕢 ^ (k + 1)) * X : PS[X]) = 1 + C (a * 𝕢 * 𝕢 ^ k) * X := by
        intro k; rw [pow_succ', mul_assoc]
      simp only [gpoly, prod_range_succ', e, pow_zero, mul_one]
    rw [hg, mul_add, mul_one, coeff_add, show gpoly (a * 𝕢) m * (C a * X) =
      C a * gpoly (a * 𝕢) m * X by ring]
    cases i with
    | zero => simp [ih]
    | succ j =>
      rw [coeff_mul_X, coeff_C_mul, ih, ih, qb_succ_succ]
      have h : 𝕢 ^ tri j = 𝕢 ^ tri (j - 1) * 𝕢 ^ j := by rw [← pow_add, tri_pred_add]
      simp only [Nat.add_sub_cancel]
      rw [h]
      ring

/-- The finite triple product `∏_{k<n} (1 + q^{k+1} Z) ∏_{k ≤ n} (Z + q^k)`. -/
noncomputable def tpoly (n : ℕ) : PS[X] :=
  (∏ k ∈ range n, (1 + C (𝕢 ^ (k + 1)) * X)) * ∏ k ∈ range (n + 1), (X + C (𝕢 ^ k))

lemma sum_range_succ_id (n : ℕ) : ∑ k ∈ range (n + 1), k = tri n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ih, tri_succ]

lemma tpoly_comp (n : ℕ) :
    (tpoly n).comp (C (𝕢 ^ n) * X) = C (𝕢 ^ tri n) * gpoly 1 (2 * n + 1) := by
  rw [tpoly, mul_comp, Polynomial.prod_comp, Polynomial.prod_comp]
  simp only [add_comp, one_comp, mul_comp, C_comp, X_comp]
  have h2 : ∏ k ∈ range (n + 1), (C (𝕢 ^ n) * X + C (𝕢 ^ k)) =
      C (𝕢 ^ tri n) * ∏ k ∈ range (n + 1), (1 + C (1 * 𝕢 ^ k) * X) := by
    have e : ∏ k ∈ range (n + 1), (C (𝕢 ^ n) * X + C (𝕢 ^ k)) =
        ∏ k ∈ range (n + 1), (C (𝕢 ^ k) * (1 + C (1 * 𝕢 ^ (n + 1 - 1 - k)) * X)) := by
      refine prod_congr rfl fun j hj => ?_
      have hj : j ≤ n := by simp at hj; omega
      have : 𝕢 ^ n = 𝕢 ^ j * 𝕢 ^ (n + 1 - 1 - j) := by
        rw [← pow_add]; congr 1; omega
      rw [this, C_mul, one_mul]; ring
    rw [e, prod_mul_distrib, prod_range_reflect (fun k => (1 + C (1 * 𝕢 ^ k) * X : PS[X])),
      ← map_prod, prod_pow_eq_pow_sum, sum_range_succ_id]
  have h1 : ∏ k ∈ range n, (1 + C (𝕢 ^ (k + 1)) * (C (𝕢 ^ n) * X)) =
      ∏ k ∈ range n, (1 + C (1 * 𝕢 ^ (n + 1 + k)) * X) := by
    refine prod_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← C_mul, ← pow_add]; ring_nf
  rw [h1, h2, gpoly, show 2 * n + 1 = (n + 1) + n by ring, prod_range_add _ (n + 1) n]
  ring

lemma coeff_tpoly_mul (n j : ℕ) :
    (𝕢 ^ n) ^ j * (tpoly n).coeff j = 𝕢 ^ (tri n + tri (j - 1)) * qb (2 * n + 1) j := by
  rw [← coeff_comp_C_mul_X, tpoly_comp, coeff_C_mul, coeff_gpoly]
  ring

lemma X_pow_ne_zero (k : ℕ) : (𝕢 ^ k : PS) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero

lemma coeff_tpoly_of_lt (n j : ℕ) (hj : 2 * n + 1 < j) : (tpoly n).coeff j = 0 := by
  have h := coeff_tpoly_mul n j
  rw [qb_eq_zero_of_lt hj, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (X_pow_ne_zero n))

lemma coeff_tpoly_high (n k : ℕ) :
    (tpoly n).coeff (n + 1 + k) = qb (2 * n + 1) (n + 1 + k) * 𝕢 ^ tri k := by
  have h := coeff_tpoly_mul n (n + 1 + k)
  refine mul_left_cancel₀ (pow_ne_zero (n + 1 + k) (X_pow_ne_zero n)) ?_
  rw [h, mul_comm (qb _ _), ← mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  have e : n + 1 + k - 1 = n + k := by omega
  rw [e]
  have := two_mul_tri n; have := two_mul_tri k; have := two_mul_tri (n + k)
  nlinarith

lemma coeff_tpoly_low (k d : ℕ) :
    (tpoly (k + d)).coeff d = qb (2 * (k + d) + 1) (k + d + 1 + k) * 𝕢 ^ tri k := by
  have h := coeff_tpoly_mul (k + d) d
  refine mul_left_cancel₀ (pow_ne_zero d (X_pow_ne_zero (k + d))) ?_
  rw [h, mul_comm (qb _ _), ← mul_assoc, ← pow_mul, ← pow_add]
  have hs : qb (2 * (k + d) + 1) (k + d + 1 + k) = qb (2 * (k + d) + 1) d := by
    have := qb_symm d (k + d + 1 + k)
    rw [show d + (k + d + 1 + k) = 2 * (k + d) + 1 by ring] at this
    exact this.symm
  rw [hs]
  congr 2
  have := two_mul_tri d; have := two_mul_tri k; have := two_mul_tri (k + d)
  have := tri_pred_add d
  nlinarith

lemma tpoly_eq_sum (n : ℕ) :
    tpoly n = ∑ j ∈ range (2 * n + 2), C ((tpoly n).coeff j) * X ^ j := by
  refine Polynomial.ext fun i => ?_
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · exact coeff_tpoly_of_lt n i (by omega)

lemma eval_derivative_tpoly (n : ℕ) :
    (derivative (tpoly n)).eval (-1) = ep n * ((-1) ^ n * ep n) := by
  have hB : ∏ k ∈ range (n + 1), (X + C (𝕢 ^ k)) =
      (∏ k ∈ range n, (X + C (𝕢 ^ (k + 1)))) * (X + 1) := by
    rw [prod_range_succ']; simp
  have hA : (∏ k ∈ range n, (1 + C (𝕢 ^ (k + 1)) * X)).eval (-1) = ep n := by
    rw [eval_prod, ep]
    refine prod_congr rfl fun k _ => ?_
    simp [sub_eq_add_neg]
  have hB' : (∏ k ∈ range n, (X + C (𝕢 ^ (k + 1)))).eval (-1) = (-1) ^ n * ep n := by
    rw [eval_prod, ep, show ((-1 : PS)) ^ n = ∏ _k ∈ range n, (-1) by simp, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ => ?_
    simp; ring
  rw [tpoly, hB, derivative_mul, derivative_mul]
  simp only [eval_add, eval_mul, hA, hB']
  simp

lemma eval_derivative_sum (N : ℕ) (c : ℕ → PS) :
    (derivative (∑ j ∈ range N, C (c j) * X ^ j)).eval (-1) =
      ∑ j ∈ range N, c j * j * (-1) ^ (j - 1) := by
  simp only [derivative_sum, derivative_C_mul_X_pow, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  simp

end Poly

lemma sum_range_pair {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ∑ j ∈ range (2 * n + 2), g j = ∑ k ∈ range (n + 1), (g (n - k) + g (n + 1 + k)) := by
  rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, sum_range_add, sum_add_distrib]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k _ => ?_
  congr 1

lemma natCast_mul_neg_one_pow_pred (j : ℕ) :
    (j : PS) * (-1) ^ (j - 1) = -((j : PS) * (-1) ^ j) := by
  cases j with
  | zero => simp
  | succ j => simp [pow_succ]

/-- The finite form of Jacobi's identity (from the finite triple product):
`∏_{i ≤ n} (1 - q^i)^2 = ∑_{k ≤ n} (-1)^k (2k+1) [2n+1, n+1+k]_q q^{k(k+1)/2}`. -/
lemma ep_sq (n : ℕ) : ep n ^ 2 = ∑ k ∈ range (n + 1),
    (-1) ^ k * (2 * k + 1) * qb (2 * n + 1) (n + 1 + k) * 𝕢 ^ tri k := by
  have h := eval_derivative_tpoly n
  rw [tpoly_eq_sum, eval_derivative_sum, sum_range_pair] at h
  have h' : ∑ k ∈ range (n + 1), ((tpoly n).coeff (n - k) * ↑(n - k) * (-1) ^ (n - k - 1) +
      (tpoly n).coeff (n + 1 + k) * ↑(n + 1 + k) * (-1) ^ (n + 1 + k - 1)) =
      (-1) ^ n * ∑ k ∈ range (n + 1),
        (-1) ^ k * (2 * k + 1) * qb (2 * n + 1) (n + 1 + k) * 𝕢 ^ tri k := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by simp at hk; omega⟩
    rw [Nat.add_sub_cancel_left, coeff_tpoly_low, coeff_tpoly_high, mul_assoc, mul_assoc,
      natCast_mul_neg_one_pow_pred, show k + d + 1 + k - 1 = 2 * k + d by omega]
    have e1 : ((-1 : PS)) ^ (2 * k + d) = (-1) ^ d := by rw [pow_add, pow_mul]; simp
    have e2 : ((-1 : PS)) ^ (k + d) * (-1) ^ k = (-1) ^ d := by
      rw [← pow_add, show k + d + k = 2 * k + d by ring, e1]
    have e3 : ((-1 : PS)) ^ (k * 2) = 1 := by rw [pow_mul']; simp
    rw [e1]
    push_cast
    ring_nf
    rw [e3]
    ring
  rw [h'] at h
  have h2 : ((-1 : PS) ^ n) * ep n ^ 2 = (-1) ^ n * ∑ k ∈ range (n + 1),
      (-1) ^ k * (2 * k + 1) * qb (2 * n + 1) (n + 1 + k) * 𝕢 ^ tri k := by
    rw [h]; ring
  exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) h2

/-! ## Jacobi's identity -/

lemma X_pow_dvd_prod_sub_one (N c m : ℕ) (h : N ≤ c + 1) :
    𝕢 ^ N ∣ ∏ i ∈ range m, (1 - 𝕢 ^ (c + i + 1)) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, show ∀ A x : PS, A * (1 - x) - 1 = (A - 1) - A * x by intros; ring]
    exact ih.sub (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _)

lemma ep_add (a b : ℕ) : ep (a + b) = ep a * ∏ i ∈ range b, (1 - 𝕢 ^ (a + i + 1)) := by
  rw [ep, ep, prod_range_add]

/-- The key congruence: `(q)_n [2n+1, n+1+k] q^{k(k+1)/2} ≡ q^{k(k+1)/2} (mod q^{n+1})`. -/
lemma key_cong (k d : ℕ) :
    𝕢 ^ (k + d + 1) ∣ ep (k + d) * qb (2 * (k + d) + 1) (k + d + 1 + k) * 𝕢 ^ tri k - 𝕢 ^ tri k := by
  set m := k + d + 1 + k with hm
  have hq := qb_mul_ep _ m d rfl
  rw [show m + d = 2 * (k + d) + 1 by omega] at hq
  set R1 := ∏ i ∈ range d, (1 - 𝕢 ^ (m + i + 1)) with hR1
  set R2 := ∏ i ∈ range k, (1 - 𝕢 ^ (d + i + 1)) with hR2
  have e1 : ep (2 * (k + d) + 1) = ep m * R1 := by
    rw [show 2 * (k + d) + 1 = m + d by omega, ep_add]
  have e2 : qb (2 * (k + d) + 1) m * ep d = R1 := by
    refine mul_left_cancel₀ (ep_ne_zero m) ?_
    rw [← e1, ← hq]; ring
  have e3 : ep (k + d) = ep d * R2 := by rw [add_comm, ep_add]
  have e4 : ep (k + d) * qb (2 * (k + d) + 1) m * 𝕢 ^ tri k - 𝕢 ^ tri k =
      (R2 * (R1 - 1) + (R2 - 1)) * 𝕢 ^ tri k := by
    rw [e3, ← e2]; ring
  rw [e4]
  have h1 : 𝕢 ^ (d + 1) ∣ R1 - 1 := X_pow_dvd_prod_sub_one _ _ _ (by omega)
  have h2 : 𝕢 ^ (d + 1) ∣ R2 - 1 := X_pow_dvd_prod_sub_one _ _ _ (by omega)
  have h3 : 𝕢 ^ (d + 1 + tri k) ∣ (R2 * (R1 - 1) + (R2 - 1)) * 𝕢 ^ tri k := by
    rw [pow_add]
    exact mul_dvd_mul ((h1.mul_left _).add h2) dvd_rfl
  exact (pow_dvd_pow _ (by have := le_tri k; omega)).trans h3

/-- Finite Jacobi identity: `(q)_n^3 ≡ ∑_{k ≤ n} (-1)^k (2k+1) q^{k(k+1)/2} (mod q^{n+1})`. -/
lemma ep_cube_cong (n : ℕ) :
    𝕢 ^ (n + 1) ∣ ep n ^ 3 - ∑ k ∈ range (n + 1), (-1) ^ k * (2 * k + 1) * 𝕢 ^ tri k := by
  have e : ep n ^ 3 - ∑ k ∈ range (n + 1), (-1) ^ k * (2 * k + 1) * 𝕢 ^ tri k =
      ∑ k ∈ range (n + 1), (-1) ^ k * (2 * k + 1) *
        (ep n * qb (2 * n + 1) (n + 1 + k) * 𝕢 ^ tri k - 𝕢 ^ tri k) := by
    rw [pow_succ', ep_sq, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  refine dvd_sum fun k hk => ?_
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by simp at hk; omega⟩
  exact (key_cong k d).mul_left _

/-- **Jacobi's series** `∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`. -/
noncomputable def jacobiSeries (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun m => ∑ k ∈ range (m + 1), if tri k = m then (-1) ^ k * (2 * k + 1) else 0

lemma coeff_partialJacobi (n m : ℕ) (hm : m ≤ n) :
    PowerSeries.coeff m (∑ k ∈ range (n + 1), (-1 : PS) ^ k * (2 * (k : PS) + 1) * 𝕢 ^ tri k) =
      PowerSeries.coeff m (jacobiSeries ℤ) := by
  rw [map_sum, jacobiSeries, PowerSeries.coeff_mk]
  have h : ∀ k : ℕ, PowerSeries.coeff m ((-1 : PS) ^ k * (2 * (k : PS) + 1) * 𝕢 ^ tri k) =
      if tri k = m then (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) else 0 := by
    intro k
    have : ((-1 : PS) ^ k * (2 * (k : PS) + 1)) = PowerSeries.C ((-1 : ℤ) ^ k * (2 * k + 1)) := by
      simp
    rw [this, PowerSeries.coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [h]
  symm
  refine sum_subset (by simp; omega) fun k hk hk' => ?_
  simp only [mem_range] at hk hk'
  have := le_tri k
  simp [show tri k ≠ m by omega]

/-- **Jacobi's identity** (topology-free form): the cube of Euler's pentagonal series is Jacobi's
series, `(∑_k (-1)^k X^{k(3k-1)/2})^3 = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`. -/
theorem pentagonalSeries_pow_three : PowerSeries.pentagonalSeries ℤ ^ 3 = jacobiSeries ℤ := by
  ext m
  have hev : ∀ᶠ s in Filter.atTop, ∀ m' ∈ range (m + 1),
      PowerSeries.coeff m' (∏ n ∈ s, (1 - PowerSeries.X ^ (n + 1) : PS)) =
        PowerSeries.coeff m' (PowerSeries.pentagonalSeries ℤ) :=
    (Filter.eventually_all_finset _).mpr fun m' _ =>
      PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq ℤ m'
  obtain ⟨N, hN, hNm⟩ :=
    ((Filter.tendsto_finset_range.eventually hev).and (Filter.eventually_ge_atTop m)).exists
  have h1 : 𝕢 ^ (m + 1) ∣ PowerSeries.pentagonalSeries ℤ - ep N := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun i hi => ?_
    rw [map_sub, ep, hN i (mem_range.mpr hi), sub_self]
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ 3)
  have h3 := (pow_dvd_pow 𝕢 (by omega : m + 1 ≤ N + 1)).trans (ep_cube_cong N)
  have h4 := PowerSeries.X_pow_dvd_iff.mp (h2.add h3) m (by omega)
  rw [← coeff_partialJacobi N m hNm]
  rw [sub_add_sub_cancel, map_sub, sub_eq_zero] at h4
  exact h4

open scoped PowerSeries.WithPiTopology in
/-- **Jacobi's identity** `∏_{n ≥ 1} (1 - X^n)^3 = ∑_{k ≥ 0} (-1)^k (2k+1) X^{k(k+1)/2}`. -/
theorem tprod_one_sub_X_pow_pow_three :
    (∏' n, (1 - PowerSeries.X ^ (n + 1) : PS)) ^ 3 = jacobiSeries ℤ := by
  rw [PowerSeries.WithPiTopology.tprod_one_sub_X_pow]
  exact pentagonalSeries_pow_three


/-! ## Euler's partition identity -/

/-- The partition generating function `∑ p(n) X^n`, `p(n) = Fintype.card (Nat.Partition n)`. -/
noncomputable def partitionSeries (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : R)

@[simp] lemma coeff_partitionSeries (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.coeff n (partitionSeries R) = Fintype.card (Nat.Partition n) := by
  simp [partitionSeries]

open scoped PowerSeries.WithPiTopology in
/-- Euler's product for the partition generating function:
`∑ p(n) X^n = ∏_{i ≥ 1} ∑_{j ≥ 0} X^{ij}`, from Mathlib's `Nat.Partition.genFun` machinery. -/
theorem hasProd_partitionSeries :
    HasProd (fun i : ℕ => ∑' j : ℕ, (PowerSeries.X : PS) ^ ((i + 1) * j)) (partitionSeries ℤ) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ => True)
  simp only [ite_true] at h
  convert h using 1
  ext n
  simp [partitionSeries, Nat.Partition.restricted]

open scoped PowerSeries.WithPiTopology in
/-- **Euler's partition identity** `(∑ p(n) X^n) · ∏_{n ≥ 1} (1 - X^n) = 1` in `ℤ⟦X⟧`. -/
theorem partitionSeries_mul_tprod :
    partitionSeries ℤ * ∏' n, (1 - PowerSeries.X ^ (n + 1) : PS) = 1 := by
  have h := hasProd_partitionSeries.mul
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow (R := ℤ)).hasProd
  have h1 : (fun i : ℕ => (∑' j : ℕ, (PowerSeries.X : PS) ^ ((i + 1) * j)) *
      (1 - PowerSeries.X ^ (i + 1))) = fun _ => 1 := by
    funext i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  rw [h1] at h
  exact h.unique hasProd_one

/-- **Euler's partition identity**, with the product expanded by the pentagonal number theorem:
`(∑ p(n) X^n) · (∑_k (-1)^k X^{k(3k-1)/2}) = 1`. -/
theorem partitionSeries_mul_pentagonalSeries :
    partitionSeries ℤ * PowerSeries.pentagonalSeries ℤ = 1 := by
  rw [← PowerSeries.WithPiTopology.tprod_one_sub_X_pow]
  exact partitionSeries_mul_tprod


/-! ## Euler's recurrence -/

lemma abs_le_pentagonal (k : ℤ) : -(pentagonal k : ℤ) ≤ k ∧ k ≤ pentagonal k := by
  have h := two_mul_natCast_pentagonal k
  constructor <;> rcases le_or_gt k 0 with hk | hk <;> nlinarith

/-- The (finite) set of indices `k ∈ ℤ` with `k(3k-1)/2 ≤ n`. -/
def eulerSet (n : ℕ) : Finset ℤ := (Icc (-(n : ℤ)) n).filter fun k => pentagonal k ≤ n

lemma mem_eulerSet {n : ℕ} {k : ℤ} : k ∈ eulerSet n ↔ pentagonal k ≤ n := by
  have := abs_le_pentagonal k
  simp only [eulerSet, mem_filter, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨⟨?_, ?_⟩, h⟩ <;> omega

/-- Convolution with the pentagonal series, written as a sum over pentagonal indices. -/
lemma sum_pentagonal_conv (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ range (n + 1), PowerSeries.coeff i (PowerSeries.pentagonalSeries ℤ) * f (n - i) =
      ∑ k ∈ eulerSet n, (k.negOnePow : ℤ) * f (n - pentagonal k) := by
  set F : ℕ → ℤ := fun j => PowerSeries.coeff j (PowerSeries.pentagonalSeries ℤ) * f (n - j)
  symm
  calc ∑ k ∈ eulerSet n, (k.negOnePow : ℤ) * f (n - pentagonal k)
      = ∑ k ∈ eulerSet n, F (pentagonal k) := by
        refine sum_congr rfl fun k _ => ?_
        simp only [F, PowerSeries.coeff_pentagonalSeries_pentagonal, Int.cast_id]
    _ = ∑ j ∈ (eulerSet n).image pentagonal, F j :=
        (sum_image fun x _ y _ h => pentagonal_injective h).symm
    _ = ∑ j ∈ range (n + 1), F j := by
        refine sum_subset ?_ ?_
        · intro j hj
          obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
          have := mem_eulerSet.mp hk
          simp only [mem_range]; omega
        · intro j hj hj'
          by_cases hr : j ∈ Set.range pentagonal
          · obtain ⟨k, rfl⟩ := hr
            exact absurd (mem_image_of_mem _ (mem_eulerSet.mpr (by simp at hj; omega))) hj'
          · simp [F, PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hr]

/-- Coefficientwise form of `partitionSeries * pentagonalSeries = 1`:
`∑_{k} (-1)^k p(n - k(3k-1)/2) = [n = 0]`. -/
theorem sum_eulerSet_partition (n : ℕ) :
    ∑ k ∈ eulerSet n, (k.negOnePow : ℤ) * Fintype.card (Nat.Partition (n - pentagonal k)) =
      if n = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) partitionSeries_mul_pentagonalSeries
  rw [mul_comm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at h
  simp only [coeff_partitionSeries] at h
  rw [← sum_pentagonal_conv n (fun m => (Fintype.card (Nat.Partition m) : ℤ)), h]

/-- **Euler's recurrence for the partition function**: for `n ≥ 1`,
`p(n) = ∑_{k ≠ 0} (-1)^{k+1} p(n - k(3k-1)/2)`, the sum over all nonzero integers `k` with
`k(3k-1)/2 ≤ n` (i.e. `p(n) = p(n-1) + p(n-2) - p(n-5) - p(n-7) + p(n-12) + p(n-15) - ⋯`). -/
theorem partition_recurrence (n : ℕ) (hn : 0 < n) :
    (Fintype.card (Nat.Partition n) : ℤ) =
      ∑ k ∈ (Icc (-(n : ℤ)) n).filter (fun k => k ≠ 0 ∧ pentagonal k ≤ n),
        ((k + 1).negOnePow : ℤ) * Fintype.card (Nat.Partition (n - pentagonal k)) := by
  have h := sum_eulerSet_partition n
  have h0 : (if n = 0 then (1 : ℤ) else 0) = 0 := by simp; omega
  have hp0 : pentagonal 0 = 0 := by decide
  rw [h0, ← add_sum_erase _ _ (mem_eulerSet.mpr (by rw [hp0]; omega))] at h
  have e : (Icc (-(n : ℤ)) n).filter (fun k => k ≠ 0 ∧ pentagonal k ≤ n) = (eulerSet n).erase 0 := by
    ext k; simp only [eulerSet, mem_filter, mem_erase]; tauto
  rw [e]
  simp only [Int.negOnePow_succ, Units.val_neg, neg_mul, sum_neg_distrib]
  rw [hp0, Int.negOnePow_zero, Nat.sub_zero] at h
  push_cast at h
  linarith


/-! ### Sanity check: `p(0), …, p(10)` computed from Euler's recurrence -/

lemma partition_recurrence_of_eq (n : ℕ) (hn : 0 < n) (S : Finset ℤ)
    (hS : (Icc (-(n : ℤ)) n).filter (fun k => k ≠ 0 ∧ pentagonal k ≤ n) = S) :
    (Fintype.card (Nat.Partition n) : ℤ) =
      ∑ k ∈ S, ((k + 1).negOnePow : ℤ) * Fintype.card (Nat.Partition (n - pentagonal k)) := by
  rw [partition_recurrence n hn, hS]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 20000 in
theorem partition_values :
    (List.range 11).map (fun n => Fintype.card (Nat.Partition n)) =
      [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42] := by
  have h0 : (Fintype.card (Nat.Partition 0) : ℤ) = 1 := by
    have h := sum_eulerSet_partition 0
    rw [show eulerSet 0 = {0} by decide] at h
    simp at h ⊢
  have p1 : pentagonal 1 = 1 := by decide
  have p2 : pentagonal (-1) = 2 := by decide
  have p3 : pentagonal 2 = 5 := by decide
  have p4 : pentagonal (-2) = 7 := by decide
  have s1 : ((2 : ℤ).negOnePow : ℤ) = 1 := by decide
  have s2 : ((0 : ℤ).negOnePow : ℤ) = 1 := by decide
  have s3 : ((3 : ℤ).negOnePow : ℤ) = -1 := by decide
  have s4 : ((-1 : ℤ).negOnePow : ℤ) = -1 := by decide
  have h1 : (Fintype.card (Nat.Partition 1) : ℤ) = 1 := by
    rw [partition_recurrence_of_eq 1 (by norm_num) {1} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0]
  have h2 : (Fintype.card (Nat.Partition 2) : ℤ) = 2 := by
    rw [partition_recurrence_of_eq 2 (by norm_num) {1, -1} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1]
  have h3 : (Fintype.card (Nat.Partition 3) : ℤ) = 3 := by
    rw [partition_recurrence_of_eq 3 (by norm_num) {1, -1} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2]
  have h4 : (Fintype.card (Nat.Partition 4) : ℤ) = 5 := by
    rw [partition_recurrence_of_eq 4 (by norm_num) {1, -1} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3]
  have h5 : (Fintype.card (Nat.Partition 5) : ℤ) = 7 := by
    rw [partition_recurrence_of_eq 5 (by norm_num) {1, -1, 2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4]
  have h6 : (Fintype.card (Nat.Partition 6) : ℤ) = 11 := by
    rw [partition_recurrence_of_eq 6 (by norm_num) {1, -1, 2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5]
  have h7 : (Fintype.card (Nat.Partition 7) : ℤ) = 15 := by
    rw [partition_recurrence_of_eq 7 (by norm_num) {1, -1, 2, -2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5, h6]
  have h8 : (Fintype.card (Nat.Partition 8) : ℤ) = 22 := by
    rw [partition_recurrence_of_eq 8 (by norm_num) {1, -1, 2, -2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5, h6, h7]
  have h9 : (Fintype.card (Nat.Partition 9) : ℤ) = 30 := by
    rw [partition_recurrence_of_eq 9 (by norm_num) {1, -1, 2, -2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have h10 : (Fintype.card (Nat.Partition 10) : ℤ) = 42 := by
    rw [partition_recurrence_of_eq 10 (by norm_num) {1, -1, 2, -2} (by decide)]
    simp [p1, p2, p3, p4, s1, s2, s3, s4, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append]
  norm_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

/-! ## Ramanujan's congruence `p(5n+4) ≡ 0 (mod 5)` -/

/-- The residue computation: `24 (k(3k-1)/2 + l(l+1)/2 + 1) = (6k-1)^2 + 3(2l+1)^2 + 20`, and
`x^2 + 3y^2 ≡ 0 (mod 5)` forces `y ≡ 0`. -/
lemma five_dvd_of_pentagonal_add_tri (k : ℤ) (l : ℕ) (h : (5 : ℤ) ∣ pentagonal k + tri l + 1) :
    (5 : ℤ) ∣ 2 * l + 1 := by
  have hP := two_mul_natCast_pentagonal k
  have hT : (2 : ℤ) * tri l = l * (l + 1) := by exact_mod_cast two_mul_tri l
  have hid : (24 : ℤ) * (pentagonal k + tri l + 1) = (6 * k - 1) ^ 2 + 3 * (2 * l + 1) ^ 2 + 20 := by
    linear_combination 12 * hP + 12 * hT
  have h0 : (((pentagonal k + tri l + 1 : ℤ)) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr (by exact_mod_cast h)
  have h1 : (((6 * k - 1 : ℤ)) : ZMod 5) ^ 2 + 3 * (((2 * l + 1 : ℤ)) : ZMod 5) ^ 2 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod 5) hid
    push_cast at this h0 ⊢
    rw [h0, mul_zero] at this
    have h20 : (20 : ZMod 5) = 0 := by decide
    rw [h20, add_zero] at this
    exact this.symm
  have key : ∀ x y : ZMod 5, x ^ 2 + 3 * y ^ 2 = 0 → y = 0 := by decide
  have h2 := key _ _ h1
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h2

lemma five_dvd_coeff_jacobi {j : ℕ} {k : ℤ} (h : (5 : ℤ) ∣ pentagonal k + j + 1) :
    (5 : ℤ) ∣ PowerSeries.coeff j (jacobiSeries ℤ) := by
  rw [jacobiSeries, PowerSeries.coeff_mk]
  refine dvd_sum fun l _ => ?_
  split_ifs with hl
  · subst hl
    exact (five_dvd_of_pentagonal_add_tri k l h).mul_left _
  · exact dvd_zero _

/-- The coefficients of `X · ∏(1 - X^n)^4 = X · (pentagonal series) · (Jacobi series)` at
multiples of `5` are divisible by `5`. -/
lemma five_dvd_coeff_X_mul_pentagonal_mul_jacobi (a : ℕ) (ha : 5 ∣ a) :
    (5 : ℤ) ∣ PowerSeries.coeff a
      (PowerSeries.X * PowerSeries.pentagonalSeries ℤ * jacobiSeries ℤ) := by
  rcases a with _ | m
  · simp
  rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
  refine dvd_sum fun x hx => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hr : x.1 ∈ Set.range pentagonal
  · obtain ⟨k, hk⟩ := hr
    refine Dvd.dvd.mul_left (five_dvd_coeff_jacobi (k := k) ?_) _
    rw [hk]
    have : (5 : ℤ) ∣ ((m + 1 : ℕ) : ℤ) := by exact_mod_cast ha
    rw [← hx] at this
    push_cast at this
    exact this
  · simp [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hr]

/-- **Ramanujan's congruence**: `p(5n + 4) ≡ 0 (mod 5)`. -/
theorem ramanujan_congruence_five (n : ℕ) : 5 ∣ Fintype.card (Nat.Partition (5 * n + 4)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := partitionSeries ℤ
  set E := PowerSeries.pentagonalSeries ℤ
  set J := jacobiSeries ℤ
  have key : (PowerSeries.X : PS) * P = (PowerSeries.X * E * J) * P ^ 5 := by
    have hPE : P * E = 1 := partitionSeries_mul_pentagonalSeries
    have hJ : E ^ 3 = J := pentagonalSeries_pow_three
    rw [← hJ]
    calc (PowerSeries.X : PS) * P = PowerSeries.X * P * (P * E) ^ 4 := by rw [hPE]; ring
      _ = _ := by ring
  set φ := PowerSeries.map (Int.castRingHom (ZMod 5))
  have key' := congrArg (fun f => PowerSeries.coeff (5 * n + 5) (φ f)) key
  simp only [map_mul, map_pow] at key'
  rw [show 5 * n + 5 = (5 * n + 4) + 1 by ring, PowerSeries.map_X, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_map] at key'
  rw [← ZMod.natCast_eq_zero_iff]
  have hp : ((Fintype.card (Nat.Partition (5 * n + 4)) : ℤ) : ZMod 5) = 0 := by
    have hl : (Int.castRingHom (ZMod 5)) (PowerSeries.coeff (5 * n + 4) P) =
        ((Fintype.card (Nat.Partition (5 * n + 4)) : ℤ) : ZMod 5) := by simp [P]
    rw [← hl, key', PowerSeries.coeff_mul]
    refine sum_eq_zero fun x hx => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h5 : 5 ∣ x.2
    · have h1 : 5 ∣ x.1 := by omega
      have := five_dvd_coeff_X_mul_pentagonal_mul_jacobi x.1 h1
      have hm : (PowerSeries.X : PowerSeries (ZMod 5)) * φ E * φ J =
          φ (PowerSeries.X * E * J) := by simp only [φ, map_mul, PowerSeries.map_X]
      rw [hm, PowerSeries.coeff_map, eq_intCast,
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr (by exact_mod_cast this), zero_mul]
    · rw [← PowerSeries.map_frobenius_expand 5 (by norm_num), PowerSeries.coeff_map,
        PowerSeries.coeff_expand_of_not_dvd 5 _ _ h5, map_zero, mul_zero]
  exact_mod_cast hp

end Fugue.Partitions
