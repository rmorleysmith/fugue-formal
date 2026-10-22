import Mathlib

set_option autoImplicit false

/-!
# Ramanujan's formula: `∑ σ_a(n) σ_b(n) n^{-s} = ζ(s)ζ(s-a)ζ(s-b)ζ(s-a-b) / ζ(2s-a-b)`

The prototype of Rankin–Selberg (the "Rankin–Selberg closure" of the multiplicativity locus).

* `key'` : the Euler-factor identity in `R⟦X⟧` (any commutative ring),
  `(∑ A_x(k) A_y(k) X^k) · ∑ (xy)^j X^{2j} = 1/((1-X)(1-xX)(1-yX)(1-xyX))`, proved by
  first-order recurrences, with no division.
* `sigma_pmul_sigma_mul_sqPow` : `(σ_a · σ_b) * S_{a+b} = ζ * Id^a * Id^b * Id^{a+b}` in
  `ArithmeticFunction ℕ`, where `S_k(m²) = m^k` and `S_k = 0` off the squares; both sides are
  multiplicative and the prime-power generating series `P p` turns `*` into power-series product.
* `LSeries_sigma_mul_sigma` : for `re s > a + b + 1`,
  `L(σ_a σ_b, s) · ζ(2s - a - b) = ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b)`.
* `LSeries_card_divisors_sq` : sanity check `a = b = 0`, `L(d², s) ζ(2s) = ζ(s)⁴`.
-/

namespace Fugue.RankinSelberg

open PowerSeries

section PowerSeriesAlgebra

variable {R : Type*} [CommRing R]

/-- A first-order recurrence `c (k+1) = d * c k + e (k+1)` in power-series form. -/
theorem mk_mul_one_sub (c e : ℕ → R) (d : R) (h0 : c 0 = e 0)
    (h : ∀ k, c (k + 1) = d * c k + e (k + 1)) :
    mk c * (1 - C d * X) = mk e := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (mk c) (C d), mul_assoc,
    coeff_C_mul]
  rcases n with _ | n
  · simp [h0]
  · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_mk, h]; ring

theorem mk_delta : (mk fun k => if k = 0 then (1 : R) else 0) = 1 := by
  ext n; simp [coeff_one]

/-- Geometric series `∑ c^k X^k`. -/
noncomputable def G (c : R) : PowerSeries R := mk fun k => c ^ k

theorem G_mul (c : R) : G c * (1 - C c * X) = 1 := by
  rw [G, mk_mul_one_sub (fun k => c ^ k) (fun k => if k = 0 then (1 : R) else 0) c (by simp)
    (fun k => by simp [pow_succ]; ring), mk_delta]

/-- The square-supported sequence `s (2j) = t^j`, `s (2j+1) = 0`. -/
noncomputable def Q (t : R) : PowerSeries R := mk fun k => if Even k then t ^ (k / 2) else 0

theorem Q_mul (t : R) : Q t * (1 - C t * X ^ 2) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (Q t) (C t), mul_assoc,
    coeff_C_mul, coeff_mul_X_pow', Q, coeff_mk, coeff_one]
  rcases n with _ | _ | n
  · simp
  · simp
  · simp only [show 2 ≤ n + 1 + 1 by omega, ite_true, coeff_mk,
      show n + 1 + 1 ≠ 0 by omega, ite_false, show n + 1 + 1 - 2 = n by omega]
    have : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
    by_cases hn : Even n
    · simp only [this.2 hn, hn, ite_true, show (n + 1 + 1) / 2 = n / 2 + 1 by omega, pow_succ]
      ring
    · simp only [mt this.1 hn, hn, ite_false]; ring

/-- `∑_{i ≤ k} x^i`. -/
def A (x : R) (k : ℕ) : R := ∑ i ∈ Finset.range (k + 1), x ^ i

theorem A_succ (x : R) (k : ℕ) : A x (k + 1) = A x k + x ^ (k + 1) := by
  rw [A, Finset.sum_range_succ, ← A]

/-- The Euler-factor identity `∑ σ_a(p^k)σ_b(p^k) X^k · (1-X)(1-xX)(1-yX)(1-xyX) = 1 - xyX²`
in coefficient form. -/
theorem key (x y : R) :
    mk (fun k => A x k * A y k) * ((1 - X) * (1 - C x * X) * (1 - C y * X) * (1 - C (x * y) * X))
      = 1 - C (x * y) * X ^ 2 := by
  set P1 : PowerSeries R := mk fun k => x ^ k * A y k
  set P2 : PowerSeries R := mk fun k => y ^ (k + 1) * A x k
  have h1 : mk (fun k => A x k * A y k) * (1 - X) = P1 + X * P2 := by
    have := mk_mul_one_sub (fun k => A x k * A y k)
      (fun k => x ^ k * A y k + if k = 0 then 0 else y ^ k * A x (k - 1)) 1
      (by simp [A])
      (fun k => by
        simp only [A_succ, show k + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
        ring)
    rw [map_one, one_mul] at this
    rw [this]
    ext n
    rcases n with _ | n
    · simp [P1, P2]
    · simp [P1, P2, coeff_succ_X_mul]
  have h2 : P1 * (1 - C x * X) = G (x * y) :=
    mk_mul_one_sub _ _ _ (by simp [A]) (fun k => by simp only [A_succ]; ring)
  have h3 : P2 * (1 - C y * X) = C y * G (x * y) := by
    have : C y * G (x * y) = mk fun k => y * (x * y) ^ k := by
      ext n; simp [G, coeff_C_mul]
    rw [this]
    exact mk_mul_one_sub _ _ _ (by simp [A]) (fun k => by simp only [A_succ]; ring)
  have h4 := G_mul (x * y)
  rw [map_mul] at h4 ⊢
  linear_combination (1 - C x * X) * (1 - C y * X) * (1 - C x * C y * X) * h1
    + (1 - C y * X) * (1 - C x * C y * X) * h2
    + X * (1 - C x * X) * (1 - C x * C y * X) * h3
    + ((1 - C y * X) + X * C y * (1 - C x * X)) * h4

/-- The power-series form of the prime-power identity. -/
theorem key' (x y : R) :
    mk (fun k => A x k * A y k) * Q (x * y) = G 1 * G x * G y * G (x * y) := by
  have hc := key x y
  have hs := Q_mul (x * y)
  have g1 := G_mul (1 : R)
  have gx := G_mul x
  have gy := G_mul y
  have gxy := G_mul (x * y)
  rw [map_one, one_mul] at g1
  set c := mk (fun k => A x k * A y k)
  set V := (1 - X) * (1 - C x * X) * (1 - C y * X) * (1 - C (x * y) * X)
  set Gs := G 1 * G x * G y * G (x * y)
  have hV : Gs * V = 1 := by
    simp only [Gs, V]
    linear_combination (G x * (1 - C x * X)) * (G y * (1 - C y * X)) *
      (G (x * y) * (1 - C (x * y) * X)) * g1
      + (G y * (1 - C y * X)) * (G (x * y) * (1 - C (x * y) * X)) * gx
      + (G (x * y) * (1 - C (x * y) * X)) * gy + gxy
  linear_combination (-(c * Q (x * y))) * hV + (Gs * Q (x * y)) * hc + Gs * hs

end PowerSeriesAlgebra

section Arithmetic

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma

/-- `S_k(m²) = m^k`, `S_k(n) = 0` if `n` is not a nonzero square. -/
def sqPow (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n ≠ 0 ∧ IsSquare n then n.sqrt ^ k else 0, by simp⟩

theorem sqPow_apply (k n : ℕ) :
    sqPow k n = if n ≠ 0 ∧ IsSquare n then n.sqrt ^ k else 0 := rfl

theorem sqPow_sq (k m : ℕ) (hm : m ≠ 0) : sqPow k (m * m) = m ^ k := by
  rw [sqPow_apply, ite_eq_left ⟨by positivity, ⟨m, rfl⟩⟩, Nat.sqrt_eq]

theorem isSquare_of_coprime {m n : ℕ} (h : m.Coprime n) (hmn : IsSquare (m * n)) :
    IsSquare m := by
  obtain ⟨w, hw⟩ := hmn
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (a := m) (b := n) (c := w) (k := 2)
    (by rw [Nat.isUnit_iff]; exact h) (by rw [hw, sq])
  exact ⟨d, by rw [hd, sq]⟩

theorem isMultiplicative_sqPow (k : ℕ) : (sqPow k).IsMultiplicative := by
  refine ⟨by simp [sqPow_apply], fun {m n} h => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sqPow_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sqPow_apply]
  by_cases hsq : IsSquare m ∧ IsSquare n
  · obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := hsq
    have hu : u ≠ 0 := by rintro rfl; simp at hm
    have hv : v ≠ 0 := by rintro rfl; simp at hn
    rw [show u * u * (v * v) = (u * v) * (u * v) by ring, sqPow_sq _ _ (by positivity),
      sqPow_sq _ _ hu, sqPow_sq _ _ hv, mul_pow]
  · have : ¬ IsSquare (m * n) := by
      intro hmn
      exact hsq ⟨isSquare_of_coprime h hmn,
        isSquare_of_coprime h.symm (by rwa [mul_comm] at hmn)⟩
    rw [sqPow_apply, ite_eq_right (by tauto)]
    rcases not_and_or.1 hsq with h' | h'
    · rw [sqPow_apply k m, ite_eq_right (by tauto), zero_mul]
    · rw [sqPow_apply k n, ite_eq_right (by tauto), mul_zero]

theorem sqPow_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    sqPow k (p ^ j) = if Even j then (p ^ (j / 2)) ^ k else 0 := by
  rw [sqPow_apply]
  by_cases hj : Even j
  · obtain ⟨i, rfl⟩ := hj
    rw [ite_eq_left ⟨pow_ne_zero _ hp.ne_zero, ⟨p ^ i, by rw [pow_add]⟩⟩, ite_eq_left ⟨i, rfl⟩,
      show (i + i) / 2 = i by omega, pow_add, Nat.sqrt_eq]
  · rw [ite_eq_right hj, ite_eq_right]
    rintro ⟨-, w, hw⟩
    apply hj
    have hw0 : w ≠ 0 := by rintro rfl; simp [hp.ne_zero] at hw
    have := congrArg (fun n => n.factorization p) hw
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_mul hw0 hw0, Finsupp.add_apply, hp.factorization_self, mul_one] at this
    exact ⟨_, this⟩

/-- The generating series of `f` along the powers of `p`, with integer coefficients. -/
noncomputable def P (p : ℕ) (f : ArithmeticFunction ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun j => ((f (p ^ j) : ℕ) : ℤ)

theorem P_mul {p : ℕ} (hp : p.Prime) (f g : ArithmeticFunction ℕ) :
    P p (f * g) = P p f * P p g := by
  ext k
  rw [P, P, P, PowerSeries.coeff_mk, PowerSeries.coeff_mul, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => f i * g j), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
      PowerSeries.coeff i (PowerSeries.mk fun j => ((f (p ^ j) : ℕ) : ℤ)) *
      PowerSeries.coeff j (PowerSeries.mk fun j => ((g (p ^ j) : ℕ) : ℤ)))]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, Nat.pow_div (by omega) hp.pos]

theorem P_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : P p (pow k) = G ((p : ℤ) ^ k) := by
  ext j
  simp [P, G, pow_apply, hp.ne_zero, ← pow_mul, mul_comm]

theorem P_sigma_pmul {p : ℕ} (hp : p.Prime) (a b : ℕ) :
    P p ((sigma a).pmul (sigma b)) =
      PowerSeries.mk fun k => A ((p : ℤ) ^ a) k * A ((p : ℤ) ^ b) k := by
  ext j
  simp [P, A, pmul_apply, sigma_apply_prime_pow hp, ← pow_mul, mul_comm]

theorem P_sqPow {p : ℕ} (hp : p.Prime) (k : ℕ) : P p (sqPow k) = Q ((p : ℤ) ^ k) := by
  ext j
  rw [P, Q, PowerSeries.coeff_mk, PowerSeries.coeff_mk, sqPow_prime_pow k hp]
  split_ifs <;> simp [← pow_mul, mul_comm]

/-- **Ramanujan's identity of arithmetic functions.**
`(σ_a · σ_b) * S_{a+b} = ζ * Id^a * Id^b * Id^{a+b}`, where `S_{a+b}(m²) = m^{a+b}`. -/
theorem sigma_pmul_sigma_mul_sqPow (a b : ℕ) :
    (sigma a).pmul (sigma b) * sqPow (a + b) = ζ * pow a * pow b * pow (a + b) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((isMultiplicative_sigma.pmul isMultiplicative_sigma).mul (isMultiplicative_sqPow _)) _
    (((isMultiplicative_zeta.mul isMultiplicative_pow).mul isMultiplicative_pow).mul
      isMultiplicative_pow)).2 fun p k hp => ?_
  have h : P p ((sigma a).pmul (sigma b) * sqPow (a + b)) = P p (ζ * pow a * pow b * pow (a + b)) := by
    rw [P_mul hp, P_mul hp, P_mul hp, P_mul hp, P_sigma_pmul hp, P_sqPow hp, ← pow_zero_eq_zeta,
      P_pow hp, P_pow hp, P_pow hp, P_pow hp, pow_zero, pow_add, key']
  have := congrArg (PowerSeries.coeff k) h
  simp only [P, PowerSeries.coeff_mk] at this
  exact_mod_cast this

end Arithmetic

section LSeries

open ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma LSeries.notation

/-- The complex sequence underlying a natural-number arithmetic function. -/
def toC (f : ArithmeticFunction ℕ) : ℕ → ℂ := fun n => ((f n : ℕ) : ℂ)

theorem toC_mul (f g : ArithmeticFunction ℕ) : toC (f * g) = toC f ⍟ toC g := by
  have hf : toC f = ⇑(f : ArithmeticFunction ℂ) := by funext n; rw [natCoe_apply]; rfl
  have hg : toC g = ⇑(g : ArithmeticFunction ℂ) := by funext n; rw [natCoe_apply]; rfl
  rw [hf, hg, ArithmeticFunction.coe_mul, ← natCoe_mul]
  funext n; rw [natCoe_apply]; rfl

/-- `∑ n^k n^{-s} = ζ(s - k)` for `re s > k + 1`. -/
theorem LSeriesHasSum_pow (k : ℕ) {s : ℂ} (hs : (k + 1 : ℝ) < s.re) :
    LSeriesHasSum (toC (pow k)) s (riemannZeta (s - k)) := by
  have h := LSeriesHasSum_one (s := s - k) (by simp; linarith)
  unfold LSeriesHasSum at h ⊢
  convert h using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have : (n : ℂ) ^ s ≠ 0 := by simp [hn']
    rw [Complex.cpow_sub _ _ hn', Complex.cpow_natCast]
    simp [toC, pow_apply, hn]

/-- `∑_m m^k (m²)^{-s} = ζ(2s - k)`. -/
theorem LSeriesHasSum_sqPow (k : ℕ) {s : ℂ} (hs : (k + 1 : ℝ) < 2 * s.re) :
    LSeriesHasSum (toC (sqPow k)) s (riemannZeta (2 * s - k)) := by
  have h := LSeriesHasSum_one (s := 2 * s - k) (by simp; linarith)
  unfold LSeriesHasSum at h ⊢
  have hinj : Function.Injective fun m : ℕ => m * m := fun m n h => Nat.mul_self_inj.1 h
  rw [← hinj.hasSum_iff]
  · convert h using 1
    funext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [Function.comp_apply]
      rw [term_of_ne_zero (by positivity), term_of_ne_zero hm, toC, sqPow_sq _ _ hm]
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have : (m : ℂ) ^ s ≠ 0 := by simp [hm']
      rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_sub _ _ hm', two_mul, Complex.cpow_add _ _ hm',
        Complex.cpow_natCast]
      simp only [Pi.one_apply, Nat.cast_pow]
      field_simp
  · intro n hn
    have : toC (sqPow k) n = 0 := by
      rw [toC, sqPow_apply, ite_eq_right, Nat.cast_zero]
      rintro ⟨-, r, rfl⟩
      exact hn ⟨r, rfl⟩
    simp [term_def, this]

theorem le_mul_apply (f g : ArithmeticFunction ℕ) (hg : g 1 = 1) (n : ℕ) : f n ≤ (f * g) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply]
  calc f n = f (n, 1).1 * g (n, 1).2 := by simp [hg]
    _ ≤ _ := Finset.single_le_sum (f := fun x : ℕ × ℕ => f x.1 * g x.2)
        (fun _ _ => Nat.zero_le _) (by simp [hn])

theorem LSeriesSummable_of_le {f g : ArithmeticFunction ℕ} (hfg : ∀ n, f n ≤ g n) {s : ℂ}
    (hg : LSeriesSummable (toC g) s) : LSeriesSummable (toC f) s := by
  refine Summable.of_norm_bounded hg.norm fun n => ?_
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · gcongr
    simp only [toC, Complex.norm_natCast]
    exact_mod_cast hfg n

/-- `∑ n^0 · n^a · n^b · n^{a+b}`-convolution: the product of four shifted zetas. -/
theorem LSeriesHasSum_four (a b : ℕ) {s : ℂ} (hs : (a + b + 1 : ℝ) < s.re) :
    LSeriesHasSum (toC (ζ * pow a * pow b * pow (a + b))) s
      (riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b)) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  rw [← pow_zero_eq_zeta, toC_mul, toC_mul, toC_mul]
  have := ((((LSeriesHasSum_pow 0 (s := s) (by push_cast; linarith)).convolution
    (LSeriesHasSum_pow a (by linarith))).convolution
    (LSeriesHasSum_pow b (by linarith))).convolution
    (LSeriesHasSum_pow (a + b) (by push_cast; linarith)))
  convert this using 2
  · simp
  · push_cast; ring_nf

end LSeries

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **Ramanujan's formula (1916).** For `re s > a + b + 1`,
`(∑ σ_a(n) σ_b(n) n^{-s}) · ζ(2s - a - b) = ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b)`. -/
theorem LSeries_sigma_mul_sigma (a b : ℕ) {s : ℂ} (hs : (a + b + 1 : ℝ) < s.re) :
    LSeries (fun n => ((σ a n * σ b n : ℕ) : ℂ)) s * riemannZeta (2 * s - a - b) =
      riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b) := by
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hR := LSeriesHasSum_four a b hs
  have hS := LSeriesHasSum_sqPow (a + b) (s := s) (by push_cast; linarith)
  have h1 : sqPow (a + b) 1 = 1 := by simpa using sqPow_sq (a + b) 1 one_ne_zero
  have hsum : LSeriesSummable (toC ((σ a).pmul (σ b))) s :=
    LSeriesSummable_of_le (fun n => (le_mul_apply _ _ h1 n).trans_eq
      (by rw [sigma_pmul_sigma_mul_sqPow])) hR.LSeriesSummable
  have h := hsum.LSeriesHasSum.convolution hS
  rw [← toC_mul, sigma_pmul_sigma_mul_sqPow] at h
  have := HasSum.unique h hR
  convert this using 3
  · funext n; simp [toC, pmul_apply]
  · push_cast; ring

/-- Sanity check (`a = b = 0`): `∑ d(n)² n^{-s} = ζ(s)⁴ / ζ(2s)`, multiplied out. -/
theorem LSeries_card_divisors_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((n.divisors.card ^ 2 : ℕ) : ℂ)) s * riemannZeta (2 * s) =
      riemannZeta s ^ 4 := by
  have := LSeries_sigma_mul_sigma 0 0 (s := s) (by simpa using hs)
  simp only [sigma_zero_apply, Nat.cast_zero, sub_zero, ← sq] at this
  rw [this]; ring

end Fugue.RankinSelberg

open ArithmeticFunction in
open scoped ArithmeticFunction.sigma in
/-- **Ramanujan's formula (1916)**, the prototype of Rankin–Selberg:
`∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b) / ζ(2s-a-b)` for `re s > a + b + 1`,
stated multiplied out. -/
theorem Fugue.LSeries_sigma_mul_sigma (a b : ℕ) {s : ℂ} (hs : (a + b + 1 : ℝ) < s.re) :
    LSeries (fun n => ((σ a n * σ b n : ℕ) : ℂ)) s * riemannZeta (2 * s - a - b) =
      riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b) :=
  Fugue.RankinSelberg.LSeries_sigma_mul_sigma a b hs
