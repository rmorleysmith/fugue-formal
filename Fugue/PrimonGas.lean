import Mathlib
import Fugue.RankinSelberg

set_option autoImplicit false

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
  · simp only [sqf_apply, pow_apply, hn, and_false, if_false, pow_zero]
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

end Fugue.PrimonGas
