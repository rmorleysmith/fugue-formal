import Mathlib

/-!
# Ramanujan's identity `σ₇ = σ₃ + 120 σ₃ ⋆ σ₃` — the two rings meet (ledger C1, C8, A2)

The corpus' two products on coefficient sequences (Ring A: Cauchy product of `q`-series;
Ring B: Dirichlet product) meet in the Eisenstein series. The `q`-expansion of `E₄` (a Ring-A
object) has coefficients `240 σ₃(n)`, where `σ₃ = ζ * Id³` is a Ring-B product. Squaring in
Ring A and using that weight-8 level-1 modular forms form a **one-dimensional** space (so
`E₄² = E₈`) gives the classical identity

  `σ₇(n) = σ₃(n) + 120 ∑_{a + b = n, a, b ≥ 1} σ₃(a) σ₃(b)`.

A Ring-A product of Ring-B products is again a Ring-B object: the "freeze the state, dial the
DNA" composition of the corpus is, at weight 8, a statement about divisor sums. Every input here
is Mathlib: the `q`-expansion of `E_k` (`EisensteinSeries.E_qExpansion_coeff`), multiplicativity
of `q`-expansions, and the dimension formula (`dimension_level_one`).
-/

open ModularForm EisensteinSeries UpperHalfPlane PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace Fugue

/-- `E₈`, the normalised weight-8 Eisenstein series. -/
noncomputable abbrev E₈ : ModularForm 𝒮ℒ 8 := E (by norm_num : 3 ≤ 8)

/-- `E₄²` as a weight-8 form. -/
noncomputable def E₄sq : ModularForm 𝒮ℒ 8 := ModularForm.mcast (by norm_num) (E₄.mul E₄) rfl

theorem qExpansion_E₄sq : qExpansion 1 E₄sq = qExpansion 1 E₄ * qExpansion 1 E₄ := by
  rw [E₄sq, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]

theorem finrank_weight_eight : Module.finrank ℂ (ModularForm 𝒮ℒ 8) = 1 := by
  have h := dimension_level_one 8 ⟨4, rfl⟩
  have h8 : ¬ (8 ≡ 2 [MOD 12]) := by decide
  rw [ite_eq_right h8] at h
  push_cast at h
  exact Module.finrank_eq_of_rank_eq (by rw [h]; norm_num)

/-- **`E₄² = E₈`.** -/
theorem E₄sq_eq : E₄sq = E₈ := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₈ (E_ne_zero _ ⟨4, rfl⟩)).mp
    finrank_weight_eight E₄sq
  have h0 := congrArg (fun f : ModularForm 𝒮ℒ 8 => (qExpansion 1 f).coeff 0) hc
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, coeff_smul,
    E_qExpansion_coeff_zero _ ⟨4, rfl⟩, qExpansion_E₄sq, coeff_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h0
  simp only [smul_eq_mul, mul_one] at h0
  rw [← hc, h0, one_smul]

theorem coeff_E₄ (m : ℕ) : (qExpansion 1 E₄).coeff m = if m = 0 then 1 else 240 * (σ 3 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
  norm_num

theorem coeff_E₈ (m : ℕ) : (qExpansion 1 E₈).coeff m = if m = 0 then 1 else 480 * (σ 7 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨4, rfl⟩, show bernoulli 8 = -1 / 30 by decide +kernel]
  norm_num

/-- **Ramanujan's identity** `σ₇(n) = σ₃(n) + 120 ∑_{0<i<n} σ₃(i) σ₃(n−i)`. -/
theorem sigma_seven_eq (n : ℕ) (hn : 0 < n) :
    σ 7 n = σ 3 n + 120 * ∑ i ∈ Finset.range (n - 1), σ 3 (i + 1) * σ 3 (n - 1 - i) := by
  have h := congrArg (fun f : ModularForm 𝒮ℒ 8 => (qExpansion 1 f).coeff n) E₄sq_eq
  rw [qExpansion_E₄sq, coeff_mul, coeff_E₈, ite_eq_right hn.ne',
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
  simp only [coeff_E₄, Nat.sub_self, Nat.sub_zero, ite_true, add_eq_zero, one_ne_zero, and_false,
    ite_false] at h
  have hint : ∀ i ∈ Finset.range m, (240 * (σ 3 (i + 1) : ℂ) *
      if m + 1 - (i + 1) = 0 then 1 else 240 * (σ 3 (m + 1 - (i + 1)) : ℂ)) =
      57600 * ((σ 3 (i + 1) * σ 3 (m - i) : ℕ) : ℂ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [ite_eq_right (by omega), show m + 1 - (i + 1) = m - i by omega]
    push_cast; ring
  rw [Finset.sum_congr rfl hint, ← Finset.mul_sum] at h
  simp only [Nat.add_sub_cancel]
  have h' : ((σ 7 (m + 1) : ℕ) : ℂ) = ((σ 3 (m + 1) + 120 *
      ∑ i ∈ Finset.range m, σ 3 (i + 1) * σ 3 (m - i) : ℕ) : ℂ) := by
    push_cast at h ⊢
    linear_combination -h / 480
  exact_mod_cast h'

end Fugue
