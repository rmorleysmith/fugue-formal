import Fugue.Ramanujan

/-!
# Products of eigenforms are not eigenforms "with the product eigenvalue" (ledger C12)

The corpus claimed (`math-connections.md`, `HSLNBridge.lean`) that the product of two Hecke
eigenforms is an eigenform whose eigenvalues are the products of the eigenvalues. Ledger C12
refuted this numerically with `Δ` and `E₄`: `a₂(Δ·E₄) = 216` but `a₂(Δ)·a₂(E₄) = −24 · 2160`.

Here the refutation is machine-checked from Mathlib's `q`-expansions:

* `tau_two` — Ramanujan's `τ(2) = −24` (the `q²`-coefficient of `Δ`), computed from
  `Δ = (E₄³ − E₆²)/1728`;
* `coeff_two_discriminant_mul_E₄` — the `q²`-coefficient of `Δ·E₄` is `216`;
* `discriminant_mul_E₄_not_multiplicative_eigenvalue` — `216 ≠ (−24)·2160`.

(`Δ·E₄` *is* an eigenform — `S₁₆` is one-dimensional — but its eigenvalues are not the products.
The true closure law is about multiplicativity of coefficient sequences, ledger C11.)
-/

open ModularForm EisensteinSeries UpperHalfPlane PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace Fugue

theorem coeff_E₆ (m : ℕ) :
    (qExpansion 1 E₆).coeff m = if m = 0 then 1 else -504 * (σ 5 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
  norm_num

/-- `E₄³ − E₆²` as a weight-12 modular form. -/
noncomputable def E₄cubeSubE₆sq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) (E₄.pow 3) rfl - ModularForm.mcast (by norm_num) (E₆.pow 2) rfl

theorem coe_discriminant_eq :
    (ModularForm.discriminant : ℍ → ℂ) = ⇑((1 / 1728 : ℂ) • E₄cubeSubE₆sq) := by
  funext z
  rw [discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [E₄cubeSubE₆sq, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, FunLike.coe_sub,
    Pi.sub_apply, coe_mcast, ModularForm.coe_pow, Pi.pow_apply]
  ring

theorem qExpansion_discriminant : qExpansion 1 ModularForm.discriminant =
    (1 / 1728 : ℂ) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  rw [coe_discriminant_eq, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  simp only [E₄cubeSubE₆sq, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem sigma_vals : σ 3 1 = 1 ∧ σ 3 2 = 9 ∧ σ 5 1 = 1 ∧ σ 5 2 = 33 := by decide

theorem coeff0_mul (p r : PowerSeries ℂ) : coeff 0 (p * r) = coeff 0 p * coeff 0 r := by
  simp [coeff_mul]

theorem coeff1_mul (p r : PowerSeries ℂ) :
    coeff 1 (p * r) = coeff 0 p * coeff 1 r + coeff 1 p * coeff 0 r := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff2_mul (p r : PowerSeries ℂ) :
    coeff 2 (p * r) = coeff 0 p * coeff 2 r + coeff 1 p * coeff 1 r + coeff 2 p * coeff 0 r := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_E₄_small : (qExpansion 1 E₄).coeff 0 = 1 ∧ (qExpansion 1 E₄).coeff 1 = 240 ∧
    (qExpansion 1 E₄).coeff 2 = 2160 := by
  obtain ⟨h31, h32, -, -⟩ := sigma_vals
  refine ⟨by simp [coeff_E₄], by simp [coeff_E₄, h31], by simp [coeff_E₄, h32]; norm_num⟩

theorem coeff_E₆_small : (qExpansion 1 E₆).coeff 0 = 1 ∧ (qExpansion 1 E₆).coeff 1 = -504 ∧
    (qExpansion 1 E₆).coeff 2 = -16632 := by
  obtain ⟨-, -, h51, h52⟩ := sigma_vals
  refine ⟨by simp [coeff_E₆], by simp [coeff_E₆, h51], by simp [coeff_E₆, h52]; norm_num⟩

theorem coeff_small_discriminant : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 ∧
    (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 ∧
    (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 := by
  obtain ⟨a0, a1, a2⟩ := coeff_E₄_small
  obtain ⟨b0, b1, b2⟩ := coeff_E₆_small
  simp only [qExpansion_discriminant, coeff_smul, map_sub, pow_succ, coeff0_mul,
    coeff1_mul, coeff2_mul, a0, a1, a2, b0, b1, b2, smul_eq_mul, pow_zero, one_mul]
  norm_num

/-- **Ramanujan's `τ(2) = −24`.** -/
theorem tau_two : (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 :=
  coeff_small_discriminant.2.2

/-- The `q²`-coefficient of `Δ·E₄` is `216`. -/
theorem coeff_two_discriminant_mul_E₄ :
    (qExpansion 1 (⇑CuspForm.discriminant * ⇑E₄)).coeff 2 = 216 := by
  rw [ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL, coeff2_mul]
  obtain ⟨e0, e1, e2⟩ := coeff_E₄_small
  obtain ⟨d0, d1, d2⟩ := coeff_small_discriminant
  rw [CuspForm.coe_discriminant, d0, d1, d2, e0, e1, e2]
  norm_num

/-- **Ledger C12, refuted.** The eigenvalue-type coefficient `a₂` of `Δ·E₄` is not
`a₂(Δ)·a₂(E₄)`. -/
theorem discriminant_mul_E₄_not_multiplicative_eigenvalue :
    (qExpansion 1 (⇑CuspForm.discriminant * ⇑E₄)).coeff 2 ≠
      (qExpansion 1 ModularForm.discriminant).coeff 2 * (qExpansion 1 E₄).coeff 2 := by
  rw [coeff_two_discriminant_mul_E₄, tau_two, coeff_E₄_small.2.2]
  norm_num

end Fugue
