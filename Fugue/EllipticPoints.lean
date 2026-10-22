import Mathlib

/-!
# Level-one modular forms vanish at the elliptic points (ledger rows A3, A8, A10)

The corpus' first figure is the zero of `E₄` at `ρ = e^{2πi/3}`. Its argument (ledger A3):
`ρ` is fixed by an element of `SL₂(ℤ)` whose automorphy factor is a primitive 6th root of
unity, so `E₄(ρ) = ρ'⁴ E₄(ρ)` with `ρ'⁴ ≠ 1`. This file proves the general statement:

* `eq_zero_at_rho` — **every** level-one form of weight `k` with `6 ∤ k` vanishes at `ρ`;
* `eq_zero_at_I` — **every** level-one form of weight `k` with `4 ∤ k` vanishes at `i`.

Consequences (using Mathlib's `Δ = (E₄³ - E₆²)/1728` and `Δ ≠ 0` on `ℍ`):

* `E₄ ρ = 0` and `E₆ i = 0`;
* `E₄ i ≠ 0` and `E₆ ρ ≠ 0` — so the two zeros are *different* points;
* `Δ ρ ≠ 0`, `Δ i ≠ 0` — weight 12 is divisible by both 4 and 6 and the forced zeros
  disappear; indeed `Δ` has no zeros in `ℍ` at all. This is the concrete content of the
  ledger's refutation A8 ("increasing weight grows the neuron count" fails at weight 12).

Proof of the key step: `γ = [[0, -1], [1, 1]]` sends `ρ ↦ -1/(ρ + 1) = ρ`, with automorphy
factor `ρ + 1 = e^{iπ/3}`, a primitive 6th root of unity `u`. So `f(ρ) = u^k f(ρ)`, and
`u^k ≠ 1` unless `6 ∣ k`. At `i`, `S = [[0, -1], [1, 0]]` fixes `i` with factor `i`, a primitive
4th root of unity.
-/

open UpperHalfPlane ModularGroup CongruenceSubgroup Complex ModularForm
open scoped MatrixGroups Real

namespace Fugue

/-! ### The sixth root of unity `u = e^{iπ/3}` and the point `ρ = u - 1 = e^{2πi/3}` -/

/-- `u = e^{iπ/3}`. -/
noncomputable def u6 : ℂ := cexp (↑(π / 3) * Complex.I)

theorem u6_isPrimitiveRoot : IsPrimitiveRoot u6 6 := by
  have : u6 = cexp (2 * π * Complex.I / (6 : ℕ)) := by rw [u6]; congr 1; push_cast; ring
  rw [this]; exact Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem u6_pow_three : u6 ^ 3 = -1 := by
  rw [u6, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 2
  push_cast; ring

theorem u6_sq : u6 ^ 2 = u6 - 1 := by
  have hne : u6 + 1 ≠ 0 := by
    intro h
    have : u6 ^ 2 = 1 := by rw [show u6 = -1 by linear_combination h]; norm_num
    exact u6_isPrimitiveRoot.pow_ne_one_of_pos_of_lt two_ne_zero (by norm_num) this
  have h3 : (u6 + 1) * (u6 ^ 2 - u6 + 1) = 0 := by linear_combination u6_pow_three
  linear_combination (mul_eq_zero.mp h3).resolve_left hne

theorem im_u6_pos : 0 < u6.im := by
  rw [u6, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])

/-- The elliptic point `ρ = e^{2πi/3}` as a point of the upper half-plane. -/
noncomputable def rho : ℍ := ⟨u6 - 1, by simpa using im_u6_pos⟩

theorem coe_rho : (rho : ℂ) = u6 - 1 := rfl

/-- `ρ` really is `e^{2πi/3}`. -/
theorem coe_rho_eq_exp : (rho : ℂ) = cexp (2 * π * Complex.I / 3) := by
  rw [coe_rho, ← u6_sq, u6, ← Complex.exp_nat_mul]
  push_cast; ring_nf

/-- The stabiliser element `γ = [[0, -1], [1, 1]]` of `ρ`. -/
def gammaRho : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two]⟩

theorem gammaRho_smul_rho : gammaRho • rho = rho := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [gammaRho, coe_rho]
  have hu : u6 ≠ 0 := u6_isPrimitiveRoot.ne_zero (by norm_num)
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [div_eq_iff (by simpa using hu)]
  linear_combination -1 * u6_sq

theorem denom_gammaRho_rho : denom gammaRho rho = u6 := by
  rw [denom_apply]
  simp [gammaRho, coe_rho]

/-! ### The vanishing theorems -/

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- **Every level-one modular form of weight `k` with `6 ∤ k` vanishes at `ρ = e^{2πi/3}`.** -/
theorem eq_zero_at_rho [SlashInvariantFormClass F 𝒮ℒ k] (hk : ¬ (6 : ℤ) ∣ k) (f : F) :
    f rho = 0 := by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have h := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one gammaRho) rho
  rw [gammaRho_smul_rho, denom_gammaRho_rho] at h
  have hk1 : u6 ^ k ≠ 1 := by
    rw [Ne, u6_isPrimitiveRoot.zpow_eq_one_iff_dvd]; exact_mod_cast hk
  have : (1 - u6 ^ k) * f rho = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hk1.symm)

/-- **Every level-one modular form of weight `k` with `4 ∤ k` vanishes at `i`.** -/
theorem eq_zero_at_I [SlashInvariantFormClass F 𝒮ℒ k] (hk : ¬ (4 : ℤ) ∣ k) (f : F) :
    f UpperHalfPlane.I = 0 := by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have h := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one S) UpperHalfPlane.I
  have hS : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    simp
  rw [hS, denom_S, UpperHalfPlane.coe_I] at h
  have hk1 : Complex.I ^ k ≠ 1 := by
    rw [Ne, Complex.isPrimitiveRoot_I.zpow_eq_one_iff_dvd]; exact_mod_cast hk
  have : (1 - Complex.I ^ k) * f UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hk1.symm)

/-! ### Consequences for `E₄`, `E₆`, `Δ` -/

/-- **Ledger A3.** `E₄(ρ) = 0`. -/
theorem E₄_rho : E₄ rho = 0 := eq_zero_at_rho (k := 4) (by decide) E₄

/-- `E₆(i) = 0`. -/
theorem E₆_I : E₆ UpperHalfPlane.I = 0 := eq_zero_at_I (k := 6) (by decide) E₆

/-- `E₄(i) ≠ 0`: from `1728 Δ = E₄³ - E₆²`, `E₆(i) = 0` and `Δ(i) ≠ 0`. -/
theorem E₄_I_ne_zero : E₄ UpperHalfPlane.I ≠ 0 := by
  intro h
  have := discriminant_eq_E₄_cube_sub_E₆_sq UpperHalfPlane.I
  rw [h, E₆_I] at this
  exact discriminant_ne_zero _ (by simpa using this)

/-- `E₆(ρ) ≠ 0`. -/
theorem E₆_rho_ne_zero : E₆ rho ≠ 0 := by
  intro h
  have := discriminant_eq_E₄_cube_sub_E₆_sq rho
  rw [h, E₄_rho] at this
  exact discriminant_ne_zero _ (by simpa using this)

/-- **Ledger A8.** Weight 12 has no forced zero: `Δ(ρ) ≠ 0` and `Δ(i) ≠ 0` (in fact `Δ` never
vanishes on `ℍ`; Mathlib's `discriminant_ne_zero`). -/
theorem discriminant_rho_ne_zero : discriminant rho ≠ 0 := discriminant_ne_zero _

end Fugue
