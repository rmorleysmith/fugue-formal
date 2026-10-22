import Fugue.HeckeEk
import Fugue.HeckeRefutation

/-!
# Hecke's theorem for the cusp form `Δ`: Ramanujan's `L`-function

Ramanujan's `τ(n)` is the `n`-th `q`-expansion coefficient of the modular discriminant
`Δ = q ∏ (1 - qⁿ)²⁴ = η²⁴` (Mathlib's `ModularForm.discriminant`, *defined* as `η²⁴` with `η` the
Dedekind eta function, see `F_eq_eta`; it is the weight-12 cusp form `CuspForm.discriminant`).
Ramanujan's `L`-function is `L(Δ, s) = ∑ τ(n) n^{-s}`.

* `τ_zero`, `τ_one`, `τ_two`, `τ_three` : `τ(0) = 0`, `τ(1) = 1`, `τ(2) = -24`, `τ(3) = 252`
  (from `Δ = (E₄³ - E₆²)/1728`, with `E₄ = 1 + 240q + 2160q² + 6720q³ + …`,
  `E₆ = 1 - 504q - 16632q² - 122976q³ - …`);
* `τ_isBigO` : Hecke's bound `τ(n) = O(n⁶)` (Mathlib's `CuspFormClass.qExpansion_isBigO`);
* `P` : the weak — in fact strong (`P_strong`, `f₀ = g₀ = 0`) — FE-pair `(F, F)`,
  `F(t) = Δ(it)`, weight `12`, root number `i¹² = (-1)⁶ = 1`, self-dual (`P_symm`).
  The `S`-transformation `F(1/t) = t¹² F(t)` (`F_feq`) and the rapid decay at `∞` come from
  Mathlib's `ModularForm.weakFEPair` of the cusp form `Δ` (with `Δ ∣ S = Δ`,
  `discriminant_S_invariant`); `Λ_eq_mathlib` identifies our `Λ := P.Λ` with Mathlib's
  `ModularForm.Λ` of `Δ`, and `Λ_eq_mellin` with the Mellin transform of `t ↦ Δ(it)`;
* `ramanujanΛ_functional_equation` : `Λ(12 - s) = Λ(s)` — the symmetry `s ↔ 12 - s` about the
  critical line `re s = 6`;
* `ramanujanΛ_differentiable` : `Λ` is **entire**. Since `Δ` is a cusp form there is no constant
  term and hence no pole — unlike `ζ(s) ζ(s - k + 1)`, the Eisenstein analogue in
  `Fugue.HeckeEk`, whose completed `L`-function has simple poles at `0` and `k`;
* `LSeriesHasSum_τ`, `LSeriesSummable_τ` : `∑ τ(n) n^{-s}` converges absolutely for `re s > 7`
  (threshold `k/2 + 1 = 7`, from Hecke's bound);
* `ramanujanΛ_eq` : for `re s > 7`, `Λ(s) = (2π)^{-s} Γ(s) L(Δ, s)`, `L(Δ, s) = LSeries τ s`;
* `ramanujanΛ_eq_of_re_lt` : the reflected formula for `re s < 5`.

Thus `(2π)^{-s} Γ(s) L(Δ, s)` continues to an entire function invariant under `s ↦ 12 - s`.

**Not formalised.** Ramanujan's conjectures: the multiplicativity of `τ` and the Hecke recursion
`τ(p^{n+1}) = τ(p) τ(pⁿ) - p¹¹ τ(p^{n-1})` (Mordell 1917, via Hecke operators — not in Mathlib),
equivalently the Euler product `L(Δ, s) = ∏_p (1 - τ(p) p^{-s} + p^{11-2s})⁻¹`; and the bound
`|τ(p)| ≤ 2 p^{11/2}` (Deligne 1974). Only the much weaker `τ(n) = O(n⁶)` is used here.
-/

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex ModularForm ModularGroup Filter Asymptotics Set PowerSeries
open scoped MatrixGroups Real ArithmeticFunction.sigma

namespace Fugue.RamanujanL

/-- Ramanujan's `τ(n)` (`ramanujanTau`): the `qⁿ`-coefficient of `Δ = q ∏ (1 - qⁿ)²⁴`. -/
noncomputable def τ (n : ℕ) : ℂ := (qExpansion 1 ModularForm.discriminant).coeff n

theorem τ_zero : τ 0 = 0 := coeff_small_discriminant.1
theorem τ_one : τ 1 = 1 := coeff_small_discriminant.2.1
theorem τ_two : τ 2 = -24 := coeff_small_discriminant.2.2

theorem coeff3_mul (p r : PowerSeries ℂ) :
    coeff 3 (p * r) = coeff 0 p * coeff 3 r + coeff 1 p * coeff 2 r + coeff 2 p * coeff 1 r +
      coeff 3 p * coeff 0 r := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem sigma_three_vals : σ 3 3 = 28 ∧ σ 5 3 = 244 := by decide

theorem τ_three : τ 3 = 252 := by
  obtain ⟨a0, a1, a2⟩ := coeff_E₄_small
  obtain ⟨b0, b1, b2⟩ := coeff_E₆_small
  have a3 : (qExpansion 1 E₄).coeff 3 = 6720 := by
    simp [coeff_E₄, sigma_three_vals.1]; norm_num
  have b3 : (qExpansion 1 E₆).coeff 3 = -122976 := by
    simp [coeff_E₆, sigma_three_vals.2]; norm_num
  simp only [τ, qExpansion_discriminant, coeff_smul, map_sub, pow_succ, coeff0_mul,
    coeff1_mul, coeff2_mul, coeff3_mul, a0, a1, a2, a3, b0, b1, b2, b3, smul_eq_mul, pow_zero,
    one_mul]
  norm_num

/-- The positive weight `12`. -/
theorem twelve_pos : (0 : ℤ) < 12 := by norm_num

/-- Mathlib's FE-pair of the cusp form `Δ`. -/
noncomputable abbrev Q : WeakFEPair ℂ := weakFEPair twelve_pos CuspForm.discriminant

/-- `F t = Δ(it)`. -/
noncomputable def F (t : ℝ) : ℂ := ModularForm.discriminant (ofComplex (I * t))

/-- `Δ = η²⁴`: on the imaginary axis `F t = η(it)²⁴` (Mathlib's definition of `Δ`). -/
theorem F_eq_eta (t : ℝ) : F t = ModularForm.eta (ofComplex (I * t)) ^ 24 := rfl

theorem Q_f : Q.f = F := rfl

theorem Q_g : Q.g = F := by
  funext t
  simp only [Q, weakFEPair_g, coe_translate, F]
  rw [show (⇑CuspForm.discriminant ∣[(12 : ℤ)] (S : GL (Fin 2) ℝ)) = ModularForm.discriminant
    from discriminant_S_invariant]

theorem Q_ε : Q.ε = 1 := by
  simp only [Q, weakFEPair_ε]
  rw [show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, I_sq]; norm_num

theorem Q_f₀ : Q.f₀ = 0 := (CuspForm.isStrongFEPair twelve_pos CuspForm.discriminant).hf₀


theorem F_feq (x : ℝ) (hx : 0 < x) : F (1 / x) = ((1 : ℂ) * ↑(x ^ (12 : ℝ))) • F x := by
  have h := Q.h_feq x hx
  rw [Q_f, Q_g, Q_ε] at h
  simpa [Q] using h

theorem F_top (r : ℝ) : (fun t => F t - 0) =O[atTop] (· ^ r) := by
  have h := Q.hf_top r
  rw [Q_f, Q_f₀] at h
  exact h

/-- The strong FE-pair `(F, F)`, weight `12`, root number `1`, constant terms `0`. -/
noncomputable def P : WeakFEPair ℂ where
  f := F
  g := F
  k := 12
  ε := 1
  f₀ := 0
  g₀ := 0
  hf_int := Q.hf_int
  hg_int := Q.hf_int
  hk := by norm_num
  hε := one_ne_zero
  h_feq := F_feq
  hf_top := F_top
  hg_top := F_top

theorem P_strong : IsStrongFEPair P := ⟨rfl, rfl⟩

theorem P_symm : P.symm = P := by
  simp only [WeakFEPair.symm, P, inv_one]

/-- The completed `L`-function of `Δ`. -/
noncomputable abbrev Λ : ℂ → ℂ := P.Λ

theorem ramanujanΛ_functional_equation (s : ℂ) : Λ (12 - s) = Λ s := by
  have h := P.functional_equation s
  have hk' : ((P.k : ℝ) : ℂ) = 12 := by simp [P]
  have hε : P.ε = 1 := rfl
  rw [P_symm, hk', hε, one_smul] at h
  exact h

theorem ramanujanΛ_differentiable : Differentiable ℂ Λ := P_strong.differentiable_Λ

theorem Λ_eq_mellin : Λ = mellin F := P_strong.Λ_eq

theorem Λ_eq_mathlib : Λ = ModularForm.Λ twelve_pos CuspForm.discriminant := by
  rw [Λ_eq_mellin, CuspForm.Λ_eq_mellin]
  rfl

theorem qExpansion_width :
    qExpansion (Subgroup.strictWidthInfty 𝒮ℒ) CuspForm.discriminant =
      qExpansion 1 ModularForm.discriminant := by
  rw [Subgroup.strictWidthInfty_SL2Z]
  rfl


/-- **Hecke's bound** `τ(n) = O(n⁶)` (Mathlib's `CuspFormClass.qExpansion_isBigO`, `k/2 = 6`). -/
theorem τ_isBigO : (fun n => τ n) =O[atTop] fun n => (n : ℝ) ^ (6 : ℝ) := by
  have h := CuspFormClass.qExpansion_isBigO (k := 12) (Γ := 𝒮ℒ) CuspForm.discriminant
  rw [qExpansion_width] at h
  convert h using 3
  · rfl
  · norm_num

theorem term_τ (s : ℂ) : LSeries.term τ s = fun n => τ n / (n : ℂ) ^ s := by
  funext n
  rcases n with _ | n
  · simp [τ_zero]
  · simp [LSeries.term_of_ne_zero]

/-- The Dirichlet series `∑ τ(n) n^{-s}` converges for `re s > 7` to Mathlib's `L(Δ, s)`. -/
theorem LSeriesHasSum_τ {s : ℂ} (hs : 7 < s.re) :
    LSeriesHasSum τ s (ModularForm.L twelve_pos CuspForm.discriminant s) := by
  have h := CuspForm.hasSum_L twelve_pos CuspForm.discriminant (s := s) (by push_cast; linarith)
  rw [qExpansion_width, Subgroup.strictWidthInfty_SL2Z] at h
  rw [LSeriesHasSum, term_τ]
  simpa [τ] using h

theorem LSeriesSummable_τ {s : ℂ} (hs : 7 < s.re) : LSeriesSummable τ s :=
  (LSeriesHasSum_τ hs).LSeriesSummable

/-- **Identification** for `re s > 7`: `Λ(s) = (2π)^{-s} Γ(s) ∑ τ(n) n^{-s}`. -/
theorem ramanujanΛ_eq {s : ℂ} (hs : 7 < s.re) :
    Λ s = (2 * π) ^ (-s) * Gamma s * LSeries τ s := by
  have hs0 : 0 < s.re := by linarith
  rw [(LSeriesHasSum_τ hs).LSeries_eq, ModularForm.L, ← Λ_eq_mathlib, Gammaℂ_def]
  have h1 : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
  have h2 : (2 * (π : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by simp [Real.pi_ne_zero])
  field_simp


/-- The reflected formula: for `re s < 5`,
`Λ(s) = (2π)^{-(12-s)} Γ(12-s) ∑ τ(n) n^{-(12-s)}`. -/
theorem ramanujanΛ_eq_of_re_lt {s : ℂ} (hs : s.re < 5) :
    Λ s = (2 * π) ^ (-(12 - s)) * Gamma (12 - s) * LSeries τ (12 - s) := by
  rw [← ramanujanΛ_eq (by simp; linarith), ramanujanΛ_functional_equation]

end Fugue.RamanujanL
