import Fugue.RamanujanL
import Fugue.Partitions

/-!
# Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)`

Ramanujan's `τ(n)` is the `qⁿ`-coefficient of the discriminant
`Δ = η²⁴ = q ∏_{n ≥ 1} (1 - qⁿ)²⁴ = ∑ τ(n) qⁿ` (`Fugue.RamanujanL.τ`). In his 1916 paper
*On certain arithmetical functions* Ramanujan observed `τ(n) ≡ σ₁₁(n) (mod 691)`. This file proves
it, without `sorry`, from Mathlib's modular forms library.

## Main results

* `qExpansion_discriminant_eq` : the `q`-expansion of `Δ` is the image of
  `X · (∏ (1 - X^{n+1}))²⁴ = X · pentagonalSeries²⁴ ∈ ℤ⟦X⟧`; hence `τ_eq_tauZ`, `τ_int`:
  `τ(n) = tauZ n ∈ ℤ`.
  Proof: for `z ∈ ℍ`, `q = e^{2πiz}`, `‖q‖ < 1`, the pentagonal series converges absolutely at `q`
  to `∏ (1 - q^{n+1})` (Mathlib's analytic pentagonal theorem, `eulerFunction_eq_tprod`);
  absolutely convergent power series evaluate multiplicatively (Cauchy product, `ev_mul`), so
  `∑ coeffₘ(X · P²⁴) qᵐ = q ∏ (1 - q^{n+1})²⁴ = Δ(z)` (`discriminant_eq_q_prod`), and
  uniqueness of `q`-expansion coefficients (`ModularFormClass.qExpansion_coeff_unique`) concludes.
* `qExpansion_G_eq` : `E₄³ - E₁₂ = (432000/691) Δ`. The difference has constant term `1 - 1 = 0`,
  so it is a cusp form, hence a multiple of `Δ` (`S₁₂` is one-dimensional,
  `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`); the multiple is read off from the
  `q`-coefficients `720 - 65520/691 = 432000/691`.
* `key_identity` : for `n ≥ 1`, `65520 σ₁₁(n) + 432000 τ(n) = 691 aₙ(E₄³)` in `ℤ`, where
  `aₙ(E₄³)` is the `n`-th coefficient of `(1 + 240 ∑ σ₃(m) qᵐ)³` (`E4Z`).
* `Fugue.tau_congr_691` : `(τ(n) : ZMod 691) = σ₁₁(n)`, and `Fugue.tau_sub_sigma_dvd` :
  `691 ∣ τ(n) - σ₁₁(n)`. Indeed `65520 ≡ 566` and `432000 ≡ -566 (mod 691)`, and `566` is a
  unit mod the prime `691`. (Sanity check: `τ(2) = -24`, `σ₁₁(2) = 2049 = 3 · 691 - 24`.)

## Where `691` comes from

The normalised Eisenstein series is `E₁₂ = 1 - (24 / B₁₂) ∑ σ₁₁(n) qⁿ` with Bernoulli number
`B₁₂ = -691/2730` (`bernoulli_twelve`), so `-24/B₁₂ = 65520/691`: the prime `691` divides the
numerator of `B₁₂` (it is an irregular prime) and appears in the *denominator* of the Eisenstein
coefficients. Clearing it, `691 E₁₂ ≡ 65520 ∑ σ₁₁(n) qⁿ` and the relation
`691 E₁₂ = 691 E₄³ - 432000 Δ` say that, modulo `691`, the Eisenstein series `∑ σ₁₁(n) qⁿ` is
congruent to a multiple of the cusp form `Δ`: "Eisenstein ≡ cusp form (mod 691)" — the
prototype of the congruences between Eisenstein series and cusp forms (Ribet's proof of the
converse of Herbrand's theorem, Mazur–Wiles). On the cusp-form side, `Δ = η²⁴`, with
`η = q^{1/24} ∏ (1 - qⁿ)` the Dedekind eta function, so the integrality of `τ` comes from Euler's
product, here expanded by the pentagonal number theorem.

All results depend only on the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex ModularForm EisensteinSeries PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

namespace Fugue.Tau691

/-! ## Evaluating absolutely convergent power series -/

/-- `∑ aₙ qⁿ` converges absolutely. -/
def AbsConv (f : PowerSeries ℂ) (q : ℂ) : Prop := Summable fun n => ‖coeff n f * q ^ n‖

/-- The value `∑ aₙ qⁿ`. -/
noncomputable def ev (f : PowerSeries ℂ) (q : ℂ) : ℂ := ∑' n, coeff n f * q ^ n

theorem coeff_mul_pow (f g : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    coeff n (f * g) * q ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2) := by
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]; ring

theorem AbsConv.mul {f g : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (hg : AbsConv g q) :
    AbsConv (f * g) q := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  unfold AbsConv
  refine h.congr fun n => ?_
  rw [coeff_mul_pow]

theorem ev_mul {f g : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (hg : AbsConv g q) :
    ev (f * g) q = ev f q * ev g q := by
  unfold ev
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  simp_rw [coeff_mul_pow]

theorem AbsConv.pow {f : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) (n : ℕ) :
    AbsConv (f ^ n) q ∧ ev (f ^ n) q = ev f q ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold AbsConv
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      simp at hn; simp [coeff_one, hn]
    · unfold ev
      rw [tsum_eq_single 0 (fun n hn => by simp [coeff_one, hn])]
      simp
  | succ n ih =>
    refine ⟨ih.1.mul hf, ?_⟩
    rw [pow_succ, ev_mul ih.1 hf, ih.2, pow_succ]

theorem absConv_X (q : ℂ) : AbsConv X q := by
  unfold AbsConv
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp at hn; simp [coeff_X, hn]

theorem ev_X (q : ℂ) : ev X q = q := by
  unfold ev
  rw [tsum_eq_single 1 (fun n hn => by simp [coeff_X, hn])]
  simp

theorem AbsConv.hasSum {f : PowerSeries ℂ} {q : ℂ} (hf : AbsConv f q) :
    HasSum (fun n => coeff n f * q ^ n) (ev f q) :=
  hf.of_norm.hasSum

/-! ## The pentagonal series at `‖q‖ < 1` -/

theorem absConv_pentagonal {q : ℂ} (hq : ‖q‖ < 1) : AbsConv (pentagonalSeries ℂ) q := by
  refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun n => ?_
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow, norm_mul, norm_pow, norm_pow]
    simp
  · simp [coeff_pentagonalSeries_eq_zero ℂ hn]

theorem ev_pentagonal {q : ℂ} (hq : ‖q‖ < 1) :
    ev (pentagonalSeries ℂ) q = ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  rw [← eulerFunction_eq_tprod hq]
  rfl

theorem map_pentagonalSeries :
    PowerSeries.map (Int.castRingHom ℂ) (pentagonalSeries ℤ) = pentagonalSeries ℂ := by
  ext n
  rw [coeff_map]
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp only [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    simp
  · simp [coeff_pentagonalSeries_eq_zero _ hn]


/-! ## Integrality of `τ` -/

local notation "𝕢" => Function.Periodic.qParam

theorem hasSum_discriminant (z : ℍ) :
    HasSum (fun m => coeff m (X * pentagonalSeries ℂ ^ 24) • 𝕢 1 (z : ℂ) ^ m)
      (ModularForm.discriminant z) := by
  have hq : ‖𝕢 1 (z : ℂ)‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hP := absConv_pentagonal hq
  have hP24 := hP.pow 24
  have hc := (absConv_X _).mul hP24.1
  convert hc.hasSum using 1
  rw [ev_mul (absConv_X _) hP24.1, ev_X, hP24.2, ev_pentagonal hq, discriminant_eq_q_prod,
    ← (multipliable_one_sub_pow hq).tprod_pow]

/-- The `q`-expansion of `Δ` is `q ∏ (1 - qⁿ)²⁴`, a power series with integer coefficients. -/
theorem qExpansion_discriminant_eq : qExpansion 1 ModularForm.discriminant =
    PowerSeries.map (Int.castRingHom ℂ) (X * pentagonalSeries ℤ ^ 24) := by
  ext m
  rw [map_mul, map_pow, map_X, map_pentagonalSeries]
  exact (ModularFormClass.qExpansion_coeff_unique (f := CuspForm.discriminant) one_pos
    one_mem_strictPeriods_SL hasSum_discriminant m).symm

/-- Ramanujan's `τ(n) ∈ ℤ`: the `qⁿ`-coefficient of `X · (∏ (1 - Xⁿ))²⁴ ∈ ℤ⟦X⟧`. -/
noncomputable def tauZ (n : ℕ) : ℤ := coeff n (X * pentagonalSeries ℤ ^ 24)

theorem τ_eq_tauZ (n : ℕ) : Fugue.RamanujanL.τ n = tauZ n := by
  rw [Fugue.RamanujanL.τ, qExpansion_discriminant_eq, coeff_map]
  rfl

theorem τ_int (n : ℕ) : ∃ t : ℤ, Fugue.RamanujanL.τ n = t := ⟨tauZ n, τ_eq_tauZ n⟩


/-! ## Weight 12: `E₄³ - E₁₂ = (432000/691) Δ` -/

/-- The normalised weight-12 Eisenstein series. -/
noncomputable abbrev E₁₂ : ModularForm 𝒮ℒ 12 := E (by norm_num : 3 ≤ 12)

theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

theorem coeff_E₁₂ (m : ℕ) :
    (qExpansion 1 E₁₂).coeff m = if m = 0 then 1 else 65520 / 691 * (σ 11 m : ℂ) := by
  rw [E_qExpansion_coeff _ ⟨6, rfl⟩, bernoulli_twelve]
  norm_num

/-- `E₄³` as a weight-12 form. -/
noncomputable def E₄cube : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) (E₄.pow 3) rfl

theorem qExpansion_E₄cube : qExpansion 1 E₄cube = qExpansion 1 E₄ ^ 3 := by
  rw [E₄cube, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

/-- The integral `q`-expansion `1 + 240 ∑ σ₃(n) qⁿ` of `E₄`. -/
noncomputable def E4Z : PowerSeries ℤ := PowerSeries.mk fun m => if m = 0 then 1 else 240 * σ 3 m

theorem qExpansion_E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) E4Z := by
  ext m
  rw [Fugue.coeff_E₄, coeff_map, E4Z, coeff_mk]
  split_ifs <;> simp

theorem qExpansion_E₄cube_eq :
    qExpansion 1 E₄cube = PowerSeries.map (Int.castRingHom ℂ) (E4Z ^ 3) := by
  rw [qExpansion_E₄cube, qExpansion_E₄_eq, map_pow]

/-- `E₄³ - E₁₂`, a weight-12 cusp form. -/
noncomputable def G : ModularForm 𝒮ℒ 12 := E₄cube - E₁₂

theorem qExpansion_G : qExpansion 1 G = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₁₂ := by
  rw [G, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    qExpansion_E₄cube]

theorem coeff_E₄_cube_zero_one : (qExpansion 1 E₄ ^ 3).coeff 0 = 1 ∧
    (qExpansion 1 E₄ ^ 3).coeff 1 = 720 := by
  obtain ⟨a0, a1, -⟩ := Fugue.coeff_E₄_small
  constructor
  · simp only [pow_succ, pow_zero, one_mul, Fugue.coeff0_mul, a0]
  · simp only [pow_succ, pow_zero, one_mul, Fugue.coeff0_mul, Fugue.coeff1_mul, a0, a1]; norm_num

theorem G_isCuspForm : IsCuspForm G := by
  rw [isCuspForm_iff_coeffZero_eq_zero, qExpansion_G, map_sub, coeff_E₄_cube_zero_one.1,
    coeff_E₁₂]
  simp

/-- `E₄³ - E₁₂ = c • Δ` for some `c`, as `q`-expansions. -/
theorem exists_qExpansion_G : ∃ c : ℂ,
    qExpansion 1 G = c • qExpansion 1 ModularForm.discriminant := by
  obtain ⟨g, hg⟩ := G_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  refine ⟨c, ?_⟩
  have h1 : (G : ℍ → ℂ) = c • (CuspForm.discriminant : ℍ → ℂ) := by
    rw [← hg, CuspForm.toModularFormₗ_eq_coe, ← hc]
    rfl
  rw [h1, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
  rfl

/-- **`E₄³ - E₁₂ = (432000/691) Δ`** (coefficientwise). -/
theorem qExpansion_G_eq :
    qExpansion 1 G = (432000 / 691 : ℂ) • qExpansion 1 ModularForm.discriminant := by
  obtain ⟨c, hc⟩ := exists_qExpansion_G
  have h1 := congrArg (coeff 1) hc
  rw [coeff_smul, ← Fugue.RamanujanL.τ, Fugue.RamanujanL.τ_one, qExpansion_G, map_sub,
    coeff_E₄_cube_zero_one.2, coeff_E₁₂] at h1
  simp only [one_ne_zero, ite_false, ArithmeticFunction.sigma_one, smul_eq_mul, mul_one] at h1
  rw [hc]
  congr 1
  rw [← h1]
  norm_num

/-! ## Ramanujan's congruence -/

/-- Comparing `qⁿ`-coefficients in `E₄³ - E₁₂ = (432000/691) Δ`:
`65520 σ₁₁(n) + 432000 τ(n) = 691 aₙ(E₄³)`, all terms integers. -/
theorem key_identity (n : ℕ) (hn : n ≠ 0) :
    65520 * (σ 11 n : ℤ) + 432000 * tauZ n = 691 * coeff n (E4Z ^ 3) := by
  have h := congrArg (coeff n) qExpansion_G_eq
  rw [coeff_smul, ← Fugue.RamanujanL.τ, τ_eq_tauZ, qExpansion_G, map_sub, ← qExpansion_E₄cube,
    qExpansion_E₄cube_eq, coeff_map, coeff_E₁₂, smul_eq_mul] at h
  simp only [hn, ite_false] at h
  have h' : ((65520 * (σ 11 n : ℤ) + 432000 * tauZ n : ℤ) : ℂ) =
      ((691 * coeff n (E4Z ^ 3) : ℤ) : ℂ) := by
    push_cast
    simp only [eq_intCast] at h
    linear_combination (-691 : ℂ) * h
  exact_mod_cast h'

theorem tauZ_zero : tauZ 0 = 0 := by simp [tauZ]

theorem tauZ_two : tauZ 2 = -24 := by
  have h := τ_eq_tauZ 2
  rw [Fugue.RamanujanL.τ_two] at h
  exact_mod_cast h.symm

/-- Sanity check: `τ(2) = -24`, `σ₁₁(2) = 2049`, `2049 + 24 = 3 · 691`. -/
example : (691 : ℤ) ∣ tauZ 2 - σ 11 2 := by
  rw [tauZ_two, show σ 11 2 = 2049 by decide]
  norm_num

/-- **Ramanujan's congruence** (1916): `τ(n) ≡ σ₁₁(n) (mod 691)`. -/
theorem _root_.Fugue.tau_congr_691 (n : ℕ) :
    (tauZ n : ZMod 691) = (σ 11 n : ZMod 691) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tauZ_zero]
  have h := congrArg (Int.cast : ℤ → ZMod 691) (key_identity n hn)
  push_cast at h
  have h691 : (691 : ZMod 691) = 0 := by decide
  have e1 : (65520 : ZMod 691) = 566 := by decide
  have e2 : (432000 : ZMod 691) = -566 := by decide
  rw [h691, zero_mul, e1, e2] at h
  have h566 : (566 : ZMod 691) ≠ 0 := by decide
  have h2 : (566 : ZMod 691) * ((σ 11 n : ZMod 691) - tauZ n) = 0 := by
    linear_combination h
  have : Fact (Nat.Prime 691) := ⟨by norm_num⟩
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 h566
  · exact (sub_eq_zero.mp h3).symm

/-- The congruence in divisibility form: `691 ∣ τ(n) - σ₁₁(n)`. -/
theorem _root_.Fugue.tau_sub_sigma_dvd (n : ℕ) : (691 : ℤ) ∣ tauZ n - σ 11 n := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 691).mp ?_
  push_cast
  rw [Fugue.tau_congr_691, sub_self]

end Fugue.Tau691
