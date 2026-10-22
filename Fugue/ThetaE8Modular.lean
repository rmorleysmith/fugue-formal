import Fugue.ThetaE8Basic

set_option autoImplicit false

/-!
# `(θ₂⁸ + θ₃⁸ + θ₄⁸)/2 = E₄` (ledger row A2, modular half)

* `thetaCombo_add_one`: `T`-invariance, from `θ₃(τ+1) = θ₄(τ)`, `θ₄(τ+1) = θ₃(τ)`,
  `θ₂(τ+1) = e^{πi/4} θ₂(τ)` (all via `jacobiTheta₂ z (τ+1) = jacobiTheta₂ (z+1/2) τ`).
* `thetaCombo_S`: `thetaCombo(-1/τ) = τ⁴ thetaCombo(τ)`, from Mathlib's
  `jacobiTheta₂_functional_equation` at `z = 0, τ/2, 1/2`, with `((-iτ)^{1/2})⁸ = τ⁴`.
* holomorphy on `ℍ` and `thetaCombo → 1` at `i∞` (`θ₃, θ₄ → 1`, `θ₂ → 0`);
* `thetaComboMF : ModularForm 𝒮ℒ 4`, and `thetaCombo_eq_E₄` by `dim M₄ = 1` and comparing
  limits at `i∞`.
-/

open Complex
open scoped Real

namespace Fugue

/-! ### Translation `τ ↦ τ + 1` -/

lemma jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  refine tsum_congr fun n => ?_
  simp only [jacobiTheta₂_term]
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  refine ⟨m, ?_⟩
  have : (n : ℂ) * (n - 1) = m + m := by exact_mod_cast hm
  linear_combination (π * I) * this

lemma θ₃_add_one (τ : ℂ) : θ₃ (τ + 1) = θ₄ τ := by
  simp only [θ₃, θ₄, jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_add_one_right, zero_add]

lemma θ₄_add_one (τ : ℂ) : θ₄ (τ + 1) = θ₃ τ := by
  simp only [θ₃, θ₄, jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_add_one_right]
  rw [show (1 / 2 + 1 / 2 : ℂ) = 0 + 1 by norm_num, jacobiTheta₂_add_left]

lemma θ₂_add_one (τ : ℂ) : θ₂ (τ + 1) = cexp (π * I / 4) * θ₂ τ := by
  simp only [θ₂, jacobiTheta₂_add_one_right]
  rw [show (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 by ring, jacobiTheta₂_add_left, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

lemma θ₂_pow_eight_add_one (τ : ℂ) : θ₂ (τ + 1) ^ 8 = θ₂ τ ^ 8 := by
  rw [θ₂_add_one, mul_pow, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (π * I / 4) = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I,
    one_mul]

lemma thetaCombo_add_one (τ : ℂ) : thetaCombo (τ + 1) = thetaCombo τ := by
  simp only [thetaCombo, θ₂_pow_eight_add_one, θ₃_add_one, θ₄_add_one]
  ring

/-! ### Inversion `τ ↦ -1/τ` -/

lemma θ₃_S (τ : ℂ) (hτ : 0 < τ.im) :
    θ₃ (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * θ₃ τ := by
  have h0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have h1 : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  have := jacobiTheta₂_functional_equation 0 τ
  simp only [θ₃, jacobiTheta_eq_jacobiTheta₂]
  rw [this]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one]
  field_simp

lemma θ₄_S (τ : ℂ) (hτ : 0 < τ.im) :
    θ₄ (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * θ₂ τ := by
  have h0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have h1 : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  have := jacobiTheta₂_functional_equation (τ / 2) τ
  rw [show τ / 2 / τ = 1 / 2 by field_simp] at this
  simp only [θ₂, θ₄]
  have he : cexp (π * I * τ / 4) * cexp (-π * I * (τ / 2) ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add, show (π : ℂ) * I * τ / 4 + -π * I * (τ / 2) ^ 2 / τ = 0 by
      field_simp; ring, Complex.exp_zero]
  have hA := mul_one_div_cancel h1
  rw [this]
  linear_combination (-(jacobiTheta₂ (1 / 2) (-1 / τ))) * hA -
    (jacobiTheta₂ (1 / 2) (-1 / τ) * ((-I * τ) ^ (1 / 2 : ℂ) * (1 / (-I * τ) ^ (1 / 2 : ℂ)))) * he

lemma θ₂_S (τ : ℂ) (hτ : 0 < τ.im) :
    θ₂ (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * θ₄ τ := by
  have h0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have h1 : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  have := jacobiTheta₂_functional_equation (1 / 2) τ
  simp only [θ₂, θ₄]
  rw [this, ← mul_assoc, ← mul_assoc, mul_one_div_cancel h1, one_mul,
    show -1 / τ / 2 = -(1 / 2 / τ) by ring, jacobiTheta₂_neg_left]
  congr 2
  ring

lemma sqrt_pow_eight (τ : ℂ) : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 8 = τ ^ 4 := by
  rw [← cpow_nat_mul]
  norm_num
  rw [mul_pow, I_pow_four, one_mul]

lemma thetaCombo_S (τ : ℂ) (hτ : 0 < τ.im) :
    thetaCombo (-1 / τ) = τ ^ 4 * thetaCombo τ := by
  simp only [thetaCombo, θ₂_S τ hτ, θ₃_S τ hτ, θ₄_S τ hτ, mul_pow, sqrt_pow_eight]
  ring

/-! ### Holomorphy -/

lemma differentiableAt_θ₂ {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ θ₂ τ := by
  have hg : DifferentiableAt ℂ (fun t : ℂ => (t / 2, t)) τ := by fun_prop
  have hJ : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (τ / 2, τ) :=
    (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
  have h : DifferentiableAt ℂ (fun t : ℂ => jacobiTheta₂ (t / 2) t) τ := by
    exact DifferentiableAt.comp (f := fun t : ℂ => (t / 2, t)) τ hJ hg
  have he : DifferentiableAt ℂ (fun t : ℂ => cexp (π * I * t / 4)) τ :=
    ((differentiableAt_id.const_mul _).div_const 4).cexp
  exact he.mul h

lemma differentiableAt_thetaCombo {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaCombo τ := by
  have h3 : DifferentiableAt ℂ θ₃ τ := differentiableAt_jacobiTheta hτ
  have h4 : DifferentiableAt ℂ θ₄ τ := differentiableAt_jacobiTheta₂_snd (1 / 2) hτ
  exact ((((differentiableAt_θ₂ hτ).pow 8).add (h3.pow 8)).add (h4.pow 8)).div_const 2

/-! ### Behaviour at `i∞` -/

open Filter Topology UpperHalfPlane Asymptotics

lemma tendsto_im_atImInfty : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap

lemma tendsto_exp_neg_mul_im {a : ℝ} (ha : 0 < a) :
    Tendsto (fun τ : ℍ => Real.exp (-a * τ.im)) atImInfty (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (tendsto_im_atImInfty.const_mul_atTop_of_neg
      (neg_lt_zero.mpr ha))

lemma tendsto_θ₃ : Tendsto (fun τ : ℍ => θ₃ τ) atImInfty (𝓝 1) := by
  have h := (isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto tendsto_coe_atImInfty).trans_tendsto
    ((tendsto_exp_neg_mul_im Real.pi_pos).congr fun τ => by simp)
  rw [← tendsto_sub_nhds_zero_iff]
  exact h

lemma tendsto_θ₄ : Tendsto (fun τ : ℍ => θ₄ τ) atImInfty (𝓝 1) := by
  have hg : Tendsto (fun τ : ℍ => (τ : ℂ) + 1) atImInfty (comap Complex.im atTop) := by
    rw [tendsto_comap_iff]
    simpa [Function.comp_def] using tendsto_im_atImInfty
  have h := (isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto hg).trans_tendsto
    ((tendsto_exp_neg_mul_im Real.pi_pos).congr fun τ => by simp)
  rw [← tendsto_sub_nhds_zero_iff]
  simpa [Function.comp_def, ← θ₃_add_one, θ₃] using h

lemma norm_jacobiTheta₂_half_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ‖ ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n (Complex.I / 2) Complex.I‖ := by
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (Complex.I / 2) Complex.I‖) :=
    summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff _ _).mpr (by simp))
  have hle : ∀ n : ℤ, ‖jacobiTheta₂_term n (τ / 2) τ‖ ≤ ‖jacobiTheta₂_term n (Complex.I / 2) Complex.I‖ := by
    intro n
    rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp]
    have hn : (0 : ℝ) ≤ n * (n + 1) := by
      have : (0 : ℤ) ≤ n * (n + 1) := by
        rcases le_or_gt 0 n with h | h <;> nlinarith
      exact_mod_cast this
    have hτ2 : (τ / 2).im = τ.im / 2 := by simp
    have hI2 : (Complex.I / 2).im = 1 / 2 := by simp
    rw [hτ2, hI2, Complex.I_im]
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_nonneg.mpr hτ)]
  exact (norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
    ((hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle).tsum_mono hs hle)

lemma tendsto_θ₂ : Tendsto (fun τ : ℍ => θ₂ τ) atImInfty (𝓝 0) := by
  set C := ∑' n : ℤ, ‖jacobiTheta₂_term n (Complex.I / 2) Complex.I‖
  have hev : ∀ᶠ τ : ℍ in atImInfty, ‖θ₂ τ‖ ≤ C * Real.exp (-(π / 4) * τ.im) := by
    refine (atImInfty_mem _).mpr ⟨1, fun τ hτ => ?_⟩
    simp only [Set.mem_ofPred_eq, θ₂, norm_mul, Complex.norm_exp]
    have hre : (π * Complex.I * (τ : ℂ) / 4).re = -(π / 4) * τ.im := by simp; ring
    rw [hre, mul_comm C]
    exact mul_le_mul_of_nonneg_left (norm_jacobiTheta₂_half_le (by simpa using hτ))
      (Real.exp_pos _).le
  refine squeeze_zero_norm' hev ?_
  simpa using (tendsto_exp_neg_mul_im (by positivity : (0 : ℝ) < π / 4)).const_mul C

lemma tendsto_thetaCombo : Tendsto (fun τ : ℍ => thetaCombo τ) atImInfty (𝓝 1) := by
  have h := (((tendsto_θ₂.pow 8).add (tendsto_θ₃.pow 8)).add (tendsto_θ₄.pow 8)).div_const 2
  norm_num at h
  exact h

/-! ### `thetaCombo` as a level-one modular form of weight 4 -/

open ModularForm ModularGroup SlashInvariantForm
open scoped MatrixGroups

set_option backward.isDefEq.respectTransparency false in
lemma denom_T' (z : ℍ) : denom T z = 1 := by simp [T, ModularGroup.denom_apply]

lemma thetaCombo_slash_T :
    (fun τ : ℍ => thetaCombo τ) ∣[(4 : ℤ)] T = fun τ : ℍ => thetaCombo τ := by
  ext z
  rw [SL_slash_apply, modular_T_smul, denom_T', one_zpow, mul_one, coe_vadd, add_comm]
  push_cast
  exact thetaCombo_add_one z

lemma thetaCombo_slash_S :
    (fun τ : ℍ => thetaCombo τ) ∣[(4 : ℤ)] S = fun τ : ℍ => thetaCombo τ := by
  ext z
  rw [SL_slash_apply, modular_S_smul, denom_S, UpperHalfPlane.coe_mk, show (-(z : ℂ))⁻¹ = -1 / z by ring,
    thetaCombo_S z z.2, zpow_neg, zpow_ofNat]
  field_simp [z.ne_zero]

/-- `(θ₂⁸ + θ₃⁸ + θ₄⁸)/2` as a modular form of level one and weight 4. -/
noncomputable def thetaComboMF : ModularForm 𝒮ℒ 4 where
  toFun τ := thetaCombo τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z thetaCombo_slash_S thetaCombo_slash_T A
  holo' := fun τ =>
    (differentiableAt_thetaCombo τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z thetaCombo_slash_S thetaCombo_slash_T γ]
    exact tendsto_thetaCombo.isBigO_one ℝ

lemma thetaComboMF_apply (τ : ℍ) : thetaComboMF τ = thetaCombo τ := rfl

/-- **`(θ₂⁸ + θ₃⁸ + θ₄⁸)/2 = E₄`.** -/
theorem thetaCombo_eq_E₄ (τ : UpperHalfPlane) : Fugue.thetaCombo τ = ModularForm.E₄ τ := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) thetaComboMF
  have hfun : ∀ τ : ℍ, thetaCombo τ = c * E₄ τ := fun τ => by
    rw [← thetaComboMF_apply, ← hc]
    rfl
  have h1 : Tendsto (fun τ : ℍ => c * E₄ τ) atImInfty (𝓝 (c * 1)) :=
    (EisensteinSeries.tendsto_E_atImInfty (k := 4)).const_mul c
  have h2 : Tendsto (fun τ : ℍ => c * E₄ τ) atImInfty (𝓝 1) :=
    tendsto_thetaCombo.congr hfun
  have hc1 : c = 1 := by simpa using tendsto_nhds_unique h1 h2
  rw [hfun, hc1, one_mul]

end Fugue
