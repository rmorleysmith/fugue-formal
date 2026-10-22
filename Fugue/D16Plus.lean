import Fugue.HeteroticE8

set_option autoImplicit false

/-!
# Witt's isospectrality: `Θ_{D16⁺} = Θ_{E8 ⊕ E8} = E₈`

## Physics context

The two ten-dimensional heterotic string theories are built on the two even unimodular
lattices of rank 16 (these are the only ones, a classical fact *not* proved here):

* `E8 ⊕ E8`, giving the `E8 × E8` heterotic string, and
* `D16⁺ = D16 ∪ (D16 + ½𝟙)`, giving the `Spin(32)/ℤ₂` heterotic string.

Witt observed that these two lattices have the **same theta series**, i.e. the same number of
vectors of every length; equivalently the flat tori `ℝ¹⁶/(E8 ⊕ E8)` and `ℝ¹⁶/D16⁺` have the same
Laplace spectrum (Milnor's 1964 example of isospectral, non-isometric manifolds). The two lattices
are *not* isometric: the 480 roots (norm-2 vectors) of `E8 ⊕ E8` form the root system `E8 ⊔ E8`
(two mutually orthogonal sets), whereas the 480 roots `±eᵢ ± eⱼ` of `D16⁺` form the irreducible root
system `D16`. **That non-isometry is not formalised in this file**; only the equality of theta
series is.

## Content

* `D16PlusY`: `D16⁺` in doubled integer coordinates `y = 2x`:
  all `yᵢ` of the same parity and `Σ yᵢ ≡ 0 (mod 4)`; `‖x‖² = ‖y‖²/4`.
* `thetaD16 τ = Σ_{y ∈ D16PlusY} e^{πiτ‖y‖²/4}` (`= Σ_{x ∈ D16⁺} q^{‖x‖²/2}`).
* `thetaD16_eq`: `thetaD16 = (θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2` — the parity split of
  `Fugue/ThetaE8Lattice.lean` in dimension 16 (`D16⁺ = 2·D16 ⊔ (2·D16 + 𝟙)` in doubled
  coordinates, and `𝟙_{Σz even} = (1 + (−1)^{Σz})/2`).
* `thetaCombo16_eq_E₈`: `(θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2 = E₈` — the transformation laws of
  `Fugue/ThetaE8Modular.lean` at 16th powers, `dim M₈ = 1` and the value `1` at `i∞`.
* `thetaD16_eq_thetaE8_sq`: **Witt's theorem** `Θ_{D16⁺} = Θ_{E8}² = Θ_{E8⊕E8}`.
-/

open Complex
open scoped Real

namespace Fugue

namespace D16Plus

open E8Lattice

/-! ### The lattice `D16⁺` and its theta series -/

/-- `D16⁺ = D16 ∪ (D16 + ½𝟙)` in doubled coordinates `y = 2x`: all coordinates of the same
parity and coordinate sum `≡ 0 (mod 4)`. -/
def D16PlusY : Set (Fin 16 → ℤ) :=
  {y | (∀ i j, y i ≡ y j [ZMOD 2]) ∧ (∑ i, y i) ≡ 0 [ZMOD 4]}

/-- The Gaussian weight in doubled coordinates: `e^{πiτ‖y‖²/4}`. -/
noncomputable def hY16 (τ : ℂ) (y : Fin 16 → ℤ) : ℂ :=
  cexp (π * I * τ * ((∑ i, y i ^ 2 : ℤ) : ℂ) / 4)

end D16Plus

open D16Plus

/-- The theta series of `D16⁺`: `Σ_{x ∈ D16⁺} e^{πiτ‖x‖²}`, written in doubled coordinates. -/
noncomputable def thetaD16 (τ : ℂ) : ℂ :=
  ∑' y : Fin 16 → ℤ, D16PlusY.indicator (hY16 τ) y

/-- The same series as a sum over the subtype `D16PlusY`. -/
theorem thetaD16_eq_tsum_subtype (τ : ℂ) :
    thetaD16 τ = ∑' y : D16PlusY, cexp (π * I * τ * ((∑ i, (y : Fin 16 → ℤ) i ^ 2 : ℤ) : ℂ) / 4) :=
  (tsum_subtype D16PlusY (hY16 τ)).symm

/-- The combination `(θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2`. -/
noncomputable def thetaCombo16 (τ : ℂ) : ℂ := (θ₂ τ ^ 16 + θ₃ τ ^ 16 + θ₄ τ ^ 16) / 2

namespace D16Plus

open E8Lattice

/-! ### Parity split -/

/-- `y = 2z` (the `D16` part) or `y = 2z + 𝟙` (the `D16 + ½𝟙` part). -/
def G16 : (Fin 16 → ℤ) ⊕ (Fin 16 → ℤ) → (Fin 16 → ℤ) :=
  Sum.elim (fun z i => 2 * z i) (fun z i => 2 * z i + 1)

theorem G16_injective : Function.Injective G16 := by
  rintro (z | z) (w | w) h <;> simp only [G16, Sum.elim_inl, Sum.elim_inr] at h
  · congr 1; funext i; have := congrFun h i; omega
  · have := congrFun h 0; omega
  · have := congrFun h 0; omega
  · congr 1; funext i; have := congrFun h i; omega

theorem D16PlusY_subset_range_G16 : D16PlusY ⊆ Set.range G16 := by
  intro y hy
  have hp : ∀ i, y i % 2 = y 0 % 2 := fun i => hy.1 i 0
  rcases Int.emod_two_eq_zero_or_one (y 0) with h | h
  · refine ⟨Sum.inl (fun i => y i / 2), ?_⟩
    funext i; have := hp i; simp only [G16, Sum.elim_inl]; omega
  · refine ⟨Sum.inr (fun i => y i / 2), ?_⟩
    funext i; have := hp i; simp only [G16, Sum.elim_inr]; omega

theorem G16_inl_mem (z : Fin 16 → ℤ) : G16 (Sum.inl z) ∈ D16PlusY ↔ (∑ i, z i) % 2 = 0 := by
  have hs : ∑ i, (2 * z i) = 2 * ∑ i, z i := (Finset.mul_sum _ _ _).symm
  simp only [D16PlusY, G16, Sum.elim_inl, Set.mem_ofPred_eq, hs, Int.ModEq]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨fun i j => by omega, by omega⟩

theorem G16_inr_mem (z : Fin 16 → ℤ) : G16 (Sum.inr z) ∈ D16PlusY ↔ (∑ i, z i) % 2 = 0 := by
  have hs : ∑ i, (2 * z i + 1) = 2 * ∑ i, z i + 16 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
  simp only [D16PlusY, G16, Sum.elim_inr, Set.mem_ofPred_eq, hs, Int.ModEq]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨fun i j => by omega, by omega⟩

theorem prod_ta' {n : ℕ} (τ : ℂ) (z : Fin n → ℤ) :
    ∏ i, ta τ (z i) = cexp (π * I * τ * ((∑ i, z i ^ 2 : ℤ) : ℂ)) := by
  simp only [ta, ← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

theorem prod_sign' {n : ℕ} (z : Fin n → ℤ) :
    ∏ i, cexp (π * I * (z i : ℂ)) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

theorem prod_tc16 (τ : ℂ) (z : Fin 16 → ℤ) :
    ∏ i, tc τ (z i) = hY16 τ (fun i => 2 * z i + 1) := by
  simp only [tc, hY16, ← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_div]
  congr 1; funext i; ring

theorem F_G16_inl (τ : ℂ) (z : Fin 16 → ℤ) :
    D16PlusY.indicator (hY16 τ) (G16 (Sum.inl z)) =
      1 / 2 * ∏ i, ta τ (z i) + 1 / 2 * ∏ i, tb τ (z i) := by
  have hb : ∏ i, tb τ (z i) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) * ∏ i, ta τ (z i) := by
    simp only [tb, Finset.prod_mul_distrib, prod_sign']
  have hh : hY16 τ (G16 (Sum.inl z)) = ∏ i, ta τ (z i) := by
    rw [prod_ta']
    simp only [hY16, G16, Sum.elim_inl]
    congr 1
    have : ∑ i, (2 * z i) ^ 2 = 4 * ∑ i, z i ^ 2 := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    rw [this]; push_cast; ring
  rw [hb, cexp_pi_I_int]
  by_cases h : (∑ i, z i) % 2 = 0
  · rw [Set.indicator_of_mem ((G16_inl_mem z).mpr h), hh]; simp only [h, ↓reduceIte]; ring
  · rw [Set.indicator_of_notMem (fun h' => h ((G16_inl_mem z).mp h'))]
    simp only [h, ↓reduceIte]; ring

theorem F_G16_inr (τ : ℂ) (z : Fin 16 → ℤ) :
    D16PlusY.indicator (hY16 τ) (G16 (Sum.inr z)) =
      1 / 2 * ∏ i, tc τ (z i) + 1 / 2 * ∏ i, td τ (z i) := by
  have hd : ∏ i, td τ (z i) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) * ∏ i, tc τ (z i) := by
    simp only [td, Finset.prod_mul_distrib, prod_sign']
  have hh : hY16 τ (G16 (Sum.inr z)) = ∏ i, tc τ (z i) := by
    rw [prod_tc16]; rfl
  rw [hd, cexp_pi_I_int]
  by_cases h : (∑ i, z i) % 2 = 0
  · rw [Set.indicator_of_mem ((G16_inr_mem z).mpr h), hh]; simp only [h, ↓reduceIte]; ring
  · rw [Set.indicator_of_notMem (fun h' => h ((G16_inr_mem z).mp h'))]
    simp only [h, ↓reduceIte]; ring

theorem hasSum_indicator16 {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (D16PlusY.indicator (hY16 τ)) (thetaCombo16 τ) := by
  have hl : HasSum (D16PlusY.indicator (hY16 τ) ∘ G16 ∘ Sum.inl)
      (1 / 2 * θ₃ τ ^ 16 + 1 / 2 * θ₄ τ ^ 16) := by
    have := ((hasSum_prod_pi (hasSum_ta hτ) 16).1.mul_left (1 / 2)).add
      ((hasSum_prod_pi (hasSum_tb hτ) 16).1.mul_left (1 / 2))
    convert this using 1
    funext z
    exact F_G16_inl τ z
  have hr : HasSum (D16PlusY.indicator (hY16 τ) ∘ G16 ∘ Sum.inr)
      (1 / 2 * θ₂ τ ^ 16 + 1 / 2 * 0 ^ 16) := by
    have := ((hasSum_prod_pi (hasSum_tc hτ) 16).1.mul_left (1 / 2)).add
      ((hasSum_prod_pi (hasSum_td hτ) 16).1.mul_left (1 / 2))
    convert this using 1
    funext z
    exact F_G16_inr τ z
  have hsum := HasSum.sum (f := D16PlusY.indicator (hY16 τ) ∘ G16) hl hr
  rw [G16_injective.hasSum_iff] at hsum
  · convert hsum using 1
    rw [thetaCombo16]; ring
  · intro y hy
    exact Set.indicator_of_notMem (fun h => hy (D16PlusY_subset_range_G16 h)) _

end D16Plus

/-- **`Θ_{D16⁺} = (θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2`**, via `D16⁺ = D16 ∪ (D16 + ½𝟙)`. -/
theorem thetaD16_eq {τ : ℂ} (hτ : 0 < τ.im) :
    thetaD16 τ = (θ₂ τ ^ 16 + θ₃ τ ^ 16 + θ₄ τ ^ 16) / 2 :=
  (hasSum_indicator16 hτ).tsum_eq

/-! ### `(θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2` is a level-one modular form of weight 8 -/

lemma θ₂_pow_sixteen_add_one (τ : ℂ) : θ₂ (τ + 1) ^ 16 = θ₂ τ ^ 16 := by
  rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul, pow_mul, θ₂_pow_eight_add_one]

lemma thetaCombo16_add_one (τ : ℂ) : thetaCombo16 (τ + 1) = thetaCombo16 τ := by
  simp only [thetaCombo16, θ₂_pow_sixteen_add_one, θ₃_add_one, θ₄_add_one]
  ring

lemma sqrt_pow_sixteen (τ : ℂ) : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 16 = τ ^ 8 := by
  rw [show (16 : ℕ) = 8 * 2 by norm_num, pow_mul, sqrt_pow_eight, ← pow_mul]

lemma thetaCombo16_S (τ : ℂ) (hτ : 0 < τ.im) :
    thetaCombo16 (-1 / τ) = τ ^ 8 * thetaCombo16 τ := by
  simp only [thetaCombo16, θ₂_S τ hτ, θ₃_S τ hτ, θ₄_S τ hτ, mul_pow, sqrt_pow_sixteen]
  ring

lemma differentiableAt_thetaCombo16 {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaCombo16 τ := by
  have h3 : DifferentiableAt ℂ θ₃ τ := differentiableAt_jacobiTheta hτ
  have h4 : DifferentiableAt ℂ θ₄ τ := differentiableAt_jacobiTheta₂_snd (1 / 2) hτ
  exact ((((differentiableAt_θ₂ hτ).pow 16).add (h3.pow 16)).add (h4.pow 16)).div_const 2

open Filter Topology UpperHalfPlane

lemma tendsto_thetaCombo16 : Tendsto (fun τ : ℍ => thetaCombo16 τ) atImInfty (𝓝 1) := by
  have h := (((tendsto_θ₂.pow 16).add (tendsto_θ₃.pow 16)).add (tendsto_θ₄.pow 16)).div_const 2
  norm_num at h
  exact h

open ModularForm ModularGroup SlashInvariantForm
open scoped MatrixGroups

lemma thetaCombo16_slash_T :
    (fun τ : ℍ => thetaCombo16 τ) ∣[(8 : ℤ)] T = fun τ : ℍ => thetaCombo16 τ := by
  ext z
  rw [SL_slash_apply, modular_T_smul, denom_T', one_zpow, mul_one, coe_vadd, add_comm]
  push_cast
  exact thetaCombo16_add_one z

lemma thetaCombo16_slash_S :
    (fun τ : ℍ => thetaCombo16 τ) ∣[(8 : ℤ)] S = fun τ : ℍ => thetaCombo16 τ := by
  ext z
  rw [SL_slash_apply, modular_S_smul, denom_S, UpperHalfPlane.coe_mk,
    show (-(z : ℂ))⁻¹ = -1 / z by ring, thetaCombo16_S z z.2, zpow_neg, zpow_ofNat]
  field_simp [z.ne_zero]

/-- `(θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2` as a modular form of level one and weight 8. -/
noncomputable def thetaCombo16MF : ModularForm 𝒮ℒ 8 where
  toFun τ := thetaCombo16 τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z thetaCombo16_slash_S thetaCombo16_slash_T A
  holo' := fun τ =>
    (differentiableAt_thetaCombo16 τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z thetaCombo16_slash_S thetaCombo16_slash_T γ]
    exact tendsto_thetaCombo16.isBigO_one ℝ

lemma thetaCombo16MF_apply (τ : ℍ) : thetaCombo16MF τ = thetaCombo16 τ := rfl

/-- **`(θ₂¹⁶ + θ₃¹⁶ + θ₄¹⁶)/2 = E₈`.** -/
theorem thetaCombo16_eq_E₈ (τ : UpperHalfPlane) :
    (θ₂ τ ^ 16 + θ₃ τ ^ 16 + θ₄ τ ^ 16) / 2 = Fugue.E₈ τ := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₈
    (EisensteinSeries.E_ne_zero _ ⟨4, rfl⟩)).mp finrank_weight_eight thetaCombo16MF
  have hfun : ∀ τ : ℍ, thetaCombo16 τ = c * E₈ τ := fun τ => by
    rw [← thetaCombo16MF_apply, ← hc]
    rfl
  have h1 : Tendsto (fun τ : ℍ => c * E₈ τ) atImInfty (𝓝 (c * 1)) :=
    (EisensteinSeries.tendsto_E_atImInfty (k := 8)).const_mul c
  have h2 : Tendsto (fun τ : ℍ => c * E₈ τ) atImInfty (𝓝 1) :=
    tendsto_thetaCombo16.congr hfun
  have hc1 : c = 1 := by simpa using tendsto_nhds_unique h1 h2
  rw [← thetaCombo16, hfun, hc1, one_mul]

/-! ### Witt's theorem -/

/-- **`Θ_{D16⁺} = E₈`.** -/
theorem thetaD16_eq_E₈ (τ : UpperHalfPlane) : thetaD16 τ = Fugue.E₈ τ := by
  rw [thetaD16_eq τ.im_pos, thetaCombo16_eq_E₈]

/-- **Witt's theorem**: `D16⁺` and `E8 ⊕ E8` have the same theta series,
`Θ_{D16⁺} = Θ_{E8}² = Θ_{E8 ⊕ E8}` (both equal `E₈`). The lattices are not isometric, but that is
not proved here. -/
theorem thetaD16_eq_thetaE8_sq (τ : UpperHalfPlane) : thetaD16 τ = thetaE8 τ ^ 2 := by
  rw [thetaD16_eq_E₈, thetaE8_sq_eq_E₈]

end Fugue
