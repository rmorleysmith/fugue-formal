import Fugue.ThetaE8Basic

set_option autoImplicit false

/-!
# `Θ_{E8} = (θ₂⁸ + θ₃⁸ + θ₄⁸)/2` (lattice half of ledger row A2)

Bourbaki simple roots `α₁ = ½(1,−1,−1,−1,−1,−1,−1,1)`, `α₂ = e₁+e₂`, `α_k = e_{k−1} − e_{k−2}`
(`k ≥ 3`) have Gram matrix exactly Mathlib's `CartanMatrix.E 8`. In doubled coordinates
`y = 2 Σ vᵢαᵢ` (`toY`) the map `v ↦ y` is a bijection from `ℤ⁸` onto
`S = {y : all yᵢ of equal parity, Σ yᵢ ≡ 0 mod 4}` with `‖y‖² = 4 vᵀAv` (`sumsq_toY`).
Splitting `S = 2·D8 ⊔ (2·D8 + 𝟙)` (`G`) and writing `𝟙_{Σz even} = (1 + (−1)^{Σz})/2`,
the sum factors into eighth powers of one-variable series: `θ₃, θ₄` on `2·D8`, and `θ₂` and
`Σ (−1)ⁿ e^{πiτ(n+½)²} = 0` (`n ↦ −1−n`) on the odd coset.
-/

open Complex
open scoped Real

namespace Fugue

namespace E8Lattice

/-- Twice the standard coordinates of `Σ vᵢ αᵢ`, Bourbaki simple roots. -/
def toY (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ![v 0 + 2 * v 1 - 2 * v 2, -v 0 + 2 * v 1 + 2 * v 2 - 2 * v 3, -v 0 + 2 * v 3 - 2 * v 4,
    -v 0 + 2 * v 4 - 2 * v 5, -v 0 + 2 * v 5 - 2 * v 6, -v 0 + 2 * v 6 - 2 * v 7,
    -v 0 + 2 * v 7, v 0]

theorem sumsq_toY (v : Fin 8 → ℤ) : ∑ i, toY v i ^ 2 = 4 * e8Form v := by
  rw [e8Form_eq]
  simp only [toY, Fin.sum_univ_eight]
  simp
  ring

/-- The doubled E8 lattice: all coordinates of the same parity, coordinate sum `≡ 0 mod 4`. -/
def S : Set (Fin 8 → ℤ) := {y | y 1 % 2 = y 0 % 2 ∧ y 2 % 2 = y 0 % 2 ∧ y 3 % 2 = y 0 % 2 ∧
  y 4 % 2 = y 0 % 2 ∧ y 5 % 2 = y 0 % 2 ∧ y 6 % 2 = y 0 % 2 ∧ y 7 % 2 = y 0 % 2 ∧
  (y 0 + y 1 + y 2 + y 3 + y 4 + y 5 + y 6 + y 7) % 4 = 0}

theorem toY_mem (v : Fin 8 → ℤ) : toY v ∈ S := by
  simp only [S, toY, Set.mem_ofPred_eq]
  simp
  omega

theorem toY_injective : Function.Injective toY := by
  intro v w h
  have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
  have h3 := congrFun h 3; have h4 := congrFun h 4; have h5 := congrFun h 5
  have h6 := congrFun h 6; have h7 := congrFun h 7
  simp only [toY] at h0 h1 h2 h3 h4 h5 h6 h7
  simp at h0 h1 h2 h3 h4 h5 h6 h7
  have e0 : v 0 = w 0 := by linarith
  have e7 : v 7 = w 7 := by linarith
  have e6 : v 6 = w 6 := by linarith
  have e5 : v 5 = w 5 := by linarith
  have e4 : v 4 = w 4 := by linarith
  have e3 : v 3 = w 3 := by linarith
  have e2 : v 2 = w 2 := by linarith
  have e1 : v 1 = w 1 := by linarith
  funext i
  fin_cases i <;> assumption

theorem S_subset_range_toY : S ⊆ Set.range toY := by
  intro y hy
  simp only [S, Set.mem_ofPred_eq] at hy
  refine ⟨![y 7, (y 0 + y 1 + y 2 + y 3 + y 4 + y 5 + y 6 + 5 * y 7) / 4,
    (-y 0 + y 1 + y 2 + y 3 + y 4 + y 5 + y 6 + 7 * y 7) / 4,
    (y 2 + y 3 + y 4 + y 5 + y 6 + 5 * y 7) / 2, (y 3 + y 4 + y 5 + y 6 + 4 * y 7) / 2,
    (y 4 + y 5 + y 6 + 3 * y 7) / 2, (y 5 + y 6 + 2 * y 7) / 2, (y 6 + y 7) / 2], ?_⟩
  funext i
  fin_cases i <;> simp [toY] <;> omega

/-! ### One-variable theta series -/

/-- Terms of `θ₃`. -/
noncomputable def ta (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * τ * (n : ℂ) ^ 2)
/-- Terms of `θ₄`. -/
noncomputable def tb (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * n) * ta τ n
/-- Terms of `θ₂`. -/
noncomputable def tc (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * τ * ((n : ℂ) + 1 / 2) ^ 2)
/-- Terms of the alternating half-integer theta series (which vanishes). -/
noncomputable def td (τ : ℂ) (n : ℤ) : ℂ := cexp (π * I * n) * tc τ n

theorem hasSum_ta {τ : ℂ} (hτ : 0 < τ.im) : HasSum (ta τ) (θ₃ τ) := by
  have := hasSum_jacobiTheta₂_term 0 hτ
  rw [θ₃, jacobiTheta_eq_jacobiTheta₂]
  convert this using 1
  funext n
  simp only [ta, jacobiTheta₂_term]
  congr 1; ring

theorem hasSum_tb {τ : ℂ} (hτ : 0 < τ.im) : HasSum (tb τ) (θ₄ τ) := by
  have := hasSum_jacobiTheta₂_term (1 / 2) hτ
  rw [θ₄]
  convert this using 1
  funext n
  simp only [tb, ta, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; ring

theorem hasSum_tc {τ : ℂ} (hτ : 0 < τ.im) : HasSum (tc τ) (θ₂ τ) := by
  have := (hasSum_jacobiTheta₂_term (τ / 2) hτ).mul_left (cexp (π * I * τ / 4))
  rw [θ₂]
  convert this using 1
  funext n
  simp only [tc, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; ring

theorem summable_td {τ : ℂ} (hτ : 0 < τ.im) : Summable (td τ) := by
  have := ((summable_jacobiTheta₂_term_iff (τ / 2 + 1 / 2) τ).mpr hτ).mul_left
    (cexp (π * I * τ / 4))
  convert this using 1
  funext n
  simp only [td, tc, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; ring

theorem td_neg (τ : ℂ) (n : ℤ) : td τ (-1 - n) = -td τ n := by
  have e : π * I * ((-1 - n : ℤ) : ℂ) + π * I * τ * (((-1 - n : ℤ) : ℂ) + 1 / 2) ^ 2 =
      (π * I * n + π * I * τ * ((n : ℂ) + 1 / 2) ^ 2 + ((-n - 1 : ℤ) : ℂ) * (2 * π * I)) +
        π * I := by
    push_cast; ring
  simp only [td, tc, ← Complex.exp_add]
  rw [e, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, exp_pi_mul_I]
  ring

theorem hasSum_td {τ : ℂ} (hτ : 0 < τ.im) : HasSum (td τ) 0 := by
  have hs := summable_td hτ
  have h1 : ∑' n, td τ n = -∑' n, td τ n := by
    calc ∑' n, td τ n = ∑' n, td τ (Equiv.subLeft (-1 : ℤ) n) :=
          ((Equiv.subLeft (-1 : ℤ)).tsum_eq (td τ)).symm
      _ = ∑' n, -td τ n := by
          congr 1; funext n
          exact td_neg τ n
      _ = _ := tsum_neg
  have h0 : ∑' n, td τ n = 0 := by
    have : (2 : ℂ) * ∑' n, td τ n = 0 := by linear_combination h1
    simpa using this
  rw [← h0]; exact hs.hasSum

/-! ### Products of absolutely convergent series over `Fin n → ℤ` -/

theorem hasSum_prod_pi {f : ℤ → ℂ} {s : ℂ} (hf : HasSum f s) (n : ℕ) :
    HasSum (fun z : Fin n → ℤ => ∏ i, f (z i)) (s ^ n) ∧
      Summable (fun z : Fin n → ℤ => ‖∏ i, f (z i)‖) := by
  have hn : Summable (fun x => ‖f x‖) := summable_norm_iff.mpr hf.summable
  induction n with
  | zero =>
    have h : HasSum (fun z : Fin 0 → ℤ => ∏ i, f (z i)) (s ^ 0) := by
      convert hasSum_single (f := fun z : Fin 0 → ℤ => ∏ i, f (z i)) (0 : Fin 0 → ℤ)
        (fun b hb => absurd (Subsingleton.elim b 0) hb) using 1
      simp
    refine ⟨h, ?_⟩
    exact (hasSum_single (f := fun z : Fin 0 → ℤ => ‖∏ i, f (z i)‖) (0 : Fin 0 → ℤ)
        (fun b hb => absurd (Subsingleton.elim b 0) hb)).summable
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
    have key : ∀ x : ℤ × (Fin n → ℤ), ∏ i, f (e x i) = f x.1 * ∏ i, f (x.2 i) := by
      intro x
      rw [Fin.prod_univ_succ]
      simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rw [← e.hasSum_iff]
      simp only [Function.comp_def, key]
      rw [pow_succ']
      have hm := summable_mul_of_summable_norm (f := f) (g := fun z : Fin n → ℤ => ∏ i, f (z i))
        hn h2
      have := HasSum.mul (f := f) (g := fun z : Fin n → ℤ => ∏ i, f (z i)) hf h1 hm
      exact this
    · rw [← e.summable_iff]
      simp only [Function.comp_def, key, norm_mul]
      exact hn.mul_of_nonneg h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-! ### Splitting the doubled lattice by parity -/

/-- The Gaussian weight in doubled coordinates: `e^{πiτ‖y‖²/4}`. -/
noncomputable def hY (τ : ℂ) (y : Fin 8 → ℤ) : ℂ := cexp (π * I * τ * ((∑ i, y i ^ 2 : ℤ) : ℂ) / 4)

/-- `y = 2z` (the `D8` part) or `y = 2z + 𝟙` (the `D8 + ½𝟙` part). -/
def G : (Fin 8 → ℤ) ⊕ (Fin 8 → ℤ) → (Fin 8 → ℤ) :=
  Sum.elim (fun z i => 2 * z i) (fun z i => 2 * z i + 1)

theorem G_injective : Function.Injective G := by
  rintro (z | z) (w | w) h <;> simp only [G, Sum.elim_inl, Sum.elim_inr] at h
  · congr 1; funext i; have := congrFun h i; omega
  · have := congrFun h 0; omega
  · have := congrFun h 0; omega
  · congr 1; funext i; have := congrFun h i; omega

theorem S_parity {y : Fin 8 → ℤ} (hy : y ∈ S) (i : Fin 8) : y i % 2 = y 0 % 2 := by
  simp only [S, Set.mem_ofPred_eq] at hy
  fin_cases i <;> simp <;> omega

theorem S_subset_range_G : S ⊆ Set.range G := by
  intro y hy
  rcases Int.emod_two_eq_zero_or_one (y 0) with h | h
  · refine ⟨Sum.inl (fun i => y i / 2), ?_⟩
    funext i; have := S_parity hy i; simp only [G, Sum.elim_inl]; omega
  · refine ⟨Sum.inr (fun i => y i / 2), ?_⟩
    funext i; have := S_parity hy i; simp only [G, Sum.elim_inr]; omega

theorem cexp_pi_I_int (m : ℤ) : cexp (π * I * m) = if m % 2 = 0 then 1 else -1 := by
  split_ifs with h
  · have e : (m : ℂ) = 2 * ((m / 2 : ℤ) : ℂ) := by exact_mod_cast (by omega : m = 2 * (m / 2))
    have : π * I * (m : ℂ) = ((m / 2 : ℤ) : ℂ) * (2 * π * I) := by rw [e]; ring
    rw [this, exp_int_mul_two_pi_mul_I]
  · have e : (m : ℂ) = 2 * ((m / 2 : ℤ) : ℂ) + 1 := by
      exact_mod_cast (by omega : m = 2 * (m / 2) + 1)
    have : π * I * (m : ℂ) = ((m / 2 : ℤ) : ℂ) * (2 * π * I) + π * I := by rw [e]; ring
    rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]

theorem prod_ta (τ : ℂ) (z : Fin 8 → ℤ) :
    ∏ i, ta τ (z i) = cexp (π * I * τ * ((∑ i, z i ^ 2 : ℤ) : ℂ)) := by
  simp only [ta, ← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

theorem prod_tc (τ : ℂ) (z : Fin 8 → ℤ) :
    ∏ i, tc τ (z i) = hY τ (fun i => 2 * z i + 1) := by
  simp only [tc, hY, ← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum, Finset.sum_div]
  congr 1; funext i; ring

theorem prod_sign (z : Fin 8 → ℤ) :
    ∏ i, cexp (π * I * (z i : ℂ)) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) := by
  rw [← Complex.exp_sum]
  congr 1; push_cast; rw [Finset.mul_sum]

theorem F_G_inl (τ : ℂ) (z : Fin 8 → ℤ) :
    S.indicator (hY τ) (G (Sum.inl z)) =
      1 / 2 * ∏ i, ta τ (z i) + 1 / 2 * ∏ i, tb τ (z i) := by
  have hb : ∏ i, tb τ (z i) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) * ∏ i, ta τ (z i) := by
    simp only [tb, Finset.prod_mul_distrib, prod_sign]
  have hh : hY τ (G (Sum.inl z)) = ∏ i, ta τ (z i) := by
    rw [prod_ta]
    simp only [hY, G, Sum.elim_inl]
    congr 1
    have : ∑ i, (2 * z i) ^ 2 = 4 * ∑ i, z i ^ 2 := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    rw [this]; push_cast; ring
  have hmem : G (Sum.inl z) ∈ S ↔ (∑ i, z i) % 2 = 0 := by
    simp only [S, G, Sum.elim_inl, Set.mem_ofPred_eq, Fin.sum_univ_eight]
    omega
  rw [hb, cexp_pi_I_int]
  by_cases h : (∑ i, z i) % 2 = 0
  · rw [Set.indicator_of_mem (hmem.mpr h), hh]; simp only [h, ↓reduceIte]; ring
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]; simp only [h, ↓reduceIte]; ring

theorem F_G_inr (τ : ℂ) (z : Fin 8 → ℤ) :
    S.indicator (hY τ) (G (Sum.inr z)) =
      1 / 2 * ∏ i, tc τ (z i) + 1 / 2 * ∏ i, td τ (z i) := by
  have hd : ∏ i, td τ (z i) = cexp (π * I * ((∑ i, z i : ℤ) : ℂ)) * ∏ i, tc τ (z i) := by
    simp only [td, Finset.prod_mul_distrib, prod_sign]
  have hh : hY τ (G (Sum.inr z)) = ∏ i, tc τ (z i) := by
    rw [prod_tc]; rfl
  have hmem : G (Sum.inr z) ∈ S ↔ (∑ i, z i) % 2 = 0 := by
    simp only [S, G, Sum.elim_inr, Set.mem_ofPred_eq, Fin.sum_univ_eight]
    omega
  rw [hd, cexp_pi_I_int]
  by_cases h : (∑ i, z i) % 2 = 0
  · rw [Set.indicator_of_mem (hmem.mpr h), hh]; simp only [h, ↓reduceIte]; ring
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h'))]; simp only [h, ↓reduceIte]; ring

theorem hasSum_indicator {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (S.indicator (hY τ)) (thetaCombo τ) := by
  have hl : HasSum (S.indicator (hY τ) ∘ G ∘ Sum.inl) (1 / 2 * θ₃ τ ^ 8 + 1 / 2 * θ₄ τ ^ 8) := by
    have := ((hasSum_prod_pi (hasSum_ta hτ) 8).1.mul_left (1 / 2)).add
      ((hasSum_prod_pi (hasSum_tb hτ) 8).1.mul_left (1 / 2))
    convert this using 1
    funext z
    exact F_G_inl τ z
  have hr : HasSum (S.indicator (hY τ) ∘ G ∘ Sum.inr) (1 / 2 * θ₂ τ ^ 8 + 1 / 2 * 0 ^ 8) := by
    have := ((hasSum_prod_pi (hasSum_tc hτ) 8).1.mul_left (1 / 2)).add
      ((hasSum_prod_pi (hasSum_td hτ) 8).1.mul_left (1 / 2))
    convert this using 1
    funext z
    exact F_G_inr τ z
  have hsum := HasSum.sum (f := S.indicator (hY τ) ∘ G) hl hr
  rw [G_injective.hasSum_iff] at hsum
  · convert hsum using 1
    rw [thetaCombo]; ring
  · intro y hy
    exact Set.indicator_of_notMem (fun h => hy (S_subset_range_G h)) _

end E8Lattice

open E8Lattice in
/-- **`Θ_{E8} = (θ₂⁸ + θ₃⁸ + θ₄⁸)/2`**, via `E8 = D8 ∪ (D8 + ½𝟙)`. -/
theorem thetaE8_eq_thetaCombo {τ : ℂ} (hτ : 0 < τ.im) : thetaE8 τ = thetaCombo τ := by
  have h := hasSum_indicator hτ
  rw [← toY_injective.hasSum_iff] at h
  · rw [thetaE8]
    convert h.tsum_eq using 2
    funext v
    rw [Function.comp_apply, Set.indicator_of_mem (toY_mem v), hY, sumsq_toY]
    congr 1; push_cast; ring
  · intro y hy
    exact Set.indicator_of_notMem (fun h => hy (S_subset_range_toY h)) _

end Fugue
