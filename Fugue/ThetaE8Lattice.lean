import Fugue.ThetaE8Basic

set_option autoImplicit false

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

end E8Lattice

end Fugue
