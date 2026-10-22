import Fugue.ThetaE8Basic
import Fugue.Ramanujan

set_option autoImplicit false

/-!
# E8 vector counts from `Θ_{E8} = E₄` (ledger row A2, numerical claims)

Assuming the identity `Θ_{E8} = E₄` on `ℍ` (proved elsewhere), we derive the corpus' numbers:
the number of E8 vectors of norm `2n` is `240 σ₃(n)`; in particular 240, 2160, 6720 for
`n = 1, 2, 3`.

* `reprCount_e8Norm_le`: `r(m) ≤ (80m+21)⁸` (box from `e8_coord_bound`);
* `summable_pow_e8Norm`: `∑_{v∈ℤ⁸} r^{Q(v)}` converges for `0 ≤ r < 1` (fibrewise, via the
  polynomial bound);
* `hasSum_thetaE8`: `Θ_{E8}(τ) = ∑_m r(m) qᵐ`, `q = e^{2πiτ}`;
* `reprCount_e8_of_theta`: uniqueness of `q`-expansion coefficients
  (`ModularFormClass.qExpansion_coeff_unique`) plus `coeff_E₄`.
-/

open Complex ModularForm PowerSeries
open scoped Real UpperHalfPlane MatrixGroups ArithmeticFunction.sigma

namespace Fugue

instance (m : ℕ) : Finite {x : Fin 8 → ℤ // e8Norm x = m} := e8Norm_finite_fibre m

/-- Polynomial bound on the number of E8 vectors of norm `2m`. -/
theorem reprCount_e8Norm_le (m : ℕ) : reprCount e8Norm m ≤ (80 * m + 21) ^ 8 := by
  set B : ℤ := 10 * (4 * m + 1) with hB
  set S : Finset (Fin 8 → ℤ) := Fintype.piFinset (fun _ : Fin 8 => Finset.Icc (-B) B)
  have hsub : {v : Fin 8 → ℤ | e8Norm v = m} ⊆ (S : Set (Fin 8 → ℤ)) := by
    intro x hx
    have hx' : e8Form x = 2 * m := (e8Norm_eq_iff x m).mp hx
    simp only [S, Fintype.coe_piFinset, Set.mem_pi, Set.mem_univ,
      Finset.coe_Icc, Set.mem_Icc, forall_const]
    intro i
    have h := abs_le.mp (e8_coord_bound hx'.le i)
    constructor
    · have := h.1; simp only [B]; exact_mod_cast this
    · have := h.2; simp only [B]; exact_mod_cast this
  have h1 : Nat.card {v : Fin 8 → ℤ // e8Norm v = m} ≤ Nat.card (S : Set (Fin 8 → ℤ)) :=
    Nat.card_mono S.finite_toSet hsub
  have h2 : Nat.card (S : Set (Fin 8 → ℤ)) = (80 * m + 21) ^ 8 := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    simp only [S, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    omega
  unfold reprCount
  omega

theorem reprCount_e8Norm_le' (m : ℕ) :
    (reprCount e8Norm m : ℝ) ≤ 101 ^ 8 * (m : ℝ) ^ 8 + 21 ^ 8 := by
  have h := reprCount_e8Norm_le m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at h ⊢
    exact_mod_cast h
  · have h' : (80 * m + 21) ^ 8 ≤ (101 * m) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    have h'' : (reprCount e8Norm m : ℝ) ≤ ((101 * m) ^ 8 : ℕ) := by exact_mod_cast h.trans h'
    push_cast at h''
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 101 * m by positivity) 8]

/-- The fibre-counted series `∑ r(m) rᵐ` converges for `0 ≤ r < 1`. -/
theorem summable_reprCount_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun m : ℕ => (reprCount e8Norm m : ℝ) * r ^ m := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hs : Summable fun m : ℕ => (101 ^ 8 * (m : ℝ) ^ 8 + 21 ^ 8) * r ^ m := by
    simp_rw [add_mul, mul_assoc]
    exact ((summable_pow_mul_geometric_of_norm_lt_one 8 hr').mul_left _).add
      ((summable_geometric_of_lt_one hr0 hr).mul_left _)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  exact mul_le_mul_of_nonneg_right (reprCount_e8Norm_le' m) (pow_nonneg hr0 _)

/-- `∑_{v ∈ ℤ⁸} r^{Q(v)}` converges for `0 ≤ r < 1`. -/
theorem summable_pow_e8Norm {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun v : Fin 8 → ℤ => r ^ e8Norm v := by
  rw [← (Equiv.sigmaFiberEquiv e8Norm).summable_iff]
  refine (summable_sigma_of_nonneg (fun _ => pow_nonneg hr0 _)).mpr ⟨fun m => Summable.of_finite, ?_⟩
  have : ∀ m : ℕ, ∑' y : {v : Fin 8 → ℤ // e8Norm v = m},
      r ^ e8Norm ((Equiv.sigmaFiberEquiv e8Norm) ⟨m, y⟩) = (reprCount e8Norm m : ℝ) * r ^ m := by
    intro m
    have hc : ∀ y : {v : Fin 8 → ℤ // e8Norm v = m},
        r ^ e8Norm ((Equiv.sigmaFiberEquiv e8Norm) ⟨m, y⟩) = r ^ m := fun y => by
      simp [Equiv.sigmaFiberEquiv, y.2]
    rw [tsum_congr hc, tsum_const, nsmul_eq_mul, reprCount]
  refine (summable_reprCount_mul_pow hr0 hr).congr fun m => ?_
  rw [← this]

theorem cexp_e8Form (τ : ℂ) (v : Fin 8 → ℤ) :
    cexp (π * I * τ * (e8Form v : ℂ)) = cexp (2 * π * I * τ) ^ e8Norm v := by
  have h : (e8Form v : ℂ) = 2 * (e8Norm v : ℂ) := by
    exact_mod_cast (e8Norm_eq_iff v _).mp rfl
  rw [h, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Fibrewise regrouping of `Θ_{E8}`**: `Θ_{E8}(τ) = ∑_m r(m) qᵐ` with `q = e^{2πiτ}`. -/
theorem hasSum_thetaE8 (τ : ℍ) :
    HasSum (fun m : ℕ => (reprCount e8Norm m : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (thetaE8 τ) := by
  set q : ℂ := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hq' : q = cexp (2 * π * I * τ) := by simp [hqdef, Function.Periodic.qParam]
  set f : (Fin 8 → ℤ) → ℂ := fun v => q ^ e8Norm v with hfdef
  have hfs : Summable f := by
    refine Summable.of_norm ?_
    simp only [f, norm_pow]
    exact summable_pow_e8Norm (norm_nonneg _) hq
  have hf : HasSum f (thetaE8 τ) := by
    have : thetaE8 τ = ∑' v, f v := by
      rw [thetaE8]
      refine tsum_congr fun v => ?_
      rw [cexp_e8Form, ← hq']
    rw [this]
    exact hfs.hasSum
  have hσ := (Equiv.sigmaFiberEquiv e8Norm).hasSum_iff.mpr hf
  refine hσ.sigma fun m => ?_
  have hs : Summable fun y : {v : Fin 8 → ℤ // e8Norm v = m} =>
      (f ∘ Equiv.sigmaFiberEquiv e8Norm) ⟨m, y⟩ := Summable.of_finite
  convert hs.hasSum using 1
  have hc : ∀ y : {v : Fin 8 → ℤ // e8Norm v = m},
      (f ∘ Equiv.sigmaFiberEquiv e8Norm) ⟨m, y⟩ = q ^ m := fun y => by
    simp [f, Equiv.sigmaFiberEquiv, y.2]
  rw [tsum_congr hc, tsum_const, nsmul_eq_mul, reprCount, smul_eq_mul]

/-- **The E8 vector count, assuming `Θ_{E8} = E₄`**: there are `240 σ₃(n)` vectors of norm `2n`. -/
theorem reprCount_e8_of_theta (h : ∀ τ : UpperHalfPlane, Fugue.thetaE8 τ = ModularForm.E₄ τ)
    (n : ℕ) (hn : 0 < n) :
    (Fugue.reprCount Fugue.e8Norm n : ℂ) = 240 * (ArithmeticFunction.sigma 3 n : ℂ) := by
  have hE : ∀ τ : ℍ, HasSum (fun m : ℕ => (reprCount e8Norm m : ℂ) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E₄ τ) := fun τ => h τ ▸ hasSum_thetaE8 τ
  rw [ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL hE n, coeff_E₄,
    ite_eq_right hn.ne']

/-- Natural-number form. -/
theorem reprCount_e8_of_theta' (h : ∀ τ : UpperHalfPlane, Fugue.thetaE8 τ = ModularForm.E₄ τ)
    (n : ℕ) (hn : 0 < n) : reprCount e8Norm n = 240 * σ 3 n := by
  exact_mod_cast reprCount_e8_of_theta h n hn

/-- `σ₃(1) = 1`, `σ₃(2) = 9`, `σ₃(3) = 28`. -/
theorem sigma_three_one : σ 3 1 = 1 := by decide
theorem sigma_three_two : σ 3 2 = 9 := by decide
theorem sigma_three_three : σ 3 3 = 28 := by decide

/-- **240** vectors of norm 2 (the roots of E8), assuming `Θ_{E8} = E₄`. -/
theorem reprCount_e8_one_of_theta (h : ∀ τ : UpperHalfPlane, Fugue.thetaE8 τ = ModularForm.E₄ τ) :
    reprCount e8Norm 1 = 240 := by
  rw [reprCount_e8_of_theta' h 1 one_pos, sigma_three_one]

/-- **2160** vectors of norm 4, assuming `Θ_{E8} = E₄`. -/
theorem reprCount_e8_two_of_theta (h : ∀ τ : UpperHalfPlane, Fugue.thetaE8 τ = ModularForm.E₄ τ) :
    reprCount e8Norm 2 = 2160 := by
  rw [reprCount_e8_of_theta' h 2 two_pos, sigma_three_two]

/-- **6720** vectors of norm 6, assuming `Θ_{E8} = E₄`. -/
theorem reprCount_e8_three_of_theta
    (h : ∀ τ : UpperHalfPlane, Fugue.thetaE8 τ = ModularForm.E₄ τ) :
    reprCount e8Norm 3 = 6720 := by
  rw [reprCount_e8_of_theta' h 3 (by norm_num), sigma_three_three]

end Fugue
