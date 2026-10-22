import Mathlib

/-!
# The dynamical claims that are theorems (ledger rows A9, E2, E3, E5)

**A9 — neurons are exactly the minima.** The corpus' "neurons" are the zeros of a holomorphic
`F`, and its dynamics is gradient descent on `|F|²`. The claim that the attractors (local
minima of `|F|`) are exactly the zeros is the *minimum modulus principle*:

* `isLocalMin_norm_of_eq_zero` — a zero is a local minimum (trivially: `|F| ≥ 0 = |F(z₀)|`);
* `eq_zero_of_isLocalMin_norm` — conversely, a local minimum of `|F|` at which `F` is *not*
  locally constant is a zero. Proof: if `F(z₀) ≠ 0`, `1/F` is holomorphic near `z₀` and `|1/F|`
  has a local *maximum*, so by the maximum modulus principle `1/F`, hence `F`, is locally
  constant.

**E2/E3/E5 — the coupling matrix.** For genus-2 states the corpus couples two flows by
`K(κ) = [[y₁², κ y₁ y₂], [κ y₁ y₂, y₂²]]` (`y₁, y₂ > 0`), which it identifies with the Siegel
metric. We prove:

* `couplingMatrix_posSemidef_iff` — `K` is positive semidefinite iff `|κ| ≤ 1`;
* `couplingMatrix_posDef_iff` — `K` is positive definite iff `|κ| < 1`;
* `equilibrium_preserved` — a common zero of the gradients stays an equilibrium for **every**
  `K`, positive or not. This sharpens ledger E5: the corpus' prose needed PSD and its Lean
  needed PosDef, but the equilibrium statement needs *neither*. What PSD buys is that the
  flow `ż = -K ∇E` still *descends*: `dE/dt = -∇Eᵀ K ∇E ≤ 0` (`descends_iff`).
-/

open Filter Topology Matrix

namespace Fugue

/-! ### A9: minimum modulus -/

theorem isLocalMin_norm_of_eq_zero {f : ℂ → ℂ} {c : ℂ} (h : f c = 0) :
    IsLocalMin (fun z => ‖f z‖) c :=
  Filter.Eventually.of_forall fun z => by simp [h]

/-- **Minimum modulus principle.** If `f` is holomorphic near `c`, `|f|` has a local minimum at
`c`, and `f` is not locally constant at `c`, then `f(c) = 0`. -/
theorem eq_zero_of_isLocalMin_norm {f : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hmin : IsLocalMin (fun z => ‖f z‖) c)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, f z = f c) : f c = 0 := by
  by_contra hc
  have hne : ∀ᶠ z in 𝓝 c, f z ≠ 0 :=
    (hd.self_of_nhds.continuousAt).eventually_ne hc
  have hd' : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (fun z => (f z)⁻¹) z := by
    filter_upwards [hd, hne] with z hz hz0 using hz.inv hz0
  have hmax : IsLocalMax (norm ∘ fun z => (f z)⁻¹) c := by
    filter_upwards [hmin, hne] with z hz hz0
    simp only [Function.comp_apply, norm_inv]
    exact inv_anti₀ (norm_pos_iff.mpr hc) hz
  have hconst := Complex.eventually_eq_of_isLocalMax_norm hd' hmax
  apply hnc
  filter_upwards [hconst] with z hz
  exact inv_injective hz

/-! ### E2/E3/E5: the coupling matrix -/

/-- The corpus' coupling matrix `K(κ) = [[y₁², κ y₁ y₂], [κ y₁ y₂, y₂²]]`. -/
def couplingMatrix (y₁ y₂ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ ^ 2, κ * y₁ * y₂; κ * y₁ * y₂, y₂ ^ 2]

theorem couplingMatrix_isHermitian (y₁ y₂ κ : ℝ) : (couplingMatrix y₁ y₂ κ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [couplingMatrix, conjTranspose]

/-- The quadratic form of `K`: `y₁² x₀² + 2κ y₁ y₂ x₀ x₁ + y₂² x₁²`. -/
theorem couplingMatrix_quadForm (y₁ y₂ κ : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (couplingMatrix y₁ y₂ κ *ᵥ x) =
      y₁ ^ 2 * x 0 ^ 2 + 2 * κ * y₁ * y₂ * x 0 * x 1 + y₂ ^ 2 * x 1 ^ 2 := by
  simp [couplingMatrix, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- Test vectors `(y₂, ∓y₁)` give `2 y₁² y₂² (1 ∓ κ)`. -/
private theorem quad_test (y₁ y₂ κ s : ℝ) :
    star (![y₂, s * y₁] : Fin 2 → ℝ) ⬝ᵥ (couplingMatrix y₁ y₂ κ *ᵥ ![y₂, s * y₁]) =
      y₁ ^ 2 * y₂ ^ 2 * (1 + 2 * κ * s + s ^ 2) := by
  rw [couplingMatrix_quadForm]; simp; ring

/-- **`K` is positive semidefinite iff `|κ| ≤ 1`.** -/
theorem couplingMatrix_posSemidef_iff {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h₂ : 0 < y₂) (κ : ℝ) :
    (couplingMatrix y₁ y₂ κ).PosSemidef ↔ |κ| ≤ 1 := by
  rw [posSemidef_iff_dotProduct_mulVec]
  have hp : 0 < y₁ ^ 2 * y₂ ^ 2 := by positivity
  constructor
  · rintro ⟨-, h⟩
    have hm := h ![y₂, -1 * y₁]
    have hp' := h ![y₂, 1 * y₁]
    rw [quad_test] at hm hp'
    rw [abs_le]
    constructor <;> nlinarith
  · intro hκ
    refine ⟨couplingMatrix_isHermitian _ _ _, fun x => ?_⟩
    rw [couplingMatrix_quadForm]
    have hκ2 : κ ^ 2 ≤ 1 := by nlinarith [abs_le.mp hκ, sq_abs κ]
    nlinarith [sq_nonneg (y₁ * x 0 + κ * y₂ * x 1), sq_nonneg (y₂ * x 1)]

/-- **`K` is positive definite iff `|κ| < 1`** (the hypothesis the corpus' Lean actually used). -/
theorem couplingMatrix_posDef_iff {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h₂ : 0 < y₂) (κ : ℝ) :
    (couplingMatrix y₁ y₂ κ).PosDef ↔ |κ| < 1 := by
  rw [posDef_iff_dotProduct_mulVec]
  have hp : 0 < y₁ ^ 2 * y₂ ^ 2 := by positivity
  constructor
  · rintro ⟨-, h⟩
    have hne : ∀ s : ℝ, (![y₂, s * y₁] : Fin 2 → ℝ) ≠ 0 := fun s h0 => by
      have := congrFun h0 0; simp at this; linarith
    have hm := h (hne (-1))
    have hp' := h (hne 1)
    rw [quad_test] at hm hp'
    rw [abs_lt]
    constructor <;> nlinarith
  · intro hκ
    refine ⟨couplingMatrix_isHermitian _ _ _, fun x hx => ?_⟩
    rw [couplingMatrix_quadForm]
    have hκ2 : κ ^ 2 < 1 := by nlinarith [abs_lt.mp hκ, sq_abs κ]
    by_cases hx1 : x 1 = 0
    · have hx0 : x 0 ≠ 0 := fun h0 => hx (by ext i; fin_cases i <;> simp [h0, hx1])
      rw [hx1]
      have : 0 < x 0 ^ 2 := by positivity
      nlinarith
    · have : 0 < (y₂ * x 1) ^ 2 := by positivity
      nlinarith [sq_nonneg (y₁ * x 0 + κ * y₂ * x 1)]

/-- **Ledger E3, sharpened.** If both gradients vanish, the coupled velocity `-K ∇E` vanishes,
for *any* matrix `K` — no positivity needed. -/
theorem equilibrium_preserved {n : Type*} [Fintype n] (K : Matrix n n ℝ) :
    -(K *ᵥ (0 : n → ℝ)) = 0 := by simp

/-- What positivity *is* for: along `ż = -K ∇E`, `dE/dt = -∇Eᵀ K ∇E`, which is `≤ 0` for every
gradient exactly when `K` is positive semidefinite, i.e. `|κ| ≤ 1`. -/
theorem descends_iff {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h₂ : 0 < y₂) (κ : ℝ) :
    (∀ g : Fin 2 → ℝ, -(g ⬝ᵥ (couplingMatrix y₁ y₂ κ *ᵥ g)) ≤ 0) ↔ |κ| ≤ 1 := by
  rw [← couplingMatrix_posSemidef_iff h₁ h₂, posSemidef_iff_dotProduct_mulVec]
  simp only [neg_nonpos, star_trivial]
  exact ⟨fun h => ⟨couplingMatrix_isHermitian _ _ _, h⟩, fun h => h.2⟩

end Fugue
