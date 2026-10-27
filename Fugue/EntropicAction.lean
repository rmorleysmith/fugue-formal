import Mathlib

set_option autoImplicit false

/-!
# The entropic action, warm-up case (Bianconi, "Gravity from entropy", PRD 111, 066001 (2025))

The owner's idea (HANDOVER §9, 27 Oct 2026): the corpus' picture "gravity warps the path, not the
destination" and Bianconi's *gravity from entropy* should match. Bianconi's Lagrangian is the
geometric quantum relative entropy between the metric `g` and the metric `G = g + α M` induced
by a matter field, `L = Tr g ln G⁻¹ = −Tr ln (G g⁻¹) = −Σ ln λ̃ₙ` over the eigenvalues `λ̃ₙ` of
`G g⁻¹`. This file makes precise the two linear-algebra facts her warm-up scenario rests on,
in flat space (`g = 1`), where `G = 1 + α · u uᵀ` with `u = ∇φ`:

* **`warmup_lagrangian`** — the rank-one determinant identity gives
  `−ln det (1 + α u uᵀ) = −ln (1 + α |u|²)`: the matter field enters the entropic action only
  through `|∇φ|²` (Bianconi's slide "the massless Klein–Gordon equation emerges").
* **`warmup_linearisation`** — the derivative of `x ↦ −ln (1 + α x)` at `x = 0` is `−α`: at low
  energy the action is `−α |∇φ|²`, the massless Klein–Gordon Lagrangian.
* **`lam_nonneg`, `lam_eq_zero_iff`, `cosmological_nonneg`, `cosmological_eq_zero_iff`** — the
  emergent cosmological "constant" `Λ ∝ Tr [G − 1 − ln G] = Σ (λᵢ − 1 − ln λᵢ)` is `≥ 0`, and
  it is `0` exactly when every eigenvalue is `1`, i.e. when `G = g`: *the entropic action vanishes
  only at the vacuum* — the precise form of "warps the path, keeps the destination".

Nothing here is about curved space, the `G`-field, or Bianconi's equations of motion; those are
the content of her paper, not of this file.
-/

namespace Fugue.EntropicAction

open Matrix Real

variable {m : Type*} [Fintype m]

/-- The metric induced by a matter field with gradient `u`, in flat space: `G = 1 + α u uᵀ`. -/
noncomputable def inducedMetric [DecidableEq m] (α : ℝ) (u : m → ℝ) : Matrix m m ℝ :=
  1 + replicateCol Unit (α • u) * replicateRow Unit u

/-- The warm-up entropic Lagrangian, `L = Tr g ln G⁻¹ = −ln det G` for `g = 1`
(`−Σ ln λ̃ₙ = −ln ∏ λ̃ₙ = −ln det G`). -/
noncomputable def warmupLagrangian [DecidableEq m] (α : ℝ) (u : m → ℝ) : ℝ :=
  -Real.log (det (inducedMetric α u))

theorem det_inducedMetric [DecidableEq m] (α : ℝ) (u : m → ℝ) :
    det (inducedMetric α u) = 1 + α * (u ⬝ᵥ u) := by
  rw [inducedMetric, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, smul_eq_mul]

/-- **Bianconi's warm-up Lagrangian.** The matter field enters only through `|∇φ|²`:
`−ln det (1 + α ∇φ ∇φᵀ) = −ln (1 + α |∇φ|²)`. -/
theorem warmup_lagrangian [DecidableEq m] (α : ℝ) (u : m → ℝ) :
    warmupLagrangian α u = -Real.log (1 + α * (u ⬝ᵥ u)) := by
  rw [warmupLagrangian, det_inducedMetric]

/-- **The low-energy limit is massless Klein–Gordon**: `x ↦ −ln (1 + α x)` has derivative `−α`
at `x = 0`, so `L = −α |∇φ|² + o(|∇φ|²)`. -/
theorem warmup_linearisation (α : ℝ) :
    HasDerivAt (fun x : ℝ => -Real.log (1 + α * x)) (-α) 0 := by
  have h : HasDerivAt (fun x : ℝ => 1 + α * x) α 0 := by
    simpa using ((hasDerivAt_id 0).const_mul α).const_add 1
  have h' := (h.log (by norm_num)).neg
  convert h' using 1
  simp

/-- The eigenvalue contribution to the emergent cosmological constant, `λ − 1 − ln λ`. -/
noncomputable def lam (x : ℝ) : ℝ := x - 1 - Real.log x

theorem lam_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ lam x := by
  have := Real.log_le_sub_one_of_pos hx
  unfold lam; linarith

theorem lam_eq_zero_iff {x : ℝ} (hx : 0 < x) : lam x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hne
    have := Real.log_lt_sub_one_of_pos hx hne
    unfold lam at h; linarith
  · rintro rfl; simp [lam]

/-- **The emergent cosmological constant is non-negative** (Bianconi's `Λ_𝒢 ∝ Tr[𝒢 − 1 − ln 𝒢]`),
as a sum over the positive eigenvalues `ev i`. -/
theorem cosmological_nonneg (ev : m → ℝ) (hev : ∀ i, 0 < ev i) :
    0 ≤ ∑ i, lam (ev i) :=
  Finset.sum_nonneg fun i _ => lam_nonneg (hev i)

/-- **… and it vanishes only in the vacuum**: `Σ (λᵢ − 1 − ln λᵢ) = 0` iff every `λᵢ = 1`,
i.e. iff the induced metric equals the metric. -/
theorem cosmological_eq_zero_iff (ev : m → ℝ) (hev : ∀ i, 0 < ev i) :
    ∑ i, lam (ev i) = 0 ↔ ∀ i, ev i = 1 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => lam_nonneg (hev i)]
  simp only [Finset.mem_univ, true_implies]
  exact forall_congr' fun i => lam_eq_zero_iff (hev i)

/-- Sanity: in one dimension with `α = 1` and `u = (2)`, `det G = 5` and `L = −ln 5`. -/
example : warmupLagrangian (m := Fin 1) 1 (fun _ => 2) = -Real.log 5 := by
  rw [warmup_lagrangian]; norm_num [dotProduct]

end Fugue.EntropicAction
