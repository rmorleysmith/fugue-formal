import Fugue.ThetaE8

/-!
# The heterotic lattice `E8 ⊕ E8`: `Θ = E₈` and `480 σ₇(n)` vectors of norm `2n`

`E8 ⊕ E8` is the even unimodular lattice of the `E8 × E8` heterotic string. Its theta series is
`Θ_{E8}² = E₄² = E₈` (the weight-8 Eisenstein series; `M₈` is one-dimensional, so by the
Sturm/valence bound *one* coefficient determines a weight-8 form). Consequently the number of
vectors of norm `2n` in `E8 ⊕ E8` is `480 σ₇(n)` — e.g. 480 roots.

(The other even unimodular lattice of rank 16, `D16⁺`, of the `Spin(32)/ℤ₂` heterotic string, has
the *same* theta series — Witt's observation behind Milnor's isospectral 16-dimensional tori. That
is not formalised here.)
-/

open ModularForm
open scoped ArithmeticFunction.sigma

namespace Fugue

theorem reprCount_e8_zero : reprCount e8Norm 0 = 1 := by
  have : {x : Fin 8 → ℤ | e8Norm x = 0} = {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, e8Norm_eq_iff]
    constructor
    · intro h; by_contra hx; have := e8Form_pos hx; omega
    · rintro rfl; simp [e8Form]
  rw [reprCount, ← Set.coe_ofPred, this, Nat.card_coe_set_eq, Set.ncard_singleton]

/-- **`Θ_{E8⊕E8} = E₈`** as functions on the upper half-plane (`Θ_{E8⊕E8} = Θ_{E8}²`). -/
theorem thetaE8_sq_eq_E₈ (τ : UpperHalfPlane) : thetaE8 τ ^ 2 = Fugue.E₈ τ := by
  rw [thetaE8_eq_E₄, ← E₄sq_eq, E₄sq, coe_mcast, coe_mul, Pi.mul_apply, pow_two]

/-- **The number of vectors of norm `2n` in `E8 ⊕ E8` is `480 σ₇(n)`.** -/
theorem reprCount_e8e8 (n : ℕ) (hn : 0 < n) :
    reprCount (directSum e8Norm e8Norm) n = 480 * σ 7 n := by
  rw [reprCount_directSum _ _ e8Norm_finite_fibre e8Norm_finite_fibre,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', sigma_seven_eq (m + 1) hn]
  simp only [Nat.sub_self, Nat.sub_zero, reprCount_e8_zero, Nat.add_sub_cancel]
  rw [reprCount_e8 (m + 1) hn]
  have hint : ∀ i ∈ Finset.range m, reprCount e8Norm (i + 1) * reprCount e8Norm (m + 1 - (i + 1)) =
      57600 * (σ 3 (i + 1) * σ 3 (m - i)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [reprCount_e8 (i + 1) (by omega), show m + 1 - (i + 1) = m - i by omega,
      reprCount_e8 (m - i) (by omega)]
    ring
  rw [Finset.sum_congr rfl hint, ← Finset.mul_sum]
  ring

/-- 480 roots in `E8 ⊕ E8`. -/
theorem reprCount_e8e8_one : reprCount (directSum e8Norm e8Norm) 1 = 480 := by
  rw [reprCount_e8e8 1 one_pos]; decide

end Fugue
