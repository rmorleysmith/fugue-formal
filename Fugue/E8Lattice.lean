import Mathlib

/-!
# The E8 lattice is even, unimodular and positive definite (ledger row A1)

The corpus' geometric kernel is the E8 lattice (ledger A1: "even unimodular lattice of rank 8;
Gram determinant 1", verified numerically there). Mathlib has the Cartan matrix `E 8`, with
`E₈_det : (E 8).det = 1` and `E₈_isSymm`. We add the two remaining properties that make it the
Gram matrix of an *even unimodular positive definite lattice*:

* `e8Form_even` — `xᵀ E₈ x` is even for every integer vector `x` (all diagonal entries are 2);
* `e8Form_pos` — `xᵀ E₈ x > 0` for every nonzero `x` (via an explicit `LDLᵀ` certificate:
  `xᵀE₈x = 2y₀² + 2y₁² + (3/2)y₂² + (5/6)y₃² + (4/5)y₄² + (3/4)y₅² + (2/3)y₆² + (1/2)y₇²`
  with `y = Lᵀx` unitriangular).

Together with `E₈_det` this is *unimodular*. (Feeding E8 into the direct-sum theorem of
`Fugue/Theta.lean` — `Θ_{E8⊕E8} = Θ_{E8}²`, the corpus' heterotic `E8 × E8` motivation — also
needs finiteness of the fibres of `e8Form`, which follows from positive definiteness but is not
yet written out.)
-/

open Matrix CartanMatrix

namespace Fugue

/-- The quadratic form `x ↦ xᵀ E₈ x` of the E8 Cartan matrix. -/
def e8Form (x : Fin 8 → ℤ) : ℤ := x ⬝ᵥ (CartanMatrix.E 8 *ᵥ x)

theorem e8Form_eq (x : Fin 8 → ℤ) : e8Form x =
    2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
      - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7) := by
  simp only [e8Form, E_eight_eq, dotProduct, mulVec, Fin.sum_univ_eight]
  simp
  ring

/-- **E8 is even.** -/
theorem e8Form_even (x : Fin 8 → ℤ) : Even (e8Form x) := by
  rw [e8Form_eq]; exact even_two_mul _

/-- The `LDLᵀ` certificate, over `ℝ`. -/
theorem e8Form_ldl (x : Fin 8 → ℤ) : (e8Form x : ℝ) =
    2 * ((x 0 : ℝ) - x 2 / 2) ^ 2 + 2 * ((x 1 : ℝ) - x 3 / 2) ^ 2
    + 3 / 2 * ((x 2 : ℝ) - 2 / 3 * x 3) ^ 2 + 5 / 6 * ((x 3 : ℝ) - 6 / 5 * x 4) ^ 2
    + 4 / 5 * ((x 4 : ℝ) - 5 / 4 * x 5) ^ 2 + 3 / 4 * ((x 5 : ℝ) - 4 / 3 * x 6) ^ 2
    + 2 / 3 * ((x 6 : ℝ) - 3 / 2 * x 7) ^ 2 + 1 / 2 * (x 7 : ℝ) ^ 2 := by
  rw [e8Form_eq]; push_cast; ring

/-- **E8 is positive definite.** -/
theorem e8Form_pos {x : Fin 8 → ℤ} (hx : x ≠ 0) : 0 < e8Form x := by
  have hnn : 0 ≤ (e8Form x : ℝ) := by rw [e8Form_ldl]; positivity
  have hnn' : 0 ≤ e8Form x := by exact_mod_cast hnn
  rcases hnn'.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have h0 : (e8Form x : ℝ) = 0 := by exact_mod_cast h.symm
    rw [e8Form_ldl] at h0
    set y0 : ℝ := (x 0 : ℝ) - x 2 / 2
    set y1 : ℝ := (x 1 : ℝ) - x 3 / 2
    set y2 : ℝ := (x 2 : ℝ) - 2 / 3 * x 3
    set y3 : ℝ := (x 3 : ℝ) - 6 / 5 * x 4
    set y4 : ℝ := (x 4 : ℝ) - 5 / 4 * x 5
    set y5 : ℝ := (x 5 : ℝ) - 4 / 3 * x 6
    set y6 : ℝ := (x 6 : ℝ) - 3 / 2 * x 7
    have p0 := sq_nonneg y0
    have p1 := sq_nonneg y1
    have p2 := sq_nonneg y2
    have p3 := sq_nonneg y3
    have p4 := sq_nonneg y4
    have p5 := sq_nonneg y5
    have p6 := sq_nonneg y6
    have p7 := sq_nonneg (x 7 : ℝ)
    have z : ∀ a : ℝ, a ^ 2 = 0 → a = 0 := fun a h => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have h7 : (x 7 : ℝ) = 0 := z _ (by linarith)
    have h6 : y6 = 0 := z _ (by linarith)
    have h5 : y5 = 0 := z _ (by linarith)
    have h4 : y4 = 0 := z _ (by linarith)
    have h3 : y3 = 0 := z _ (by linarith)
    have h2 : y2 = 0 := z _ (by linarith)
    have h1 : y1 = 0 := z _ (by linarith)
    have h0' : y0 = 0 := z _ (by linarith)
    have x7 : (x 7 : ℝ) = 0 := h7
    have x6 : (x 6 : ℝ) = 0 := by simp only [y6] at h6; linarith
    have x5 : (x 5 : ℝ) = 0 := by simp only [y5] at h5; linarith
    have x4 : (x 4 : ℝ) = 0 := by simp only [y4] at h4; linarith
    have x3 : (x 3 : ℝ) = 0 := by simp only [y3] at h3; linarith
    have x2 : (x 2 : ℝ) = 0 := by simp only [y2] at h2; linarith
    have x1 : (x 1 : ℝ) = 0 := by simp only [y1] at h1; linarith
    have x0 : (x 0 : ℝ) = 0 := by simp only [y0] at h0'; linarith
    funext i
    fin_cases i <;> simp only [Pi.zero_apply] <;>
      first
      | exact_mod_cast x0 | exact_mod_cast x1 | exact_mod_cast x2 | exact_mod_cast x3
      | exact_mod_cast x4 | exact_mod_cast x5 | exact_mod_cast x6 | exact_mod_cast x7

/-- **E8 is unimodular** (Mathlib's `E₈_det`). -/
theorem e8_unimodular : (CartanMatrix.E 8).det = 1 := E₈_det

end Fugue
