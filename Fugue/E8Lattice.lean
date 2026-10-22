import Fugue.Theta

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

/-- Every coordinate of a vector of E8-norm `≤ 2n` is bounded by `10(4n+1)`. -/
theorem e8_coord_bound {x : Fin 8 → ℤ} {n : ℕ} (hx : e8Form x ≤ 2 * n) (i : Fin 8) :
    |(x i : ℝ)| ≤ 10 * (4 * n + 1) := by
  have hQ : (e8Form x : ℝ) ≤ 2 * n := by exact_mod_cast hx
  rw [e8Form_ldl] at hQ
  set y0 : ℝ := (x 0 : ℝ) - x 2 / 2
  set y1 : ℝ := (x 1 : ℝ) - x 3 / 2
  set y2 : ℝ := (x 2 : ℝ) - 2 / 3 * x 3
  set y3 : ℝ := (x 3 : ℝ) - 6 / 5 * x 4
  set y4 : ℝ := (x 4 : ℝ) - 5 / 4 * x 5
  set y5 : ℝ := (x 5 : ℝ) - 4 / 3 * x 6
  set y6 : ℝ := (x 6 : ℝ) - 3 / 2 * x 7
  set M : ℝ := 4 * n + 1
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hM : 0 ≤ M := by positivity
  have p0 := sq_nonneg y0; have p1 := sq_nonneg y1; have p2 := sq_nonneg y2
  have p3 := sq_nonneg y3; have p4 := sq_nonneg y4; have p5 := sq_nonneg y5
  have p6 := sq_nonneg y6; have p7 := sq_nonneg (x 7 : ℝ)
  have hM2 : 4 * (n : ℝ) ≤ M ^ 2 := by simp only [M]; nlinarith
  have b : ∀ a : ℝ, a ^ 2 ≤ 4 * n → -M ≤ a ∧ a ≤ M := fun a ha =>
    abs_le_of_sq_le_sq' (ha.trans hM2) hM
  obtain ⟨a0, b0⟩ := b y0 (by linarith)
  obtain ⟨a1, b1⟩ := b y1 (by linarith)
  obtain ⟨a2, b2⟩ := b y2 (by linarith)
  obtain ⟨a3, b3⟩ := b y3 (by linarith)
  obtain ⟨a4, b4⟩ := b y4 (by linarith)
  obtain ⟨a5, b5⟩ := b y5 (by linarith)
  obtain ⟨a6, b6⟩ := b y6 (by linarith)
  obtain ⟨a7, b7⟩ := b (x 7 : ℝ) (by linarith)
  simp only [y0, y1, y2, y3, y4, y5, y6] at *
  rw [abs_le]
  fin_cases i <;> simp <;> constructor <;> linarith

/-- The vectors of E8-norm `2n` form a finite set. -/
theorem e8_finite_fibre (n : ℕ) : {x : Fin 8 → ℤ | e8Form x = 2 * n}.Finite := by
  set B : ℤ := 10 * (4 * n + 1)
  refine (Set.finite_Icc (fun _ : Fin 8 => -B) (fun _ => B)).subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h := (abs_le.mp (e8_coord_bound hx.le i)).1
    simp only [B]; exact_mod_cast h
  · have h := (abs_le.mp (e8_coord_bound hx.le i)).2
    simp only [B]; exact_mod_cast h

theorem e8Form_nonneg (x : Fin 8 → ℤ) : 0 ≤ e8Form x := by
  by_cases hx : x = 0
  · subst hx; simp [e8Form]
  · exact (e8Form_pos hx).le

/-- The E8 norm `Q(v) = ‖v‖²/2 ∈ ℕ` (well defined since the form is even and nonnegative). -/
def e8Norm (x : Fin 8 → ℤ) : ℕ := (e8Form x / 2).toNat

theorem e8Norm_eq_iff (x : Fin 8 → ℤ) (n : ℕ) : e8Norm x = n ↔ e8Form x = 2 * n := by
  obtain ⟨k, hk⟩ := e8Form_even x
  have h0 := e8Form_nonneg x
  unfold e8Norm
  rw [hk] at h0 ⊢
  constructor
  · intro h; omega
  · intro h; omega

theorem e8Norm_finite_fibre (n : ℕ) : Finite {x : Fin 8 → ℤ // e8Norm x = n} := by
  have : {x : Fin 8 → ℤ | e8Norm x = n} = {x | e8Form x = 2 * n} := by
    ext x; exact e8Norm_eq_iff x n
  exact Set.Finite.to_subtype (s := {x | e8Norm x = n}) (this ▸ e8_finite_fibre n)

/-- **`Θ_{E8 ⊕ E8} = Θ_{E8}²`** — the theta series of the heterotic lattice `E8 ⊕ E8` is the square
of that of E8 (as formal power series in `q`, with `Q = ‖v‖²/2`). -/
theorem theta_e8_sum_e8 : theta (directSum e8Norm e8Norm) = theta e8Norm * theta e8Norm :=
  theta_directSum e8Norm e8Norm e8Norm_finite_fibre e8Norm_finite_fibre

end Fugue
