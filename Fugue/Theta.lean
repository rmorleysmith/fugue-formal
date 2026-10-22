import Mathlib

/-!
# Theta series of direct sums multiply (ledger rows B9, C13)

The corpus' "freeze the state, dial the gravity DNA" move (figure 12) rests on
`Θ_{L ⊕ M} = Θ_L · Θ_M`: the theta series of an orthogonal direct sum of lattices is the product
of the theta series. For `E8 ⊕ E8` this is `Θ = E₄²`.

At the level of coefficients this is pure counting, and it holds for *any* two "norm maps"
`Q₁ : V₁ → ℕ`, `Q₂ : V₂ → ℕ` with finite fibres (for a positive definite integral lattice,
`Q(v) = ‖v‖²/2` has finite fibres):

  `r_{Q₁ ⊕ Q₂}(n) = ∑_{a + b = n} r_{Q₁}(a) · r_{Q₂}(b)`,

i.e. the **Cauchy product** — multiplication in Ring A (`PowerSeries`). This settles ledger B9:
"direct sum" and "tensor product" of DNAs are the *same* operation on coefficients (Cauchy
convolution); they differ only in how the state is embedded.
-/

open PowerSeries Finset

namespace Fugue

variable {V₁ V₂ : Type*}

/-- Number of vectors of norm `n`. -/
noncomputable def reprCount (Q : V₁ → ℕ) (n : ℕ) : ℕ := Nat.card {v // Q v = n}

/-- The theta series `∑ r_Q(n) qⁿ` as a formal power series (Ring A). -/
noncomputable def theta (Q : V₁ → ℕ) : PowerSeries ℕ := PowerSeries.mk (reprCount Q)

/-- The orthogonal direct sum of two norm maps. -/
def directSum (Q₁ : V₁ → ℕ) (Q₂ : V₂ → ℕ) : V₁ × V₂ → ℕ := fun p => Q₁ p.1 + Q₂ p.2

/-- The fibre of the direct sum over `n`, decomposed by how `n` splits. -/
def fibreEquiv (Q₁ : V₁ → ℕ) (Q₂ : V₂ → ℕ) (n : ℕ) :
    {p // directSum Q₁ Q₂ p = n} ≃
      Σ ab : antidiagonal n, {v // Q₁ v = ab.1.1} × {w // Q₂ w = ab.1.2} where
  toFun p := ⟨⟨(Q₁ p.1.1, Q₂ p.1.2), mem_antidiagonal.mpr p.2⟩, ⟨p.1.1, rfl⟩, ⟨p.1.2, rfl⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by
    have h := mem_antidiagonal.mp x.1.2
    simp only [directSum, x.2.1.2, x.2.2.2, h]⟩
  left_inv p := rfl
  right_inv := by
    rintro ⟨⟨⟨a, b⟩, hab⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩
    simp only at hv hw
    subst hv hw
    rfl

/-- **Coefficient form of `Θ_{L⊕M} = Θ_L Θ_M`.** -/
theorem reprCount_directSum (Q₁ : V₁ → ℕ) (Q₂ : V₂ → ℕ)
    (h₁ : ∀ n, Finite {v // Q₁ v = n}) (h₂ : ∀ n, Finite {w // Q₂ w = n}) (n : ℕ) :
    reprCount (directSum Q₁ Q₂) n =
      ∑ ab ∈ antidiagonal n, reprCount Q₁ ab.1 * reprCount Q₂ ab.2 := by
  unfold reprCount
  rw [Nat.card_congr (fibreEquiv Q₁ Q₂ n), Nat.card_sigma]
  rw [← Finset.sum_coe_sort (antidiagonal n)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Nat.card_prod]

/-- **`Θ_{L ⊕ M} = Θ_L · Θ_M`** in Ring A. -/
theorem theta_directSum (Q₁ : V₁ → ℕ) (Q₂ : V₂ → ℕ)
    (h₁ : ∀ n, Finite {v // Q₁ v = n}) (h₂ : ∀ n, Finite {w // Q₂ w = n}) :
    theta (directSum Q₁ Q₂) = theta Q₁ * theta Q₂ := by
  ext n
  rw [theta, coeff_mk, reprCount_directSum Q₁ Q₂ h₁ h₂, coeff_mul]
  simp [theta]

/-! ### Example: sums of squares -/

/-- `x ↦ x²` on `ℤ`, as a norm map. -/
def sq : ℤ → ℕ := fun x => x.natAbs ^ 2

theorem finite_fibre_sq (n : ℕ) : Finite {x : ℤ // sq x = n} := by
  apply Set.Finite.to_subtype (s := {x : ℤ | sq x = n})
  refine (Set.finite_Icc (-(n : ℤ)) n).subset fun x hx => ?_
  simp only [Set.mem_ofPred_eq, sq] at hx
  simp only [Set.mem_Icc]
  have h1 : x.natAbs ≤ n := by
    rw [← hx]; nlinarith [Nat.zero_le x.natAbs]
  constructor <;> omega

/-- `r₂(n) = ∑_{a+b=n} r₁(a) r₁(b)`: the two-squares counts are the Cauchy square of the
one-square counts (`ϑ(q)² = ∑ r₂(n) qⁿ`). -/
theorem theta_two_squares :
    theta (directSum sq sq) = theta sq * theta sq :=
  theta_directSum sq sq finite_fibre_sq finite_fibre_sq

end Fugue
