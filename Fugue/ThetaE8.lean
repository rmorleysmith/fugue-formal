import Fugue.ThetaE8Modular
import Fugue.ThetaE8Lattice
import Fugue.ThetaE8Count

/-!
# `Θ_{E8} = E₄` (ledger row A2)

The theta series of the E8 lattice equals the Eisenstein series `E₄`. Combined with
`Fugue/HeckeE4.lean` this closes the chain **E8 lattice → E₄ → functional equation of
`ζ(s)ζ(s−3)`** — the corpus' motivating picture, machine-checked.
-/

namespace Fugue

/-- **`Θ_{E8} = E₄`.** -/
theorem thetaE8_eq_E₄ (τ : UpperHalfPlane) : thetaE8 τ = ModularForm.E₄ τ := by
  rw [thetaE8_eq_thetaCombo τ.im_pos, thetaCombo_eq_E₄]

/-! ### The corpus' numbers, as theorems -/

/-- **The number of E8 vectors of norm `2n` is `240 σ₃(n)`** (ledger A2: 240, 2160, 6720 …). -/
theorem reprCount_e8 (n : ℕ) (hn : 0 < n) :
    reprCount e8Norm n = 240 * ArithmeticFunction.sigma 3 n :=
  reprCount_e8_of_theta' thetaE8_eq_E₄ n hn

theorem reprCount_e8_one : reprCount e8Norm 1 = 240 := reprCount_e8_one_of_theta thetaE8_eq_E₄
theorem reprCount_e8_two : reprCount e8Norm 2 = 2160 := reprCount_e8_two_of_theta thetaE8_eq_E₄
theorem reprCount_e8_three : reprCount e8Norm 3 = 6720 := reprCount_e8_three_of_theta thetaE8_eq_E₄

end Fugue
