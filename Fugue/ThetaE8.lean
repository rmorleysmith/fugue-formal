import Fugue.ThetaE8Modular
import Fugue.ThetaE8Lattice

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

end Fugue
