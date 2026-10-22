import Fugue.E8Lattice

/-!
# Interfaces for `Θ_{E8} = E₄` (ledger row A2)

The corpus' foundational identity: the theta series of the E8 lattice is the Eisenstein series
`E₄ = 1 + 240 Σ σ₃(n) qⁿ` (verified there only numerically: 240, 2160, 6720 vectors of norm
2, 4, 6). The classical proof goes through the Jacobi theta functions:

  `Θ_{E8} = (θ₂⁸ + θ₃⁸ + θ₄⁸)/2`  (E8 = D8 ∪ (D8 + ½·𝟙))   and   `(θ₂⁸ + θ₃⁸ + θ₄⁸)/2 = E₄`
  (it is a level-one modular form of weight 4 with constant term 1, and `dim M₄ = 1`).

This file fixes the definitions; `Fugue/ThetaE8Modular.lean` and `Fugue/ThetaE8Lattice.lean`
prove the two halves.
-/

open Complex
open scoped Real

namespace Fugue

/-- `θ₃(τ) = Σ_{n∈ℤ} e^{πi n² τ}` (Mathlib's `jacobiTheta`). -/
noncomputable def θ₃ (τ : ℂ) : ℂ := jacobiTheta τ

/-- `θ₄(τ) = Σ_{n∈ℤ} (−1)ⁿ e^{πi n² τ} = jacobiTheta₂ (1/2) τ`. -/
noncomputable def θ₄ (τ : ℂ) : ℂ := jacobiTheta₂ (1 / 2) τ

/-- `θ₂(τ) = Σ_{n∈ℤ} e^{πi (n+1/2)² τ} = e^{πiτ/4} · jacobiTheta₂ (τ/2) τ`. -/
noncomputable def θ₂ (τ : ℂ) : ℂ := cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- The combination `(θ₂⁸ + θ₃⁸ + θ₄⁸)/2`. -/
noncomputable def thetaCombo (τ : ℂ) : ℂ := (θ₂ τ ^ 8 + θ₃ τ ^ 8 + θ₄ τ ^ 8) / 2

/-- **The theta series of E8**, in Cartan coordinates: `Θ(τ) = Σ_{v ∈ ℤ⁸} e^{πiτ·vᵀAv}`, where
`A` is the E8 Cartan matrix (`Fugue.e8Form v = vᵀAv`, even), i.e. `Σ_v q^{vᵀAv/2}`. -/
noncomputable def thetaE8 (τ : ℂ) : ℂ :=
  ∑' v : Fin 8 → ℤ, cexp (π * I * τ * (e8Form v : ℂ))

end Fugue
