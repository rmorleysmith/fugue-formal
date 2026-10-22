/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# The quasi-Riemann hypothesis

The *quasi-Riemann hypothesis* asks for a zero-free half-plane `Re s > θ` for the Riemann zeta
function with some `θ < 1`. Before 2026 no such `θ` was known: the classical zero-free regions
(de la Vallée Poussin, Vinogradov–Korobov) shrink towards the line `Re s = 1` as `|Im s| → ∞`.
The Riemann hypothesis is the case `θ = 1/2` (and `θ = 1/2` is the best possible, since there
are zeros on the critical line).

OpenAI (October 2026) proved that `ζ(s) ≠ 0` and, more generally, `L(s, χ) ≠ 0` for every
Dirichlet character `χ`, whenever `Re s > 7/8`, with a Lean formalisation checked against
Mathlib.

*References:*
- OpenAI, *A quasi-Riemann hypothesis for Dirichlet L-functions*, October 2026.
  [Lean formalisation](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
- [Wikipedia](https://en.wikipedia.org/wiki/Riemann_hypothesis#Zero-free_regions)
-/

@[expose] public section

namespace QuasiRiemannHypothesis

/-- `ζ` has no zeros in the half-plane `Re s > θ`. -/
def ZeroFreeRight (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- **The quasi-Riemann hypothesis**: `ζ` is zero-free on some half-plane `Re s > θ` with
`θ < 1`. Solved by OpenAI (2026) with `θ = 7/8`. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L29"]
theorem quasi_riemann_hypothesis : ∃ θ < (1 : ℝ), ZeroFreeRight θ := by
  sorry

/-- OpenAI's explicit exponent: `ζ(s) ≠ 0` for `Re s > 7/8`. -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L29"]
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  sorry

/-- **The quasi-generalised Riemann hypothesis for Dirichlet `L`-functions**, with OpenAI's
exponent `7/8`, uniformly in the modulus. (At `s = 1` the trivial character has its pole.) -/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean#L19"]
theorem dirichletL_ne_zero_of_seven_eighths_lt_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

/-- Sanity check: `ZeroFreeRight 1` is the classical theorem of Hadamard and de la Vallée
Poussin (1896). -/
@[category test, AMS 11]
theorem zeroFreeRight_one : ZeroFreeRight 1 := fun _ hs =>
  riemannZeta_ne_zero_of_one_le_re hs.le

/-- Sanity check: no `θ < -2` works, because of the trivial zero `ζ(-2) = 0`. -/
@[category test, AMS 11]
theorem not_zeroFreeRight_of_lt_neg_two {θ : ℝ} (hθ : θ < -2) : ¬ ZeroFreeRight θ := fun h =>
  h (-2) (by simpa using hθ) (by simpa using riemannZeta_neg_two_mul_nat_add_one 0)

/-- The Riemann hypothesis implies the quasi-Riemann hypothesis with `θ = 1/2`. -/
@[category API, AMS 11]
theorem zeroFreeRight_half_of_riemannHypothesis (h : RiemannHypothesis) :
    ZeroFreeRight (1 / 2) := by
  intro s hs hzero
  have hs1 : s ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hzero
  have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : ((-2 * ((n : ℂ) + 1)) : ℂ).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := h s hzero htriv hs1
  linarith

end QuasiRiemannHypothesis
