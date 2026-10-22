import QuasiRH
import Fugue
open QuasiRH
-- 1. Every headline theorem rests only on Lean's three standard axioms (no `sorryAx`).
#print axioms zeroFreeRight_one
#print axioms zeroFreeRight_half_of_RH
#print axioms quasiRiemannHypothesis_of_openAI
#print axioms vonMangoldt_LSeries_continuation
#print axioms vonMangoldt_LSeries_continuation_of_openAI
#print axioms meromorphicOrderAt_negLogDerivZeta
#print axioms zeroFreeRight_iff_differentiableOn
#print axioms openAIStatement_iff_differentiableOn
#print axioms quasiRiemannHypothesis_iff

-- 2. Non-vacuity checks: the objects are what we think they are.
-- `region θ` is nonempty for every θ (it contains θ+2 shifted off the real point 1).
example (θ : ℝ) : ((θ + 2 : ℝ) : ℂ) + Complex.I ∈ region θ := by
  refine ⟨by simp, fun h => ?_⟩
  have := congrArg Complex.im h; simp at this
-- The characterisation is genuinely about ζ: it is *known* to hold at θ = 1 …
example : DifferentiableOn ℂ negLogDerivZeta (region 1) :=
  (zeroFreeRight_iff_differentiableOn 1).mp zeroFreeRight_one
-- … and is *false* far to the left, because ζ(-2) = 0 is a (trivial) zero.
example : ¬ DifferentiableOn ℂ negLogDerivZeta (region (-3)) := by
  rw [← zeroFreeRight_iff_differentiableOn]
  intro h
  exact h (-2) (by norm_num) (by simpa using riemannZeta_neg_two_mul_nat_add_one 0)

-- 3. Chapters 3-5 (continuation, reflection, Ingham easy direction).
#print axioms zeroFreeRight_of_eqOn
#print axioms isPreconnected_region
#print axioms riemannHypothesis_iff_zeroFreeRight_half
#print axioms LSeries_vonMangoldt_eq_mellin
#print axioms zeroFreeRight_of_psiError
#print axioms riemannHypothesis_of_psiError
#print axioms psiError_one

-- Non-vacuity of `PsiError`: satisfiable at θ = 1 (Chebyshev) …
example : PsiError 1 := psiError_one
-- … and false at θ = -3 (it would kill the trivial zero ζ(-2) = 0).
example : ¬ PsiError (-3) := fun h =>
  zeroFreeRight_of_psiError h (-2) (by norm_num) (by simpa using riemannZeta_neg_two_mul_nat_add_one 0)

-- 4. The Fugue library (corpus-derived theorems).
#print axioms Fugue.cauchy_ne_dirichlet
#print axioms Fugue.ArithmeticFunction.not_isPrincipalIdealRing
#print axioms Fugue.not_ringEquiv_powerSeries
#print axioms Fugue.sigma_three_ne_zeta_pow_four
#print axioms Fugue.pmul_log_mul
#print axioms Fugue.eq_zero_at_rho
#print axioms Fugue.eq_zero_at_I
#print axioms Fugue.E₄_rho
#print axioms Fugue.E₄_I_ne_zero
#print axioms Fugue.E₆_rho_ne_zero
#print axioms Fugue.eq_zero_of_isLocalMin_norm
#print axioms Fugue.couplingMatrix_posSemidef_iff
#print axioms Fugue.couplingMatrix_posDef_iff
#print axioms Fugue.sum_exp_eq
#print axioms Fugue.totient_reveals_factors
#print axioms Fugue.pos_injective_odd

-- Non-vacuity: the hypotheses of the vanishing theorems are not empty conditions —
-- E₄ is a genuine nonzero form (it is nonzero at i), so `E₄ ρ = 0` is not `0 = 0` for a zero form.
example : (ModularForm.E₄ : UpperHalfPlane → ℂ) ≠ 0 := fun h =>
  Fugue.E₄_I_ne_zero (by simpa using congrFun h UpperHalfPlane.I)
-- The coupling matrix is PSD but not PD at the boundary κ = 1 (the E5 gap is real).
example : (Fugue.couplingMatrix 1 1 1).PosSemidef ∧ ¬ (Fugue.couplingMatrix 1 1 1).PosDef :=
  ⟨(Fugue.couplingMatrix_posSemidef_iff one_pos one_pos 1).mpr (by simp),
   fun h => by simpa using (Fugue.couplingMatrix_posDef_iff one_pos one_pos 1).mp h⟩
-- `pos` is NOT injective on all naturals (pos 6 = pos 3), so the oddness hypothesis is needed.
example : Fugue.pos 6 = Fugue.pos 3 := by
  have := Fugue.pos_two_mul (x := 3) (by norm_num); norm_num at this; exact this
-- The Miller identity on an actual semiprime: 15 = 3·5, φ(15) = 8, 3 + 5 = 15 + 1 - 8.
example : Nat.totient 15 = 8 := by decide
