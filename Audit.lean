import QuasiRH
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
