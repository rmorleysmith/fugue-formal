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

-- 5. Chapter 3 (Dirichlet L-functions).
#print axioms zeroFree_iff_differentiableOn_negLogDeriv
#print axioms zeroFreeRightL_iff
#print axioms LSeries_twist_vonMangoldt_eq_negLogDerivL
#print axioms twistedVonMangoldt_continuation_of_openAI
#print axioms openAIStatement_of_dirichlet
-- Non-vacuity: every Dirichlet L-function is zero-free right of 1 (Mathlib), so the
-- characterisation has content at θ = 1 for every χ.
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ZeroFreeRightL χ 1 :=
  fun _ hs hpole => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (by tauto) hs.le

-- 6. Theta series of direct sums (C13, B9).
#print axioms Fugue.reprCount_directSum
#print axioms Fugue.theta_directSum
-- Non-vacuity: r₁(1) = 2 (x = ±1), so the theta series are not trivially zero.
example : Fugue.reprCount Fugue.sq 1 = 2 := by
  have : {x : ℤ | Fugue.sq x = 1} = {1, -1} := by
    ext x; simp only [Fugue.sq, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h; have : x.natAbs = 1 := by nlinarith [Nat.zero_le x.natAbs]
      omega
    · rintro (rfl | rfl) <;> rfl
  rw [Fugue.reprCount, ← Set.coe_ofPred, this, Nat.card_coe_set_eq, Set.ncard_pair (by decide)]

-- 7. Jacobi's two-square theorem (C6).
#print axioms Fugue.card_sq_add_sq
-- Non-vacuity: concrete counts r₂(5) = 8, r₂(3) = 0 follow (examples inside the file).

-- 8. The E8 lattice (A1).
#print axioms Fugue.e8Form_even
#print axioms Fugue.e8Form_pos
-- Non-vacuity: the root e₀ has norm 2 (so the form is not identically zero and the
-- positivity statement is not about an empty set of vectors).
example : Fugue.e8Form (Pi.single 0 1) = 2 := by rw [Fugue.e8Form_eq]; simp
#print axioms Fugue.e8_finite_fibre
#print axioms Fugue.theta_e8_sum_e8
-- Non-vacuity: the constant term of Θ_{E8} is 1 (only the zero vector has norm 0).
example : Fugue.reprCount Fugue.e8Norm 0 = 1 := by
  have : {x : Fin 8 → ℤ | Fugue.e8Norm x = 0} = {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Fugue.e8Norm_eq_iff]
    constructor
    · intro h; by_contra hx; have := Fugue.e8Form_pos hx; omega
    · rintro rfl; simp [Fugue.e8Form]
  rw [Fugue.reprCount, ← Set.coe_ofPred, this, Nat.card_coe_set_eq, Set.ncard_singleton]

-- 9. L(1, χ₋₄) = π/4 (D6).
#print axioms Fugue.LFunction_chi4_one
-- Non-vacuity: χ₄' is not the trivial character (so this is not ζ's pole value).
example : Fugue.χ₄' ≠ 1 := Fugue.χ₄'_ne_one

-- 10. Ramanujan's σ₇ = σ₃ + 120 σ₃⋆σ₃ via E₄² = E₈ (the two rings meet).
#print axioms Fugue.E₄sq_eq
#print axioms Fugue.sigma_seven_eq
-- Non-vacuity: at n = 2: σ₇(2) = 129 = σ₃(2) + 120·σ₃(1)² = 9 + 120.
example : ArithmeticFunction.sigma 7 2 = 129 := by decide
example : ArithmeticFunction.sigma 7 2 =
    ArithmeticFunction.sigma 3 2 + 120 * ∑ i ∈ Finset.range 1,
      ArithmeticFunction.sigma 3 (i + 1) * ArithmeticFunction.sigma 3 (2 - 1 - i) :=
  Fugue.sigma_seven_eq 2 (by norm_num)

-- 11. C12 refuted: a₂(Δ·E₄) = 216 ≠ a₂(Δ)·a₂(E₄); Ramanujan τ(2) = -24.
#print axioms Fugue.tau_two
#print axioms Fugue.discriminant_mul_E₄_not_multiplicative_eigenvalue

-- 12. D9 sieve, C15 eta quotients.
#print axioms Fugue.sieve_2357
#print axioms Fugue.etaQuotient_ne_zero

-- 13. Hecke's theorem for E₄: modularity ⇒ continuation + functional equation of ζ(s)ζ(s−3).
#print axioms Fugue.HeckeE4.heckeE4_functional_equation
#print axioms Fugue.HeckeE4.heckeE4_eq
#print axioms Fugue.HeckeE4.heckeE4_residue_four

-- 14. Eisenstein integers: #{a² − ab + b² = n} = 6 Σ_{d∣n} χ₋₃(d) (C7), ζ_{ℚ(√−3)} coefficients.
#print axioms Fugue.card_hexagonal
