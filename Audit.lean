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

-- 15. Hecke for all E_k (root number (−1)^{k/2}); E₆'s centre zero = trivial zero ζ(−2) = 0.
#print axioms Fugue.HeckeEk.heckeEk_functional_equation
#print axioms Fugue.HeckeEk.heckeEk_eq
#print axioms Fugue.HeckeEk.heckeEk_eq_of_ne
#print axioms Fugue.HeckeEk.heckeE6_centre_eq_zeta

-- 16. Ramanujan's formula (Rankin–Selberg prototype), C11.
#print axioms Fugue.LSeries_sigma_mul_sigma
#print axioms Fugue.RankinSelberg.sigma_pmul_sigma_mul_sqPow
#print axioms Fugue.RankinSelberg.LSeries_card_divisors_sq

-- 17. (θ₂⁸ + θ₃⁸ + θ₄⁸)/2 = E₄ (half of Θ_E8 = E₄).
#print axioms Fugue.thetaCombo_eq_E₄
#print axioms Fugue.thetaE8_eq_thetaCombo
#print axioms Fugue.thetaE8_eq_E₄
#print axioms Fugue.reprCount_e8
#print axioms Fugue.reprCount_e8_three
example : Fugue.reprCount Fugue.e8Norm 2 = 2160 := Fugue.reprCount_e8_two

-- 18. Heterotic E8⊕E8: Θ = E₈, 480σ₇(n) vectors of norm 2n.
#print axioms Fugue.thetaE8_sq_eq_E₈
#print axioms Fugue.reprCount_e8e8
example : Fugue.reprCount (Fugue.directSum Fugue.e8Norm Fugue.e8Norm) 1 = 480 := Fugue.reprCount_e8e8_one

-- 19. Witt: D16⁺ and E8⊕E8 are isospectral (same theta series = E₈).
#print axioms Fugue.thetaD16_eq_E₈
#print axioms Fugue.thetaD16_eq_thetaE8_sq

-- 20. Ramanujan's L-function of Δ = η²⁴: entire, Λ(12−s) = Λ(s); τ(3) = 252.
#print axioms Fugue.RamanujanL.ramanujanΛ_functional_equation
#print axioms Fugue.RamanujanL.ramanujanΛ_differentiable
#print axioms Fugue.RamanujanL.ramanujanΛ_eq
#print axioms Fugue.RamanujanL.τ_three

-- 21. Primon gas: bosons ζ(s), fermions ζ(s)/ζ(2s), (−1)^F = μ, Witten index 1/ζ(s).
#print axioms Fugue.PrimonGas.fermionic_partition
#print axioms Fugue.PrimonGas.witten_index
#print axioms Fugue.PrimonGas.fockEquiv

-- 22. Epstein zeta functions of E8, E8⊕E8, ℤ², hexagonal lattice.
#print axioms Fugue.Epstein.epstein_E8
#print axioms Fugue.Epstein.epstein_E8E8
#print axioms Fugue.Epstein.epstein_square
#print axioms Fugue.Epstein.epstein_hexagonal

-- 23. Golden-ratio primes: p = x² + xy − y² ⇔ p = 5 or p ≡ ±1 (mod 5); Cassini.
#print axioms Fugue.golden_prime_iff
#print axioms Fugue.Golden.prime_of_inert
#print axioms Fugue.Golden.fib_cassini

-- 24. Partitions: Euler's identity and recurrence, Jacobi's identity, Ramanujan p(5n+4) ≡ 0 mod 5.
#print axioms Fugue.Partitions.partitionSeries_mul_pentagonalSeries
#print axioms Fugue.Partitions.partition_recurrence
#print axioms Fugue.Partitions.pentagonalSeries_pow_three
#print axioms Fugue.Partitions.ramanujan_congruence_five
example : (List.range 11).map (fun n => Fintype.card (Nat.Partition n)) =
    [1,1,2,3,5,7,11,15,22,30,42] := Fugue.Partitions.partition_values

-- 25. Ramanujan's τ(n) ≡ σ₁₁(n) (mod 691); τ integral via Δ = q∏(1−qⁿ)²⁴.
#print axioms Fugue.tau_congr_691
#print axioms Fugue.Tau691.qExpansion_discriminant_eq
example : (691 : ℤ) ∣ Fugue.Tau691.tauZ 2 - ArithmeticFunction.sigma 11 2 := Fugue.tau_sub_sigma_dvd 2

-- 26. Direct sum: E8 ⊕ E8 Gram = block-diagonal, det 1, even, symmetric.
#print axioms Fugue.e8e8_det
#print axioms Fugue.e8e8_diag

-- 27. Composing per-prime Euler factors (zeta_compose.py, fig 32): ∏_{p∈S} eulerFactor p = indicator
--     of S-smooth numbers; all-ones row on the window n ≤ N; Mathlib's analytic Euler product.
#print axioms Fugue.EulerCompose.prod_eulerFactor
#print axioms Fugue.EulerCompose.smooth_mul_smooth
#print axioms Fugue.EulerCompose.prod_eulerFactor_apply_of_le
#print axioms Fugue.EulerCompose.prod_eulerFactor_eq_zeta_of_le
#print axioms Fugue.EulerCompose.smooth_tendsto_zeta
#print axioms Fugue.EulerCompose.zeta_eulerProduct
-- non-vacuity: 6 = 2·3 is {2,3}-smooth, 5 and 12·5 are not; the Euler factor of 2 is 1 at 8 and 0 at 6.
example : (∏ p ∈ ({2, 3} : Finset ℕ), Fugue.EulerCompose.eulerFactor p) 6 = 1 := by
  rw [Fugue.EulerCompose.prod_eulerFactor_apply]; decide +kernel
example : (∏ p ∈ ({2, 3} : Finset ℕ), Fugue.EulerCompose.eulerFactor p) 5 = 0 := by
  rw [Fugue.EulerCompose.prod_eulerFactor_apply]; decide +kernel
example : Fugue.EulerCompose.eulerFactor 2 8 = 1 := by
  simpa using Fugue.EulerCompose.eulerFactor_prime_pow Nat.prime_two 3
example : Fugue.EulerCompose.eulerFactor 2 6 = 0 := by
  rw [Fugue.EulerCompose.eulerFactor, Fugue.EulerCompose.smooth_apply]; decide +kernel

-- 28. Bianconi's entropic action, warm-up case: −ln det(1 + α u uᵀ) = −ln(1 + α|u|²); low-energy limit
--     is massless Klein–Gordon; the emergent cosmological constant Σ(λ−1−ln λ) ≥ 0, = 0 iff vacuum.
#print axioms Fugue.EntropicAction.warmup_lagrangian
#print axioms Fugue.EntropicAction.warmup_linearisation
#print axioms Fugue.EntropicAction.cosmological_nonneg
#print axioms Fugue.EntropicAction.cosmological_eq_zero_iff
example : Fugue.EntropicAction.lam 1 = 0 := by simp [Fugue.EntropicAction.lam]
