import Mathlib
import Fugue.Ramanujan

/-!
# Hecke's theorem for `E₄`: modularity ⟹ the functional equation of `ζ(s) ζ(s - 3)`

Hecke's converse-direction theorem in its simplest instance. The normalised Eisenstein series
`E₄ = 1 + 240 ∑ σ₃(n) qⁿ` (Mathlib's `ModularForm.E₄ : ModularForm 𝒮ℒ 4`; classically also the
theta series of the `E₈` lattice — that identification is *not* formalised here) satisfies
`E₄(-1/τ) = τ⁴ E₄(τ)`. Restricted to the imaginary axis this says that `F(y) = E₄(iy)` obeys

  `F(1/y) = y⁴ F(y)`,  `F(y) - 1 = O(y^r)` at `∞` for every `r`,

i.e. `(F, F)` is a weak FE-pair of weight `4` and root number `1` in the sense of
`Mathlib.NumberTheory.LSeries.AbstractFuncEq`. The abstract Mellin machinery then produces a
meromorphic `Λ` with

* `heckeE4_functional_equation` : `Λ (4 - s) = Λ s` for **all** `s : ℂ`;
* `heckeE4_differentiableAt`    : `Λ` is holomorphic away from `s = 0` and `s = 4`
  (`heckeE4_residue_four`, `heckeE4_residue_zero`: simple poles with residues `1` and `-1`);
* `heckeE4_eq` : for `4 < re s`,
  `Λ s = 240 (2π)^{-s} Γ(s) ζ(s) ζ(s - 3)`,
  because `Λ s = ∫₀^∞ y^{s-1} (E₄(iy) - 1) dy = 240 ∑ σ₃(n) ∫₀^∞ y^{s-1} e^{-2πny} dy` and
  `∑ σ₃(n) n^{-s} = ζ(s) ζ(s - 3)` (`σ₃ = ζ ⋆ Id³`, Dirichlet convolution);
* `heckeE4_eq_of_re_neg` : the reflected formula for `re s < 0`.

So the completed product `240 (2π)^{-s} Γ(s) ζ(s) ζ(s-3)` continues meromorphically to `ℂ` and is
symmetric under `s ↔ 4 - s`: the symmetry is *derived* from the modularity of `E₄`, not from the
functional equation of `ζ`.

**Ledger D3 (the corpus' own insight).** A functional equation alone says nothing about where the
zeros are. `Λ` here has exactly the same shape of symmetry as the completed Riemann zeta function,
yet (by analytic continuation of the identity below) its zeros include the nontrivial zeros of
`ζ(s)`, in `0 < re s < 1`, *and* those of `ζ(s - 3)`, in `3 < re s < 4` (on `re s = 1/2` and
`re s = 7/2` under RH) — never on the symmetry line `re s = 2`. The reflection `s ↦ 4 - s` merely
swaps the two families. Symmetry constrains zeros only to come in reflected pairs; any statement
locating them needs input beyond the functional equation. (Only the statements listed above are
formalised; this paragraph is commentary.)

Conventions: `F t = E₄ (ofComplex (I * t))`, which equals `E₄ ⟨I * t, _⟩` for `t > 0` (`F_eq`);
values at `t ≤ 0` are irrelevant (all Mellin integrals are over `Ioi 0`).
-/

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex ModularForm ModularGroup CongruenceSubgroup Filter Asymptotics Set
open scoped MatrixGroups Real

namespace Fugue.HeckeE4

/-- `F y = E₄(iy)` on the positive imaginary axis. -/
noncomputable def F (t : ℝ) : ℂ := E₄ (ofComplex (I * t))

/-- For `t > 0`, `F t` is `E₄` at the point `it ∈ ℍ`. -/
theorem F_eq (t : ℝ) (ht : 0 < t) : F t = E₄ ⟨I * t, by simpa using ht⟩ := by
  rw [F, ofComplex_apply_of_im_pos]

/-- The constant term of `E₄` at `i∞` is `1`. -/
theorem valueAtInfty_E₄ : valueAtInfty (E₄ : ℍ → ℂ) = 1 :=
  (EisensteinSeries.tendsto_E_atImInfty (k := 4)).limUnder_eq

/-- **The `S`-transformation on the imaginary axis:** `E₄(i/x) = x⁴ E₄(ix)`. -/
theorem F_feq (x : ℝ) (hx : 0 < x) : F (1 / x) = ((1 : ℂ) * ↑(x ^ (4 : ℝ))) • F x := by
  have : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) Γ(1) 4 := Gamma_one_coe_eq_SL ▸ inferInstance
  have h := SlashInvariantForm.slash_action_eqn_SL'' E₄ (mem_Gamma_one S) ⟨I * x, by simpa using hx⟩
  rw [denom_S] at h
  have hS : S • (⟨I * x, by simpa using hx⟩ : ℍ) = ⟨I * ↑(1 / x), by simpa using hx⟩ := by
    apply UpperHalfPlane.ext
    rw [modular_S_smul]
    show (-(I * (x:ℂ)))⁻¹ = I * ((1 / x : ℝ) : ℂ)
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp
    push_cast
    field_simp
    simp [I_sq]
  rw [hS] at h
  rw [F_eq _ (by positivity), F_eq _ hx, h, smul_eq_mul, one_mul]
  congr 1
  rw [show ((x ^ (4:ℝ) : ℝ) : ℂ) = (x : ℂ) ^ (4:ℕ) by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; push_cast; rfl]
  rw [mul_zpow]; norm_num

/-- Rapid decay: `E₄(iy) - 1 = O(y^r)` as `y → ∞`, for every `r`. -/
theorem F_top (r : ℝ) : (fun t => F t - 1) =O[atTop] (· ^ r) := by
  have := (weakFEPair (k := 4) (by norm_num) E₄).hf_top r
  simpa [valueAtInfty_E₄, F] using this

/-- The weak FE-pair `(F, F)` of weight `4`, root number `1`, constant terms `1`. -/
noncomputable def P : WeakFEPair ℂ where
  f := F
  g := F
  k := 4
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (weakFEPair (k := 4) (by norm_num) E₄).hf_int
  hg_int := (weakFEPair (k := 4) (by norm_num) E₄).hf_int
  hk := by norm_num
  hε := one_ne_zero
  h_feq := F_feq
  hf_top := F_top
  hg_top := F_top

/-- The pair is self-dual. -/
theorem P_symm : P.symm = P := by
  simp only [WeakFEPair.symm, P, inv_one]

/-- The completed `L`-function of `E₄`. -/
noncomputable abbrev Λ : ℂ → ℂ := P.Λ

/-- **Functional equation** `Λ(4 - s) = Λ(s)`. -/
theorem heckeE4_functional_equation (s : ℂ) : Λ (4 - s) = Λ s := by
  have h := P.functional_equation s
  have hk : ((P.k : ℝ) : ℂ) = 4 := by simp [P]
  have hε : P.ε = 1 := rfl
  rw [P_symm, hk, hε, one_smul] at h
  exact h

/-- `Λ` is holomorphic on `ℂ ∖ {0, 4}`. -/
theorem heckeE4_differentiableAt {s : ℂ} (hs0 : s ≠ 0) (hs4 : s ≠ 4) :
    DifferentiableAt ℂ Λ s :=
  P.differentiableAt_Λ (Or.inl hs0) (Or.inl (by simpa [P] using hs4))

/-- Simple pole at `s = 4` with residue `1`. -/
theorem heckeE4_residue_four :
    Tendsto (fun s : ℂ ↦ (s - 4) * Λ s) (nhdsWithin 4 {4}ᶜ) (nhds 1) := by
  have h := P.Λ_residue_k
  have hk : ((P.k : ℝ) : ℂ) = 4 := by simp [P]
  have hε : P.ε = 1 := rfl
  have hg : P.g₀ = 1 := rfl
  rw [hk, hε, hg, one_smul] at h
  simpa only [smul_eq_mul] using h

/-- Simple pole at `s = 0` with residue `-1`. -/
theorem heckeE4_residue_zero :
    Tendsto (fun s : ℂ ↦ s * Λ s) (nhdsWithin 0 {0}ᶜ) (nhds (-1)) := by
  have h := P.Λ_residue_zero
  have hf : P.f₀ = 1 := rfl
  rw [hf] at h
  simpa only [smul_eq_mul] using h

/-- The `q`-expansion on the imaginary axis: `E₄(it) - 1 = ∑_{n ≥ 1} a_n e^{-2πnt}`. -/
theorem hasSum_F_sub_one (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ if ((2 * n : ℕ) : ℝ) = 0 then 0 else
      (PowerSeries.coeff n (qExpansion 1 E₄)) * Real.exp (-π * ((2 * n : ℕ) : ℝ) * t)) (F t - 1) := by
  have := ModularForm.hasSum_qExpansion E₄ one_pos one_mem_strictPeriods_SL (ofComplex (I * t))
  convert! hasSum_ite_sub_hasSum this 0 using 2 with n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
      grind [I_sq]
  · simp [coeff_E₄]


section Identification

open LSeries LSeries.notation
open ArithmeticFunction (natCoe_apply natCoe_mul pow pow_apply zeta_mul_pow_eq_sigma)
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

/-- `∑ n³ n^{-s} = ζ(s - 3)` for `re s > 4`. -/
theorem LSeriesHasSum_pow_three {s : ℂ} (hs : 4 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ 3) s (riemannZeta (s - 3)) := by
  have h := LSeriesHasSum_one (s := s - 3) (by simp; linarith)
  unfold LSeriesHasSum at h ⊢
  convert h using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cpow_sub _ _ this, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, cpow_natCast]
    have : (n : ℂ) ^ s ≠ 0 := by simp [this]
    simp

/-- `σ₃ = ζ ⋆ Id³` as sequences in `ℂ`. -/
theorem convolution_sigma_three :
    (fun n : ℕ ↦ ((ζ n : ℕ) : ℂ)) ⍟ (fun n : ℕ ↦ (n : ℂ) ^ 3) = fun n ↦ ((σ 3 n : ℕ) : ℂ) := by
  have h1 : (fun n : ℕ ↦ ((ζ n : ℕ) : ℂ)) = ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    funext n; rw [natCoe_apply]
  have h2 : (fun n : ℕ ↦ (n : ℂ) ^ 3) = ⇑((pow 3 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    funext n; rw [natCoe_apply, pow_apply]; simp
  rw [h1, h2, ArithmeticFunction.coe_mul, ← natCoe_mul, zeta_mul_pow_eq_sigma]
  funext n; rw [natCoe_apply]

/-- `∑ σ₃(n) n^{-s} = ζ(s) ζ(s - 3)` for `re s > 4`. -/
theorem LSeriesHasSum_sigma_three {s : ℂ} (hs : 4 < s.re) :
    LSeriesHasSum (fun n ↦ ((σ 3 n : ℕ) : ℂ)) s (riemannZeta s * riemannZeta (s - 3)) := by
  rw [← convolution_sigma_three]
  exact (ArithmeticFunction.LSeriesHasSum_zeta (by linarith)).convolution (LSeriesHasSum_pow_three hs)


theorem coeff_E₄_pos {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (qExpansion 1 E₄) = 240 * ((σ 3 n : ℕ) : ℂ) := by
  rw [coeff_E₄]; simp [hn]

/-- Absolute convergence of the Dirichlet series of the `q`-coefficients for `re s > 4`. -/
theorem summable_coeff {s : ℂ} (hs : 4 < s.re) :
    Summable fun n : ℕ ↦ ‖PowerSeries.coeff n (qExpansion 1 E₄)‖ / (((2 * n : ℕ) : ℝ)) ^ s.re := by
  have hL := (LSeriesHasSum_sigma_three hs).summable.norm.mul_left (240 / 2 ^ s.re)
  refine hL.congr fun n => ?_
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (show s.re ≠ 0 by linarith)]
  · simp only [hn, ite_false]
    rw [coeff_E₄_pos hn, norm_mul, Nat.cast_mul, Real.mul_rpow (by norm_num) (by positivity)]
    simp only [Nat.cast_ofNat, Complex.norm_natCast, Complex.norm_ofNat]
    field_simp

/-- Termwise comparison of the Mellin-transformed `q`-series with `L(σ₃, s)`. -/
theorem term_eq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ↑π ^ (-s) * Gamma s * PowerSeries.coeff n (qExpansion 1 E₄) / ((((2 * n : ℕ) : ℝ)) : ℂ) ^ s =
      (240 * (2 * π) ^ (-s) * Gamma s) * term (fun n ↦ ((σ 3 n : ℕ) : ℂ)) s n := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zero_cpow hs0]
  · rw [term_of_ne_zero hn, coeff_E₄_pos hn, Nat.cast_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    have h2 : (2 * (π : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s) := by
      have := mul_cpow_ofReal_nonneg (a := 2) (b := π) (by norm_num) Real.pi_pos.le (-s)
      push_cast at this; exact this
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have h3 : (n : ℂ) ^ s ≠ 0 := by simp [hn']
    have h4 : (2 : ℂ) ^ s ≠ 0 := by simp
    rw [h2, cpow_neg, cpow_neg]
    push_cast
    field_simp

/-- **Identification** for `re s > 4`: `Λ s = 240 (2π)^{-s} Γ(s) ζ(s) ζ(s - 3)`. -/
theorem heckeE4_eq {s : ℂ} (hs : 4 < s.re) :
    Λ s = 240 * (2 * π) ^ (-s) * Gamma s * riemannZeta s * riemannZeta (s - 3) := by
  have hs0 : 0 < s.re := by linarith
  have hM := (P.hasMellin (s := s) (by simpa [P] using hs)).2
  have key := hasSum_mellin_pi_mul₀ (a := fun n => PowerSeries.coeff n (qExpansion 1 E₄))
    (p := fun n : ℕ => ((2 * n : ℕ) : ℝ)) (F := fun t => F t - 1) (s := s)
    (fun n => Nat.cast_nonneg _) hs0 (fun t ht => hasSum_F_sub_one t ht) (summable_coeff hs)
  have hL := ((LSeriesHasSum_sigma_three hs).mul_left (240 * (2 * π) ^ (-s) * Gamma s))
  simp_rw [term_eq hs0] at key
  have := key.unique hL
  show P.Λ s = _
  rw [← hM, mul_assoc _ (riemannZeta s)]
  exact this

/-- The reflected formula: for `re s < 0`,
`Λ s = 240 (2π)^{-(4-s)} Γ(4-s) ζ(4-s) ζ(1-s)`. -/
theorem heckeE4_eq_of_re_neg {s : ℂ} (hs : s.re < 0) :
    Λ s = 240 * (2 * π) ^ (-(4 - s)) * Gamma (4 - s) * riemannZeta (4 - s) *
      riemannZeta (4 - s - 3) := by
  rw [← heckeE4_eq (by simp; linarith), heckeE4_functional_equation]

end Identification

end Fugue.HeckeE4
