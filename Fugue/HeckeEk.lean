import Mathlib
import Fugue.HeckeE4

/-!
# Hecke's theorem for every level-one Eisenstein series `E_k`

Generalisation of `Fugue.HeckeE4` to the normalised Eisenstein series
`E_k = 1 - (2k / B_k) ∑ σ_{k-1}(n) qⁿ` (Mathlib's `EisensteinSeries.E hk : ModularForm 𝒮ℒ k`),
for `k ≥ 3` even (so `k ≥ 4`). Restricted to the imaginary axis, `E_k(-1/τ) = τ^k E_k(τ)` reads

  `F(1/y) = i^k y^k F(y) = (-1)^{k/2} y^k F(y)`,  `F(y) = E_k(iy)`,

so `(F, F)` is a weak FE-pair of weight `k`, root number `ε_k = (-1)^{k/2}` and constant terms `1`.
Since `ε_k⁻¹ = ε_k` and `f = g`, the pair is self-dual (`P_symm`), and with `Λ_k := P.Λ`:

* `heckeEk_functional_equation` : `Λ_k (k - s) = (-1)^{k/2} • Λ_k s` for all `s`;
* `heckeEk_differentiableAt`, `heckeEk_residue_k`, `heckeEk_residue_zero` : holomorphic off
  `{0, k}`, simple poles with residues `(-1)^{k/2}` at `k` and `-1` at `0`;
* `heckeEk_eq` : for `k < re s`,
  `Λ_k s = -(2k / B_k) (2π)^{-s} Γ(s) ζ(s) ζ(s - k + 1)`
  (`q`-coefficients from `EisensteinSeries.E_qExpansion_coeff`, `σ_{k-1} = ζ ⋆ Id^{k-1}`);
* `heckeEk_eq_of_ne` : the same identity for every `s ∉ {1, k, 0, -1, -2, …}`, by the identity
  theorem (analytic continuation);
* `heckeEk_centre_eq_zero` : if `k ≡ 2 (mod 4)` then `ε_k = -1` and `Λ_k (k/2) = 0`.

Corollaries: `Λ_four` (at `k = 4` the construction *is* `Fugue.HeckeE4.Λ`),
`heckeE4_functional_equation'`, `heckeE4_eq'` (constant `-(8 / B₄) = 240`); for `E₆`
(constant `-(12 / B₆) = -504`, root number `-1`): `heckeE6_functional_equation`
(`Λ₆(6 - s) = -Λ₆(s)`), `heckeE6_eq`, `heckeE6_centre` (`Λ₆(3) = 0`), and
`heckeE6_centre_eq_zeta`: `Λ₆(3) = -504 (2π)^{-3} Γ(3) ζ(3) ζ(-2)` with `ζ(-2) = 0` — the zero
forced by the sign of the functional equation is the trivial zero `ζ(-2) = 0`.
-/

set_option autoImplicit false

open UpperHalfPlane hiding I
open Complex ModularForm ModularGroup CongruenceSubgroup Filter Asymptotics Set
open EisensteinSeries
open scoped MatrixGroups Real

namespace Fugue.HeckeEk

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

/-- `F y = E_k(iy)` on the positive imaginary axis. -/
noncomputable def F (t : ℝ) : ℂ := E hk (ofComplex (I * t))

theorem F_eq (t : ℝ) (ht : 0 < t) : F hk t = E hk ⟨I * t, by simpa using ht⟩ := by
  rw [F, ofComplex_apply_of_im_pos]

/-- The root number `ε_k = (-1)^{k/2} = i^k`. -/
noncomputable def ε (k : ℕ) : ℂ := (-1) ^ (k / 2)

theorem ε_ne_zero : ε k ≠ 0 := pow_ne_zero _ (by norm_num)

theorem ε_inv : (ε k)⁻¹ = ε k := by
  rw [ε, ← inv_pow, inv_neg, inv_one]

include hk2 in
theorem I_pow_eq_ε : I ^ k = ε k := by
  rw [ε, ← Nat.two_mul_div_two_of_even hk2, pow_mul, I_sq, Nat.two_mul_div_two_of_even hk2]

include hk2 in
/-- **The `S`-transformation on the imaginary axis:** `E_k(i/x) = (-1)^{k/2} x^k E_k(ix)`. -/
theorem F_feq (x : ℝ) (hx : 0 < x) :
    F hk (1 / x) = (ε k * ↑(x ^ (k : ℝ))) • F hk x := by
  have : SlashInvariantFormClass (ModularForm 𝒮ℒ k) Γ(1) k := Gamma_one_coe_eq_SL ▸ inferInstance
  have h := SlashInvariantForm.slash_action_eqn_SL'' (E hk) (mem_Gamma_one S)
    ⟨I * x, by simpa using hx⟩
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
  rw [F_eq _ _ (by positivity), F_eq _ _ hx, h, smul_eq_mul]
  congr 1
  rw [Real.rpow_natCast, ofReal_pow, ← I_pow_eq_ε hk2, ← mul_pow]
  simp

include hk2 in
theorem valueAtInfty_E : valueAtInfty (E hk : ℍ → ℂ) = 1 :=
  (tendsto_E_atImInfty hk hk2).limUnder_eq

include hk2 in
/-- Rapid decay: `E_k(iy) - 1 = O(y^r)` as `y → ∞`, for every `r`. -/
theorem F_top (r : ℝ) : (fun t => F hk t - 1) =O[atTop] (· ^ r) := by
  have := (weakFEPair (k := k) (by omega) (E hk)).hf_top r
  simpa [valueAtInfty_E hk hk2, F] using this

/-- The weak FE-pair `(F, F)` of weight `k`, root number `(-1)^{k/2}`, constant terms `1`. -/
noncomputable def P : WeakFEPair ℂ where
  f := F hk
  g := F hk
  k := k
  ε := ε k
  f₀ := 1
  g₀ := 1
  hf_int := (weakFEPair (k := k) (by omega) (E hk)).hf_int
  hg_int := (weakFEPair (k := k) (by omega) (E hk)).hf_int
  hk := by simp; omega
  hε := ε_ne_zero
  h_feq := F_feq hk hk2
  hf_top := F_top hk hk2
  hg_top := F_top hk hk2

/-- The pair is self-dual (since `ε⁻¹ = ε`). -/
theorem P_symm : (P hk hk2).symm = P hk hk2 := by
  simp only [WeakFEPair.symm, P, ε_inv]


/-- The completed `L`-function of `E_k`. -/
noncomputable abbrev Λ : ℂ → ℂ := (P hk hk2).Λ

/-- **Functional equation** `Λ(k - s) = (-1)^{k/2} Λ(s)`. -/
theorem heckeEk_functional_equation (s : ℂ) :
    Λ hk hk2 (k - s) = (-1 : ℂ) ^ (k / 2) • Λ hk hk2 s := by
  have h := (P hk hk2).functional_equation s
  have hk' : (((P hk hk2).k : ℝ) : ℂ) = k := by simp [P]
  rw [P_symm, hk'] at h
  exact h

/-- `Λ` is holomorphic on `ℂ ∖ {0, k}`. -/
theorem heckeEk_differentiableAt {s : ℂ} (hs0 : s ≠ 0) (hsk : s ≠ k) :
    DifferentiableAt ℂ (Λ hk hk2) s :=
  (P hk hk2).differentiableAt_Λ (Or.inl hs0) (Or.inl (by simpa [P] using hsk))

/-- Simple pole at `s = k` with residue `(-1)^{k/2}`. -/
theorem heckeEk_residue_k :
    Tendsto (fun s : ℂ ↦ (s - k) * Λ hk hk2 s) (nhdsWithin k {(k : ℂ)}ᶜ)
      (nhds ((-1) ^ (k / 2))) := by
  have h := (P hk hk2).Λ_residue_k
  have hk' : (((P hk hk2).k : ℝ) : ℂ) = k := by simp [P]
  have hε : (P hk hk2).ε = (-1) ^ (k / 2) := rfl
  have hg : (P hk hk2).g₀ = 1 := rfl
  rw [hk', hε, hg, smul_eq_mul, mul_one] at h
  simpa only [smul_eq_mul] using h

/-- Simple pole at `s = 0` with residue `-1`. -/
theorem heckeEk_residue_zero :
    Tendsto (fun s : ℂ ↦ s * Λ hk hk2 s) (nhdsWithin 0 {0}ᶜ) (nhds (-1)) := by
  have h := (P hk hk2).Λ_residue_zero
  have hf : (P hk hk2).f₀ = 1 := rfl
  rw [hf] at h
  simpa only [smul_eq_mul] using h

/-- The constant `-(2k / B_k)` in the `q`-expansion of `E_k`. -/
noncomputable abbrev c (k : ℕ) : ℂ := -(2 * k / bernoulli k : ℂ)

include hk2 in
/-- The `q`-expansion on the imaginary axis: `E_k(it) - 1 = ∑_{n ≥ 1} a_n e^{-2πnt}`. -/
theorem hasSum_F_sub_one (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ if ((2 * n : ℕ) : ℝ) = 0 then 0 else
      (PowerSeries.coeff n (qExpansion 1 (E hk))) * Real.exp (-π * ((2 * n : ℕ) : ℝ) * t))
      (F hk t - 1) := by
  have := ModularForm.hasSum_qExpansion (E hk) one_pos one_mem_strictPeriods_SL (ofComplex (I * t))
  convert! hasSum_ite_sub_hasSum this 0 using 2 with n
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne', Function.Periodic.qParam, ofComplex_apply_eq_ite, ht, ← exp_nat_mul]
      grind [I_sq]
  · simp [E_qExpansion_coeff_zero hk hk2]

section Identification

open LSeries LSeries.notation
open ArithmeticFunction (natCoe_apply natCoe_mul pow pow_apply zeta_mul_pow_eq_sigma)
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

/-- `∑ n^m n^{-s} = ζ(s - m)` for `re s > m + 1`. -/
theorem LSeriesHasSum_pow (m : ℕ) {s : ℂ} (hs : m + 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (n : ℂ) ^ m) s (riemannZeta (s - m)) := by
  have h := LSeriesHasSum_one (s := s - m) (by simp; linarith)
  unfold LSeriesHasSum at h ⊢
  convert h using 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [cpow_sub _ _ this, cpow_natCast]
    have : (n : ℂ) ^ s ≠ 0 := by simp [this]
    simp

/-- `σ_m = ζ ⋆ Id^m` as sequences in `ℂ`. -/
theorem convolution_sigma {m : ℕ} (hm : m ≠ 0) :
    (fun n : ℕ ↦ ((ζ n : ℕ) : ℂ)) ⍟ (fun n : ℕ ↦ (n : ℂ) ^ m) = fun n ↦ ((σ m n : ℕ) : ℂ) := by
  have h1 : (fun n : ℕ ↦ ((ζ n : ℕ) : ℂ)) =
      ⇑((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    funext n; rw [natCoe_apply]
  have h2 : (fun n : ℕ ↦ (n : ℂ) ^ m) =
      ⇑((pow m : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
    funext n; rw [natCoe_apply, pow_apply]; simp [hm]
  rw [h1, h2, ArithmeticFunction.coe_mul, ← natCoe_mul, zeta_mul_pow_eq_sigma]
  funext n; rw [natCoe_apply]

/-- `∑ σ_m(n) n^{-s} = ζ(s) ζ(s - m)` for `re s > m + 1`. -/
theorem LSeriesHasSum_sigma {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : m + 1 < s.re) :
    LSeriesHasSum (fun n ↦ ((σ m n : ℕ) : ℂ)) s (riemannZeta s * riemannZeta (s - m)) := by
  rw [← convolution_sigma hm]
  have h1 : 1 < s.re := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  exact (ArithmeticFunction.LSeriesHasSum_zeta h1).convolution (LSeriesHasSum_pow m hs)

include hk2 in
theorem coeff_E_pos {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff n (qExpansion 1 (E hk)) = c k * ((σ (k - 1) n : ℕ) : ℂ) := by
  rw [E_qExpansion_coeff hk hk2]; simp [hn]

include hk in
theorem sub_one_add_one_lt {s : ℂ} (hs : k < s.re) : (((k - 1 : ℕ) : ℝ)) + 1 < s.re := by
  have : 1 ≤ k := by omega
  push_cast [this]; linarith

include hk2 in
/-- Absolute convergence of the Dirichlet series of the `q`-coefficients for `re s > k`. -/
theorem summable_coeff {s : ℂ} (hs : k < s.re) :
    Summable fun n : ℕ ↦
      ‖PowerSeries.coeff n (qExpansion 1 (E hk))‖ / (((2 * n : ℕ) : ℝ)) ^ s.re := by
  have hL := (LSeriesHasSum_sigma (m := k - 1) (by omega) (sub_one_add_one_lt hk hs)).summable.norm.mul_left
    (‖c k‖ / 2 ^ s.re)
  have hs0 : 0 < s.re := by have : (3 : ℝ) ≤ k := by exact_mod_cast hk
                            linarith
  refine hL.congr fun n => ?_
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hs0.ne']
  · simp only [hn, ite_false]
    rw [coeff_E_pos hk hk2 hn, norm_mul, Nat.cast_mul, Real.mul_rpow (by norm_num) (by positivity)]
    simp only [Nat.cast_ofNat, Complex.norm_natCast]
    field_simp

include hk2 in
/-- Termwise comparison of the Mellin-transformed `q`-series with `L(σ_{k-1}, s)`. -/
theorem term_eq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ↑π ^ (-s) * Gamma s * PowerSeries.coeff n (qExpansion 1 (E hk)) /
      ((((2 * n : ℕ) : ℝ)) : ℂ) ^ s =
      (c k * (2 * π) ^ (-s) * Gamma s) * term (fun n ↦ ((σ (k - 1) n : ℕ) : ℂ)) s n := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zero_cpow hs0]
  · rw [term_of_ne_zero hn, coeff_E_pos hk hk2 hn, Nat.cast_mul, ofReal_mul,
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

/-- **Identification** for `re s > k`:
`Λ s = -(2k / B_k) (2π)^{-s} Γ(s) ζ(s) ζ(s - k + 1)`. -/
theorem heckeEk_eq {s : ℂ} (hs : k < s.re) :
    Λ hk hk2 s = -(2 * k / bernoulli k) * (2 * π) ^ (-s) * Gamma s * riemannZeta s *
      riemannZeta (s - k + 1) := by
  have hs0 : 0 < s.re := by have : (3 : ℝ) ≤ k := by exact_mod_cast hk
                            linarith
  have hM := ((P hk hk2).hasMellin (s := s) (by simpa [P] using hs)).2
  have key := hasSum_mellin_pi_mul₀ (a := fun n => PowerSeries.coeff n (qExpansion 1 (E hk)))
    (p := fun n : ℕ => ((2 * n : ℕ) : ℝ)) (F := fun t => F hk t - 1) (s := s)
    (fun n => Nat.cast_nonneg _) hs0 (fun t ht => hasSum_F_sub_one hk hk2 t ht)
    (summable_coeff hk hk2 hs)
  have hL := ((LSeriesHasSum_sigma (m := k - 1) (by omega) (sub_one_add_one_lt hk hs)).mul_left
    (c k * (2 * π) ^ (-s) * Gamma s))
  simp_rw [term_eq hk hk2 hs0] at key
  have := key.unique hL
  have hsub : s - ((k - 1 : ℕ) : ℂ) = s - k + 1 := by
    have : 1 ≤ k := by omega
    push_cast [this]; ring
  rw [hsub] at this
  show (P hk hk2).Λ s = _
  rw [← hM, mul_assoc _ (riemannZeta s)]
  exact this

end Identification

/-! ### Analytic continuation of the identification -/

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := {1}ᶜ)
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- **Identification on all of `ℂ`** (away from the poles of the right-hand side): for
`s ∉ {1, k, 0, -1, -2, …}`, `Λ s = -(2k / B_k) (2π)^{-s} Γ(s) ζ(s) ζ(s - k + 1)`.
Proved from `heckeEk_eq` by the identity theorem on the connected set `ℂ ∖ ({1, k} ∪ -ℕ)`. -/
theorem heckeEk_eq_of_ne {s : ℂ} (hs1 : s ≠ 1) (hsk : s ≠ k) (hsn : ∀ n : ℕ, s ≠ -n) :
    Λ hk hk2 s = -(2 * k / bernoulli k) * (2 * π) ^ (-s) * Gamma s * riemannZeta s *
      riemannZeta (s - k + 1) := by
  set G : ℂ → ℂ := fun s ↦ -(2 * k / bernoulli k) * (2 * π) ^ (-s) * ((Gamma s)⁻¹)⁻¹ *
    riemannZeta s * riemannZeta (s - k + 1) with hG
  suffices Λ hk hk2 s = G s by simpa [G] using this
  let S : Set ℂ := {1, (k : ℂ)} ∪ Set.range (fun n : ℕ ↦ -(n : ℂ))
  let U : Set ℂ := Sᶜ
  have hSc : S.Countable := (Set.toFinite _).countable.union (Set.countable_range _)
  have hUp : IsPreconnected U :=
    (hSc.isConnected_compl_of_one_lt_rank (by simp only [rank_real_complex, Nat.one_lt_ofNat]))
      |>.isPreconnected
  have memU {z : ℂ} : z ∈ U ↔ z ≠ 1 ∧ z ≠ k ∧ ∀ n : ℕ, z ≠ -n := by
    simp only [U, S, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_range, not_or, not_exists]
    exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, fun n h => c n h.symm⟩,
      fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, fun n h => c n h.symm⟩⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  -- `Λ` is analytic on `U`
  have hΛ : AnalyticOnNhd ℂ (Λ hk hk2) U := by
    intro z hz
    obtain ⟨-, hzk, hzn⟩ := memU.mp hz
    have hz0 : z ≠ 0 := by simpa using hzn 0
    refine DifferentiableOn.analyticAt (s := {0, (k : ℂ)}ᶜ) (fun w hw => ?_) ?_
    · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hw
      exact (heckeEk_differentiableAt hk hk2 hw.1 hw.2).differentiableWithinAt
    · exact (Set.toFinite _).isClosed.isOpen_compl.mem_nhds (by simp [hz0, hzk])
  -- `G` is analytic on `U`
  have hGa : AnalyticOnNhd ℂ G U := by
    intro z hz
    obtain ⟨hz1, hzk, hzn⟩ := memU.mp hz
    have h1 : AnalyticAt ℂ (fun s : ℂ ↦ (2 * (π : ℂ)) ^ (-s)) z :=
      Differentiable.analyticAt (fun w => (differentiableAt_id.neg).const_cpow
        (Or.inl (by simp [Real.pi_ne_zero]))) z
    have h2 : AnalyticAt ℂ (fun s : ℂ ↦ ((Gamma s)⁻¹)⁻¹) z :=
      (Differentiable.analyticAt differentiable_one_div_Gamma z).inv
        (inv_ne_zero (Gamma_ne_zero hzn))
    have h3 : AnalyticAt ℂ riemannZeta z := analyticAt_riemannZeta hz1
    have h4 : AnalyticAt ℂ (fun s : ℂ ↦ riemannZeta (s - k + 1)) z := by
      refine (analyticAt_riemannZeta ?_).comp ((analyticAt_id.sub analyticAt_const).add
        analyticAt_const)
      intro h; apply hzk; linear_combination h
    exact (((analyticAt_const.mul h1).mul h2).mul h3).mul h4
  -- they agree near `k + 1`
  have hkU : ((k : ℂ) + 1) ∈ U := by
    refine memU.mpr ⟨?_, ?_, fun n h => ?_⟩
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this
    · have := congrArg Complex.re h; simp at this; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hV : {z : ℂ | (k : ℝ) < z.re} ∈ nhds ((k : ℂ) + 1) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hEq : Λ hk hk2 =ᶠ[nhds ((k : ℂ) + 1)] G := eventually_of_mem hV fun z hz => by
    rw [heckeEk_eq hk hk2 hz]; simp [G]
  exact hΛ.eqOn_of_preconnected_of_eventuallyEq hGa hUp hkU hEq (memU.mpr ⟨hs1, hsk, hsn⟩)

/-! ### Centre of symmetry -/

/-- When `k ≡ 2 (mod 4)` the root number is `-1`, so `Λ_k` vanishes at the centre `s = k / 2`. -/
theorem heckeEk_centre_eq_zero (hodd : Odd (k / 2)) : Λ hk hk2 ((k : ℂ) / 2) = 0 := by
  have h := heckeEk_functional_equation hk hk2 ((k : ℂ) / 2)
  rw [hodd.neg_one_pow, show (k : ℂ) - k / 2 = k / 2 by ring, neg_one_smul] at h
  exact CharZero.eq_neg_self_iff.mp h

/-! ### Weight 4: consistency with `Fugue.HeckeE4` -/

section Four

/-- At `k = 4` the construction is literally the pair of `Fugue.HeckeE4`. -/
theorem P_four : P (k := 4) (by norm_num) (by decide) = HeckeE4.P := by
  unfold P HeckeE4.P ε
  congr 1
  norm_num

theorem Λ_four : Λ (k := 4) (by norm_num) (by decide) = HeckeE4.Λ := by
  show (P _ _).Λ = HeckeE4.P.Λ
  rw [P_four]

/-- Weight 4 recovered from the general theorem: `Λ₄(4 - s) = Λ₄(s)`. -/
theorem heckeE4_functional_equation' (s : ℂ) :
    HeckeE4.Λ (4 - s) = HeckeE4.Λ s := by
  have h := heckeEk_functional_equation (k := 4) (by norm_num) (by decide) s
  rw [Λ_four] at h
  norm_num at h
  exact h

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by decide +kernel

/-- Weight 4 recovered from the general theorem:
`Λ₄(s) = 240 (2π)^{-s} Γ(s) ζ(s) ζ(s - 3)` for `re s > 4`. -/
theorem heckeE4_eq' {s : ℂ} (hs : 4 < s.re) :
    HeckeE4.Λ s = 240 * (2 * π) ^ (-s) * Gamma s * riemannZeta s * riemannZeta (s - 3) := by
  have h := heckeEk_eq (k := 4) (by norm_num) (by decide) (s := s) (by exact_mod_cast hs)
  have hc : -(2 * ((4 : ℕ) : ℂ) / ((bernoulli 4 : ℚ) : ℂ)) = 240 := by
    rw [bernoulli_four]; push_cast; norm_num
  have hz : s - ((4 : ℕ) : ℂ) + 1 = s - 3 := by push_cast; ring
  rw [Λ_four, hc, hz] at h
  exact h

end Four

/-! ### Weight 6: root number `-1` -/

section Six

/-- The completed `L`-function of `E₆`. -/
noncomputable abbrev Λ₆ : ℂ → ℂ := Λ (k := 6) (by norm_num) (by decide)

/-- **Functional equation for `E₆`** : `Λ₆(6 - s) = -Λ₆(s)` (root number `-1`). -/
theorem heckeE6_functional_equation (s : ℂ) : Λ₆ (6 - s) = -Λ₆ s := by
  have h := heckeEk_functional_equation (k := 6) (by norm_num) (by decide) s
  norm_num at h
  exact h

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

/-- `Λ₆(s) = -504 (2π)^{-s} Γ(s) ζ(s) ζ(s - 5)` for `re s > 6`. -/
theorem heckeE6_eq {s : ℂ} (hs : 6 < s.re) :
    Λ₆ s = -504 * (2 * π) ^ (-s) * Gamma s * riemannZeta s * riemannZeta (s - 5) := by
  have h := heckeEk_eq (k := 6) (by norm_num) (by decide) (s := s) (by exact_mod_cast hs)
  have hc : -(2 * ((6 : ℕ) : ℂ) / ((bernoulli 6 : ℚ) : ℂ)) = -504 := by
    rw [bernoulli_six]; push_cast; norm_num
  have hz : s - ((6 : ℕ) : ℂ) + 1 = s - 5 := by push_cast; ring
  rw [hc, hz] at h
  exact h

/-- The root number `-1` forces a zero at the centre: `Λ₆(3) = 0`. -/
theorem heckeE6_centre : Λ₆ 3 = 0 := by
  have h := heckeEk_centre_eq_zero (k := 6) (by norm_num) (by decide) (by decide)
  norm_num at h
  exact h

/-- **Consistency check.** By the analytic continuation `heckeEk_eq_of_ne`,
`Λ₆(3) = -504 (2π)^{-3} Γ(3) ζ(3) ζ(-2)`, and this vanishes because `ζ(-2) = 0` is a trivial zero
of `ζ` — independently of the functional equation, which forces `Λ₆(3) = 0` via the root number
`-1` (`heckeE6_centre`). -/
theorem heckeE6_centre_eq_zeta :
    Λ₆ 3 = -504 * (2 * π) ^ (-3 : ℂ) * Complex.Gamma 3 * riemannZeta 3 * riemannZeta (-2) ∧
      riemannZeta (-2) = 0 := by
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  refine ⟨?_, hz⟩
  have h := heckeEk_eq_of_ne (k := 6) (by norm_num) (by decide) (s := 3) (by norm_num)
    (by norm_num) (fun n h => by
      have := congrArg Complex.re h; simp at this; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
  have hc : -(2 * ((6 : ℕ) : ℂ) / ((bernoulli 6 : ℚ) : ℂ)) = -504 := by
    rw [bernoulli_six]; push_cast; norm_num
  have hz' : (3 : ℂ) - ((6 : ℕ) : ℂ) + 1 = -2 := by push_cast; ring
  rw [hc, hz'] at h
  exact h

end Six

end Fugue.HeckeEk
