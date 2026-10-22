import QuasiRH.Continuation

/-!
# Chapter 3: the same characterisation for every Dirichlet `L`-function

OpenAI's main theorem is not only about `ζ`: it proves `L(s, χ) ≠ 0` for `Re s > 7/8` for
**every** Dirichlet character `χ` (`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`,
statement copied verbatim below as `OpenAIDirichletStatement`).

The link to primes is the twisted von Mangoldt series: for `Re s > 1`,

  `∑ χ(n) Λ(n) n^{-s} = -L'(s, χ) / L(s, χ)`      (Mathlib: `LSeries_twist_vonMangoldt_eq`).

This series counts primes *in arithmetic progressions* (via orthogonality of characters).

## Contents

* A general lemma (`zeroFree_iff_differentiableOn_negLogDeriv`): for any `f` holomorphic on
  `ℂ \ {1}` and not identically zero, `f` is zero-free on `region θ` iff `-f'/f` is holomorphic
  there. Chapter 2 was the case `f = ζ`; the proof is the same.
* `zeroFreeRightL_iff` — the characterisation for `L(s, χ)`.
* `OpenAIDirichletStatement` and `twistedVonMangoldt_continuation_of_openAI` — granting OpenAI,
  every `∑ χ(n) Λ(n) n^{-s}` continues holomorphically to `{7/8 < Re s, s ≠ 1}`.
-/

open Complex Filter Topology Set DirichletCharacter
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

namespace QuasiRH

/-! ### The general lemma -/

section General

variable {f : ℂ → ℂ}

theorem not_eventually_zero_of_ne_zero (hf : DifferentiableOn ℂ f {1}ᶜ) {z₀ : ℂ} (hz₀ : z₀ ≠ 1)
    (hfz₀ : f z₀ ≠ 0) {s : ℂ} (hs : s ≠ 1) : ¬ (f =ᶠ[𝓝 s] 0) := by
  intro h
  have hzero := (hf.analyticOnNhd isOpen_compl_singleton
    ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_compl_one hs h
  exact hfz₀ (by simpa using hzero (show z₀ ∈ ({1}ᶜ : Set ℂ) from hz₀))

theorem meromorphicOrderAt_negLogDeriv (hf : DifferentiableOn ℂ f {1}ᶜ) {z₀ : ℂ} (hz₀ : z₀ ≠ 1)
    (hfz₀ : f z₀ ≠ 0) {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ : f ρ = 0) :
    meromorphicOrderAt (fun s => -deriv f s / f s) ρ = -1 := by
  have han : AnalyticAt ℂ f ρ := hf.analyticAt (isOpen_compl_singleton.mem_nhds hρ1)
  have hne0 : analyticOrderAt f ρ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han, hρ⟩
  have hnetop : analyticOrderAt f ρ ≠ ⊤ := fun h =>
    not_eventually_zero_of_ne_zero hf hz₀ hfz₀ hρ1 (analyticOrderAt_eq_top.mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne0 (by rw [← hn]; simp)
  have hord : meromorphicOrderAt f ρ = (n : ℤ) := by
    rw [han.meromorphicOrderAt_eq, ← hn, ENat.map_natCast]
  have heq : (fun s => -deriv f s / f s) = -(logDeriv f) := by
    funext s; simp [logDeriv_apply, neg_div]
  rw [heq, ← meromorphicOrderAt_neg]
  refine meromorphicOrderAt_logDeriv_eq_neg_one han.meromorphicAt ?_ ?_ <;> rw [hord]
  · exact_mod_cast hn0
  · exact WithTop.coe_ne_top

/-- **General characterisation.** For `f` holomorphic on `ℂ \ {1}` and not identically zero,
`f` has no zeros in `region θ` iff `-f'/f` is holomorphic on `region θ`. -/
theorem zeroFree_iff_differentiableOn_negLogDeriv (hf : DifferentiableOn ℂ f {1}ᶜ) {z₀ : ℂ}
    (hz₀ : z₀ ≠ 1) (hfz₀ : f z₀ ≠ 0) (θ : ℝ) :
    (∀ s ∈ region θ, f s ≠ 0) ↔
      DifferentiableOn ℂ (fun s => -deriv f s / f s) (region θ) := by
  have hsub : region θ ⊆ {1}ᶜ := fun _ hs => hs.2
  constructor
  · intro hz
    exact ((hf.deriv isOpen_compl_singleton).mono hsub).neg.div (hf.mono hsub) hz
  · intro hd s hs hzero
    have hnonneg := (hd.analyticAt ((isOpen_region θ).mem_nhds hs)).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_negLogDeriv hf hz₀ hfz₀ hs.2 hzero] at hnonneg
    exact absurd hnonneg (by decide)

end General

/-! ### Dirichlet `L`-functions -/

section Dirichlet

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- `-L'(s, χ)/L(s, χ)`. -/
noncomputable def negLogDerivL (s : ℂ) : ℂ :=
  -deriv (LFunction χ) s / LFunction χ s

/-- No zeros of `L(s, χ)` with `Re s > θ` (excluding the pole `s = 1` of the trivial character,
exactly as in OpenAI's statement). -/
def ZeroFreeRightL (θ : ℝ) : Prop :=
  ∀ s : ℂ, θ < s.re → ¬ (χ = 1 ∧ s = 1) → LFunction χ s ≠ 0

theorem differentiableOn_LFunction : DifferentiableOn ℂ (LFunction χ) {1}ᶜ := fun s hs =>
  (differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt

theorem LFunction_two_ne_zero : LFunction χ 2 ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)

/-- **Characterisation for `L(s, χ)`.** -/
theorem zeroFreeRightL_iff (θ : ℝ) :
    ZeroFreeRightL χ θ ↔ DifferentiableOn ℂ (negLogDerivL χ) (region θ) := by
  have key := zeroFree_iff_differentiableOn_negLogDeriv (differentiableOn_LFunction χ)
    (z₀ := 2) (by norm_num) (LFunction_two_ne_zero χ) θ
  rw [← show (fun s => -deriv (LFunction χ) s / LFunction χ s) = negLogDerivL χ from rfl, ← key]
  constructor
  · intro h s hs
    exact h s hs.1 (fun h' => hs.2 h'.2)
  · intro h s hs hpole
    by_cases hs1 : s = 1
    · subst hs1
      have hχ : χ ≠ 1 := fun hχ => hpole ⟨hχ, rfl⟩
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
    · exact h s ⟨hs, hs1⟩

/-- On `Re s > 1`, `-L'/L` is the twisted von Mangoldt series `∑ χ(n) Λ(n) n^{-s}`. -/
theorem LSeries_twist_vonMangoldt_eq_negLogDerivL {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s = negLogDerivL χ s := by
  rw [LSeries_twist_vonMangoldt_eq χ hs, negLogDerivL, LFunction_eq_LSeries χ hs]
  congr 2
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact (LFunction_eq_LSeries χ hz).symm

/-- If `L(s, χ)` is zero-free right of `θ`, the twisted prime series continues holomorphically
to `region θ`. -/
theorem twistedVonMangoldt_continuation {θ : ℝ} (hz : ZeroFreeRightL χ θ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (region θ) ∧
      ∀ s : ℂ, 1 < s.re → L (↗χ * ↗Λ) s = F s :=
  ⟨negLogDerivL χ, (zeroFreeRightL_iff χ θ).mp hz,
    fun _ hs => LSeries_twist_vonMangoldt_eq_negLogDerivL χ hs⟩

end Dirichlet

/-! ### OpenAI's theorem for Dirichlet `L`-functions -/

/-- OpenAI's main theorem, in the form of their Lean statement
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`. A hypothesis here; their
proof is not imported. -/
def OpenAIDirichletStatement : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}, (7 / 8 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) → LFunction χ s ≠ 0

theorem zeroFreeRightL_of_openAI (h : OpenAIDirichletStatement) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ZeroFreeRightL χ (7 / 8) := fun _ hs hpole => h χ hs hpole

/-- **Building on OpenAI, Dirichlet version.** Granting OpenAI's theorem, every twisted prime
series `∑ χ(n) Λ(n) n^{-s}` continues holomorphically to `{7/8 < Re s, s ≠ 1}`. -/
theorem twistedVonMangoldt_continuation_of_openAI (h : OpenAIDirichletStatement) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (region (7 / 8)) ∧
      ∀ s : ℂ, 1 < s.re → L (↗χ * ↗Λ) s = F s :=
  twistedVonMangoldt_continuation χ (zeroFreeRightL_of_openAI h χ)

/-- The Dirichlet statement contains the `ζ` statement (take the character mod 1). -/
theorem openAIStatement_of_dirichlet (h : OpenAIDirichletStatement) : OpenAIStatement := by
  intro s hs
  have := h (q := 1) (1 : DirichletCharacter ℂ 1) hs
  by_cases hs1 : s = 1
  · subst hs1; exact riemannZeta_one_ne_zero
  · simpa [LFunction_modOne_eq] using this (fun h' => hs1 h'.2)

end QuasiRH
