import Fugue.HeteroticE8
import Fugue.TwoSquares
import Fugue.HexagonalCount
import Fugue.HeckeE4
import Fugue.HeckeEk
import Fugue.LeibnizL

/-!
# Epstein zeta functions of `E8`, `E8 ⊕ E8`, `ℤ²` and `A₂` as products of `L`-functions

The Epstein zeta function of a lattice `L` with integral quadratic form `Q` is
`Z_Q(s) = ∑_{v ≠ 0} Q(v)^{-s}`; grouping by the value of `Q` it is the Dirichlet series of the
representation numbers `r_Q(n) = #{v | Q v = n}`: `Z_Q(s) = ∑_{n ≥ 1} r_Q(n) n^{-s}`. We state
everything as `LSeries` identities of the counts (`LSeries` ignores `n = 0`, i.e. `v = 0`).

From the representation counts proved elsewhere in `Fugue` we obtain, in the half-planes of
absolute convergence:

* `epstein_E8`        : `Z_{E8}(s) = 240 ζ(s) ζ(s - 3)`          (`Q = ‖v‖²/2`, `4 < re s`);
* `epstein_E8E8`      : `Z_{E8⊕E8}(s) = 480 ζ(s) ζ(s - 7)`       (`8 < re s`);
* `epstein_square`    : `Z_{ℤ²}(s) = 4 ζ(s) L(χ₋₄, s) = 4 ζ_{ℚ(i)}(s)`       (`1 < re s`);
* `epstein_hexagonal` : `Z_{A₂}(s) = 6 ζ(s) L(χ₋₃, s) = 6 ζ_{ℚ(√-3)}(s)`     (`1 < re s`),

where `4` and `6` are the numbers of units of `ℤ[i]` and `ℤ[ω]`. (The Dedekind-zeta
interpretation `ζ_K = ζ · L(χ_K)` is commentary; it is not formalised here.)

Method: each count is `c · (ζ ⋆ g)(n)` for a Dirichlet convolution of `ζ` with `n ↦ n^k` or with
a Dirichlet character, so `LSeriesHasSum.convolution` turns it into a product of `L`-series.
-/

set_option autoImplicit false

open LSeries LSeries.notation
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

namespace Fugue.Epstein

/-- `∑ σ₃(n) n^{-s}` as an `LSeries`. -/
theorem LSeries_sigma_three {s : ℂ} (hs : 4 < s.re) :
    LSeries (fun n ↦ ((σ 3 n : ℕ) : ℂ)) s = riemannZeta s * riemannZeta (s - 3) :=
  (HeckeE4.LSeriesHasSum_sigma_three hs).LSeries_eq

/-- `∑ σ₇(n) n^{-s}` as an `LSeries`. -/
theorem LSeries_sigma_seven {s : ℂ} (hs : 8 < s.re) :
    LSeries (fun n ↦ ((σ 7 n : ℕ) : ℂ)) s = riemannZeta s * riemannZeta (s - 7) := by
  have h := (HeckeEk.LSeriesHasSum_sigma (m := 7) (by norm_num) (s := s)
    (by push_cast; linarith)).LSeries_eq
  rw [h]; push_cast; rfl

/-- **The Epstein zeta function of `E8` is `240 ζ(s) ζ(s − 3)`** (for `re s > 4`; norm `‖v‖²/2`).

Its zeros (after continuation) are those of `ζ(s)` and of `ζ(s − 3)` — so Epstein zetas of these
lattices inherit RH-type questions from `ζ`; for general lattices, Epstein zetas can have zeros
off the line (Davenport–Heilbronn phenomenon, ledger D3). -/
theorem epstein_E8 {s : ℂ} (hs : 4 < s.re) :
    LSeries (fun n ↦ (reprCount e8Norm n : ℂ)) s = 240 * riemannZeta s * riemannZeta (s - 3) := by
  rw [LSeries_congr (g := (240 : ℂ) • fun n ↦ ((σ 3 n : ℕ) : ℂ))
    (fun {n} hn ↦ by simp [reprCount_e8 n (Nat.pos_of_ne_zero hn)]) s,
    LSeries_smul, LSeries_sigma_three hs, mul_assoc]

/-- **The Epstein zeta function of `E8 ⊕ E8` is `480 ζ(s) ζ(s − 7)`** (for `re s > 8`). -/
theorem epstein_E8E8 {s : ℂ} (hs : 8 < s.re) :
    LSeries (fun n ↦ (reprCount (directSum e8Norm e8Norm) n : ℂ)) s =
      480 * riemannZeta s * riemannZeta (s - 7) := by
  rw [LSeries_congr (g := (480 : ℂ) • fun n ↦ ((σ 7 n : ℕ) : ℂ))
    (fun {n} hn ↦ by simp [reprCount_e8e8 n (Nat.pos_of_ne_zero hn)]) s,
    LSeries_smul, LSeries_sigma_seven hs, mul_assoc]

/-- Dirichlet convolution with `ζ` is the divisor sum. -/
theorem zeta_convolution (f : ℕ → ℂ) (n : ℕ) :
    ((fun n ↦ ((ζ n : ℕ) : ℂ)) ⍟ f) n = ∑ d ∈ n.divisors, f d := by
  rw [convolution_def]
  simp only
  rw [Nat.sum_divisorsAntidiagonal' (fun a b ↦ ((ζ a : ℕ) : ℂ) * f b)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have : n / d ≠ 0 := by
    have := Nat.divisor_le hd
    have := Nat.pos_of_mem_divisors hd
    exact (Nat.div_pos (by omega) this).ne'
  simp [ArithmeticFunction.zeta_apply, this]

/-- If `f` is the divisor sum of a summable `g`, its `LSeries` is `ζ(s) · L(g, s)`. -/
theorem LSeries_divisorSum {f g : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re) (hg : LSeriesSummable g s)
    (hfg : ∀ n, n ≠ 0 → f n = ∑ d ∈ n.divisors, g d) :
    LSeries f s = riemannZeta s * LSeries g s := by
  have h := (ArithmeticFunction.LSeriesHasSum_zeta hs).convolution hg.LSeriesHasSum
  rw [← h.LSeries_eq]
  exact LSeries_congr (fun {n} hn ↦ by rw [hfg n hn, zeta_convolution g n]) s

/-! ### The square lattice `ℤ²` (Gaussian integers) -/

/-- **The Epstein zeta function of `ℤ²` is `4 ζ(s) L(χ₋₄, s)`** (`= 4 ζ_{ℚ(i)}(s)`, `re s > 1`). -/
theorem epstein_square {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℂ)) s =
      4 * riemannZeta s * DirichletCharacter.LFunction χ₄' s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ₄' hs, LSeries_congr
    (g := (4 : ℂ) • fun n : ℕ ↦ ∑ d ∈ n.divisors, χ₄' (d : ZMod 4)) (fun {n} hn ↦ ?_) s,
    LSeries_smul,
    LSeries_divisorSum hs (χ₄'.LSeriesSummable_of_one_lt_re hs) (fun n _ ↦ rfl), mul_assoc]
  have h := card_sq_add_sq n (Nat.pos_of_ne_zero hn)
  have h' := congrArg (fun z : ℤ ↦ (z : ℂ)) h
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_sum, Int.cast_ofNat] at h'
  rw [h']
  simp [χ₄'_apply]

/-! ### The hexagonal lattice `A₂` (Eisenstein integers) -/

/-- The nontrivial character mod 3 (`χ₋₃`), integer-valued. -/
def χ₃Z : MulChar (ZMod 3) ℤ where
  toFun a := match a with | 0 => 0 | 1 => 1 | 2 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- The nontrivial Dirichlet character mod 3, as a complex-valued character. -/
noncomputable def χ₃' : DirichletCharacter ℂ 3 := χ₃Z.ringHomComp (Int.castRingHom ℂ)

theorem χ₃Z_natCast (n : ℕ) : χ₃Z (n : ZMod 3) = χ₃ n := by
  have h1 : χ₃ n = χ₃ (n % 3) := by simp [χ₃]
  rw [h1, ← ZMod.natCast_mod n 3]
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = r at h3 ⊢
  interval_cases r <;> rfl

theorem χ₃'_natCast (n : ℕ) : χ₃' (n : ZMod 3) = (χ₃ n : ℂ) := by
  rw [← χ₃Z_natCast]; rfl

/-- `χ₃'` is the nontrivial character. -/
theorem χ₃'_ne_one : χ₃' ≠ 1 := by
  intro h
  have h2 : IsUnit (2 : ZMod 3) := by decide
  have := congrArg (fun χ : DirichletCharacter ℂ 3 ↦ χ 2) h
  simp only [MulChar.one_apply h2] at this
  have h' : χ₃' 2 = -1 := by
    have := χ₃'_natCast 2
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num [χ₃]
  rw [h'] at this
  norm_num at this

/-- **The Epstein zeta function of the hexagonal lattice is `6 ζ(s) L(χ₋₃, s)`**
(`= 6 ζ_{ℚ(√−3)}(s)`, `re s > 1`), for the form `a² − ab + b²`. -/
theorem epstein_hexagonal {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = n} : ℂ)) s =
      6 * riemannZeta s * DirichletCharacter.LFunction χ₃' s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ₃' hs, LSeries_congr
    (g := (6 : ℂ) • fun n : ℕ ↦ ∑ d ∈ n.divisors, χ₃' (d : ZMod 3)) (fun {n} hn ↦ ?_) s,
    LSeries_smul,
    LSeries_divisorSum hs (χ₃'.LSeriesSummable_of_one_lt_re hs) (fun n _ ↦ rfl), mul_assoc]
  have h := card_hexagonal n (Nat.pos_of_ne_zero hn)
  have h' := congrArg (fun z : ℤ ↦ (z : ℂ)) h
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_sum, Int.cast_ofNat] at h'
  rw [h']
  simp [χ₃'_natCast]


end Fugue.Epstein
