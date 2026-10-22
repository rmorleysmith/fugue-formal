import Mathlib

set_option autoImplicit false

/-!
# Where the primes lie in the golden ring `ℤ[φ]`

`φ = (1 + √5)/2`; the ring of integers of `ℚ(√5)` is `ℤ[φ]`, modelled as
`QuadraticAlgebra ℤ 1 1` (`φ² = 1 + φ`), with norm form `N(x + yφ) = x² + xy - y²`.

Main result (`Fugue.golden_prime_iff`): for a prime `p`,
  `(∃ x y : ℤ, x² + xy - y² = p) ↔ (p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4)`.

Also: `5 = (√5)²` with `√5 = 2φ - 1` (ramified), primes `p ≡ ±2 (mod 5)` are prime in `ℤ[φ]`
(inert, `Golden.prime_of_inert`), primes `p ≡ ±1 (mod 5)` are not (split), and
`φ^(n+1) = F_n + F_{n+1} φ`, giving Cassini's identity `Golden.fib_cassini`.

## Proof outline
* (⇒) Mod 5, `x² + xy - y² ≡ (x + 3y)²`, so `p % 5 ∈ {0, 1, 4}`; `5 ∣ p` forces `p = 5`.
* (⇐) `ℤ[φ]` is a domain (`(2x+y)² = 5y²` forces `x = y = 0`) and Euclidean for `|N|`
  (rounded division gives `|N(r)| ≤ |N(y)|/2`). For `p ≡ ±1 (mod 5)`, quadratic reciprocity
  makes `5` a square mod `p`, so `p ∣ t² + t - 1 = N(t + φ)` while `p ∤ t + φ, t + φ̄`; hence
  `p` is not prime, i.e. not irreducible, so `p = a b` with `|N a| = p`. If `N a = -p`, replace
  `a` by `φ a` (`N φ = -1`).
-/

namespace Fugue

namespace Golden

/-- The golden integers `ℤ[φ]`, `φ² = 1 + φ`. -/
abbrev G := QuadraticAlgebra ℤ 1 1

open QuadraticAlgebra hiding norm

local notation "N" => (QuadraticAlgebra.norm : G →* ℤ)

lemma norm_eq (z : G) : N z = z.re ^ 2 + z.re * z.im - z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma norm_mk (x y : ℤ) : N (⟨x, y⟩ : G) = x ^ 2 + x * y - y ^ 2 := norm_eq _

lemma four_norm (z : G) : 4 * N z = (2 * z.re + z.im) ^ 2 - 5 * z.im ^ 2 := by
  rw [norm_eq]; ring

instance : Zsqrtd.Nonsquare 5 := ⟨fun n h => by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> omega
  · nlinarith⟩

lemma N_eq_zero_iff (z : G) : N z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h4 := four_norm z
    rw [h, mul_zero] at h4
    have : (2 * z.re + z.im) * (2 * z.re + z.im) = ((5 : ℕ) : ℤ) * z.im * z.im := by
      push_cast; linear_combination -h4
    obtain ⟨h1, h2⟩ := Zsqrtd.divides_sq_eq_zero_z this
    ext <;> simp <;> omega
  · rintro rfl; simp

instance : NoZeroDivisors G where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have := congrArg N h
    rw [map_mul, QuadraticAlgebra.norm_zero, mul_eq_zero, N_eq_zero_iff, N_eq_zero_iff] at this
    exact this

instance : IsDomain G := NoZeroDivisors.to_isDomain G

/-! ### Euclidean division with respect to `|N|` -/

/-- Rounded quotient `≈ u / m` for `m > 0`. -/
def rdiv (u m : ℤ) : ℤ := (2 * u + m) / (2 * m)

lemma rdiv_spec (u m : ℤ) (hm : 0 < m) :
    -m ≤ 2 * (u - m * rdiv u m) ∧ 2 * (u - m * rdiv u m) ≤ m := by
  have h1 := Int.mul_ediv_add_emod (2 * u + m) (2 * m)
  have h2 := Int.emod_nonneg (2 * u + m) (show 2 * m ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * u + m) (show 0 < 2 * m by omega)
  unfold rdiv
  constructor <;> nlinarith

/-- Quotient in `ℤ[φ]`: round `x * star y / N y` coordinatewise. -/
def quot (x y : G) : G :=
  ⟨Int.sign (N y) * rdiv (x * star y).re |N y|, Int.sign (N y) * rdiv (x * star y).im |N y|⟩

lemma quot_zero (x : G) : quot x 0 = 0 := by
  ext <;> simp [quot]

lemma N_cast (z : G) : ((N z : ℤ) : G) = z * star z := by
  rw [← algebraMap_norm_eq_mul_star]; rfl

lemma re_mul_int (w : G) (n : ℤ) : (w * (n : G)).re = w.re * n := by simp [re_mul]

lemma im_mul_int (w : G) (n : ℤ) : (w * (n : G)).im = w.im * n := by simp [im_mul]

lemma natAbs_norm_sub_quot_lt (x y : G) (hy : y ≠ 0) :
    (N (x - y * quot x y)).natAbs < (N y).natAbs := by
  have hn0 : N y ≠ 0 := (N_eq_zero_iff y).not.2 hy
  set n := N y with hn
  set m := |n| with hm
  have hmpos : 0 < m := abs_pos.2 hn0
  have hsn : n * Int.sign n = m := by rw [mul_comm, Int.sign_mul_self_eq_abs]
  set u := (x * star y).re
  set v := (x * star y).im
  set a := u - m * rdiv u m with ha
  set b := v - m * rdiv v m with hb
  have key : (x - y * quot x y) * star y = ⟨a, b⟩ := by
    have hyy : y * star y = (n : G) := (N_cast y).symm
    rw [sub_mul, mul_comm y, mul_assoc, hyy]
    ext
    · rw [re_sub, re_mul_int]
      show u - (Int.sign n * rdiv u m) * n = a
      rw [ha, ← hsn]; ring
    · rw [im_sub, im_mul_int]
      show v - (Int.sign n * rdiv v m) * n = b
      rw [hb, ← hsn]; ring
  obtain ⟨ha1, ha2⟩ := rdiv_spec u m hmpos
  obtain ⟨hb1, hb2⟩ := rdiv_spec v m hmpos
  rw [← ha] at ha1 ha2
  rw [← hb] at hb1 hb2
  have hnorm : N (x - y * quot x y) * n = a ^ 2 + a * b - b ^ 2 := by
    rw [← norm_mk, ← key, map_mul, QuadraticAlgebra.norm_star]
  have hup : 2 * (a ^ 2 + a * b - b ^ 2) ≤ m ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha2) (neg_le_iff_add_nonneg.1 hb1),
      mul_nonneg (neg_le_iff_add_nonneg.1 ha1) (sub_nonneg.2 hb2),
      mul_nonneg (sub_nonneg.2 ha2) (neg_le_iff_add_nonneg.1 ha1)]
  have hlo : -(m ^ 2) ≤ 2 * (a ^ 2 + a * b - b ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hb2),
      mul_nonneg (neg_le_iff_add_nonneg.1 ha1) (neg_le_iff_add_nonneg.1 hb1),
      mul_nonneg (sub_nonneg.2 hb2) (neg_le_iff_add_nonneg.1 hb1)]
  set r := N (x - y * quot x y)
  have habs : |r| * m * 2 ≤ m * m := by
    have : |2 * (a ^ 2 + a * b - b ^ 2)| ≤ m ^ 2 := abs_le.2 ⟨hlo, hup⟩
    rw [← hnorm, abs_mul, abs_mul, hm] at this
    simp only [abs_two] at this
    nlinarith
  have h2 : |r| * 2 ≤ m := by
    have := le_of_mul_le_mul_left (a := m) (by linarith) hmpos
    nlinarith
  have : |r| < |n| := by rw [← hm]; omega
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
  exact_mod_cast this

lemma N_pos_abs {z : G} (hz : z ≠ 0) : 0 < (N z).natAbs :=
  Int.natAbs_pos.2 ((N_eq_zero_iff z).not.2 hz)

instance : EuclideanDomain G :=
  { (inferInstance : CommRing G), (inferInstance : Nontrivial G) with
    quotient := quot
    remainder := fun x y => x - y * quot x y
    quotient_zero := quot_zero
    quotient_mul_add_remainder_eq := fun _ _ => by ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ (N : G → ℤ))).wf
    remainder_lt := fun x y hy => natAbs_norm_sub_quot_lt x y hy
    mul_left_not_lt := fun a b hb => by
      show ¬ (N (a * b)).natAbs < (N a).natAbs
      rw [map_mul, Int.natAbs_mul]
      have := Nat.le_mul_of_pos_right (N a).natAbs (N_pos_abs hb)
      omega }

lemma isUnit_iff_N (z : G) : IsUnit z ↔ (N z).natAbs = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff_natAbs_eq]

lemma natCast_dvd_iff (p : ℕ) (z : G) : (p : G) ∣ z ↔ (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  rw [← algebraMap_dvd_iff]; rfl

/-- The golden ratio `φ` itself, a unit of norm `-1`. -/
def φ : G := ⟨0, 1⟩

lemma N_φ : N φ = -1 := by rw [φ, norm_mk]; norm_num

/-! ### Factorizations of a rational prime -/

lemma N_eq_of_factor (p : ℕ) (hp : p.Prime) (a b : G) (hab : (p : G) = a * b)
    (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : (N a).natAbs = p := by
  rw [isUnit_iff_N] at ha hb
  have hNat : (N a).natAbs * (N b).natAbs = p ^ 2 := by
    rw [← Int.natAbs_mul, ← map_mul, ← hab, QuadraticAlgebra.norm_natCast, Int.natAbs_pow,
      Int.natAbs_natCast]
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hNat)
  interval_cases i
  · rw [pow_zero] at hai; omega
  · rw [pow_one] at hai; omega
  · rw [hai] at hNat
    have : (N b).natAbs = 1 := by
      have hp2 : 0 < p ^ 2 := by have := hp.pos; positivity
      nlinarith
    omega

/-! ### Necessity: reduction mod 5 -/

/-- Mod 5 the golden norm form is a perfect square: `x² + xy - y² ≡ (x + 3y)²`. -/
lemma mod_five_square (x y : ℤ) :
    ((x ^ 2 + x * y - y ^ 2 : ℤ) : ZMod 5) = ((x + 3 * y : ℤ) : ZMod 5) ^ 2 := by
  have h5 : (5 : ZMod 5) = 0 := rfl
  push_cast
  linear_combination (-(x : ZMod 5) * y - 2 * y ^ 2) * h5

lemma mod_five_of_rep (n : ℕ) (x y : ℤ) (h : x ^ 2 + x * y - y ^ 2 = n) :
    n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 4 := by
  have h' := mod_five_square x y
  rw [h] at h'
  have hn : ((n : ℤ) : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := by
    rw [Int.cast_natCast, ZMod.natCast_mod]
  rw [hn] at h'
  generalize ((x + 3 * y : ℤ) : ZMod 5) = c at h'
  have : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at h' this ⊢
  interval_cases r <;> revert c <;> decide

/-! ### Sufficiency: split primes `p ≡ ±1 mod 5` -/

lemma exists_dvd_quad (p : ℕ) (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 + t - 1 := by
  have := Fact.mk hp
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hsq5 : IsSquare ((p : ℕ) : ZMod 5) := by
    rw [← ZMod.natCast_mod]
    rcases h with h | h <;> rw [h]
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨s, hs⟩ :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2).1 hsq5
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  set t : ZMod p := (s - 1) / 2 with ht
  have hq : t ^ 2 + t - 1 = 0 := by
    have hs' : (5 : ZMod p) = s * s := by exact_mod_cast hs
    rw [ht]
    field_simp
    linear_combination -hs'
  refine ⟨(t.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hq

lemma not_prime_of_split (p : ℕ) (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    ¬ Prime (p : G) := by
  intro hpr
  obtain ⟨t, ht⟩ := exists_dvd_quad p hp h
  have hdvd : (p : G) ∣ (⟨t, 1⟩ : G) * star (⟨t, 1⟩ : G) := by
    rw [← N_cast, norm_mk]
    obtain ⟨c, hc⟩ := ht
    refine ⟨(c : G), ?_⟩
    rw [show t ^ 2 + t * 1 - 1 ^ 2 = t ^ 2 + t - 1 by ring, hc]; push_cast; ring
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hpr.dvd_or_dvd hdvd with h | h
  · rw [natCast_dvd_iff] at h
    exact hp1 h.2
  · rw [natCast_dvd_iff] at h
    exact hp1 (by simpa using h.2)

lemma exists_natAbs_norm_eq (p : ℕ) (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ z : G, (N z).natAbs = p := by
  have hni : ¬ Irreducible (p : G) := fun hi => not_prime_of_split p hp h hi.prime
  rw [irreducible_iff] at hni
  push Not at hni
  have hnu : ¬ IsUnit (p : G) := by
    rw [isUnit_iff_N, QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]
    have := hp.two_le
    nlinarith
  obtain ⟨a, b, hab, ha, hb⟩ := hni hnu
  exact ⟨a, N_eq_of_factor p hp a b hab ha hb⟩

lemma exists_norm_eq (p : ℕ) (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ z : G, N z = p := by
  obtain ⟨z, hz⟩ := exists_natAbs_norm_eq p hp h
  rcases Int.natAbs_eq (N z) with h1 | h1
  · exact ⟨z, by rw [h1, hz]⟩
  · refine ⟨φ * z, ?_⟩
    rw [map_mul, N_φ, h1, hz]; ring

end Golden

open Golden in
/-- **Primes of the form `x² + xy - y²`.** A prime `p` is the norm of an element of `ℤ[φ]`,
`φ = (1 + √5)/2`, iff `p = 5` (ramified) or `p ≡ ±1 (mod 5)` (split). -/
theorem golden_prime_iff (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = p) ↔ (p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    rcases mod_five_of_rep p x y hxy with h | h | h
    · left
      have h5 : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 h5).symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (rfl | h)
    · exact ⟨2, 1, by norm_num⟩
    · obtain ⟨z, hz⟩ := exists_norm_eq p hp h
      exact ⟨z.re, z.im, by rw [← norm_eq]; exact hz⟩


namespace Golden

open QuadraticAlgebra hiding norm

local notation "N" => (QuadraticAlgebra.norm : G →* ℤ)

/-! ### The three behaviours of rational primes in `ℤ[φ]` -/

/-- `√5 = 2φ - 1`. -/
def sqrt5 : G := ⟨-1, 2⟩

lemma sqrt5_eq : sqrt5 = 2 * φ - 1 := by
  ext <;> simp [sqrt5, φ]

/-- `5` ramifies: `5 = (√5)²`. -/
lemma sqrt5_sq : sqrt5 ^ 2 = 5 := by
  ext <;> simp [sqrt5, sq]

lemma N_sqrt5 : N sqrt5 = -5 := by rw [sqrt5, norm_mk]; norm_num

/-- Primes `p ≡ ±2 (mod 5)` stay prime in `ℤ[φ]` (inert). -/
theorem prime_of_inert (p : ℕ) (hp : p.Prime) (h : p % 5 = 2 ∨ p % 5 = 3) : Prime (p : G) := by
  apply Irreducible.prime
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_N, QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]
    have := hp.two_le
    nlinarith
  · intro a b hab
    by_contra hcon
    push Not at hcon
    have ha := N_eq_of_factor p hp a b hab hcon.1 hcon.2
    obtain ⟨z, hz⟩ : ∃ z : G, N z = p := by
      rcases Int.natAbs_eq (N a) with h1 | h1
      · exact ⟨a, by rw [h1, ha]⟩
      · exact ⟨φ * a, by rw [map_mul, N_φ, h1, ha]; ring⟩
    have := mod_five_of_rep p z.re z.im (by rw [← norm_eq]; exact hz)
    omega

/-- Primes `p ≡ ±1 (mod 5)` split in `ℤ[φ]`: `p` is not prime there. -/
theorem not_prime_of_split' (p : ℕ) (hp : p.Prime) (h : p % 5 = 1 ∨ p % 5 = 4) :
    ¬ Prime (p : G) :=
  not_prime_of_split p hp h

/-! ### Fibonacci numbers: powers of `φ` and Cassini's identity -/

/-- `φ^(n+1) = F_n + F_{n+1} φ`. -/
theorem φ_pow (n : ℕ) : φ ^ (n + 1) = ⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ := by
  induction n with
  | zero => ext <;> simp [φ]
  | succ n ih =>
    rw [pow_succ', ih]
    ext <;> simp [φ, Nat.fib_add_two]

/-- **Cassini's identity** in golden form: `F_n² + F_n F_{n+1} - F_{n+1}² = (-1)^(n+1)`,
i.e. `F_n + F_{n+1} φ` is a unit of norm `±1` (it is `φ^(n+1)`). -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib n : ℤ) ^ 2 + Nat.fib n * Nat.fib (n + 1) - (Nat.fib (n + 1) : ℤ) ^ 2 =
      (-1) ^ (n + 1) := by
  rw [← norm_mk, ← φ_pow, map_pow, N_φ]

end Golden

/-! ### Sanity checks -/

example : (2 : ℤ) ^ 2 + 2 * 1 - 1 ^ 2 = 5 := by norm_num
example : (3 : ℤ) ^ 2 + 3 * 1 - 1 ^ 2 = 11 := by norm_num
example : (4 : ℤ) ^ 2 + 4 * 1 - 1 ^ 2 = 19 := by norm_num
example : (5 : ℤ) ^ 2 + 5 * 1 - 1 ^ 2 = 29 := by norm_num
example : (5 : ℤ) ^ 2 + 5 * 2 - 2 ^ 2 = 31 := by norm_num

theorem golden_rep_eleven : ∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = 11 := ⟨3, 1, by norm_num⟩

theorem golden_rep_nineteen : ∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = 19 := ⟨4, 1, by norm_num⟩

theorem golden_not_rep_two : ¬ ∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = 2 := by
  have := golden_prime_iff 2 Nat.prime_two
  push_cast at this
  rw [this]; norm_num

theorem golden_not_rep_three : ¬ ∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = 3 := by
  have := golden_prime_iff 3 Nat.prime_three
  push_cast at this
  rw [this]; norm_num

theorem golden_not_rep_seven : ¬ ∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = 7 := by
  have := golden_prime_iff 7 (by norm_num)
  push_cast at this
  rw [this]; norm_num

/-- Since `N(φ) = -1`, `p` and `-p` are represented together. -/
theorem golden_rep_neg_iff (n : ℤ) :
    (∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = n) ↔ (∃ x y : ℤ, x ^ 2 + x * y - y ^ 2 = -n) := by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨y, x + y, by linear_combination -h⟩
  · rintro ⟨x, y, h⟩; exact ⟨y, x + y, by linear_combination -h⟩

end Fugue
