import Mathlib

set_option autoImplicit false

/-!
# Representation numbers of the hexagonal (A₂) lattice

We prove `#{(a, b) ∈ ℤ² | a² - ab + b² = n} = 6 ∑_{d ∣ n} χ₋₃(d)` for `n > 0`
(`Fugue.card_hexagonal`), i.e. the coefficient-level identity `ζ_{ℚ(√-3)} = ζ · L(·, χ₋₃)`.

## Proof outline

The Eisenstein integers are modelled as `QuadraticAlgebra ℤ (-1) (-1)` (`ω² = -1 - ω`), whose
norm is `x² - xy + y²`. We show it is a domain and build a `EuclideanDomain` instance by hand
(rounded division: `N(x - qy) ≤ ¾ N(y)`), so irreducibles are prime.

Let `R n = #{z ∈ ℤ[ω] | N z = n}` and `F n = ∑_{d ∣ n} χ₃ d`. For a prime `p` both satisfy
  `X (p k) = (1 + χ₃ p) X k - χ₃ p · [p ∣ k] X (k / p)`:
* for `F` by inclusion–exclusion on `divisors (p k) = divisors k ∪ p • divisors k`;
* for `R` from the arithmetic of `ℤ[ω]`:
  - `p = 3`: every `w` with `N w = 3k` is divisible by `λ = 1 - ω` (`star λ = λ (1 + ω)`);
  - `p ≡ 2 (mod 3)`: `p` is inert (no element has norm `p`, by reduction mod 3);
  - `p ≡ 1 (mod 3)`: an element of order 3 in `(ZMod p)ˣ` gives `p ∣ t² + t + 1 = N(t - ω)`,
    so `p` is not prime, hence `p = π π̄` with `π, π̄` non-associated primes, and
    inclusion–exclusion on `π · S k ∪ π̄ · S k` applies.
Strong induction on `n` (splitting off `n.minFac`) gives `R n = 6 F n`, since `R 1 = 6`.
-/

namespace Fugue

namespace Hexagonal

/-- The Eisenstein integers `ℤ[ω]`, `ω² = -1 - ω`. -/
abbrev E := QuadraticAlgebra ℤ (-1) (-1)

open QuadraticAlgebra hiding norm

local notation "N" => (QuadraticAlgebra.norm : E →* ℤ)

lemma norm_eq (z : E) : N z = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma norm_mk (x y : ℤ) : N (⟨x, y⟩ : E) = x ^ 2 - x * y + y ^ 2 := norm_eq _

lemma four_norm (z : E) : 4 * N z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
  rw [norm_eq]; ring

lemma N_nonneg (z : E) : 0 ≤ N z := by
  have := four_norm z
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

lemma N_eq_zero_iff (z : E) : N z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h4 := four_norm z
    rw [h] at h4
    have h1 : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have h2 : z.re = 0 := by rw [h1] at h4; nlinarith
    ext <;> simp [h1, h2]
  · rintro rfl; simp

instance : NoZeroDivisors E where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have := congrArg N h
    rw [map_mul, QuadraticAlgebra.norm_zero, mul_eq_zero, N_eq_zero_iff, N_eq_zero_iff] at this
    exact this

instance : IsDomain E := NoZeroDivisors.to_isDomain E

/-! ### Euclidean division -/

/-- Rounded quotient `≈ u / n`. -/
def rdiv (u n : ℤ) : ℤ := (2 * u + n) / (2 * n)

lemma rdiv_spec (u n : ℤ) (hn : 0 < n) :
    (2 * (u - n * rdiv u n)) ^ 2 ≤ n ^ 2 := by
  have h1 := Int.mul_ediv_add_emod (2 * u + n) (2 * n)
  have h2 := Int.emod_nonneg (2 * u + n) (show 2 * n ≠ 0 by omega)
  have h3 := Int.emod_lt_of_pos (2 * u + n) (show 0 < 2 * n by omega)
  unfold rdiv
  set q := (2 * u + n) / (2 * n)
  set s := (2 * u + n) % (2 * n)
  have : 2 * (u - n * q) = s - n := by linarith
  rw [this]
  nlinarith

/-- Quotient in `ℤ[ω]`. -/
def quot (x y : E) : E :=
  ⟨rdiv (x * star y).re (N y), rdiv (x * star y).im (N y)⟩

lemma quot_zero (x : E) : quot x 0 = 0 := by
  ext <;> simp [quot, rdiv]

lemma norm_sub_quot_lt (x y : E) (hy : y ≠ 0) : N (x - y * quot x y) < N y := by
  have hn : 0 < N y :=
    lt_of_le_of_ne (N_nonneg y) (Ne.symm ((N_eq_zero_iff y).not.2 hy))
  set n := N y
  set u := (x * star y).re
  set v := (x * star y).im
  have key : (x - y * quot x y) * star y = ⟨u - n * rdiv u n, v - n * rdiv v n⟩ := by
    have hyy : y * star y = (n : E) := by
      rw [← algebraMap_norm_eq_mul_star]; rfl
    rw [sub_mul, mul_comm y, mul_assoc, hyy]
    ext <;> simp [quot, u, v, n] <;> ring
  have h1 := rdiv_spec u n hn
  have h2 := rdiv_spec v n hn
  set a := u - n * rdiv u n
  set b := v - n * rdiv v n
  have hab : 4 * (a ^ 2 - a * b + b ^ 2) ≤ 3 * n ^ 2 := by
    have ha : (2 * a) ^ 2 ≤ n ^ 2 := h1
    have hb : (2 * b) ^ 2 ≤ n ^ 2 := h2
    have ha' : |2 * a| ≤ n := abs_le_of_sq_le_sq' ha hn.le |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    have hb' : |2 * b| ≤ n := abs_le_of_sq_le_sq' hb hn.le |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    rw [abs_le] at ha' hb'
    nlinarith [mul_nonneg (sub_nonneg.2 ha'.2) (neg_le_iff_add_nonneg.1 hb'.1),
      mul_nonneg (neg_le_iff_add_nonneg.1 ha'.1) (sub_nonneg.2 hb'.2)]
  have hnorm : N (x - y * quot x y) * n = a ^ 2 - a * b + b ^ 2 := by
    rw [← norm_mk, ← key, map_mul, QuadraticAlgebra.norm_star]
  nlinarith [N_nonneg (x - y * quot x y)]

lemma N_pos {z : E} (hz : z ≠ 0) : 0 < N z :=
  lt_of_le_of_ne (N_nonneg z) (Ne.symm ((N_eq_zero_iff z).not.2 hz))

lemma N_le_N_mul_left (a : E) {b : E} (hb : b ≠ 0) : N a ≤ N (a * b) := by
  rw [map_mul]
  have := N_pos hb
  nlinarith [N_nonneg a]

instance : EuclideanDomain E :=
  { (inferInstance : CommRing E), (inferInstance : Nontrivial E) with
    quotient := quot
    remainder := fun x y => x - y * quot x y
    quotient_zero := quot_zero
    quotient_mul_add_remainder_eq := fun _ _ => by ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ (N : E → ℤ))).wf
    remainder_lt := fun x y hy => by
      show (N (x - y * quot x y)).natAbs < (N y).natAbs
      have := norm_sub_quot_lt x y hy
      have := N_nonneg (x - y * quot x y)
      omega
    mul_left_not_lt := fun a b hb => by
      show ¬ (N (a * b)).natAbs < (N a).natAbs
      have := N_le_N_mul_left a hb
      have := N_nonneg a
      omega }

lemma isUnit_iff_N (z : E) : IsUnit z ↔ N z = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  have := N_nonneg z
  constructor
  · rintro (h | h)
    · exact h
    · change N z = -1 at h; omega
  · exact Or.inl

lemma prime_of_N_prime (π : E) (h : Nat.Prime (N π).natAbs) : Prime π := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · intro hu
    rw [isUnit_iff_N] at hu
    rw [hu] at h
    exact Nat.not_prime_one h
  · intro a b hab
    have : (N a).natAbs * (N b).natAbs = (N π).natAbs := by
      rw [hab, map_mul, Int.natAbs_mul]
    rw [← this] at h
    have ha := N_nonneg a
    have hb := N_nonneg b
    rcases Nat.prime_mul_iff.1 h with ⟨_, hb'⟩ | ⟨_, ha'⟩
    · right; rw [isUnit_iff_N]; omega
    · left; rw [isUnit_iff_N]; omega

lemma N_cast (z : E) : ((N z : ℤ) : E) = z * star z := by
  rw [← algebraMap_norm_eq_mul_star]; rfl

lemma natCast_dvd_iff (p : ℕ) (z : E) : (p : E) ∣ z ↔ (p : ℤ) ∣ z.re ∧ (p : ℤ) ∣ z.im := by
  rw [← algebraMap_dvd_iff]; rfl

/-! ### Sets of elements of given norm -/

/-- Eisenstein integers of norm `k`. -/
def S (k : ℤ) : Set E := {z | N z = k}

lemma mem_S {k : ℤ} {z : E} : z ∈ S k ↔ N z = k := Iff.rfl

lemma S_finite (k : ℤ) : (S k).Finite := by
  have : S k ⊆ (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : E)) '' (Set.Icc (-2 * k) (2 * k) ×ˢ
      Set.Icc (-2 * k) (2 * k)) := by
    intro z hz
    refine ⟨(z.re, z.im), ?_, rfl⟩
    have h : z.re ^ 2 - z.re * z.im + z.im ^ 2 = k := by rw [← norm_eq]; exact hz
    have h1 := Int.le_self_sq z.re
    have h2 := Int.le_self_sq (-z.re)
    have h3 := Int.le_self_sq z.im
    have h4 := Int.le_self_sq (-z.im)
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg (2 * z.im - z.re)]
  exact (((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).image _).subset this

/-- Pairs `(a, b)` with `a² - ab + b² = n` correspond to Eisenstein integers of norm `n`. -/
def equivS (n : ℤ) : {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = n} ≃ S n where
  toFun p := ⟨⟨p.1.1, p.1.2⟩, by rw [mem_S, norm_eq]; exact p.2⟩
  invFun z := ⟨(z.1.re, z.1.im), by rw [← norm_eq]; exact z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `R n` = number of Eisenstein integers of norm `n`. -/
noncomputable def R (n : ℕ) : ℕ := (S n).ncard

lemma card_eq_R (n : ℕ) :
    Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = n} = R n := by
  rw [R, ← Nat.card_coe_set_eq]; exact Nat.card_congr (equivS n)

lemma image_mul_S (π : E) (hπ : π ≠ 0) (k : ℤ) :
    (π * ·) '' S k = {w | w ∈ S (N π * k) ∧ π ∣ w} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by rw [mem_S, map_mul, mem_S.1 hz], dvd_mul_right _ _⟩
  · rintro ⟨hw, z, rfl⟩
    refine ⟨z, ?_, rfl⟩
    have h1 : N π * N z = N π * k := by
      rw [← map_mul]; exact hw
    exact mul_left_cancel₀ (N_pos hπ).ne' h1

lemma ncard_image_mul (π : E) (hπ : π ≠ 0) (X : Set E) :
    ((π * ·) '' X).ncard = X.ncard :=
  Set.ncard_image_of_injective X (mul_right_injective₀ hπ)

lemma dvd_or_star_dvd {π w : E} (hπ : Prime π) (h : π ∣ w * star w) :
    π ∣ w ∨ star π ∣ w := by
  rcases hπ.dvd_or_dvd h with h | ⟨c, hc⟩
  · exact Or.inl h
  · right; exact ⟨star c, by rw [← star_mul', ← hc, star_star]⟩

lemma dvd_mul_star_of_mem {π w : E} {k : ℤ} (hw : w ∈ S (N π * k)) :
    π ∣ w * star w := by
  rw [← N_cast, mem_S.1 hw, Int.cast_mul, N_cast, mul_assoc]
  exact dvd_mul_right _ _

/-- Multiples of `p` among the Eisenstein integers of norm `p k`. -/
def D (p : ℕ) (k : ℤ) : Set E := {w | w ∈ S (p * k) ∧ (p : E) ∣ w}

lemma D_mul (p : ℕ) (hp : p ≠ 0) (m : ℤ) : D p (p * m) = ((p : E) * ·) '' S m := by
  have hp' : (p : E) ≠ 0 := by exact_mod_cast hp
  rw [image_mul_S _ hp', QuadraticAlgebra.norm_natCast, D, sq, mul_assoc]

lemma D_empty (p : ℕ) (hp : p ≠ 0) (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : D p k = ∅ := by
  ext w
  simp only [D, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hw ⟨z, rfl⟩
  apply h
  refine ⟨N z, ?_⟩
  have h1 : (p : ℤ) * k = p * (p * N z) := by
    rw [← mem_S.1 hw, map_mul, QuadraticAlgebra.norm_natCast, sq, mul_assoc]
  exact mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp) h1

lemma ncard_D_mul (p : ℕ) (hp : p ≠ 0) (m : ℤ) : (D p (p * m)).ncard = (S m).ncard := by
  rw [D_mul p hp, ncard_image_mul _ (by exact_mod_cast hp)]

lemma ncard_D_not_dvd (p : ℕ) (hp : p ≠ 0) (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : (D p k).ncard = 0 := by
  rw [D_empty p hp k h, Set.ncard_empty]

/-! ### Factorizations of a rational prime -/

lemma N_eq_of_factor (p : ℕ) (hp : p.Prime) (a b : E) (hab : (p : E) = a * b)
    (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) : N a = p := by
  rw [isUnit_iff_N] at ha hb
  have hN : N a * N b = (p : ℤ) ^ 2 := by
    rw [← map_mul, ← hab, QuadraticAlgebra.norm_natCast]
  have hA := N_nonneg a
  have hB := N_nonneg b
  have hNat : (N a).natAbs * (N b).natAbs = p ^ 2 := by
    have := congrArg Int.natAbs hN
    rwa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hNat)
  interval_cases i
  · rw [pow_zero] at hai; omega
  · rw [pow_one] at hai; omega
  · rw [hai] at hNat
    have : (N b).natAbs = 1 := by
      have hp2 : 0 < p ^ 2 := by have := hp.pos; positivity
      nlinarith
    omega

/-! ### Inert primes `p ≡ 2 mod 3` -/

lemma N_ne_of_two (p : ℕ) (h2 : p % 3 = 2) (z : E) : N z ≠ p := by
  intro h
  have h' : ((N z : ℤ) : ZMod 3) = ((p : ℤ) : ZMod 3) := by rw [h]
  rw [norm_eq] at h'
  push_cast at h'
  have hp : ((p : ℕ) : ZMod 3) = 2 := by rw [← ZMod.natCast_mod, h2]; rfl
  rw [hp] at h'
  generalize (z.re : ZMod 3) = a at h'
  generalize (z.im : ZMod 3) = b at h'
  revert a b; decide

lemma prime_of_two (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) : Prime (p : E) := by
  apply Irreducible.prime
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_N, QuadraticAlgebra.norm_natCast]
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  · intro a b hab
    by_contra hcon
    push Not at hcon
    exact N_ne_of_two p h2 a (N_eq_of_factor p hp a b hab hcon.1 hcon.2)

lemma S_eq_D_of_two (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) (k : ℤ) : S (p * k) = D p k := by
  have hpr : Prime (p : E) := prime_of_two p hp h2
  ext w
  refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
  have hdvd : (p : E) ∣ w * star w := by
    rw [← N_cast, mem_S.1 hw, Int.cast_mul, Int.cast_natCast]
    exact dvd_mul_right _ _
  rcases dvd_or_star_dvd hpr hdvd with h | h
  · exact h
  · simpa using h

/-! ### Split primes `p ≡ 1 mod 3` -/

lemma exists_dvd_quad (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 + t + 1 := by
  have := Fact.mk hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]; have := hp.two_le; omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by intro h; rw [h, orderOf_one] at hg; norm_num at hg
  set x : ZMod p := (g : ZMod p) with hxdef
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hx1 : x ≠ 1 := fun h => hg1 (Units.ext h)
  have hq : x ^ 2 + x + 1 = 0 := by
    have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hx1
    · exact h
  refine ⟨(x.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hq

lemma not_prime_of_one (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) : ¬ Prime (p : E) := by
  intro hpr
  obtain ⟨t, ht⟩ := exists_dvd_quad p hp h1
  have hdvd : (p : E) ∣ (⟨t, -1⟩ : E) * star (⟨t, -1⟩ : E) := by
    rw [← N_cast, norm_mk]
    obtain ⟨c, hc⟩ := ht
    refine ⟨(c : E), ?_⟩
    rw [show t ^ 2 - t * -1 + (-1) ^ 2 = t ^ 2 + t + 1 by ring, hc]; push_cast; ring
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hpr.dvd_or_dvd hdvd with h | h
  · rw [natCast_dvd_iff] at h
    exact hp1 ((dvd_neg).1 h.2)
  · rw [natCast_dvd_iff] at h
    exact hp1 (by simpa using h.2)

lemma exists_norm_eq (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ x y : ℤ, x ^ 2 - x * y + y ^ 2 = p := by
  have hni : ¬ Irreducible (p : E) := fun h => not_prime_of_one p hp h1 h.prime
  rw [irreducible_iff] at hni
  push Not at hni
  have hnu : ¬ IsUnit (p : E) := by
    rw [isUnit_iff_N, QuadraticAlgebra.norm_natCast]
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  obtain ⟨a, b, hab, ha, hb⟩ := hni hnu
  refine ⟨a.re, a.im, ?_⟩
  rw [← norm_eq]
  exact N_eq_of_factor p hp a b hab ha hb

lemma N_dvd_N {a b : E} (h : a ∣ b) : N a ∣ N b := by
  obtain ⟨c, rfl⟩ := h; exact ⟨N c, map_mul _ _ _⟩

section split

variable (p : ℕ) (x y : ℤ)

lemma star_dvd_self_false (hp : p.Prime) (h1 : p % 3 = 1) (hxy : x ^ 2 - x * y + y ^ 2 = p) :
    ¬ star (⟨x, y⟩ : E) ∣ ⟨x, y⟩ := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnorm : N (star (⟨x, y⟩ : E)) = p := by
    rw [QuadraticAlgebra.norm_star, norm_mk]; exact hxy
  have hx : star (⟨x, y⟩ : E) ∣ ⟨2 * x - y, 0⟩ := by
    have : (⟨2 * x - y, 0⟩ : E) = ⟨x, y⟩ + star ⟨x, y⟩ := by
      ext <;> simp; ring
    rw [this]; exact dvd_add h dvd_rfl
  have hy : star (⟨x, y⟩ : E) ∣ ⟨y, 2 * y⟩ := by
    have : (⟨y, 2 * y⟩ : E) = ⟨x, y⟩ - star ⟨x, y⟩ := by
      ext <;> simp; ring
    rw [this]; exact dvd_sub h dvd_rfl
  have hx' := N_dvd_N hx
  have hy' := N_dvd_N hy
  rw [hnorm, norm_mk] at hx' hy'
  have h3 : ¬ (p : ℤ) ∣ 3 := by
    intro h3
    have : p ∣ 3 := by exact_mod_cast h3
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    interval_cases p <;> simp_all
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h2
    have : p ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    interval_cases p; simp_all
  have hpy : (p : ℤ) ∣ y := by
    have : (p : ℤ) ∣ 3 * y ^ 2 := by convert hy' using 1; ring
    exact hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd this).resolve_left h3)
  have hpx : (p : ℤ) ∣ x := by
    have : (p : ℤ) ∣ (2 * x - y) ^ 2 := by convert hx' using 1; ring
    have h2x : (p : ℤ) ∣ 2 * x := by
      have := hpZ.dvd_of_dvd_pow this
      have := dvd_add this hpy
      simpa using this
    exact (hpZ.dvd_or_dvd h2x).resolve_left h2
  obtain ⟨a, rfl⟩ := hpx
  obtain ⟨b, rfl⟩ := hpy
  have : (p : ℤ) * (p * (a ^ 2 - a * b + b ^ 2)) = p * 1 := by linear_combination hxy
  have h1' := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
  have : (p : ℤ) ∣ 1 := ⟨_, h1'.symm⟩
  have : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

lemma norm_mk_eq (hxy : x ^ 2 - x * y + y ^ 2 = p) : N (⟨x, y⟩ : E) = p := by
  rw [norm_mk]; exact hxy

lemma norm_star_mk_eq (hxy : x ^ 2 - x * y + y ^ 2 = p) : N (star (⟨x, y⟩ : E)) = p := by
  rw [QuadraticAlgebra.norm_star, norm_mk]; exact hxy

lemma mk_ne_zero (hp : p.Prime) (hxy : x ^ 2 - x * y + y ^ 2 = p) : (⟨x, y⟩ : E) ≠ 0 := by
  intro h
  have := norm_mk_eq p x y hxy
  rw [h, QuadraticAlgebra.norm_zero] at this
  exact hp.ne_zero (by exact_mod_cast this.symm)

lemma star_mk_ne_zero (hp : p.Prime) (hxy : x ^ 2 - x * y + y ^ 2 = p) :
    star (⟨x, y⟩ : E) ≠ 0 := by
  intro h
  have := norm_star_mk_eq p x y hxy
  rw [h, QuadraticAlgebra.norm_zero] at this
  exact hp.ne_zero (by exact_mod_cast this.symm)

lemma dvd_of_both_dvd (hp : p.Prime) (h1 : p % 3 = 1) (hxy : x ^ 2 - x * y + y ^ 2 = p) (w : E)
    (ha : (⟨x, y⟩ : E) ∣ w) (hb : star (⟨x, y⟩ : E) ∣ w) : (p : E) ∣ w := by
  obtain ⟨u, rfl⟩ := ha
  have hpr : Prime (star (⟨x, y⟩ : E)) := by
    apply prime_of_N_prime
    rw [norm_star_mk_eq p x y hxy, Int.natAbs_natCast]; exact hp
  rcases hpr.dvd_or_dvd hb with h | ⟨v, rfl⟩
  · exact absurd h (star_dvd_self_false p x y hp h1 hxy)
  · refine ⟨v, ?_⟩
    rw [← mul_assoc, ← N_cast, norm_mk_eq p x y hxy, Int.cast_natCast]

lemma S_split (hp : p.Prime) (hxy : x ^ 2 - x * y + y ^ 2 = p) (k : ℤ) :
    S (p * k) = ((⟨x, y⟩ : E) * ·) '' S k ∪ (star (⟨x, y⟩ : E) * ·) '' S k := by
  rw [image_mul_S _ (mk_ne_zero p x y hp hxy), image_mul_S _ (star_mk_ne_zero p x y hp hxy),
    norm_mk_eq p x y hxy, norm_star_mk_eq p x y hxy]
  ext w
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hw
    have hpr : Prime (⟨x, y⟩ : E) := by
      apply prime_of_N_prime
      rw [norm_mk_eq p x y hxy, Int.natAbs_natCast]; exact hp
    have hw' : w ∈ S (N (⟨x, y⟩ : E) * k) := by
      rw [norm_mk_eq p x y hxy]; exact hw
    rcases dvd_or_star_dvd hpr (dvd_mul_star_of_mem hw') with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  · rintro (h | h) <;> exact h.1

lemma inter_split (hp : p.Prime) (h1 : p % 3 = 1) (hxy : x ^ 2 - x * y + y ^ 2 = p) (k : ℤ) :
    ((⟨x, y⟩ : E) * ·) '' S k ∩ (star (⟨x, y⟩ : E) * ·) '' S k = D p k := by
  rw [image_mul_S _ (mk_ne_zero p x y hp hxy), image_mul_S _ (star_mk_ne_zero p x y hp hxy),
    norm_mk_eq p x y hxy, norm_star_mk_eq p x y hxy]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, D]
  constructor
  · rintro ⟨⟨hw, ha⟩, -, hb⟩
    exact ⟨hw, dvd_of_both_dvd p x y hp h1 hxy w ha hb⟩
  · rintro ⟨hw, hd⟩
    have hpe : (p : E) = ⟨x, y⟩ * star ⟨x, y⟩ := by
      rw [← N_cast, norm_mk_eq p x y hxy, Int.cast_natCast]
    refine ⟨⟨hw, ?_⟩, hw, ?_⟩
    · exact dvd_trans ⟨_, hpe⟩ hd
    · exact dvd_trans ⟨_, hpe.trans (mul_comm _ _)⟩ hd

lemma ncard_split (hp : p.Prime) (h1 : p % 3 = 1) (hxy : x ^ 2 - x * y + y ^ 2 = p) (k : ℤ) :
    (S (p * k)).ncard + (D p k).ncard = 2 * (S k).ncard := by
  rw [S_split p x y hp hxy, ← inter_split p x y hp h1 hxy,
    Set.ncard_union_add_ncard_inter _ _ ((S_finite k).image _) ((S_finite k).image _),
    ncard_image_mul _ (mk_ne_zero p x y hp hxy), ncard_image_mul _ (star_mk_ne_zero p x y hp hxy)]
  ring

end split

/-! ### The ramified prime `3 = -ω² (1 - ω)²` -/

/-- `λ = 1 - ω`, of norm `3`. -/
def lam : E := ⟨1, -1⟩

lemma N_lam : N lam = 3 := by rw [lam, norm_mk]; norm_num

lemma lam_ne_zero : lam ≠ 0 := by
  intro h; have := N_lam; rw [h, QuadraticAlgebra.norm_zero] at this; norm_num at this

lemma S_three_mul (k : ℤ) : S (3 * k) = (lam * ·) '' S k := by
  rw [image_mul_S _ lam_ne_zero, N_lam]
  ext w
  refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
  have hpr : Prime lam := by
    apply prime_of_N_prime; rw [N_lam]; norm_num
  have hw' : w ∈ S (N lam * k) := by rw [N_lam]; exact hw
  rcases dvd_or_star_dvd hpr (dvd_mul_star_of_mem hw') with h | h
  · exact h
  · refine dvd_trans ⟨⟨1, 1⟩, ?_⟩ h
    ext <;> simp [lam]

/-! ### Norm one: the six units -/

lemma S_one : S 1 = {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩} := by
  ext z
  rw [mem_S, norm_eq]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg (2 * z.im - z.re), Int.le_self_sq z.re]
    have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg (2 * z.im - z.re), Int.le_self_sq (-z.re)]
    have h3 : z.im ≤ 1 := by nlinarith [sq_nonneg (2 * z.re - z.im), Int.le_self_sq z.im]
    have h4 : -1 ≤ z.im := by nlinarith [sq_nonneg (2 * z.re - z.im), Int.le_self_sq (-z.im)]
    obtain ⟨a, b⟩ := z
    simp only at h h1 h2 h3 h4
    simp only [QuadraticAlgebra.mk.injEq]
    interval_cases a <;> interval_cases b <;> simp_all
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

lemma R_one : R 1 = 6 := by
  rw [R, Nat.cast_one, S_one]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_pair] <;>
    simp [QuadraticAlgebra.ext_iff]

/-! ### Recursions for `R` -/

lemma R_three_mul (k : ℕ) : R (3 * k) = R k := by
  rw [R, R, Nat.cast_mul, Nat.cast_ofNat, S_three_mul, ncard_image_mul _ lam_ne_zero]

lemma R_two_dvd (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) (m : ℕ) : R (p * (p * m)) = R m := by
  rw [R, R, Nat.cast_mul, S_eq_D_of_two p hp h2, Nat.cast_mul, ncard_D_mul p hp.ne_zero]

lemma R_two_not_dvd (p : ℕ) (hp : p.Prime) (h2 : p % 3 = 2) (k : ℕ) (hk : ¬ p ∣ k) :
    R (p * k) = 0 := by
  rw [R, Nat.cast_mul, S_eq_D_of_two p hp h2, ncard_D_not_dvd p hp.ne_zero]
  exact_mod_cast hk

lemma R_one_dvd (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) (m : ℕ) :
    R (p * (p * m)) + R m = 2 * R (p * m) := by
  obtain ⟨x, y, hxy⟩ := exists_norm_eq p hp h1
  have := ncard_split p x y hp h1 hxy (p * m)
  rw [ncard_D_mul p hp.ne_zero] at this
  simpa only [R, Nat.cast_mul] using this

lemma R_one_not_dvd (p : ℕ) (hp : p.Prime) (h1 : p % 3 = 1) (k : ℕ) (hk : ¬ p ∣ k) :
    R (p * k) = 2 * R k := by
  obtain ⟨x, y, hxy⟩ := exists_norm_eq p hp h1
  have := ncard_split p x y hp h1 hxy k
  rw [ncard_D_not_dvd p hp.ne_zero _ (by exact_mod_cast hk), add_zero] at this
  simpa only [R, Nat.cast_mul] using this

end Hexagonal

/-- The nontrivial Dirichlet character mod `3`, as a function `ℕ → ℤ`. -/
def χ₃ (d : ℕ) : ℤ := if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

lemma χ₃_mul (a b : ℕ) : χ₃ (a * b) = χ₃ a * χ₃ b := by
  have ha := Nat.mod_lt a (show 0 < 3 by norm_num)
  have hb := Nat.mod_lt b (show 0 < 3 by norm_num)
  unfold χ₃
  rw [Nat.mul_mod]
  interval_cases a % 3 <;> interval_cases b % 3 <;> simp

lemma χ₃_of_one {p : ℕ} (h : p % 3 = 1) : χ₃ p = 1 := by simp [χ₃, h]

lemma χ₃_of_two {p : ℕ} (h : p % 3 = 2) : χ₃ p = -1 := by simp [χ₃, h]

lemma χ₃_three : χ₃ 3 = 0 := by decide

namespace Hexagonal

/-! ### The divisor sum `F n = ∑_{d ∣ n} χ₃(d)` -/

/-- `F n = ∑_{d ∣ n} χ₃ d`. -/
def F (n : ℕ) : ℤ := ∑ d ∈ n.divisors, χ₃ d

lemma divisors_prime_mul (p k : ℕ) (hp : p.Prime) :
    (p * k).divisors = k.divisors ∪ k.divisors.image (p * ·) := by
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hpk⟩
    have hk : k ≠ 0 := by rintro rfl; simp at hpk
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      right; exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd, hk⟩, rfl⟩
    · left
      have hc : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
      exact ⟨hc.dvd_of_dvd_mul_left hd, hk⟩
  · rintro (⟨hd, hk⟩ | ⟨e, ⟨he, hk⟩, rfl⟩)
    · exact ⟨Dvd.dvd.mul_left hd p, mul_ne_zero hp.ne_zero hk⟩
    · exact ⟨mul_dvd_mul_left p he, mul_ne_zero hp.ne_zero hk⟩

lemma divisors_inter_not_dvd (p k : ℕ) (hk : ¬ p ∣ k) :
    k.divisors ∩ k.divisors.image (p * ·) = ∅ := by
  ext d
  simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors, Finset.notMem_empty,
    iff_false, not_and]
  rintro ⟨hd, -⟩ ⟨e, -, rfl⟩
  exact hk (dvd_trans (dvd_mul_right p e) hd)

lemma divisors_inter_dvd (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    (p * m).divisors ∩ (p * m).divisors.image (p * ·) = m.divisors.image (p * ·) := by
  ext d
  simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors]
  have hpm : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm
  constructor
  · rintro ⟨⟨hd, -⟩, e, -, rfl⟩
    exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd, hm⟩, rfl⟩
  · rintro ⟨e, ⟨he, -⟩, rfl⟩
    exact ⟨⟨mul_dvd_mul_left p he, hpm⟩, e, ⟨Dvd.dvd.mul_left he p, hpm⟩, rfl⟩

lemma sum_image_mul (p : ℕ) (hp : p.Prime) (s : Finset ℕ) :
    ∑ d ∈ s.image (p * ·), χ₃ d = χ₃ p * ∑ d ∈ s, χ₃ d := by
  rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => χ₃_mul p d

lemma F_prime_mul_not_dvd (p k : ℕ) (hp : p.Prime) (hk : ¬ p ∣ k) :
    F (p * k) = (1 + χ₃ p) * F k := by
  have := Finset.sum_union_inter (s₁ := k.divisors) (s₂ := k.divisors.image (p * ·))
    (f := χ₃)
  rw [← divisors_prime_mul p k hp, divisors_inter_not_dvd p k hk, Finset.sum_empty, add_zero,
    sum_image_mul p hp] at this
  rw [F, this, F]; ring

lemma F_prime_mul_dvd (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    F (p * (p * m)) + χ₃ p * F m = (1 + χ₃ p) * F (p * m) := by
  have := Finset.sum_union_inter (s₁ := (p * m).divisors) (s₂ := (p * m).divisors.image (p * ·))
    (f := χ₃)
  rw [← divisors_prime_mul p _ hp, divisors_inter_dvd p m hp hm, sum_image_mul p hp,
    sum_image_mul p hp] at this
  simp only [F]; rw [this]; ring

lemma F_one : F 1 = 1 := by simp [F, χ₃]

/-! ### Main induction -/

theorem R_eq_six_mul_F (n : ℕ) (hn : 0 < n) : (R n : ℤ) = 6 * F n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [R_one, F_one]; norm_num
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨k, hk⟩ := n.minFac_dvd
  generalize n.minFac = p at hp hk
  subst hk
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hn
  have hkn : k < p * k := lt_mul_left hk0 hp.one_lt
  have hcases : p = 3 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
    by_cases h3 : p = 3
    · exact Or.inl h3
    · right
      have : p % 3 ≠ 0 := by
        intro h0
        exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
  have hχ : (p = 3 ∧ χ₃ p = 0) ∨ (p % 3 = 1 ∧ χ₃ p = 1) ∨ (p % 3 = 2 ∧ χ₃ p = -1) := by
    rcases hcases with h3 | h1 | h2
    · subst h3; exact Or.inl ⟨rfl, χ₃_three⟩
    · exact Or.inr (Or.inl ⟨h1, χ₃_of_one h1⟩)
    · exact Or.inr (Or.inr ⟨h2, χ₃_of_two h2⟩)
  by_cases hpk : p ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    have hm0 : 0 < m := Nat.pos_of_mul_pos_left hk0
    have hmk : m < p * m := lt_mul_left hm0 hp.one_lt
    have ih1 := ih (p * m) hkn hk0
    have ih2 := ih m (hmk.trans hkn) hm0
    have hF := F_prime_mul_dvd p m hp hm0.ne'
    rcases hχ with ⟨h3, hc⟩ | ⟨h1, hc⟩ | ⟨h2, hc⟩
    · subst h3
      rw [R_three_mul, ih1]
      rw [hc] at hF; linarith
    · have hR := R_one_dvd p hp h1 m
      rw [hc] at hF
      have hR' : (R (p * (p * m)) : ℤ) + R m = 2 * R (p * m) := by exact_mod_cast hR
      linarith
    · rw [R_two_dvd p hp h2, ih2]
      rw [hc] at hF; linarith
  · have hF := F_prime_mul_not_dvd p k hp hpk
    have ih1 := ih k hkn hk0
    rcases hχ with ⟨h3, hc⟩ | ⟨h1, hc⟩ | ⟨h2, hc⟩
    · subst h3
      rw [R_three_mul, ih1, hF, hc]; ring
    · rw [R_one_not_dvd p hp h1 k hpk, hF, hc]; push_cast; rw [ih1]; ring
    · rw [R_two_not_dvd p hp h2 k hpk, hF, hc]; ring

end Hexagonal

open Hexagonal in
/-- **Representation numbers of the hexagonal (A₂) lattice**: for `n > 0`,
`#{(a, b) ∈ ℤ² | a² - ab + b² = n} = 6 ∑_{d ∣ n} χ₋₃(d)`. -/
theorem card_hexagonal (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = n} : ℤ) =
      6 * ∑ d ∈ n.divisors, χ₃ d := by
  rw [card_eq_R]; exact R_eq_six_mul_F n hn

/-! ### Sanity checks -/

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = 1} = 6 := by
  have h := card_hexagonal 1 (by norm_num)
  have hs : ∑ d ∈ (1 : ℕ).divisors, χ₃ d = 1 := by decide
  rw [hs] at h
  exact_mod_cast h

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = 3} = 6 := by
  have h := card_hexagonal 3 (by norm_num)
  have hs : ∑ d ∈ (3 : ℕ).divisors, χ₃ d = 1 := by decide
  rw [hs] at h
  exact_mod_cast h

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = 7} = 12 := by
  have h := card_hexagonal 7 (by norm_num)
  have hs : ∑ d ∈ (7 : ℕ).divisors, χ₃ d = 2 := by decide
  rw [hs] at h
  exact_mod_cast h

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = 2} = 0 := by
  have h := card_hexagonal 2 (by norm_num)
  have hs : ∑ d ∈ (2 : ℕ).divisors, χ₃ d = 0 := by decide
  rw [hs] at h
  exact_mod_cast h

end Fugue
