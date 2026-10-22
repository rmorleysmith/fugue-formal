import Mathlib

set_option autoImplicit false

/-!
# Jacobi's two-square theorem

We prove `r₂(n) = 4 ∑_{d ∣ n} χ₋₄(d)` for `n > 0` (`Fugue.card_sq_add_sq`), where
`r₂(n) = #{(a, b) ∈ ℤ² | a² + b² = n}`.

## Proof outline

Let `R n = #{z ∈ ℤ[i] | N z = n}` and `F n = ∑_{d ∣ n} χ₄ d`. For a prime `p` both satisfy
the recursion
  `X (p k) = (1 + χ₄ p) X k - χ₄ p · [p ∣ k] X (k / p)`
(with the `[p ∣ k]` term absent when `p ∤ k`):
* for `F` this is inclusion–exclusion on `divisors (p k) = divisors k ∪ p • divisors k`;
* for `R` it comes from the arithmetic of `ℤ[i]`:
  - `p = 2`: every `w` with `N w = 2k` is divisible by `1 + i`, so `R (2k) = R k`;
  - `p ≡ 3 (mod 4)`: `p` is prime in `ℤ[i]`, so every `w` with `N w = p k` is divisible by `p`;
  - `p ≡ 1 (mod 4)`: `p = π π̄` with `π, π̄` non-associated primes; `{N w = p k}` is the union
    of `π · {N z = k}` and `π̄ · {N z = k}`, whose intersection is `p · {N z = k / p}`.
Strong induction on `n` (splitting off `n.minFac`) then gives `R n = 4 F n`, since `R 1 = 4`
and `F 1 = 1`.
-/

namespace Fugue

namespace TwoSquares

local notation "ℤ[i]" => GaussianInt

/-- Gaussian integers of norm `k`. -/
def S (k : ℤ) : Set ℤ[i] := {z | Zsqrtd.norm z = k}

lemma mem_S {k : ℤ} {z : ℤ[i]} : z ∈ S k ↔ Zsqrtd.norm z = k := Iff.rfl

lemma norm_eq_sq (z : ℤ[i]) : Zsqrtd.norm z = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma S_finite (k : ℤ) : (S k).Finite := by
  have : S k ⊆ (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : ℤ[i])) '' (Set.Icc (-k) k ×ˢ Set.Icc (-k) k) := by
    intro z hz
    refine ⟨(z.re, z.im), ?_, rfl⟩
    have h : z.re ^ 2 + z.im ^ 2 = k := by rw [← norm_eq_sq]; exact hz
    have h1 := Int.le_self_sq z.re
    have h2 := Int.le_self_sq (-z.re)
    have h3 := Int.le_self_sq z.im
    have h4 := Int.le_self_sq (-z.im)
    simp only [Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  exact (((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).image _).subset this

/-- Pairs `(a, b)` with `a² + b² = n` correspond to Gaussian integers of norm `n`. -/
def equivS (n : ℤ) : {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} ≃ S n where
  toFun p := ⟨⟨p.1.1, p.1.2⟩, by rw [mem_S, norm_eq_sq]; exact p.2⟩
  invFun z := ⟨(z.1.re, z.1.im), by rw [← norm_eq_sq]; exact z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `R n` = number of Gaussian integers of norm `n`. -/
noncomputable def R (n : ℕ) : ℕ := (S n).ncard

lemma card_eq_R (n : ℕ) : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} = R n := by
  rw [R, ← Nat.card_coe_set_eq]; exact Nat.card_congr (equivS n)

/-- Multiplying by a nonzero `π` identifies `S k` with the multiples of `π` of norm `N(π) k`. -/
lemma image_mul_S (π : ℤ[i]) (hπ : π ≠ 0) (k : ℤ) :
    (π * ·) '' S k = {w | w ∈ S (Zsqrtd.norm π * k) ∧ π ∣ w} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by rw [mem_S, Zsqrtd.norm_mul, mem_S.1 hz], dvd_mul_right _ _⟩
  · rintro ⟨hw, z, rfl⟩
    refine ⟨z, ?_, rfl⟩
    have h1 : Zsqrtd.norm π * Zsqrtd.norm z = Zsqrtd.norm π * k := by
      rw [← Zsqrtd.norm_mul]; exact hw
    have h2 : Zsqrtd.norm π ≠ 0 := by rwa [Ne, GaussianInt.norm_eq_zero]
    exact mul_left_cancel₀ h2 h1

lemma ncard_image_mul (π : ℤ[i]) (hπ : π ≠ 0) (X : Set ℤ[i]) :
    ((π * ·) '' X).ncard = X.ncard :=
  Set.ncard_image_of_injective X (mul_right_injective₀ hπ)

lemma prime_of_norm_prime (π : ℤ[i]) (h : Nat.Prime (Zsqrtd.norm π).natAbs) : Prime π := by
  apply Irreducible.prime
  refine ⟨?_, ?_⟩
  · intro hu
    rw [← Zsqrtd.norm_eq_one_iff] at hu
    rw [hu] at h
    exact Nat.not_prime_one h
  · intro a b hab
    have : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = (Zsqrtd.norm π).natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rw [← this] at h
    rcases Nat.prime_mul_iff.1 h with ⟨_, hb⟩ | ⟨_, ha⟩
    · right; exact Zsqrtd.norm_eq_one_iff.1 hb
    · left; exact Zsqrtd.norm_eq_one_iff.1 ha

lemma dvd_or_star_dvd {π w : ℤ[i]} (hπ : Prime π) (h : π ∣ w * star w) :
    π ∣ w ∨ star π ∣ w := by
  rcases hπ.dvd_or_dvd h with h | ⟨c, hc⟩
  · exact Or.inl h
  · right; exact ⟨star c, by rw [← star_mul', ← hc, star_star]⟩

lemma dvd_mul_star_of_mem {π w : ℤ[i]} {k : ℤ} (hw : w ∈ S (Zsqrtd.norm π * k)) :
    π ∣ w * star w := by
  rw [← Zsqrtd.norm_eq_mul_conj, mem_S.1 hw, Int.cast_mul, Zsqrtd.norm_eq_mul_conj, mul_assoc]
  exact dvd_mul_right _ _

/-- Multiples of `p` among the Gaussian integers of norm `p k`. -/
def D (p : ℕ) (k : ℤ) : Set ℤ[i] := {w | w ∈ S (p * k) ∧ (p : ℤ[i]) ∣ w}

lemma D_mul (p : ℕ) (hp : p ≠ 0) (m : ℤ) : D p (p * m) = ((p : ℤ[i]) * ·) '' S m := by
  have hp' : (p : ℤ[i]) ≠ 0 := by exact_mod_cast hp
  rw [image_mul_S _ hp', Zsqrtd.norm_natCast, D, mul_assoc]

lemma D_empty (p : ℕ) (hp : p ≠ 0) (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : D p k = ∅ := by
  ext w
  simp only [D, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hw ⟨z, rfl⟩
  apply h
  refine ⟨Zsqrtd.norm z, ?_⟩
  have h1 : (p : ℤ) * k = p * (p * Zsqrtd.norm z) := by
    rw [← mem_S.1 hw, Zsqrtd.norm_mul, Zsqrtd.norm_natCast, mul_assoc]
  exact mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp) h1

lemma ncard_D_mul (p : ℕ) (hp : p ≠ 0) (m : ℤ) : (D p (p * m)).ncard = (S m).ncard := by
  rw [D_mul p hp, ncard_image_mul _ (by exact_mod_cast hp)]

lemma ncard_D_not_dvd (p : ℕ) (hp : p ≠ 0) (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : (D p k).ncard = 0 := by
  rw [D_empty p hp k h, Set.ncard_empty]

/-! ### Inert primes `p ≡ 3 mod 4` -/

lemma S_eq_D_of_three (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (k : ℤ) : S (p * k) = D p k := by
  have := Fact.mk hp
  have hpr : Prime (p : ℤ[i]) := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p h3
  ext w
  refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
  have hdvd : (p : ℤ[i]) ∣ w * star w := by
    rw [← Zsqrtd.norm_eq_mul_conj, mem_S.1 hw, Int.cast_mul, Int.cast_natCast]
    exact dvd_mul_right _ _
  rcases dvd_or_star_dvd hpr hdvd with h | h
  · exact h
  · simpa using h

/-! ### Split primes `p ≡ 1 mod 4` -/

section split

variable (p : ℕ) (x y : ℤ)

lemma star_dvd_self_false (hp : p.Prime) (h1 : p % 4 = 1) (hxy : x ^ 2 + y ^ 2 = p) :
    ¬ star (⟨x, y⟩ : ℤ[i]) ∣ ⟨x, y⟩ := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnorm : Zsqrtd.norm (star (⟨x, y⟩ : ℤ[i])) = p := by
    rw [Zsqrtd.norm_conj, norm_eq_sq]; exact hxy
  have hn : ∀ a b : ℤ[i], a ∣ b → Zsqrtd.norm a ∣ Zsqrtd.norm b := by
    rintro a b ⟨c, rfl⟩; exact ⟨Zsqrtd.norm c, Zsqrtd.norm_mul _ _⟩
  have hx : star (⟨x, y⟩ : ℤ[i]) ∣ ⟨2 * x, 0⟩ := by
    have : (⟨2 * x, 0⟩ : ℤ[i]) = ⟨x, y⟩ + star ⟨x, y⟩ := by
      ext <;> simp [Zsqrtd.star_mk, two_mul]
    rw [this]; exact dvd_add h dvd_rfl
  have hy : star (⟨x, y⟩ : ℤ[i]) ∣ ⟨0, 2 * y⟩ := by
    have : (⟨0, 2 * y⟩ : ℤ[i]) = ⟨x, y⟩ - star ⟨x, y⟩ := by
      ext <;> simp [Zsqrtd.star_mk, two_mul]
    rw [this]; exact dvd_sub h dvd_rfl
  have hx' := hn _ _ hx
  have hy' := hn _ _ hy
  rw [hnorm, norm_eq_sq] at hx' hy'
  simp only at hx' hy'
  have h4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have : p ∣ 4 := by exact_mod_cast h4
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    interval_cases p <;> simp_all
  have hpx : (p : ℤ) ∣ x := by
    have : (p : ℤ) ∣ 4 * x ^ 2 := by convert hx' using 1; ring
    exact hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd this).resolve_left h4)
  have hpy : (p : ℤ) ∣ y := by
    have : (p : ℤ) ∣ 4 * y ^ 2 := by convert hy' using 1; ring
    exact hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd this).resolve_left h4)
  obtain ⟨a, rfl⟩ := hpx
  obtain ⟨b, rfl⟩ := hpy
  have : (p : ℤ) * (p * (a ^ 2 + b ^ 2)) = p * 1 := by linear_combination hxy
  have h1' := mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
  have : (p : ℤ) ∣ 1 := ⟨_, h1'.symm⟩
  have : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

lemma norm_mk_eq (hxy : x ^ 2 + y ^ 2 = p) : Zsqrtd.norm (⟨x, y⟩ : ℤ[i]) = p := by
  rw [norm_eq_sq]; exact hxy

lemma norm_star_mk_eq (hxy : x ^ 2 + y ^ 2 = p) : Zsqrtd.norm (star (⟨x, y⟩ : ℤ[i])) = p := by
  rw [Zsqrtd.norm_conj, norm_eq_sq]; exact hxy

lemma mk_ne_zero (hp : p.Prime) (hxy : x ^ 2 + y ^ 2 = p) : (⟨x, y⟩ : ℤ[i]) ≠ 0 := by
  intro h
  have := norm_mk_eq p x y hxy
  rw [h, Zsqrtd.norm_zero] at this
  exact hp.ne_zero (by exact_mod_cast this.symm)

lemma star_mk_ne_zero (hp : p.Prime) (hxy : x ^ 2 + y ^ 2 = p) : star (⟨x, y⟩ : ℤ[i]) ≠ 0 := by
  intro h
  have := norm_star_mk_eq p x y hxy
  rw [h, Zsqrtd.norm_zero] at this
  exact hp.ne_zero (by exact_mod_cast this.symm)

lemma dvd_of_both_dvd (hp : p.Prime) (h1 : p % 4 = 1) (hxy : x ^ 2 + y ^ 2 = p) (w : ℤ[i])
    (ha : (⟨x, y⟩ : ℤ[i]) ∣ w) (hb : star (⟨x, y⟩ : ℤ[i]) ∣ w) : (p : ℤ[i]) ∣ w := by
  obtain ⟨u, rfl⟩ := ha
  have hpr : Prime (star (⟨x, y⟩ : ℤ[i])) := by
    apply prime_of_norm_prime
    rw [norm_star_mk_eq p x y hxy, Int.natAbs_natCast]; exact hp
  rcases hpr.dvd_or_dvd hb with h | ⟨v, rfl⟩
  · exact absurd h (star_dvd_self_false p x y hp h1 hxy)
  · refine ⟨v, ?_⟩
    rw [← mul_assoc, ← Zsqrtd.norm_eq_mul_conj, norm_mk_eq p x y hxy, Int.cast_natCast]

lemma S_split (hp : p.Prime) (hxy : x ^ 2 + y ^ 2 = p) (k : ℤ) :
    S (p * k) = ((⟨x, y⟩ : ℤ[i]) * ·) '' S k ∪ (star (⟨x, y⟩ : ℤ[i]) * ·) '' S k := by
  rw [image_mul_S _ (mk_ne_zero p x y hp hxy), image_mul_S _ (star_mk_ne_zero p x y hp hxy),
    norm_mk_eq p x y hxy, norm_star_mk_eq p x y hxy]
  ext w
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro hw
    have hpr : Prime (⟨x, y⟩ : ℤ[i]) := by
      apply prime_of_norm_prime
      rw [norm_mk_eq p x y hxy, Int.natAbs_natCast]; exact hp
    have hw' : w ∈ S (Zsqrtd.norm (⟨x, y⟩ : ℤ[i]) * k) := by
      rw [norm_mk_eq p x y hxy]; exact hw
    rcases dvd_or_star_dvd hpr (dvd_mul_star_of_mem hw') with h | h
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨hw, h⟩
  · rintro (h | h) <;> exact h.1

lemma inter_split (hp : p.Prime) (h1 : p % 4 = 1) (hxy : x ^ 2 + y ^ 2 = p) (k : ℤ) :
    ((⟨x, y⟩ : ℤ[i]) * ·) '' S k ∩ (star (⟨x, y⟩ : ℤ[i]) * ·) '' S k = D p k := by
  rw [image_mul_S _ (mk_ne_zero p x y hp hxy), image_mul_S _ (star_mk_ne_zero p x y hp hxy),
    norm_mk_eq p x y hxy, norm_star_mk_eq p x y hxy]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, D]
  constructor
  · rintro ⟨⟨hw, ha⟩, -, hb⟩
    exact ⟨hw, dvd_of_both_dvd p x y hp h1 hxy w ha hb⟩
  · rintro ⟨hw, hd⟩
    have hpe : (p : ℤ[i]) = ⟨x, y⟩ * star ⟨x, y⟩ := by
      rw [← Zsqrtd.norm_eq_mul_conj, norm_mk_eq p x y hxy, Int.cast_natCast]
    refine ⟨⟨hw, ?_⟩, hw, ?_⟩
    · exact dvd_trans ⟨_, hpe⟩ hd
    · exact dvd_trans ⟨_, hpe.trans (mul_comm _ _)⟩ hd

lemma ncard_split (hp : p.Prime) (h1 : p % 4 = 1) (hxy : x ^ 2 + y ^ 2 = p) (k : ℤ) :
    (S (p * k)).ncard + (D p k).ncard = 2 * (S k).ncard := by
  rw [S_split p x y hp hxy, ← inter_split p x y hp h1 hxy,
    Set.ncard_union_add_ncard_inter _ _ ((S_finite k).image _) ((S_finite k).image _),
    ncard_image_mul _ (mk_ne_zero p x y hp hxy), ncard_image_mul _ (star_mk_ne_zero p x y hp hxy)]
  ring

end split

/-! ### The ramified prime `2` -/

lemma S_two_mul (k : ℤ) : S (2 * k) = ((⟨1, 1⟩ : ℤ[i]) * ·) '' S k := by
  have hn : Zsqrtd.norm (⟨1, 1⟩ : ℤ[i]) = 2 := by rw [norm_eq_sq]; norm_num
  have hne : (⟨1, 1⟩ : ℤ[i]) ≠ 0 := by intro h; rw [h, Zsqrtd.norm_zero] at hn; norm_num at hn
  rw [image_mul_S _ hne, hn]
  ext w
  refine ⟨fun hw => ⟨hw, ?_⟩, fun hw => hw.1⟩
  have hpr : Prime (⟨1, 1⟩ : ℤ[i]) := by
    apply prime_of_norm_prime; rw [hn]; norm_num
  have hw' : w ∈ S (Zsqrtd.norm (⟨1, 1⟩ : ℤ[i]) * k) := by rw [hn]; exact hw
  rcases dvd_or_star_dvd hpr (dvd_mul_star_of_mem hw') with h | h
  · exact h
  · refine dvd_trans ⟨⟨0, -1⟩, ?_⟩ h
    ext <;> simp [Zsqrtd.star_mk]

/-! ### Norm one -/

lemma S_one : S 1 = {⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} := by
  ext z
  rw [mem_S, norm_eq_sq]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.im, Int.le_self_sq z.re]
    have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg z.im, Int.le_self_sq (-z.re)]
    have h3 : z.im ≤ 1 := by nlinarith [sq_nonneg z.re, Int.le_self_sq z.im]
    have h4 : -1 ≤ z.im := by nlinarith [sq_nonneg z.re, Int.le_self_sq (-z.im)]
    obtain ⟨a, b⟩ := z
    simp only at h h1 h2 h3 h4
    simp only [Zsqrtd.mk.injEq]
    interval_cases a <;> interval_cases b <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num

lemma R_one : R 1 = 4 := by
  rw [R, Nat.cast_one, S_one]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair] <;>
    simp [Zsqrtd.ext_iff]

/-! ### Recursions for `R` -/

lemma R_two_mul (k : ℕ) : R (2 * k) = R k := by
  have hne : (⟨1, 1⟩ : ℤ[i]) ≠ 0 := by intro h; simpa using congrArg Zsqrtd.re h
  rw [R, R, Nat.cast_mul, Nat.cast_two, S_two_mul, ncard_image_mul _ hne]

lemma R_three_dvd (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (m : ℕ) : R (p * (p * m)) = R m := by
  rw [R, R, Nat.cast_mul, S_eq_D_of_three p hp h3, Nat.cast_mul, ncard_D_mul p hp.ne_zero]

lemma R_three_not_dvd (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) (k : ℕ) (hk : ¬ p ∣ k) :
    R (p * k) = 0 := by
  rw [R, Nat.cast_mul, S_eq_D_of_three p hp h3, ncard_D_not_dvd p hp.ne_zero]
  exact_mod_cast hk

lemma exists_sq_add_sq (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) :
    ∃ x y : ℤ, x ^ 2 + y ^ 2 = p := by
  have := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  exact ⟨a, b, by exact_mod_cast hab⟩

lemma R_one_dvd (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) (m : ℕ) :
    R (p * (p * m)) + R m = 2 * R (p * m) := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq p hp h1
  have := ncard_split p x y hp h1 hxy (p * m)
  rw [ncard_D_mul p hp.ne_zero] at this
  simpa only [R, Nat.cast_mul] using this

lemma R_one_not_dvd (p : ℕ) (hp : p.Prime) (h1 : p % 4 = 1) (k : ℕ) (hk : ¬ p ∣ k) :
    R (p * k) = 2 * R k := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq p hp h1
  have := ncard_split p x y hp h1 hxy k
  rw [ncard_D_not_dvd p hp.ne_zero _ (by exact_mod_cast hk), add_zero] at this
  simpa only [R, Nat.cast_mul] using this

/-! ### The divisor sum `F n = ∑_{d ∣ n} χ₄(d)` -/

/-- `F n = ∑_{d ∣ n} χ₄ d`. -/
def F (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ)

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
    ∑ d ∈ s.image (p * ·), (ZMod.χ₄ (d : ZMod 4) : ℤ) =
      ZMod.χ₄ (p : ZMod 4) * ∑ d ∈ s, (ZMod.χ₄ (d : ZMod 4) : ℤ) := by
  rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Nat.cast_mul, map_mul]

lemma F_prime_mul_not_dvd (p k : ℕ) (hp : p.Prime) (hk : ¬ p ∣ k) :
    F (p * k) = (1 + ZMod.χ₄ (p : ZMod 4)) * F k := by
  have := Finset.sum_union_inter (s₁ := k.divisors) (s₂ := k.divisors.image (p * ·))
    (f := fun d => (ZMod.χ₄ (d : ZMod 4) : ℤ))
  rw [← divisors_prime_mul p k hp, divisors_inter_not_dvd p k hk, Finset.sum_empty, add_zero,
    sum_image_mul p hp] at this
  rw [F, this, F]; ring

lemma F_prime_mul_dvd (p m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    F (p * (p * m)) + ZMod.χ₄ (p : ZMod 4) * F m =
      (1 + ZMod.χ₄ (p : ZMod 4)) * F (p * m) := by
  have := Finset.sum_union_inter (s₁ := (p * m).divisors) (s₂ := (p * m).divisors.image (p * ·))
    (f := fun d => (ZMod.χ₄ (d : ZMod 4) : ℤ))
  rw [← divisors_prime_mul p _ hp, divisors_inter_dvd p m hp hm, sum_image_mul p hp,
    sum_image_mul p hp] at this
  simp only [F]; rw [this]; ring

lemma F_one : F 1 = 1 := by simp [F]

lemma χ₄_two : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide

/-! ### Main induction -/

theorem R_eq_four_mul_F (n : ℕ) (hn : 0 < n) : (R n : ℤ) = 4 * F n := by
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
  have hcases : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · exact Or.inl h2
    · omega
  have hχ : (p = 2 ∧ ZMod.χ₄ (p : ZMod 4) = 0) ∨ (p % 4 = 1 ∧ ZMod.χ₄ (p : ZMod 4) = 1) ∨
      (p % 4 = 3 ∧ ZMod.χ₄ (p : ZMod 4) = -1) := by
    rcases hcases with h2 | h1 | h3
    · subst h2; exact Or.inl ⟨rfl, χ₄_two⟩
    · exact Or.inr (Or.inl ⟨h1, ZMod.χ₄_nat_one_mod_four h1⟩)
    · exact Or.inr (Or.inr ⟨h3, ZMod.χ₄_nat_three_mod_four h3⟩)
  by_cases hpk : p ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    have hm0 : 0 < m := Nat.pos_of_mul_pos_left hk0
    have hmk : m < p * m := lt_mul_left hm0 hp.one_lt
    have ih1 := ih (p * m) hkn hk0
    have ih2 := ih m (hmk.trans hkn) hm0
    have hF := F_prime_mul_dvd p m hp hm0.ne'
    rcases hχ with ⟨h2, hc⟩ | ⟨h1, hc⟩ | ⟨h3, hc⟩
    · subst h2
      rw [R_two_mul, ih1]
      rw [hc] at hF; linarith
    · have hR := R_one_dvd p hp h1 m
      rw [hc] at hF
      have hR' : (R (p * (p * m)) : ℤ) + R m = 2 * R (p * m) := by exact_mod_cast hR
      linarith
    · rw [R_three_dvd p hp h3, ih2]
      rw [hc] at hF; linarith
  · have hF := F_prime_mul_not_dvd p k hp hpk
    have ih1 := ih k hkn hk0
    rcases hχ with ⟨h2, hc⟩ | ⟨h1, hc⟩ | ⟨h3, hc⟩
    · subst h2
      rw [R_two_mul, ih1, hF, hc]; ring
    · rw [R_one_not_dvd p hp h1 k hpk, hF, hc]; push_cast; rw [ih1]; ring
    · rw [R_three_not_dvd p hp h3 k hpk, hF, hc]; ring

end TwoSquares

open TwoSquares in
/-- **Jacobi's two-square theorem**: `r₂(n) = 4 ∑_{d ∣ n} χ₋₄(d)` for `n > 0`. -/
theorem card_sq_add_sq (n : ℕ) (hn : 0 < n) :
    (Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = n} : ℤ) =
      4 * ∑ d ∈ n.divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) := by
  rw [card_eq_R]; exact R_eq_four_mul_F n hn

/-! ### Sanity checks -/

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = 5} = 8 := by
  have h := card_sq_add_sq 5 (by norm_num)
  have hs : ∑ d ∈ (5 : ℕ).divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) = 2 := by decide
  rw [hs] at h
  exact_mod_cast h

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = 3} = 0 := by
  have h := card_sq_add_sq 3 (by norm_num)
  have hs : ∑ d ∈ (3 : ℕ).divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) = 0 := by decide
  rw [hs] at h
  exact_mod_cast h

example : Nat.card {p : ℤ × ℤ // p.1 ^ 2 + p.2 ^ 2 = 25} = 12 := by
  have h := card_sq_add_sq 25 (by norm_num)
  have hs : ∑ d ∈ (25 : ℕ).divisors, (ZMod.χ₄ (d : ZMod 4) : ℤ) = 3 := by decide
  rw [hs] at h
  exact_mod_cast h

end Fugue
