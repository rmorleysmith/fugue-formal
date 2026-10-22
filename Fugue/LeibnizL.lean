import Mathlib

set_option autoImplicit false

open Filter Topology Real

namespace Fugue

/-- The nontrivial Dirichlet character mod 4, as a complex-valued character. -/
noncomputable def χ₄' : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma χ₄'_apply (a : ZMod 4) : χ₄' a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

lemma χ₄'_ne_one : χ₄' ≠ 1 := by
  intro h
  have h3 : IsUnit (3 : ZMod 4) := by decide
  have := congrArg (fun χ : DirichletCharacter ℂ 4 => χ 3) h
  simp only [MulChar.one_apply h3, χ₄'_apply] at this
  have h' : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [h'] at this
  norm_num at this

/-- The paired Leibniz terms. -/
noncomputable def a (k : ℕ) (s : ℝ) : ℝ := (4 * k + 1 : ℝ) ^ (-s) - (4 * k + 3 : ℝ) ^ (-s)

lemma leibniz_pair (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i / (2 * i + 1) =
      ∑ j ∈ Finset.range k, (1 / (4 * j + 1 : ℝ) - 1 / (4 * j + 3)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    rw [pow_succ, pow_mul]
    push_cast
    ring

lemma a_one (k : ℕ) : a k 1 = 1 / (4 * k + 1 : ℝ) - 1 / (4 * k + 3) := by
  simp [a, Real.rpow_neg_one]

lemma a_nonneg (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ a k s := by
  unfold a
  rw [sub_nonneg]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

lemma hasSum_a_one : HasSum (fun k => a k 1) (π / 4) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => a_nonneg k zero_le_one)]
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_id.const_mul_atTop' two_pos
  have := Real.tendsto_sum_pi_div_four.comp h2
  refine this.congr fun k => ?_
  simp only [Function.comp_apply, leibniz_pair, a_one]

lemma a_le (k : ℕ) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    a k s ≤ 8 / ((k : ℝ) + 1) ^ 2 := by
  set x : ℝ := 4 * k + 1 with hx
  set y : ℝ := 4 * k + 3 with hy
  have hx1 : 1 ≤ x := by rw [hx]; have : (0:ℝ) ≤ k := k.cast_nonneg; linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by rw [hy]; positivity
  have hxy : x / y ≤ 1 := by rw [div_le_one hy0, hx, hy]; linarith
  have hxy0 : 0 < x / y := div_pos hx0 hy0
  have key : y ^ (-s) = x ^ (-s) * (x / y) ^ s := by
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le, Real.div_rpow hx0.le hy0.le]
    have : 0 < x ^ s := Real.rpow_pos_of_pos hx0 s
    field_simp
  have h1 : (x / y) ^ (2 : ℝ) ≤ (x / y) ^ s :=
    Real.rpow_le_rpow_of_exponent_ge hxy0 hxy hs2
  have h2 : x ^ (-s) ≤ x ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : 0 ≤ x ^ (-s) := (Real.rpow_pos_of_pos hx0 _).le
  have h4 : (x / y) ^ s ≤ 1 := Real.rpow_le_one hxy0.le hxy (by linarith)
  have e : a k s = x ^ (-s) * (1 - (x / y) ^ s) := by
    simp only [a]; rw [← hx, ← hy, key]; ring
  rw [e]
  calc x ^ (-s) * (1 - (x / y) ^ s) ≤ x ^ (-1 : ℝ) * (1 - (x / y) ^ (2 : ℝ)) := by
        apply mul_le_mul h2 (by linarith) (by linarith) (by positivity)
    _ = 4 * (x + 1) / (x * y ^ 2) := by
        rw [Real.rpow_neg_one, Real.rpow_two, hx, hy]; field_simp; ring
    _ ≤ 8 / ((k : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hk : (0:ℝ) ≤ k := k.cast_nonneg
        rw [hx, hy]
        nlinarith [mul_nonneg hk hk, mul_nonneg (mul_nonneg hk hk) hk,
          mul_nonneg (mul_nonneg hk hk) (mul_nonneg hk hk)]

lemma summable_bound : Summable (fun k : ℕ => 8 / ((k : ℝ) + 1) ^ 2) := by
  have := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 8
  have := (summable_nat_add_iff 1).mpr this
  refine this.congr fun k => ?_
  push_cast; ring

lemma tendsto_tsum_a :
    Tendsto (fun s : ℝ => ∑' k, a k s) (𝓝[>] 1) (𝓝 (π / 4)) := by
  rw [← hasSum_a_one.tsum_eq]
  apply tendsto_tsum_of_dominated_convergence summable_bound
  · intro k
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun s : ℝ => a k s) := by
      unfold a
      apply Continuous.sub
      · exact (continuous_const.rpow continuous_neg fun _ => Or.inl (by positivity))
      · exact (continuous_const.rpow continuous_neg fun _ => Or.inl (by positivity))
    exact hc.tendsto 1
  · have : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT one_lt_two
    filter_upwards [this] with s hs k
    rw [Real.norm_eq_abs, abs_of_nonneg (a_nonneg k (by linarith [hs.1]))]
    exact a_le k hs.1.le hs.2.le

end Fugue
