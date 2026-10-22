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

lemma χ₄'_nat (n : ℕ) :
    χ₄' (n : ZMod 4) = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [χ₄'_apply, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> simp

lemma term_even (s : ℂ) (n : ℕ) (hn : n % 2 = 0) :
    LSeries.term (fun n : ℕ => χ₄' n) s n = 0 := by
  rw [LSeries.term_def]; split_ifs <;> simp [χ₄'_nat, hn]

lemma term_one (s : ℝ) (m : ℕ) :
    LSeries.term (fun n : ℕ => χ₄' n) s (1 + 4 * m) = (((4 * m + 1 : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [LSeries.term_def, ite_eq_right (by omega), χ₄'_nat, ite_eq_right (by omega), ite_eq_left (by omega),
    Real.rpow_neg (by positivity), Complex.ofReal_inv, Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

lemma term_three (s : ℝ) (m : ℕ) :
    LSeries.term (fun n : ℕ => χ₄' n) s (3 + 4 * m) = -(((4 * m + 3 : ℝ) ^ (-s) : ℝ) : ℂ) := by
  rw [LSeries.term_def, ite_eq_right (by omega), χ₄'_nat, ite_eq_right (by omega), ite_eq_right (by omega),
    Real.rpow_neg (by positivity), Complex.ofReal_inv, Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

lemma summable_shift (s : ℝ) (hs : 1 < s) (r : ℕ) (hr : 0 < r) :
    Summable (fun m : ℕ => (4 * m + r : ℝ) ^ (-s)) := by
  have h := (Real.summable_nat_rpow_inv.mpr hs).comp_injective
    (show Function.Injective (fun m : ℕ => 4 * m + r) from fun a b h => by simp at h; omega)
  refine h.congr fun m => ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_neg (by positivity)]
  push_cast; ring_nf

lemma LFunction_eq_tsum_a (s : ℝ) (hs : 1 < s) :
    DirichletCharacter.LFunction χ₄' s = ((∑' k, a k s : ℝ) : ℂ) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs', LSeries,
    Nat.sumByResidueClasses (ZMod.LSeriesSummable_of_one_lt_re _ hs') 4]
  change ∑ j : Fin 4, ∑' m : ℕ, LSeries.term (fun x => χ₄' x) s ((j : ℕ) + 4 * m) = _
  rw [Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl]
  have h0 : ∀ m : ℕ, LSeries.term (fun x : ℕ => χ₄' x) s (4 * m) = 0 :=
    fun m => term_even _ _ (by omega)
  have h2 : ∀ m : ℕ, LSeries.term (fun x : ℕ => χ₄' x) s (2 + 4 * m) = 0 :=
    fun m => term_even _ _ (by omega)
  simp only [h0, h2, term_one, term_three, tsum_zero,
    zero_add, add_zero, tsum_neg, ← Complex.ofReal_tsum]
  rw [← sub_eq_add_neg, ← Complex.ofReal_sub, ← Summable.tsum_sub]
  · rfl
  · exact_mod_cast summable_shift s hs 1 one_pos
  · exact_mod_cast summable_shift s hs 3 (by norm_num)

/-- **Leibniz / class number formula for `ℚ(i)`**: `L(1, χ₋₄) = π / 4`. -/
theorem LFunction_chi4_one :
    DirichletCharacter.LFunction (χ₄' : DirichletCharacter ℂ 4) 1 = (Real.pi / 4 : ℂ) := by
  have hcont : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ₄' (s : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ₄' 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have := ((DirichletCharacter.differentiable_LFunction χ₄'_ne_one).continuous.comp
      Complex.continuous_ofReal).tendsto 1
    simpa [Function.comp_def] using this
  have hlim : Tendsto (fun s : ℝ => DirichletCharacter.LFunction χ₄' (s : ℂ)) (𝓝[>] 1)
      (𝓝 ((π / 4 : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp tendsto_tsum_a
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (LFunction_eq_tsum_a s hs).symm
  have := tendsto_nhds_unique hcont hlim
  rw [this]; push_cast; rfl

end Fugue
